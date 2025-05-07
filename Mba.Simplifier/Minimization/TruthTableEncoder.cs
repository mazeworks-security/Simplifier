using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    // Class for encoding tables of minimized boolean functions.
    public class TruthTableEncoder
    {
        private const int MAX_TABLES = 4;

        private const int BIT_WIDTH = 64;

        private readonly AstCtx ctx = new AstCtx();

        private List<AstIdx> variables;

        private IReadOnlyList<List<AstIdx>> inputTables;

        public void Run()
        {
            AstIdx.ctx = ctx;
            variables = Enumerable.Range(0, MAX_TABLES).Select(x => ctx.Symbol($"v{x}", BIT_WIDTH)).ToList();
            inputTables = GetInputTables(ctx, variables);

            // Write the serialized truth table to disk.
            for(int i = 0; i < inputTables.Count; i++)
            {
                var encoded = EncodeTable((uint)i + 2, inputTables[i]);
                Directory.CreateDirectory("Output");
                File.WriteAllBytes($@"Output\{i + 2}variable_truthtable.bc", encoded.ToArray());
            }
        }

        private static IReadOnlyList<List<AstIdx>> GetInputTables(AstCtx ctx, List<AstIdx> variables)
        {
            var tables = new List<List<AstIdx>>();  
            // Load all 2^t bitwise functions for each variable count
            for (int numVars = 2; numVars <= MAX_TABLES; numVars++)
            {
                var table = new List<AstIdx>();
                for (int vecIdx = 0; vecIdx < (int)Math.Pow(2, Math.Pow(2, numVars)); vecIdx++)
                {
                    var result = TableDatabase.Instance.GetTableEntry(ctx, variables.Take(numVars).ToList(), vecIdx);
                    table.Add(result);
                }

                tables.Add(table);
            }

            return tables;
        }

        private IReadOnlyList<byte> EncodeTable(uint numVars, List<AstIdx> inputTable)
        {
            var cache = new Dictionary<AstIdx, int>();

            // We want to start the table of truth tables using 2^t ulongs, where the first 4 bytes indicate the cost of the AST,
            // and the next 4 bytes indicate what offset to start deserializing the AST at.
            var buffer = new List<byte>();
            for(int tableIdx = 0; tableIdx < inputTable.Count; tableIdx++)
            {
                // Initially we set the "start deserializing index" to zero, because the serialized ASTs have a variable length.s
                EncodeUint(buffer, 0);
                EncodeUint(buffer, ctx.GetCost(inputTable[tableIdx]));
            }

            // Serialize each boolean expr
            for (int tableIdx = 0; tableIdx < inputTable.Count; tableIdx++)
            {
                // Serialize the boolean expression
                var start = Serialize(buffer, inputTable[tableIdx], cache);
                // Update the index map to point to the start of the serialized expr
                var bytes = BitConverter.GetBytes((uint)start);
                for(int byteOffset = 0; byteOffset < 4; byteOffset++)
                {
                   buffer[(tableIdx * 8) + byteOffset] = bytes[byteOffset];
                }

                // Verify that deserialization yields the same result
                var deserialized = GetTableAst(ctx, buffer, variables, (uint)tableIdx);
                if (deserialized != inputTable[tableIdx])
                    throw new InvalidOperationException("Deserialization failure!");
            }

            // Serialize each boolean expr
            for (int tableIdx = 0; tableIdx < inputTable.Count; tableIdx++)
            {
                // Verify that deserialization yields the same result
                var deserialized = GetTableAst(ctx, buffer, variables, (uint)tableIdx);
                if (deserialized != inputTable[tableIdx])
                    throw new InvalidOperationException("Deserialization failure!");

            }

            return buffer;
        }

        private int Serialize(List<byte> buffer, AstIdx idx, Dictionary<AstIdx, int> cache)
        {
            // Optionally enable sharing of DAG nodes.
            if (cache.TryGetValue(idx, out var existing))
                return existing;

            var opcode = ctx.GetOpcode(idx);
            switch(opcode)
            {
                case AstOp.Symbol:
                    var len = buffer.Count;
                    EncodeUint(buffer, GetOpcodeId(opcode));
                    EncodeUint(buffer, (byte)variables.IndexOf(idx));
                    cache[idx] = len;
                    return len;
                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                    var a = Serialize(buffer, ctx.GetOp0(idx), cache);
                    var b = Serialize(buffer, ctx.GetOp1(idx), cache);
                    var offset = buffer.Count;
                    EncodeUint(buffer, GetOpcodeId(opcode));
                    EncodeUint(buffer, (uint)a);
                    EncodeUint(buffer, (uint)b);
                    cache[idx] = offset;
                    return offset;
                case AstOp.Neg:
                    var src = Serialize(buffer, ctx.GetOp0(idx), cache);
                    var negOffset = buffer.Count;
                    EncodeUint(buffer, GetOpcodeId(opcode));
                    EncodeUint(buffer, (uint)src);
                    cache[idx] = negOffset;
                    return negOffset;
                default:
                    throw new InvalidOperationException($"Cannot encode type {opcode}");
            }
        }

        private static AstIdx GetTableAst(AstCtx ctx, List<byte> buffer, List<AstIdx> variables, uint tableIdx)
        {
            var offset = 8 * tableIdx;
            var start = DecodeUint(buffer, (int)offset);
            return Deserialize(ctx, buffer, variables, (int)start);
        }

        private static AstIdx Deserialize(AstCtx ctx, List<byte> buffer, List<AstIdx> variables, int offset)
        {
            var id = buffer[offset];
            offset += 4;

            switch(id)
            {
                case 2:
                    var symbolIdx = buffer[offset];
                    return variables[symbolIdx];
                case 8:
                case 9:
                case 10:
                    var aOffset = DecodeUint(buffer, offset);
                    offset += 4;
                    var bOffset = DecodeUint(buffer, offset);

                    var a = Deserialize(ctx, buffer, variables, (int)aOffset);

                    var b = Deserialize(ctx, buffer, variables, (int)bOffset);

                    var opcode = id switch
                    {
                        8 => AstOp.And,
                        9 => AstOp.Or,
                        10 => AstOp.Xor,
                    };

                    return ctx.Binop(opcode, a, b);

                case 11:
                    var srcOffset = DecodeUint(buffer, offset);
                    var src = Deserialize(ctx, buffer, variables, (int)srcOffset);
                    return ctx.Neg(src);

                default:
                    throw new InvalidOperationException($"Cannot deserialize opcode {id}");
            }
        }

        private static byte GetOpcodeId(AstOp opcode)
        {
            return opcode switch
            {
                AstOp.Symbol => 2,
                AstOp.And => 8,
                AstOp.Or => 9,
                AstOp.Xor => 10,
                AstOp.Neg => 11,
                _ => throw new InvalidOperationException($"Cannot encode type {opcode}")
            };
        }

        private static void EncodeByte(List<byte> buffer, byte value)
        {
            buffer.Add(value);
        }

        private static void EncodeUint(List<byte> buffer, uint value)
        {
            var bytes = BitConverter.GetBytes(value);
            buffer.AddRange(bytes);
        }

        private static uint DecodeUint(List<byte> buffer, int start)
        {
            return BitConverter.ToUInt32(buffer.Skip(start).Take(4).ToArray());
        }
    }
}
