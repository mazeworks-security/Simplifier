using Mba.Ast;
using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public class TruthTables
    {
        private IReadOnlyList<byte[]> Tables { get; }

        private readonly TruthTableDb db;

        public static readonly TruthTables Instance = new();

        private TruthTables()
        {
            Tables = new List<byte[]>()
            {
                LoadTruthTableBinary(1),
                LoadTruthTableBinary(2),
                LoadTruthTableBinary(3),
                LoadTruthTableBinary(4),
            };

            db = new TruthTableDb();
        }

        public static unsafe byte[] LoadTruthTableBinary(int numVars)
        {
            // Fetch the serialized truth table from our embedded resources.
            var path = $"{numVars}variable_truthtable.bc";
            var name = Assembly.GetExecutingAssembly().GetManifestResourceNames().Single(x => x.Contains(path));
            var stream = Assembly.GetExecutingAssembly().GetManifestResourceStream(name);
            var bytes = new byte[stream.Length];
            stream.Read(bytes, 0, bytes.Length);
            return bytes;
        }

        public unsafe AstIdx GetTableEntry(AstCtx ctx, IReadOnlyList<AstIdx> vars, int index)
        {
            return db.GetBoolean(ctx, (uint)vars.Count, vars, (ulong)index);
        }

        private static unsafe AstIdx ParseBinaryBooleanFunc(AstCtx ctx, IReadOnlyList<AstIdx> vars, byte* bytes, ref uint i)
        {
            byte opcode = bytes[i];
            i += 1;

            var binop = (AstOp opcode, ref uint i)
                => ctx.Binop(opcode, ParseBinaryBooleanFunc(ctx, vars, bytes, ref i), ParseBinaryBooleanFunc(ctx, vars, bytes, ref i));

            switch (opcode)
            {
                case 0:
                    ulong constant = *(ulong*)&bytes[i];
                    return ctx.Constant(constant, ctx.GetWidth(vars[0]));
                case 2:
                    byte idx = bytes[i];
                    i += 1;
                    return vars[idx];
                case 8:
                    return binop(AstOp.And, ref i);
                case 9:
                    return binop(AstOp.Or, ref i);
                case 10:
                    return binop(AstOp.Xor, ref i);
                case 11:
                    var a = ParseBinaryBooleanFunc(ctx, vars, bytes, ref i);
                    return ctx.Neg(a);
                // Other operators (add, mul, pow) will not be present in serialized binary truth tables.
                default:
                    throw new InvalidOperationException($"Unrecognized opcode: {opcode}");
            }
        }
    }
}
