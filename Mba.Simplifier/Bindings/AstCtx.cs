using Mba.Interop;
using Mba.Common.Interop;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using Mba.Utility;

namespace Mba.Simplifier.Bindings
{
    public struct OpaqueAstCtx { }

    public enum AstOp : byte
    {
        None = 0,
        Add = 1,
        Mul = 2,
        Pow = 3,
        And = 4,
        Or = 5,
        Xor = 6,
        Neg = 7,
        Constant = 8,
        Symbol = 9,
        Zext = 10,
    }

    public class AstCtx
    {
        private readonly nint handle;

        public AstCtx(nint handle)
        {
            this.handle = handle;
        }

        public unsafe AstCtx()
        {
            handle = (nint)Api.CreateContext();
        }

        public unsafe void Clear() => Api.ContextClear(this);

        // Constructors
        public unsafe AstIdx Add(AstIdx a, AstIdx b) => Api.ContextAdd(this, a, b);
        public unsafe AstIdx Mul(AstIdx a, AstIdx b) => Api.ContextMul(this, a, b);
        public unsafe AstIdx Pow(AstIdx a, AstIdx b) => Api.ContextPow(this, a, b);
        public unsafe AstIdx And(AstIdx a, AstIdx b) => Api.ContextAnd(this, a, b);
        public unsafe AstIdx Or(AstIdx a, AstIdx b) => Api.ContextOr(this, a, b);
        public unsafe AstIdx Xor(AstIdx a, AstIdx b) => Api.ContextXor(this, a, b);
        public unsafe AstIdx Neg(AstIdx a) => Api.ContextNeg(this, a);
        public unsafe AstIdx Zext(AstIdx a, byte width) => Api.ContextZext(this, a, width);
        public unsafe AstIdx Constant(ulong c, byte width) => Api.ContextConstant(this, c, width);
        public unsafe AstIdx Constant(ulong c, uint width) => Api.ContextConstant(this, c, (byte)width);
        public unsafe AstIdx Symbol(string s, byte width) => Api.ContextSymbol(this, new MarshaledString(s), width);

        public AstIdx Binop(AstOp opcode, AstIdx a, AstIdx b)
        {
            return opcode switch
            {
                AstOp.Add => Add(a, b),
                AstOp.Mul => Mul(a, b),
                AstOp.Pow => Pow(a, b),
                AstOp.And => And(a, b),
                AstOp.Or => Or(a, b),
                AstOp.Xor => Xor(a, b),
                _ => throw new NotImplementedException(),
            };
        }

        public AstIdx Add(IEnumerable<AstIdx> nodes)
        {
            var initial = nodes.First();
            foreach (var node in nodes.Skip(1))
            {
                initial = Add(initial, node);
            }

            return initial;
        }

        public AstIdx And(IEnumerable<AstIdx> nodes)
        {
            var initial = nodes.First();
            foreach (var node in nodes.Skip(1))
            {
                initial = And(initial, node);
            }

            return initial;
        }

        public AstIdx Or(IEnumerable<AstIdx> nodes)
        {
            var initial = nodes.First();
            foreach (var node in nodes.Skip(1))
            {
                initial = Or(initial, node);
            }

            return initial;
        }

        // Getters
        public unsafe AstOp GetOpcode(AstIdx id) => Api.ContextGetOpcode(this, id);
        public unsafe byte GetWidth(AstIdx id) => Api.ContextGetWidth(this, id);
        public unsafe uint GetCost(AstIdx id) => Api.ContextGetCost(this, id);
        public unsafe bool GetHasPoly(AstIdx id) => Api.ContextGetHasPoly(this, id);
        public unsafe AstClassification GetClass(AstIdx id) => Api.ContextGetClass(this, id);
        public unsafe AstIdx GetOp0(AstIdx id) => Api.ContextGetOp0(this, id);
        public unsafe AstIdx GetOp1(AstIdx id) => Api.ContextGetOp1(this, id);
        public unsafe ulong GetConstantValue(AstIdx id) => Api.ContextGetConstantValue(this, id);

        public unsafe bool IsConstant(AstIdx id) => GetOpcode(id) == AstOp.Constant;
        public unsafe bool IsAdd(AstIdx id) => GetOpcode(id) == AstOp.Add;

        public unsafe ulong? TryGetConstantValue(AstIdx idx)
        {
            var opcode = GetOpcode(idx);
            if (opcode != AstOp.Constant)
                return null;

            return GetConstantValue(idx);
        }
        public unsafe string GetSymbolName(AstIdx id) => StringMarshaler.AcquireString(Api.ContextGetSymbolName(this, id));

        // Utility:
        public unsafe AstIdx ParseAstString(string astStr) => Api.ContextParseAstString(this, new MarshaledString(astStr));
        public unsafe string GetAstString(AstIdx id) => StringMarshaler.AcquireString(Api.ContextGetAstString(this, id));

        // Get a unique list of all input variables, sorted in alphabetical order.
        public unsafe List<AstIdx> CollectVariables(AstIdx id)
        {
            var vec = new List<AstIdx>();
            CollectVariables(id, vec);
            return vec;
        }

        // Get a unique list of all input variables, sorted in alphabetical order.
        public unsafe IReadOnlyList<AstIdx> CollectVariables(AstIdx id, List<AstIdx> vec)
        {
            ulong len = 0;
            var ptr = Api.ContextCollectVariables(this, id, &len);
            var capacity = (int)len;
            for (int i = 0; i < capacity; i++)
            {
                // Get a ptr to the elem at this idx.
                var pItem = &ptr[i];

                // Push the variable.
                var value = *pItem;
                vec.Add(value);
            }

            return vec;
        }

        // Evaluate the AST for all possible combinations of zeroes and ones.
        // Note that this method orders the input variables alphabetically, with the same ordering returned by CollectVariables.
        public unsafe ulong[] EvaluateForZeroesAndOnes(AstIdx id, ulong mask)
        {
            ulong len = 0;
            var ptr = Api.ContextEvaluateForAllZeroesAndOnes(this, id, mask, &len);

            var capacity = (int)len;
            var vec = new ulong[capacity];
            for (int i = 0; i < capacity; i++)
            {
                // Get a ptr to the elem at this idx.
                var pItem = &ptr[i];

                // Push the variable.
                var value = *pItem;
                vec[i] = value;
            }

            return vec;
        }

        public unsafe void JitEvaluate(AstIdx id, ulong mask, bool isMultibit, uint bitWidth, AstIdx[] variables, ulong numCombinations, nint rwxPagePtr, nint outputArrayPtr)
        {
            fixed (AstIdx* arrPtr = &variables[0])
            {
                Api.ContextJit(this, id, mask, isMultibit ? 1u : 0, bitWidth, arrPtr, (ulong)variables.Length, numCombinations, (ulong*)rwxPagePtr, (ulong*)outputArrayPtr);
            }
        }

        // Apply recursive term rewriting via ISLE.
        public unsafe AstIdx RecursiveSimplify(AstIdx id) => Api.ContextRecursiveSimplify(this, id);

        public unsafe static implicit operator OpaqueAstCtx*(AstCtx ctx) => (OpaqueAstCtx*)ctx.handle;

        public unsafe static implicit operator AstCtx(OpaqueAstCtx* ctx) => new AstCtx((nint)ctx);

        protected static class Api
        {
            [DllImport("eq_sat")]
            public unsafe static extern OpaqueAstCtx* CreateContext();

            [DllImport("eq_sat")]
            public unsafe static extern void ContextClear(OpaqueAstCtx* ctx);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextAdd(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextMul(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextPow(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextAnd(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextOr(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextXor(OpaqueAstCtx* ctx, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextNeg(OpaqueAstCtx* ctx, AstIdx a);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextZext(OpaqueAstCtx* ctx, AstIdx a, byte width);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextConstant(OpaqueAstCtx* ctx, ulong c, byte width);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextSymbol(OpaqueAstCtx* ctx, sbyte* name, byte width);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern AstOp ContextGetOpcode(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern byte ContextGetWidth(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern uint ContextGetCost(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            [return: MarshalAs(UnmanagedType.U1)]
            public unsafe static extern bool ContextGetHasPoly(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern AstClassification ContextGetClass(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern AstIdx ContextGetOp0(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern AstIdx ContextGetOp1(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            [SuppressGCTransition]
            public unsafe static extern ulong ContextGetConstantValue(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            public unsafe static extern sbyte* ContextGetSymbolName(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextParseAstString(OpaqueAstCtx* ctx, sbyte* astStr);

            [DllImport("eq_sat")]
            public unsafe static extern sbyte* ContextGetAstString(OpaqueAstCtx* ctx, AstIdx id);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx* ContextCollectVariables(OpaqueAstCtx* ctx, AstIdx id, ulong* outLen);

            [DllImport("eq_sat")]
            public unsafe static extern ulong* ContextEvaluateForAllZeroesAndOnes(OpaqueAstCtx* ctx, AstIdx id, ulong mask, ulong* outLen);

            [DllImport("eq_sat")]
            public unsafe static extern ulong* ContextJit(OpaqueAstCtx* ctx, AstIdx id, ulong mask, uint isMultiBit, uint bitWidth, AstIdx* variableArray, ulong varCount, ulong numCombinations, ulong* rwxJitPage, ulong* outputArray);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx ContextRecursiveSimplify(OpaqueAstCtx* ctx, AstIdx id);
        }
    }
}
