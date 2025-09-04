using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public static class SimpleAstEvaluator
    {
        public static ulong Evaluate(AstCtx ctx, AstIdx idx, Dictionary<AstIdx, ulong> valueMap)
        {
            var op0 = () => Evaluate(ctx, ctx.GetOp0(idx), valueMap);
            var op1 = () => Evaluate(ctx, ctx.GetOp1(idx), valueMap);

            return (ulong)ModuloReducer.GetMask(ctx.GetWidth(idx)) & ctx.GetOpcode(idx) switch
            {
                AstOp.Pow => Pow(op0(), op1()),
                AstOp.Add => op0() + op1(),
                AstOp.Mul => op0() * op1(),
                AstOp.And => op0() & op1(),
                AstOp.Or => op0() | op1(),
                AstOp.Xor => op0() ^ op1(),
                AstOp.Neg => ~op0(),
                AstOp.Zext => op0(),
                AstOp.Trunc => op0(),
                AstOp.Lshr => op0() >> (ushort)op1(),
                AstOp.Constant => ctx.GetConstantValue(idx),
                AstOp.Symbol => valueMap[idx],
                _ => throw new NotImplementedException()
            };
        }

        public static ulong Pow(ulong bbase, ulong exponent)
        {
            ulong result = 1;

            for (ulong term = bbase; exponent != 0; term = term * term)
            {
                if (exponent % 2 != 0) { result *= term; }
                exponent /= 2;
            }

            return result;
        }
    }
}
