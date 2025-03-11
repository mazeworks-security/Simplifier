using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public static class AstRewriter
    {
        public static AstIdx ChangeBitwidth(AstCtx ctx, AstIdx node, uint newWidth)
        {
            var opcode = ctx.GetOpcode(node);
            var binop = () => ctx.Binop(opcode, ChangeBitwidth(ctx, ctx.GetOp0(node), newWidth), ChangeBitwidth(ctx,ctx.GetOp1(node), newWidth));

            return opcode switch
            {
                AstOp.Add => binop(),
                AstOp.Mul => binop(),
                AstOp.And => binop(),
                AstOp.Or => binop(),
                AstOp.Xor => binop(),
                AstOp.Neg => ctx.Neg(ChangeBitwidth(ctx, ctx.GetOp0(node), newWidth)),
                AstOp.Constant => ctx.Constant(ctx.GetConstantValue(node) & (ulong)ModuloReducer.GetMask(newWidth), newWidth),
                AstOp.Symbol => ctx.Symbol(ctx.GetSymbolName(node), (byte)newWidth),
                _ => throw new InvalidOperationException($"Cannot change width of opcode {opcode}"),
            };
        }
    }
}
