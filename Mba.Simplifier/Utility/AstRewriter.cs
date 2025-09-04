using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public static class AstRewriter
    {
        public static AstIdx ChangeBitwidth(AstCtx ctx, AstIdx node, uint newWidth, Dictionary<AstIdx, AstIdx> cache)
        {
            // We are working with DAGs, so we need a cache to avoid exponentially visiting nodes with high sharing.
            if (cache.TryGetValue(node, out var existing))
                return existing;

            var opcode = ctx.GetOpcode(node);
            var op0 = () => ChangeBitwidth(ctx, ctx.GetOp0(node), newWidth, cache);
            var binop = () => ctx.Binop(opcode, ChangeBitwidth(ctx, ctx.GetOp0(node), newWidth, cache), ChangeBitwidth(ctx,ctx.GetOp1(node), newWidth, cache));

            if (opcode == AstOp.Trunc)
            {
                var v0 = op0();
                var w = ctx.GetWidth(v0);
                // If the width is now the same, do nothing.
                if (w == newWidth)
                    return v0;
                if (w > newWidth)
                    return ctx.Zext(v0, (byte)newWidth);
                return ctx.Trunc(v0, (byte)newWidth);
            }

            if (opcode == AstOp.Zext)
            {
                var v0 = op0();
                var w = ctx.GetWidth(v0);
                // If the width is now the same, do nothing.
                if (w == newWidth)
                    return v0;
                if (w > newWidth)
                    return ctx.Zext(v0, (byte)newWidth);
                return ctx.Trunc(v0, (byte)newWidth);
            }

            var result = opcode switch
            {
                AstOp.Add => binop(),
                AstOp.Mul => binop(),
                AstOp.Pow => binop(),
                AstOp.And => binop(),
                AstOp.Or => binop(),
                AstOp.Xor => binop(),
                AstOp.Neg => ctx.Neg(op0()),
                // For lshrs we can't truncate any before, because the high bits may now effect the low bits!
                AstOp.Lshr => ctx.Trunc(node, (byte)newWidth),
                AstOp.Constant => ctx.Constant(ctx.GetConstantValue(node), newWidth),
                AstOp.Symbol => ResizeValue(ctx, node, (byte)newWidth),
                _ => throw new InvalidOperationException($"Cannot change width of opcode {opcode}"),
            };

            cache.Add(node, result);
            return result;
        }

        private static AstIdx ResizeValue(AstCtx ctx, AstIdx node, byte target)
        {
            var w = ctx.GetWidth(node);
            if (w == target)
                return node;
            if (w > target)
                return ctx.Trunc(node, target);
            else
                return ctx.Zext(node, target);
        }
    }
}
