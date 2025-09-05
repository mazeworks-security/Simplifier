using Mba.Ast;
using Mba.Simplifier.Bindings;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public class Z3Translator
    {
        private readonly AstCtx ctx;

        private readonly Context z3Ctx;

        private readonly Dictionary<AstIdx, Expr> cache = new Dictionary<AstIdx, Expr>();

        public Z3Translator(AstCtx ctx) : this(ctx, new Context())
        {
        }

        public Z3Translator(AstCtx ctx, Context z3Context)
        {
            this.ctx = ctx;
            this.z3Ctx = z3Context;
        }

        public Expr Translate(AstIdx idx)
        {
            if (cache.TryGetValue(idx, out var existing))
                return existing;

            var op0 = () => (BitVecExpr)Translate(ctx.GetOp0(idx));
            var op1 = () => (BitVecExpr)Translate(ctx.GetOp1(idx));

            var opcode = ctx.GetOpcode(idx);
            Expr z3Ast = opcode switch
            {
                AstOp.Add => z3Ctx.MkBVAdd(op0(), op1()),
                AstOp.Mul => z3Ctx.MkBVMul(op0(), op1()),
                AstOp.Pow => Power(idx),
                AstOp.And => z3Ctx.MkBVAND(op0(), op1()),
                AstOp.Or => z3Ctx.MkBVOR(op0(), op1()),
                AstOp.Xor => z3Ctx.MkBVXOR(op0(), op1()),
                AstOp.Lshr => z3Ctx.MkBVLSHR(op0(), op1()),
                AstOp.Neg => z3Ctx.MkBVNot(op0()),
                AstOp.Constant => z3Ctx.MkBV(ctx.GetConstantValue(idx), ctx.GetWidth(idx)),
                AstOp.Symbol => z3Ctx.MkBVConst(ctx.GetSymbolName(idx), ctx.GetWidth(idx)),
                AstOp.Zext => z3Ctx.MkZeroExt((uint)ctx.GetWidth(idx) - ctx.GetWidth(ctx.GetOp0(idx)), op0()),
                AstOp.Trunc => z3Ctx.MkExtract((uint)ctx.GetWidth(idx) - 1, 0, op0()),
                _ => throw new InvalidOperationException($"Cannot translate opcode {opcode} to z3!")
            };

            cache[idx] = z3Ast;
            return z3Ast;
        }

        private Expr Power(AstIdx idx)
        {
            var lhs = ctx.GetOp0(idx);
            var rhs = ctx.GetOp1(idx);
            if (!ctx.IsConstant(rhs))
                throw new InvalidOperationException($"Z3 does not support exponeniation to an unknown degree!");

            var width = ctx.GetWidth(idx);
            return Power(Translate(lhs), ctx.GetConstantValue(rhs), width);
        }

        private Expr Power(Expr x, ulong y, uint bitWidth)
        {
            if (y == 0)
                return z3Ctx.MkBV(1, bitWidth);
            if (y == 1)
                return x;

            var originalBv = x;
            for (ulong i = 0; i < y - 1; i++)
            {
                // x = x * original;
                x = z3Ctx.MkBVMul((BitVecExpr)x, (BitVecExpr)originalBv);
            }

            return x;
        }
    }
}
