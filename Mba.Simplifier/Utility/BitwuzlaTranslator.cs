using Mba.Simplifier.Bindings;
using Mba.Simplifier.Synth;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public class BitwuzlaTranslator
    {
        private readonly AstCtx ctx;

        private readonly TermManager z3Ctx;

        public readonly Dictionary<AstIdx, Term> cache = new();

        public BitwuzlaTranslator(AstCtx ctx) : this(ctx, new())
        {
            this.ctx = ctx;
        }

        public BitwuzlaTranslator(AstCtx ctx, TermManager z3Ctx)
        {
            this.ctx = ctx;
            this.z3Ctx = z3Ctx;
        }

        public Term Translate(AstIdx idx)
        {
            if (cache.TryGetValue(idx, out Term existing))
                return existing;

            var op0 = () => Translate(ctx.GetOp0(idx));
            var op1 = () => Translate(ctx.GetOp1(idx));

            var opcode = ctx.GetOpcode(idx);
            var ast = opcode switch
            {
                AstOp.Add => op0() + op1(),
                AstOp.Mul => op0() * op1(),
                AstOp.And => op0() & op1(),
                AstOp.Or => op0() | op1(),
                AstOp.Xor => op0() ^ op1(),
                AstOp.Neg => ~op0(),
                AstOp.Lshr => op0() >> op1(),
                AstOp.Constant => z3Ctx.MkBvValue(ctx.GetConstantValue(idx), ctx.GetWidth(idx)),
                AstOp.Symbol => z3Ctx.MkBvConst(ctx.GetSymbolName(idx), ctx.GetWidth(idx)),
                _ => throw new InvalidOperationException(),
            };

            cache[idx] = ast;
            return ast;
        }
    }
}
