using Bitwuzla;
using Mba.Common.Ast;
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
            var op2 = () => Translate(ctx.GetOp2(idx));

            var icmp = (Predicate kind) =>
            {
                return kind switch
                {
                    Predicate.Eq => BitwuzlaKind.BITWUZLA_KIND_EQUAL,
                   // Predicate.Ne => BitwuzlaKind.Eq,
                    Predicate.Ugt => BitwuzlaKind.BITWUZLA_KIND_BV_UGT,
                    Predicate.Uge => BitwuzlaKind.BITWUZLA_KIND_BV_UGE,
                    Predicate.Ult => BitwuzlaKind.BITWUZLA_KIND_BV_ULT,
                    Predicate.Ule => BitwuzlaKind.BITWUZLA_KIND_BV_ULE,
                    Predicate.Sgt => throw new NotImplementedException(),
                    Predicate.Sge => throw new NotImplementedException(),
                    Predicate.Slt => throw new NotImplementedException(),
                    Predicate.Sle => throw new NotImplementedException(),
                };
            };

            var opcode = ctx.GetOpcode(idx);
            Term ast = opcode switch
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
                AstOp.Select => z3Ctx.MkIte(op0(), op1(), op2()),
                AstOp.ICmp => ToBv(z3Ctx.MkTerm(icmp(ctx.GetPredicate(idx)), op0(), op1())),
                AstOp.Zext => z3Ctx.MkZext((uint)ctx.GetWidth(idx) - ctx.GetWidth(ctx.GetOp0(idx)), op0()),
                _ => throw new InvalidOperationException(),
            };

            cache[idx] = ast;
            return ast;
        }

        private Term ToBv(Term term, uint width = 1)
            => z3Ctx.MkIte(term, z3Ctx.MkBvValue(1, width), z3Ctx.MkBvValue(0, width));
    }
}
