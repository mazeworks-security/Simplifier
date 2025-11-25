using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public static class DagRustFormatter
    {
        public static string Format(AstCtx ctx, AstIdx idx)
        {
            var sb = new StringBuilder();
            Format(sb, ctx, idx, new());
            return sb.ToString();
        }

        private static void Format(StringBuilder sb, AstCtx ctx, AstIdx idx, Dictionary<AstIdx, int> valueNumbers)
        {
            // Allocate value numbers for the operands if necessary
            var opc = ctx.GetOpcode(idx);
            var opcount = GetOpCount(opc);
            if (opcount >= 1 && !valueNumbers.ContainsKey(ctx.GetOp0(idx)) && !IsConstOrSymbol(ctx, ctx.GetOp0(idx)))
                Format(sb, ctx, ctx.GetOp0(idx), valueNumbers);
            if (opcount >= 2 && !valueNumbers.ContainsKey(ctx.GetOp1(idx)) && !IsConstOrSymbol(ctx, ctx.GetOp1(idx)))
                Format(sb, ctx, ctx.GetOp1(idx), valueNumbers);

            var op0 = () => $"{Lookup(ctx, ctx.GetOp0(idx), valueNumbers)}";
            var op1 = () => $"{Lookup(ctx, ctx.GetOp1(idx), valueNumbers)}";

            var vNum = valueNumbers.Count;
            valueNumbers.Add(idx, vNum);
            var width = ctx.GetWidth(idx);

            var tName = $"u{width}";

            if (opc == AstOp.Symbol)
                sb.AppendLine($"let t{vNum} = ctx.arena.symbol_with_name({ctx.GetSymbolName(idx)}, {width})");
            else if (opc == AstOp.Constant)
                sb.AppendLine($"let t{vNum} = {ctx.GetConstantValue(idx)}");
            else if (opc == AstOp.Neg)
                sb.AppendLine($"let t{vNum} = ctx.arena.neg({op0()})");
            else if (opc == AstOp.Zext || opc == AstOp.Trunc)
            {
                sb.AppendLine($"i{width} t{vNum} = {GetOperatorName(opc)} i{ctx.GetWidth(ctx.GetOp0(idx))} {op0()} to i{width}");
            }
            else
            {
                sb.AppendLine($"i{width} t{vNum} = {op0()} {GetOperatorName(opc)} {op1()}");
            }
        }

        private static bool IsConstOrSymbol(AstCtx ctx, AstIdx idx)
            => ctx.GetOpcode(idx) == AstOp.Constant || ctx.GetOpcode(idx) == AstOp.Symbol;

        private static string Lookup(AstCtx ctx, AstIdx idx, Dictionary<AstIdx, int> valueNumbers)
        {
            var opc = ctx.GetOpcode(idx);
            if (opc == AstOp.Constant)
                return ctx.GetConstantValue(idx).ToString();
            if (opc == AstOp.Symbol)
                return ctx.GetSymbolName(idx);
            return $"t{valueNumbers[idx]}";
        }

        private static int GetOpCount(AstOp opc)
        {
            return opc switch
            {
                AstOp.None => 0,
                AstOp.Add => 2,
                AstOp.Mul => 2,
                AstOp.Pow => 2,
                AstOp.And => 2,
                AstOp.Or => 2,
                AstOp.Xor => 2,
                AstOp.Neg => 1,
                AstOp.Lshr => 2,
                AstOp.Constant => 0,
                AstOp.Symbol => 0,
                AstOp.Zext => 1,
                AstOp.Trunc => 1,
            };
        }

        private static string GetOperatorName(AstOp opc)
        {
            return opc switch
            {
                AstOp.Add => "+",
                AstOp.Mul => "*",
                AstOp.Pow => "**",
                AstOp.And => "&",
                AstOp.Or => "|",
                AstOp.Xor => "^",
                AstOp.Neg => "~",
                AstOp.Lshr => ">>",
                AstOp.Zext => "zext",
                AstOp.Trunc => "trunc",
                _ => throw new InvalidOperationException(),
            };
        }
    }
}
