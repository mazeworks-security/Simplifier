using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization.Factoring
{
    public static class BoolExprFormatter
    {
        public static string FormatAst(BoolCtx ctx, ExprId id)
        {
            var sb = new StringBuilder();
            FormatInternal(ctx, id, ref sb);
            return sb.ToString();
        }

        private static void FormatInternal(BoolCtx ctx, ExprId id, ref StringBuilder sb)
        {
            var node = ctx.Get(id);
            switch (node.Kind)
            {
                case ExprKind.Var:
                    sb.Append(ctx.GetVarName(node));
                    break;
                case ExprKind.Const:
                    sb.Append(ctx.GetConstValue(node));
                    break;
                case ExprKind.Add:
                case ExprKind.Mul:
                    sb.Append("(");

                    for (int i = 0; i < node.Children.Count; i++)
                    {
                        FormatInternal(ctx, node.Children[i], ref sb);
                        if (i != node.Children.Count - 1)
                            sb.Append(GetOperatorName(node.Kind));
                    }


                    sb.Append(")");
                    break;
                default:
                    throw new InvalidOperationException();
            }
        }

        private static string GetOperatorName(ExprKind exprKind)
        {
            return exprKind switch
            {
                ExprKind.Add => "+",
                ExprKind.Mul => "*",
                _ => throw new InvalidOperationException($"Unrecognized operator: {exprKind}")
            };
        }
    }
}
