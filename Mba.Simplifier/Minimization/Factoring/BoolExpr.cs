using Mba.Simplifier.Bindings;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization.Factoring
{
    public struct ExprId
    {
        public int Idx;

        public ExprId(int idx)
        {
            Idx = idx;
        }

        public override string ToString()
        {
            if (ctx == null)
                return Idx.ToString();
            //return ctx.GetAstString(Idx);
            return BoolExprFormatter.FormatAst(ctx, Idx);
        }

        public unsafe static implicit operator int(ExprId reg) => reg.Idx;

        public unsafe static implicit operator ExprId(int reg) => new ExprId(reg);

        // This is a hack to allow viewing AST nodes in the debugger.
        public static BoolCtx ctx;
    }

    public enum ExprKind : byte
    {
        Var = 0,
        Const = 1,
        Add = 2,
        Mul = 3,
    }

    // Hash consed immutable AST structure.
    // Technically this is a DAG.
    public struct BoolExpr
    {
        public readonly ExprKind Kind;

        public readonly IReadOnlyList<ExprId> Children;

        // Optional field for variable names and constant values.
        public readonly uint Data;
        private readonly int hash;

        public BoolExpr(ExprKind exprId, List<ExprId> children, uint data = 0)
        {
            Kind = exprId;
            Children = children;
            Data = data;
            hash = CalcHash();
        }

        private int CalcHash()
        {
            int hash = 17;
            hash = hash * 23 + (int)Kind;
            foreach (var id in Children)
                hash = hash * 23 + id.GetHashCode();
            return hash;
        }

        public override int GetHashCode()
        {
            return hash;
        }

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if (obj is not BoolExpr other)
                return false;

            if (hash != other.GetHashCode() || Kind != other.Kind || Data != other.Data || Children.Count != other.Children.Count)
                return false;

            for (int i = 0; i < Children.Count; i++)
            {
                if (Children[i] != other.Children[i])
                    return false;
            }

            return true;
        }
    }
}
