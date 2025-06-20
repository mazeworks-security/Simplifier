using Mba.Ast;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization.Factoring
{
    public class BoolCtx
    {
        // Hash consed list of all unique nodes
        private readonly List<BoolExpr> elements = new(20000);

        // Mapping of unique nodes to their corresponding indices
        private readonly Dictionary<BoolExpr, ExprId> exprToIdx = new(20000);

        // Reduce allocations by reusing the same empty list across all childless nodes.
        private readonly List<ExprId> emptyList = new();

        public int VarCount { get; private set; } = 0;

        // Expr id of the constant 1
        public ExprId Constant1Id { get; set; }

        public BoolCtx()
        {
            Constant1Id = Constant(1);
        }

        public ExprId Var(uint varIdx)
        {
            VarCount = Math.Max(VarCount, (int)varIdx + 1);
            var vNode = new BoolExpr(ExprKind.Var, emptyList, (uint)varIdx);
            return AddExpr(vNode);
        }

        public ExprId Constant(uint constant)
        {
            // Reduce the constant modulo 2.
            constant &= 1;

            var vNode = new BoolExpr(ExprKind.Const, emptyList, constant);
            return AddExpr(vNode);
        }

        public ExprId Add(List<ExprId> children)
        {
            var output = new List<ExprId>();
            Hoist(ExprKind.Add, children, output);
            children = output;

            children = ReduceSumCoefficient(children);
            if (children.Count == 1)
                return children[0];

            children = Sort(children);

            var vNode = new BoolExpr(ExprKind.Add, children);
            return AddExpr(vNode);
        }

        private void Hoist(ExprKind kind, IReadOnlyList<ExprId> children, List<ExprId> output)
        {
            foreach(var child in children)
            {
                if (Get(child).Kind != kind)
                {
                    output.Add(child);
                    continue;
                }

                Hoist(kind, Get(child).Children, output);
            }
        }


        private List<ExprId> ReduceSumCoefficient(List<ExprId> children)
        {
            //return children;
            var output = new List<ExprId>();

            var grouped = children.GroupBy(x => x);
            foreach (var group in grouped)
            {
                var coeff = ((uint)group.Count()) & 1;
                if (coeff == 0)
                    continue;

                output.Add(group.First());
            }

            return output;
        }


        public ExprId Add(ExprId op1, ExprId op2)
          => Add(new() { op1, op2 });

        public ExprId Mul(List<ExprId> children)
        {
            var output = new List<ExprId>();
            Hoist(ExprKind.Mul, children, output);
            children = output;

            if (children.Count == 1)
                return children[0];

            //children = ReduceMulPower(children);
            children = Sort(children);
            /*
            for(int i = children.Count - 1; i >= 0; i++)
            {
                if (i == 0)
                    continue;

                var op0Id = children[i];
                var op0 = Get(op0Id);
                var op0Kind = op0.Kind;

                var op1Id = children[i - 1];
                var op1 = Get(op1Id);
                var op1Kind = op1.Kind;
            }
            */

            var vNode = new BoolExpr(ExprKind.Mul, children);
            return AddExpr(vNode);
        }

        private List<ExprId> ReduceMulPower(List<ExprId> children)
        {
            var output = new List<ExprId>();

            var grouped = children.GroupBy(x => x);
            foreach (var group in grouped)
            {
                output.Add(group.First());
                continue;
            }

            return output;
        }

        // TODO: Rewrite more performantly.
        // Attempt to canonicalize the order of operands.
        private List<ExprId> Sort(IReadOnlyList<ExprId> children)
        {
            return children.OrderBy(x => GetSort(x)).ToList(); ;
        }

        public ulong GetSort(ExprId id)
        {
            var expr = Get(id);

            ulong output = 0;

            // Constants always take priority.
            output |= ((ulong)Convert.ToUInt64(expr.Kind == ExprKind.Const)) << (ushort)63;
            // Variables take the next priority.
            output |= ((ulong)Convert.ToUInt64(expr.Kind == ExprKind.Var)) << (ushort)62;
            // Anything else, we don't care about
            output |= 0x3FFFFFFFFFFFFFFFu & (uint)id.Idx;
            return output;
        }

        public ExprId Mul(ExprId op1, ExprId op2)
        {
            var v0 = Get(op1);
            if (TryGetConstValue(op1, out var constant))
            {
                return constant == 1 ? op2 : op1;
            }
            var v1 = Get(op2);
            if (TryGetConstValue(op2, out constant))
            {
                return constant == 1 ? op1 : op2;
            }

            return Mul(new() { op1, op2 });
        }

        // ~x => x+1
        public ExprId Neg(ExprId op1)
            => Add(Constant1Id, op1);

        // x&y = x*y
        public ExprId And(ExprId op1, ExprId op2)
            => Mul(op1, op2);

        // x|y = ~((~x)*(~y))
        public ExprId Or(ExprId op1, ExprId op2)
        => Neg(Mul(Neg(op1), Neg(op2)));

        public ExprId Xor(ExprId op1, ExprId op2)
            => Add(op1, op2);

        public ExprId AddExpr(BoolExpr expr)
        {
            if (exprToIdx.TryGetValue(expr, out ExprId existingId))
                return existingId;

            var id = elements.Count;
            elements.Add(expr);
            exprToIdx[expr] = id;
            return id;
        }

        public BoolExpr Get(ExprId id)
            => elements[id];

        public ExprKind GetOpcode(ExprId id)
            => elements[id].Kind;

        public string GetVarName(BoolExpr expr)
        {
            return $"x{expr.Data}";
        }

        public uint GetVarIndex(BoolExpr expr)
            => expr.Data;

        public uint GetConstValue(BoolExpr expr)
        {
            return expr.Data;
        }

        public bool TryGetConstValue(ExprId exprId, out uint constant)
        {
            var v0 = Get(exprId);
            if (v0.Kind == ExprKind.Const)
            {
                constant = GetConstValue(v0);
                return true;
            }

            constant = 0;
            return false;
        }
    }
}
