using Mba.Ast;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Testing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public static class BooleanMinimizer
    {
        private const bool useLegacyMinimizer = true;


        public static Random rng = new();


        public static ulong AppendVariables(ulong truthTable, ulong numExistingVars, ulong numVarsToAdd)
        {
            ulong outTable = truthTable;
            var numOriginal = (ulong)Math.Pow(2, numExistingVars);
            var numIter = (ulong)Math.Pow(2, numExistingVars + numVarsToAdd);
            for (ulong i = 0; i < numIter; i++)
            {
                var bitIdx = i % numOriginal;
                var oldBit = (truthTable >> (ushort)bitIdx) & 1;
                outTable |= (oldBit << (ushort)i);
            }

            return outTable;
        }

        public static AstIdx GetBitwise(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable, bool negate = false)
        {
            //truthTable.arr[0] = uint.MaxValue & RandomBitGenerator.GenerateUniformWeightUInt64();
            //var other = MobiusTransform(truthTable.arr[0]);


            //var dnf2 = EspressoMinimizer.SimplifyBoolean(ctx, truthTable.AsList(), variables).ast;
            //truthTable.arr[0] = 0xc1ea5ead149dc922;
            // truthTable.arr[0] = MobiusTransform(truthTable.arr[0]);
            //truthTable.arr[0] = Transform(truthTable.arr[0]);
            var rand = new Random();

            truthTable.arr[0] = AppendVariables(truthTable.arr[0], (ulong)truthTable.NumVars, (ulong)6 - (ulong)truthTable.NumVars);
            truthTable.NumVars = 6;
            variables = variables.Concat(new List<AstIdx>() { ctx.Symbol("zzzz", ctx.GetWidth(variables[0])) }).ToList();

            var old = truthTable.arr[0];
            var og = GroebnerMinimizer.Run(ctx, variables, truthTable);
            var best = uint.MaxValue;

            while(false)
            {
                //var mask = RandomBitGenerator.GenerateUniformWeightUInt64();
                var mask = (ulong)0;
                if ((old ^ mask) == 0 || (old ^ mask) == ulong.MaxValue)
                    continue;
                if ((mask) == 0 || (mask) == ulong.MaxValue)
                    continue;
                truthTable.arr[0] = old ^ mask;
             
                var r1 = GroebnerMinimizer.Run(ctx, variables, truthTable);
                truthTable.arr[0] = mask;

                var r2 = GroebnerMinimizer.Run(ctx, variables, truthTable);

                var rr = ctx.Add(r1, r2);

                var cost = ctx.GetCost(rr);
                if(cost < best)
                {
                    best = cost;
                    Console.WriteLine($"{rr} with cost {cost} and mask {mask}");
                }
            }

            return 0;

            // If requested, negate the result vector to find a negated expression.
            if (negate)
            {
                truthTable.Negate();
            }
            //z`
            // Exit early if the boolean function is a constant.
            var asConstant = AsConstant(ctx, truthTable, ctx.GetWidth(variables[0]));
            if (asConstant != null)
                return asConstant.Value;

            if (variables.Count == 1)
            {
                return truthTable.GetBit(0) == false ? variables[0] : ctx.Neg(variables[0]);
            }

            // If there are four or less variables, we can pull the optimal representation from the truth table.
            // TODO: One could possibly construct a 5 variable truth table for all 5 variable NPN classes.
            //if (variables.Count <= 4)
            if (false)
            {
                return FromTruthTable(ctx, variables, truthTable);
            }

            // For debugging purposes we still want to keep the legacy boolean minimization logic around.
            if (useLegacyMinimizer)
            {
                // Otherwise use Espresso to compute a semi optimal version of the boolean function.
                var xnf = AnfMinimizer.SimplifyBoolean(ctx, variables, truthTable);
                var dnf = EspressoMinimizer.SimplifyBoolean(ctx, truthTable.AsList(), variables).ast;

                var c1 = LinearSimplifier.GetCost(ctx, xnf, false, 1);
                var c2 = LinearSimplifier.GetCost(ctx, dnf, false, 1);
                if (c1 < c2)
                    return xnf;
                return dnf;
            }

            // Though now we prefer to use the new minimizer implemented purely in rust. It's faster and generally yields better results.
            return ctx.MinimizeAnf(TableDatabase.Instance.db, truthTable, (List<AstIdx>)variables, MultibitSiMBA.JitPage.Value);
        }

        private static AstIdx? AsConstant(AstCtx ctx, TruthTable table, uint width)
        {
            var first = table.GetBit(0);
            for (int i = 1; i < table.NumBits; i++)
            {
                if (table.GetBit(i) != first)
                    return null;
            }

            ulong constant = first ? (ulong)ModuloReducer.GetMask(width) : 0;
            return ctx.Constant(constant, width);
        }

        public static AstIdx FromTruthTable(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
        {
            // Fetch the truth table entry corresponding to this node.
            var ast = TableDatabase.Instance.GetTableEntry(ctx, (List<AstIdx>)variables, (int)(uint)truthTable.arr[0]);
            return ast;
        }

        public static AstNode RewriteUsingNewVariables(AstNode ast, Func<VarNode, VarNode> getVar)
        {
            var op1 = () => RewriteUsingNewVariables(ast.Children[0], getVar);
            var op2 = () => RewriteUsingNewVariables(ast.Children[1], getVar);
            return ast switch
            {
                ConstNode constNode => new ConstNode(constNode.Value, ast.BitSize),
                VarNode varNode => getVar(varNode),
                PowerNode powerNode => new PowerNode(op1(), op2()),
                AddNode => new AddNode(op1(), op2()),
                MulNode mulNode => new MulNode(op1(), op2()),
                AndNode andNode => new AndNode(op1(), op2()),
                OrNode orNode => new OrNode(op1(), op2()),
                XorNode => new XorNode(op1(), op2()),
                NegNode => new NegNode(op1()),
            };
        }
    }
}
