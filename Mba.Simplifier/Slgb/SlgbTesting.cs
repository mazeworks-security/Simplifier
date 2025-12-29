using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Minimization;
using Mba.Simplifier.Utility;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Slgb
{
    public static class SlgbTesting
    {
        public static void Run()
        {
            var ctx = new AstCtx();

            Globs.Width = 8;
            Globs.ModuloMask = (ulong)ModuloReducer.GetMask((uint)Globs.Width);

            var width = (uint)Globs.Width;

            var str = "((((x&7)^(y&3)))|(z&3))";
            str = "((((x&103)^(y&115)))|(z&174))";

            str = "x0|x1|x2|c3";

            //str = "((((x&7)^(y&3)))|(z&3))";
            var boolean = RustAstParser.Parse(ctx, str, width);


            var variables = ctx.CollectVariables(boolean);
            var ttSize = (int)Math.Pow(2, variables.Count);

            var vector = new ulong[width * ttSize];

            // Compute a multi-bit truth table for this boolean
            int arrIdx = 0;
            for (ushort bitIndex = 0; bitIndex < width; bitIndex++)
            {
                for (int i = 0; i < ttSize; i++)
                {
                    // Compute the value of each variable
                    var vMap = new Dictionary<AstIdx, ulong>();
                    for (uint v = 0; v < variables.Count; v++)
                    {
                        // Compute the value of variable `v` for the input combination specified by `i`
                        var varValue = (i & (1 << (ushort)v)) == 0 ? 0ul : 1ul;
                        varValue <<= bitIndex;

                        vMap[variables[(int)v]] = varValue;
                    }

                    var eval = Eval(ctx, boolean, vMap);
                    vector[arrIdx] = eval >> bitIndex;
                    arrIdx++;
                }
            }

            // Convert each row to ANF...
            // Actually we don't want this, it just converts each individual bit pos to ANF..
            /*
            for (ushort bitIndex = 0; bitIndex < width; bitIndex++)
            {
                // Convert this to ANF.
                var start = bitIndex * ttSize;
                var list = vector.Skip(start).Take(ttSize).ToArray();
                ToAnf(variables.Count, list);

                Array.Copy(list, 0, vector, start, ttSize);
            }
            */

            // Instead we want a normal truth table with 64 bits per entry, to store the bitmask...
            arrIdx = 0;
            var withMasks = new ulong[ttSize];
            for (ushort bitIndex = 0; bitIndex < width; bitIndex++)
            {
                for (int i = 0; i < ttSize; i++)
                {
                    withMasks[i] |= (vector[arrIdx] << bitIndex);
                    arrIdx++;
                }
            }

            var polys = new List<(ulong, List<uint>)>();
            for (int i = 0; i < withMasks.Length; i++)
            {
                if (withMasks[i] == 0)
                    continue;

                var monoms = SlgbCalculator.GetRowAnf(variables.Count, i);
                polys.Add((withMasks[i], monoms));
            }


            var system = polys.Select(x => new Polynomial(x.Item2.Select(y => Monomial.CreateProduct(x.Item1, y)).ToList()))
                .ToList();

            var calc = new SlgbCalculator();
            var gb = calc.Buchberger(system);


            var optimized = SlgbCalculator.Optimize(gb);

            var gb2 = calc.Buchberger(optimized);
            Debugger.Break();

            Debugger.Break();
        }

        

        private unsafe static void ToAnf(int varCount, ulong[] resultVec)
        {
            var variableCombinations = MultibitSiMBA.GetVariableCombinations(varCount);

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            var groupSizes = MultibitSiMBA.GetGroupSizes(varCount);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var comb = variableCombinations[i];
                var myIndex = MultibitSiMBA.GetGroupSizeIndex(groupSizes, comb);
                combToMaskAndIdx.Add((comb, (int)myIndex));
            }

            bool onlyOneVar = varCount == 1;
            int width = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));
            List<int> terms = new();
            fixed (ulong* ptr = &resultVec[0])
            {
                for (int i = 0; i < variableCombinations.Length; i++)
                {
                    // Fetch the result vector index for this conjunction.
                    // If the coefficient is zero, we can skip it.
                    var comb = variableCombinations[i];
                    var (trueMask, index) = combToMaskAndIdx[i];
                    var coeff = ptr[index];
                    if (coeff == 0)
                        continue;

                    // Subtract the coefficient from the result vector.
                    MultibitSiMBA.SubtractCoeff(1, ptr, 0, coeff, index, width, varCount, onlyOneVar, trueMask);
                    terms.Add(i);
                }
            }

            foreach (var term in terms)
                if (resultVec[term + 1] != 1)
                    throw new InvalidOperationException();
        }

        private static ulong Eval(AstCtx ctx, AstIdx idx, Dictionary<AstIdx, ulong> valueMap)
        {
            var op0 = () => Eval(ctx, ctx.GetOp0(idx), valueMap);
            var op1 = () => Eval(ctx, ctx.GetOp1(idx), valueMap);

            var moduloMask = (ulong)ModuloReducer.GetMask(ctx.GetWidth(idx));
            var opc = ctx.GetOpcode(idx);
            return moduloMask & opc switch
            {
                AstOp.Constant => ctx.GetConstantValue(idx),
                AstOp.Symbol => valueMap[idx],
                AstOp.Neg => ~op0(),
                AstOp.And => op0() & op1(),
                AstOp.Or => op0() | op1(),
                AstOp.Xor => op0() ^ op1(),
                _ => throw new NotImplementedException($"")
            };
        }
    }
}
