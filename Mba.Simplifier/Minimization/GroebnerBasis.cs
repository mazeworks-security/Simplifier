using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.FastGb;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public class GroebnerBasis
    {
        private readonly TruthTable table;

        private readonly ulong[] variableCombinations;

        private readonly List<int> groupSizes;

        public static (List<List<uint>> gb, bool negated) Compute(TruthTable table) => new GroebnerBasis(table).Compute();

        private GroebnerBasis(TruthTable table)
        {
            this.table = table;
            variableCombinations = MultibitSiMBA.GetVariableCombinations(table.NumVars);
            groupSizes = MultibitSiMBA.GetGroupSizes(table.NumVars);
        }

        private unsafe (List<List<uint>> gb, bool negated) Compute()
        {
            var sb = new StringBuilder();
            sb.AppendLine("$fieldsize 2");
            sb.AppendLine($"$vars {table.NumVars} x");
            // Eliminate the nil entry if possible.
            bool negated = false;
            if(table.GetBit(0))
            {
                negated = true;
                table.Negate();
            }

            bool log = false;

            List<BoolPoly<TableSize>> newPolys = new();

            HashSet<string> allMs = new();
            // Construct a system of boolean polynomials out of the truth table(ignoring nil rows)
            var polys = new List<List<uint>>();
            for(int i = 0; i < table.NumBits; i++)
            {
                // Skip nil rows
                if (!table.GetBit(i))
                    continue;

                // If the row is positive, construct algebraic normal form for this row.
                // TODO: Use a more space / time efficienty method, 'GetRowAnf' is overkill.
                var monoms = GetRowAnf(i);

                List<string> terms = new();
                foreach (var m in monoms)
                {
                    List<string> variables = new();
                    for (int vIdx = 0; vIdx < table.NumVars; vIdx++)
                    {
                        if ((m & (1u << (ushort)vIdx)) != 0)
                        {
                            if (log)
                                variables.Add($"x{vIdx}");
                        }
                    }

                    if (log)
                    {
                        var s = String.Join("*", variables);
                        terms.Add(s);
                        allMs.Add(s);
                    }
                }

                if(log)
                    sb.AppendLine(String.Join(" + ", terms));
                //Console.WriteLine(String.Join(" + ", terms));


                var p = new BoolPoly<TableSize>();
                foreach(var m in monoms)
                {
                    p.SetBit((int)m, true);
                }

                polys.Add(monoms);
                newPolys.Add(p);
            }

            /*
            List<string> sPolys = new();
            foreach(var poly in polys)
            {
                List<string> monomials = new();
                foreach(var m in poly)
                {
                    var vs = new List<string>();
                    for(ushort i = 0; i < (ushort)table.NumVars; i++)
                    {
                        if ((m & (1 << i)) != 0)
                            vs.Add("x" + i.ToString());
                    }

                    monomials.Add(String.Join("*", vs)); 
                }

                sPolys.Add(String.Join(" + ", monomials));
            }


            var rr = String.Join(", ", sPolys);

            Console.WriteLine("\n");
            Console.WriteLine(rr);
            */

            File.WriteAllText("system.in", sb.ToString());

            foreach (var poly in newPolys)
            {
                poly.UpdateLm();
            }


            //Console.WriteLine("SORTING");
            //newPolys = newPolys.OrderByDescending(x => x).ToList();
            // Compute Lm so we don't have to do this again..
  
            while (true)
            {
                var sw = Stopwatch.StartNew();
                for (int i = 0; i < 2000; i++)
                {
                 
                    var clone = new List<BoolPoly<TableSize>>(newPolys.Count());
                    clone.Clear();
                    foreach (var p in newPolys)
                        clone.Add(p.Clone());
                    
                    var gb = new BoolGb().Buchberger(clone);
                    var gbUint = gb.Select(x => x.Monomials.Select(y => (uint)y.Index).ToList()).ToList();
                    return (gbUint, negated);
               
                }

                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms");
            }
            // Serialize the buffer to a C-compatible memory representation.
            var inBuffer = SerializeSystem(polys);

            // Construct a groebner basis
            uint* outBuffer;
            uint outSize = 0;
            fixed (uint* ptr = &inBuffer[0])
            {
                outBuffer = Api.GetGroebnerBasis((uint)table.NumVars, ptr, &outSize);
                while (false)
                {
                    var sw = Stopwatch.StartNew();
                    outBuffer = Api.GetGroebnerBasis((uint)table.NumVars, ptr, &outSize);
                    sw.Stop();

                    Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms");

                }
            }


            var groebnerBasis = DeserializeSystem(outBuffer);
            Api.FreeGroebnerBasis((nint)outBuffer);

            return (groebnerBasis, negated);
        }

        // Convert a single truth table row to algebraic normal form
        private unsafe List<uint> GetRowAnf(int idx)
        {
            var resultVec = new ulong[table.NumBits];
            resultVec[idx] = 1;

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            var groupSizes = MultibitSiMBA.GetGroupSizes(table.NumVars);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var comb = variableCombinations[i];
                var myIndex = MultibitSiMBA.GetGroupSizeIndex(groupSizes, comb);
                combToMaskAndIdx.Add((comb, (int)myIndex));
            }

            var varCount = table.NumVars;
            bool onlyOneVar = varCount == 1;
            int width = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));
            List<uint> terms = new();
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
                    terms.Add((uint)variableCombinations[i]);
                }
            }

            return terms;
        }

        private uint[] SerializeSystem(List<List<uint>> polys)
        {
            // Compute the size of the buffer
            uint wordSize = 1;
            foreach(var poly in polys)
            {
                wordSize += 1;
                wordSize += (uint)poly.Count;
            }

            // Allocate the buffer
            var buffer = new uint[wordSize];

            // Serialize the system to the buffer
            int idx = 0;
            buffer[idx] = (uint)polys.Count;
            idx += 1;
            foreach(var poly in polys)
            {
                buffer[idx] = (uint)poly.Count;
                idx += 1;
                foreach(var monom in poly)
                {
                    // Write the monomial to the buffer.
                    // MAYBE:  we need to shift all of the conjunctions up by one, because SymbSAT uses the first bit of the monomial to represent the constant offset.
                    buffer[idx] = (monom << 1);
                    //buffer[idx] = monom;
                    idx += 1;
                }
            }

            return buffer;
        }

        private unsafe List<List<uint>> DeserializeSystem(uint* outBuffer)
        {
            var system = new List<List<uint>>();

            var polyCount = *outBuffer;
            outBuffer++;

            for(int _ = 0; _ < polyCount; _++)
            {
                var monomCount = *outBuffer;
                outBuffer++;

                var poly = new List<uint>();
                for (int i = 0; i < monomCount; i++)
                {
                    var monom = *outBuffer;
                    poly.Add(monom >> 1); // Shift the conjunction down by one to account for SymbSAT's internal representation
                    outBuffer++;
                }

                system.Add(poly);
            }

            return system;
        }

        public static class Api
        {
            [DllImport("Mba.FFI")]
            public unsafe static extern uint* GetGroebnerBasis(uint numVars, uint* inBuffer, uint* outSize);

            [DllImport("Mba.FFI")]
            public unsafe static extern uint* FreeGroebnerBasis(nint buffer);
        }
    }
}
