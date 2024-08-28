using Mba.Ast;
using Mba.Interop;
using Mba.Testing;
using Mba.Common.Interop;
using Microsoft.Z3;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using Mba.Common.Utility;
using System.Reflection.Metadata.Ecma335;
using Mba.Common.Minimization;
using Mba.Simplifier.Bindings;

namespace Mba.Simplifier.Minimization
{
    public static class EspressoMinimizer
    {
        public static (AstIdx ast, List<OnOffSet> onOffs) SimplifyBoolean(AstCtx ctx, List<int> resultVector, IReadOnlyList<AstIdx> variables)
        {
            // Run espresso.
            var pla = GeneratePLA(resultVector, variables);
            var output = EspressoApi.Run(pla);

            // Parse espresso's output into a boolean function.
            return ParsePLA(ctx, output, resultVector, variables);
        }

        // Generate an instance of Espresso's file format.
        // https://user.engineering.uiowa.edu/~switchin/OldSwitching/espresso.5.html
        public static string GeneratePLA(List<int> resultVector, IReadOnlyList<AstIdx> variables)
        {
            ulong varCount = (ulong)variables.Count;
            var numCombinations = (ulong)Math.Pow(2, varCount);
            Debug.Assert(numCombinations == (ulong)resultVector.Count);

            var sb = new StringBuilder();
            sb.AppendLine($".i {varCount}");
            sb.AppendLine($".o 1");

            for (ulong i = 0; i < numCombinations; i++)
            {
                // Evaluate the ast at this combination of zeroes and ones.
                for (uint v = 0; v < varCount; v++)
                {
                    // Compute a mask for this this variable.
                    ulong varMask = (ulong)1 << (ushort)v;

                    // Compute the value of this specific variable.
                    ulong varValue = i & varMask;

                    // Shift the value back down
                    varValue = varValue >> (ushort)v;

                    // Set the variable value.
                    var node = variables[(int)v];
                    sb.Append(varValue);
                }

                // Isolate only the first bit. 
                var eval = resultVector[(int)i];
                sb.AppendLine($" {eval}");
            }
            sb.AppendLine(".e");

            return sb.ToString();
        }

        private static (AstIdx ast, List<OnOffSet> onOffs) ParsePLA(AstCtx ctx, string output, List<int> resultVector, IReadOnlyList<AstIdx> variables)
        {
            var lines = output.Split(new string[] { "\r\n", "\r", "\n" },
                StringSplitOptions.None).ToList();
            var firstIndex = lines.IndexOf(lines.Single(x => x.Contains(".p")));
            lines = lines.Skip(firstIndex + 1).TakeWhile(x => !x.StartsWith(".e")).ToList();

            var width = ctx.GetWidth(variables[0]);
            var onOff = new List<OnOffSet>();
            var terms = new List<AstIdx>();
            foreach (var line in lines)
            {
                var andClauses = new List<AstIdx>();
                var strTt = line.Split(" ", StringSplitOptions.RemoveEmptyEntries)[0];

                ulong demandedMask = 0;
                ulong dontCareMask = 0;
                for (int i = 0; i < variables.Count; i++)
                {
                    var c = strTt[i];
                    // - means don't care
                    if (c == '-')
                    {
                        dontCareMask = dontCareMask | 1u << (ushort)i;
                        continue;
                    }

                    else if (c == '0')
                    {
                        // Negated bits can be implicitly inferred using the dontcare + demanded mask.
                        andClauses.Add(ctx.Neg(variables[i]));
                    }

                    else if (c == '1')
                    {
                        demandedMask |= 1u << (ushort)i;
                        andClauses.Add(variables[i]);
                    }
                }

                onOff.Add(new(demandedMask, dontCareMask));
                var anded = ctx.And(andClauses);
                terms.Add(anded);
            }

            if (!terms.Any())
            {
                Debug.Assert(resultVector.All(x => x == 0));
                var constant = ctx.Constant(0, width);
                return (constant, onOff);
            }

            var ored = ctx.Or(terms);
            return (ored, onOff);
        }

        public static AstNode ToBoolean(IReadOnlyList<VarNode> variables, List<OnOffSet> onOffset)
        {
            List<AstNode> terms = new();
            foreach (var set in onOffset)
            {
                List<AstNode> clauses = new();
                for (int i = 0; i < variables.Count; i++)
                {
                    // Skip if the variable is not demanded.
                    ulong varMask = 1u << (ushort)i;
                    bool isDontCare = (set.DontCareMask & varMask) != 0;
                    if (isDontCare)
                        continue;

                    bool isNegated = (set.DemandedMask & varMask) == 0;
                    if (isNegated)
                        clauses.Add(new NegNode(variables[i]));
                    else
                        clauses.Add(variables[i]);
                }

                if (!clauses.Any())
                    continue;

                var anded = clauses.And();
                terms.Add(anded);
            }

            var or = terms.Or();
            return or;
        }
    }

    // Espresso FFI wrapper
    public static class EspressoApi
    {
        // Thread safe boolean simplification cache.
        private static ConcurrentDictionary<string, string> espressoCache = new();

        public static unsafe string Run(string lines)
        {
            if (espressoCache.TryGetValue(lines, out string value))
                return value;

            // Run espresso.
            var ms = new MarshaledString(lines);
            sbyte* buffer;
            run_espresso_from_data(ms, (uint)ms.Length, &buffer);
            var output = StringMarshaler.AcquireString(buffer);

            espressoCache.TryAdd(lines, output);
            return output;
        }

        [DllImport("Espresso")]
        public unsafe static extern sbyte* run_espresso_from_data(sbyte* data, uint l, sbyte** output);

        [DllImport("Espresso")]
        public unsafe static extern sbyte* run_d1merge_from_data(sbyte* data, uint l, sbyte** output);
    }
}
