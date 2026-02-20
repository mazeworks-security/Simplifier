using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace Mba.Simplifier.Verification
{
    public class MsolveWrapper
    {
        private readonly string msolvePath = @"C:\Users\colton\Downloads\msolve-win64\bin\msolve.exe";
        private readonly string outputFile = "out.ms";
        private readonly string inputFile = "in.ms";

        public static List<Poly> Run(List<Poly> polys)
            => new MsolveWrapper().ComputeGroebnerBasis(polys);

        private MsolveWrapper()
        {
            
        }

        public List<Poly> ComputeGroebnerBasis(List<Poly> polys)
        {
            // 1. Collect all unique variables
            var allVars = new HashSet<SymVar>();
            foreach (var p in polys)
            {
                foreach (var m in p.Coeffs.Keys)
                {
                    foreach (var v in m.SortedVars)
                    {
                        allVars.Add(v);
                    }
                }
            }
            var sortedVars = allVars.OrderBy(v => v).ToList();
            var varNames = sortedVars.Select(v => v.Name).ToList();

            // Assert that x*x == x for all boolean input variables
            // TODO: Maybe we can do this for output variables too?
            //foreach (var v in sortedVars.Where(x => x.Kind == SymKind.Input))
            // Actually I think we can do this for all variables regardless
            foreach(var v in sortedVars)
            {
                Poly m = new Monomial(v);
                polys.Add(new Monomial(v, v) - m);
            }

            if (File.Exists(inputFile))
                File.Delete(inputFile);
            // 2. Write input file
            using (var writer = new StreamWriter(inputFile))
            {
                // Variables
                writer.WriteLine(string.Join(",", varNames));

                // Characteristic (0 for rational)
                writer.WriteLine("0");

                // Polynomials
                for (int i = 0; i < polys.Count; i++)
                {
                    writer.Write(PolyToString(polys[i]));
                    if (i < polys.Count - 1)
                        writer.WriteLine(",");
                    else
                        writer.WriteLine();
                }
            }

            // 3. Invoke msolve
            var process = new Process
            {
                StartInfo = new ProcessStartInfo
                {
                    FileName = msolvePath,
                    Arguments = $"-g 2 -f {inputFile} -o {outputFile}",
                    RedirectStandardOutput = true,
                    RedirectStandardError = true,
                    UseShellExecute = false,
                    CreateNoWindow = true
                }
            };

            process.Start();
            process.WaitForExit();

            if (process.ExitCode != 0)
            {
                var error = process.StandardError.ReadToEnd();
                throw new Exception($"msolve failed with exit code {process.ExitCode}: {error}");
            }

            // 4. Read output file
            if (!File.Exists(outputFile))
            {
                throw new FileNotFoundException($"Output file {outputFile} not found.");
            }

            var outputContent = File.ReadAllText(outputFile);
            return ParseOutput(outputContent, sortedVars.ToDictionary(v => v.Name, v => v));
        }

        private string PolyToString(Poly p)
        {
            if (p.Coeffs.Count == 0 || p.Coeffs.All(c => c.Value == 0))
                return "0";

            var sb = new List<string>();
            foreach (var kvp in p.Coeffs)
            {
                var m = kvp.Key;
                var coeff = kvp.Value;

                if (coeff == 0) continue;

                string monStr = "";
                if (m.SortedVars != null && m.SortedVars.Count > 0)
                {
                    // Group vars by name to reconstruct powers
                    var groups = m.SortedVars.GroupBy(v => v.Name);
                    var termParts = new List<string>();
                    foreach (var g in groups)
                    {
                        if (g.Count() > 1)
                            termParts.Add($"{g.Key}^{g.Count()}");
                        else
                            termParts.Add(g.Key);
                    }
                    monStr = string.Join("*", termParts);
                }

                string term;
                if (monStr == "") // constant
                {
                    term = $"{coeff}";
                }
                else
                {
                    // handle 1 and -1 for clean output
                    if (coeff == 1)
                        term = monStr;
                    else if (coeff == -1)
                        term = $"-{monStr}";
                    else
                        term = $"{coeff}*{monStr}";
                }
                sb.Add(term);
            }
            if (sb.Count == 0) return "0";
            return string.Join("+", sb).Replace("+-", "-");
        }

        private List<Poly> ParseOutput(string content, Dictionary<string, SymVar> varMap)
        {
            // Parse [poly1, poly2, ...]
            // Clean up content
            var dataStart = content.IndexOf('[');
            var dataEnd = content.LastIndexOf(']');
            if (dataStart == -1 || dataEnd == -1)
                return new List<Poly>();

            var body = content.Substring(dataStart + 1, dataEnd - dataStart - 1);

            // Handle potentially multiline body
            body = body.Replace("\r", "").Replace("\n", "");

            // Split by comma. Since polys don't contain commas, this works.
            var polyStrs = body.Split(new[] { ',' }, StringSplitOptions.RemoveEmptyEntries);

            var result = new List<Poly>();
            foreach (var ps in polyStrs)
            {
                if (string.IsNullOrWhiteSpace(ps)) continue;
                result.Add(ParsePoly(ps.Trim(), varMap));
            }
            return result;
        }

        private Poly ParsePoly(string polyStr, Dictionary<string, SymVar> varMap)
        {
            polyStr = polyStr.Replace(" ", "").Replace("\n", "").Replace("\r", "");

            var terms = Regex.Split(polyStr, @"(?=[+-])").Where(s => !string.IsNullOrWhiteSpace(s)).ToList();

            var poly = new Poly();
            foreach (var term in terms)
            {
                ParseTerm(term.Trim(), varMap, poly);
            }
            return poly;
        }

        private void ParseTerm(string termStr, Dictionary<string, SymVar> varMap, Poly poly)
        {
            if (string.IsNullOrWhiteSpace(termStr)) return;

            long sign = 1;
            if (termStr.StartsWith("-"))
            {
                sign = -1;
                termStr = termStr.Substring(1);
            }
            else if (termStr.StartsWith("+"))
            {
                termStr = termStr.Substring(1);
            }

            termStr = termStr.Trim();
            if (string.IsNullOrEmpty(termStr)) return;

            string coeffPart = "1";
            string monPart = "";

            if (char.IsDigit(termStr[0]))
            {
                int starIdx = termStr.IndexOf('*');
                if (starIdx != -1)
                {
                    coeffPart = termStr.Substring(0, starIdx);
                    monPart = termStr.Substring(starIdx + 1);
                }
                else
                {
                    coeffPart = termStr;
                    monPart = "";
                }
            }
            else
            {
                coeffPart = "1";
                monPart = termStr;
            }

            long coeff;
            if (coeffPart.Contains("/"))
            {
                coeff = -999999999;
            }
            else
            {
                if (long.TryParse(coeffPart, out long val))
                {
                    coeff = val;
                }
                else
                {
                    coeff = 1;
                }
            }
            coeff *= sign;

            var vars = new List<SymVar>();
            if (!string.IsNullOrEmpty(monPart))
            {
                var parts = monPart.Split('*');
                foreach (var p in parts)
                {
                    string name = p;
                    int exp = 1;
                    if (p.Contains("^"))
                    {
                        var splits = p.Split('^');
                        name = splits[0];
                        if (splits.Length > 1 && int.TryParse(splits[1], out int e))
                        {
                            exp = e;
                        }
                    }

                    if (varMap.TryGetValue(name, out var symVar))
                    {
                        for (int k = 0; k < exp; k++)
                            vars.Add(symVar);
                    }
                }
            }

            if (vars.Count == 0 && string.IsNullOrEmpty(monPart) && coeff == 0)
                return; // 0 polynomial handling?

            var monomial = new Monomial(vars);
            poly.Add(monomial, coeff);
        }
    }
}
