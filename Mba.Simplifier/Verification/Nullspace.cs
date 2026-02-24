using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Verification
{
    public struct Fraction : IEquatable<Fraction>
    {
        public readonly long Num;
        public readonly long Den;

        public Fraction(long num, long den = 1)
        {
            if (den == 0) throw new DivideByZeroException("Denominator cannot be zero.");

            // Normalize sign so the denominator is always positive
            if (den < 0)
            {
                num = -num;
                den = -den;
            }

            long g = Gcd(Math.Abs(num), den);
            Num = num / g;
            Den = den / g;
        }

        public static Fraction Zero => new Fraction(0, 1);
        public static Fraction One => new Fraction(1, 1);

        public bool IsZero => Num == 0;

        public Fraction Inverse() => new Fraction(Den, Num);

        public static Fraction operator +(Fraction a, Fraction b) => new Fraction(a.Num * b.Den + b.Num * a.Den, a.Den * b.Den);
        public static Fraction operator -(Fraction a, Fraction b) => new Fraction(a.Num * b.Den - b.Num * a.Den, a.Den * b.Den);
        public static Fraction operator *(Fraction a, Fraction b) => new Fraction(a.Num * b.Num, a.Den * b.Den);
        public static Fraction operator /(Fraction a, Fraction b) => a * b.Inverse();

        public static implicit operator Fraction(long value) => new Fraction(value, 1);

        public static bool operator ==(Fraction a, Fraction b) => a.Num == b.Num && a.Den == b.Den;
        public static bool operator !=(Fraction a, Fraction b) => !(a == b);

        public bool Equals(Fraction other) => this == other;
        public override bool Equals(object? obj) => obj is Fraction f && Equals(f);
        public override int GetHashCode() => HashCode.Combine(Num, Den);
        public override string ToString() => Den == 1 ? Num.ToString() : $"{Num}/{Den}";

        private static long Gcd(long a, long b)
        {
            while (b != 0)
            {
                long temp = b;
                b = a % b;
                a = temp;
            }
            return a;
        }
    }

    public class Nullspace
    {
        public static List<Poly> FindLinearIdentities(List<Poly> equations)
        {
            if (equations == null)
                throw new ArgumentNullException(nameof(equations));

            var rewrites = BuildRewriteMap(equations);

            var gateMonomials = equations
                .Where(p => p.Coeffs.Count > 0)
                .Select(p => p.Lm)
                .Where(m => m.Degree == 1 && m.SortedVars[0].Kind != SymKind.Input)
                .Distinct()
                .OrderBy(m => m)
                .ToList();

            if (gateMonomials.Count == 0)
                return new List<Poly>();

            var memo = new Dictionary<Monomial, Poly>();
            var expandedRows = new List<Poly>(gateMonomials.Count);
            foreach (var g in gateMonomials)
            {
                var expanded = ExpandMonomial(g, rewrites, memo, new HashSet<Monomial>());
                expanded.Simplify();
                expandedRows.Add(expanded);
            }

            var signatureColumns = expandedRows
                .SelectMany(p => p.Coeffs.Keys)
                .Distinct()
                .OrderBy(m => m)
                .ToList();

            if (signatureColumns.Count == 0)
                return new List<Poly>();

            var colIndex = new Dictionary<Monomial, int>(signatureColumns.Count);
            for (int i = 0; i < signatureColumns.Count; i++)
                colIndex[signatureColumns[i]] = i;

            var signature = new Fraction[gateMonomials.Count, signatureColumns.Count];
            for (int r = 0; r < gateMonomials.Count; r++)
            {
                for (int c = 0; c < signatureColumns.Count; c++)
                    signature[r, c] = Fraction.Zero;

                foreach (var (m, coeff) in expandedRows[r].Coeffs)
                {
                    if (coeff != 0 && colIndex.TryGetValue(m, out int c))
                        signature[r, c] = new Fraction(coeff, 1);
                }
            }

            var leftKernel = LeftNullspace(signature);
            var identities = new List<Poly>();

            foreach (var basisVec in leftKernel)
            {
                var integerVec = ToIntegerVector(basisVec);
                var relation = new Poly();
                for (int i = 0; i < integerVec.Length; i++)
                {
                    var coeff = integerVec[i];
                    if (coeff == 0)
                        continue;

                    relation.Add(gateMonomials[i], coeff);
                }

                relation.Simplify();
                if (relation.Coeffs.Count > 1)
                    identities.Add(NormalizeRelationSign(relation));
            }

            return identities
                .Distinct()
                .OrderBy(p => p)
                .ToList();
        }

        private static Dictionary<Monomial, Poly> BuildRewriteMap(List<Poly> equations)
        {
            var rewrites = new Dictionary<Monomial, Poly>();

            foreach (var eq in equations)
            {
                if (eq.Coeffs.Count == 0)
                    continue;

                var lm = eq.Lm;
                if (lm.Degree != 1)
                    continue;

                if (lm.SortedVars[0].Kind == SymKind.Input)
                    continue;

                var lc = eq.Coeffs[lm];
                if (lc != 1 && lc != -1)
                    continue;

                var rhs = eq.Clone();
                rhs.Remove(lm);
                rhs = -1L * rhs;
                if (lc == -1)
                    rhs = -1L * rhs;

                rhs.Simplify();
                rewrites[lm] = rhs;
            }

            return rewrites;
        }

        private static Poly ExpandMonomial(
            Monomial monomial,
            Dictionary<Monomial, Poly> rewrites,
            Dictionary<Monomial, Poly> memo,
            HashSet<Monomial> stack)
        {
            if (memo.TryGetValue(monomial, out var existing))
                return existing.Clone();

            if (stack.Contains(monomial))
                return new Poly(monomial);

            stack.Add(monomial);

            Poly result = Poly.Constant(1);
            foreach (var variable in monomial.SortedVars)
            {
                var single = new Monomial(variable);

                Poly varExpansion;
                if (rewrites.TryGetValue(single, out var rhs))
                {
                    varExpansion = ExpandPoly(rhs, rewrites, memo, stack);
                }
                else
                {
                    varExpansion = new Poly(single);
                }

                result = result * varExpansion;
                result.Simplify();
            }

            stack.Remove(monomial);
            result.Simplify();
            memo[monomial] = result.Clone();
            return result;
        }

        private static Poly ExpandPoly(
            Poly poly,
            Dictionary<Monomial, Poly> rewrites,
            Dictionary<Monomial, Poly> memo,
            HashSet<Monomial> stack)
        {
            var expanded = new Poly();

            foreach (var (monomial, coeff) in poly.Coeffs)
            {
                if (coeff == 0)
                    continue;

                var em = ExpandMonomial(monomial, rewrites, memo, stack);
                expanded += coeff * em;
            }

            expanded.Simplify();
            return expanded;
        }

        private static List<Fraction[]> LeftNullspace(Fraction[,] matrix)
        {
            int rows = matrix.GetLength(0);
            int cols = matrix.GetLength(1);

            var transposed = new Fraction[cols, rows];
            for (int r = 0; r < rows; r++)
                for (int c = 0; c < cols; c++)
                    transposed[c, r] = matrix[r, c];

            return NullspaceBasis(transposed);
        }

        private static List<Fraction[]> NullspaceBasis(Fraction[,] matrix)
        {
            int rows = matrix.GetLength(0);
            int cols = matrix.GetLength(1);

            var rref = new Fraction[rows, cols];
            for (int r = 0; r < rows; r++)
                for (int c = 0; c < cols; c++)
                    rref[r, c] = matrix[r, c];

            var pivotCols = RrefInPlace(rref);
            var pivotSet = new HashSet<int>(pivotCols.Where(x => x >= 0));
            var freeCols = Enumerable.Range(0, cols).Where(c => !pivotSet.Contains(c)).ToList();

            var basis = new List<Fraction[]>();
            foreach (var freeCol in freeCols)
            {
                var vec = Enumerable.Repeat(Fraction.Zero, cols).ToArray();
                vec[freeCol] = Fraction.One;

                int pivotRow = 0;
                for (int c = 0; c < cols && pivotRow < rows; c++)
                {
                    if (pivotCols[pivotRow] != c)
                        continue;

                    var v = rref[pivotRow, freeCol];
                    vec[c] = new Fraction(-v.Num, v.Den);
                    pivotRow++;
                }

                basis.Add(vec);
            }

            return basis;
        }

        private static int[] RrefInPlace(Fraction[,] matrix)
        {
            int rows = matrix.GetLength(0);
            int cols = matrix.GetLength(1);

            var pivots = Enumerable.Repeat(-1, rows).ToArray();
            int pivotRow = 0;

            for (int col = 0; col < cols && pivotRow < rows; col++)
            {
                int bestRow = -1;
                for (int r = pivotRow; r < rows; r++)
                {
                    if (!matrix[r, col].IsZero)
                    {
                        bestRow = r;
                        break;
                    }
                }

                if (bestRow == -1)
                    continue;

                if (bestRow != pivotRow)
                {
                    for (int c = 0; c < cols; c++)
                    {
                        (matrix[pivotRow, c], matrix[bestRow, c]) = (matrix[bestRow, c], matrix[pivotRow, c]);
                    }
                }

                var pivot = matrix[pivotRow, col];
                if (pivot != Fraction.One)
                {
                    var inv = pivot.Inverse();
                    for (int c = 0; c < cols; c++)
                        matrix[pivotRow, c] = matrix[pivotRow, c] * inv;
                }

                for (int r = 0; r < rows; r++)
                {
                    if (r == pivotRow)
                        continue;

                    var factor = matrix[r, col];
                    if (factor.IsZero)
                        continue;

                    for (int c = 0; c < cols; c++)
                        matrix[r, c] = matrix[r, c] - factor * matrix[pivotRow, c];
                }

                pivots[pivotRow] = col;
                pivotRow++;
            }

            return pivots;
        }

        private static long[] ToIntegerVector(Fraction[] vec)
        {
            long lcm = 1;
            foreach (var v in vec)
            {
                if (!v.IsZero)
                    lcm = Lcm(lcm, v.Den);
            }

            var outVec = new long[vec.Length];
            for (int i = 0; i < vec.Length; i++)
                outVec[i] = vec[i].Num * (lcm / vec[i].Den);

            long gcd = 0;
            for (int i = 0; i < outVec.Length; i++)
                gcd = Gcd(gcd, Math.Abs(outVec[i]));

            if (gcd > 1)
            {
                for (int i = 0; i < outVec.Length; i++)
                    outVec[i] /= gcd;
            }

            for (int i = 0; i < outVec.Length; i++)
            {
                if (outVec[i] == 0)
                    continue;
                if (outVec[i] < 0)
                {
                    for (int j = 0; j < outVec.Length; j++)
                        outVec[j] = -outVec[j];
                }
                break;
            }

            return outVec;
        }

        private static Poly NormalizeRelationSign(Poly relation)
        {
            if (relation.Coeffs.Count == 0)
                return relation;

            var lm = relation.Lm;
            var lc = relation.Coeffs[lm];
            if (lc < 0)
                relation = -1L * relation;

            return relation;
        }

        private static long Gcd(long a, long b)
        {
            a = Math.Abs(a);
            b = Math.Abs(b);
            while (b != 0)
            {
                (a, b) = (b, a % b);
            }
            return a;
        }

        private static long Lcm(long a, long b)
        {
            if (a == 0 || b == 0)
                return 0;
            return Math.Abs(a / Gcd(a, b) * b);
        }
    }
}
