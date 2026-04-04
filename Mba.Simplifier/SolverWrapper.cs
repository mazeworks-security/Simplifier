using Bitwuzla;
using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection.Metadata.Ecma335;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier
{
    /// <summary>
    /// Represents the result of a satisfiability check.
    /// </summary>
    public enum Result
    {
        Sat = BitwuzlaResult.BITWUZLA_SAT,
        Unsat = BitwuzlaResult.BITWUZLA_UNSAT,
        Unknown = BitwuzlaResult.BITWUZLA_UNKNOWN
    }

    /// <summary>
    /// Rounding mode for floating-point operations.
    /// </summary>
    public enum RoundingMode
    {
        Rne = BitwuzlaRoundingMode.BITWUZLA_RM_RNE,
        Rna = BitwuzlaRoundingMode.BITWUZLA_RM_RNA,
        Rtp = BitwuzlaRoundingMode.BITWUZLA_RM_RTP,
        Rtn = BitwuzlaRoundingMode.BITWUZLA_RM_RTN,
        Rtz = BitwuzlaRoundingMode.BITWUZLA_RM_RTZ
    }

    /// <summary>
    /// High-level wrapper for Bitwuzla options.
    /// </summary>
    public class Options : IDisposable
    {
        internal readonly BitwuzlaOptions native;

        public Options()
        {
            native = BitwuzlaNative.bitwuzla_options_new();
        }

        public Options(BitwuzlaOptions native)
        {
            this.native = native;
        }

        public void Set(BitwuzlaOption option, ulong value)
            => BitwuzlaNative.bitwuzla_set_option(native, option, value);

        public void Set(BitwuzlaOption option, string value)
            => BitwuzlaNative.bitwuzla_set_option_mode(native, option, value);

        public void Set(BitwuzlaOption option, bool value)
            => BitwuzlaNative.bitwuzla_set_option(native, option, value ? 1ul : 0ul);

        public ulong Get(BitwuzlaOption option)
            => BitwuzlaNative.bitwuzla_get_option(native, option);

        public void Dispose()
        {
            BitwuzlaNative.bitwuzla_options_delete(native);
        }

        public static implicit operator BitwuzlaOptions(Options options) => options.native;
    }

    /// <summary>
    /// High-level wrapper for a Bitwuzla Sort.
    /// </summary>
    public class Sort : IDisposable
    {
        internal readonly BitwuzlaSort native;

        public Sort(BitwuzlaSort native)
        {
            this.native = native;
        }

        public bool IsBv => BitwuzlaNative.bitwuzla_sort_is_bv(native);
        public bool IsBool => BitwuzlaNative.bitwuzla_sort_is_bool(native);
        public bool IsFp => BitwuzlaNative.bitwuzla_sort_is_fp(native);
        public bool IsArray => BitwuzlaNative.bitwuzla_sort_is_array(native);
        public bool IsFun => BitwuzlaNative.bitwuzla_sort_is_fun(native);
        public bool IsRm => BitwuzlaNative.bitwuzla_sort_is_rm(native);

        public ulong BvSize => BitwuzlaNative.bitwuzla_sort_bv_get_size(native);
        public ulong FpExpSize => BitwuzlaNative.bitwuzla_sort_fp_get_exp_size(native);
        public ulong FpSigSize => BitwuzlaNative.bitwuzla_sort_fp_get_sig_size(native);
        public ulong FunArity => BitwuzlaNative.bitwuzla_sort_fun_get_arity(native);

        public Sort ArrayIndexSort => new Sort(BitwuzlaNative.bitwuzla_sort_array_get_index(native));
        public Sort ArrayElementSort => new Sort(BitwuzlaNative.bitwuzla_sort_array_get_element(native));
        public Sort FunCodomain => new Sort(BitwuzlaNative.bitwuzla_sort_fun_get_codomain(native));

        // Domain sorts for functions omitted for brevity, would require array marshaling

        public override string ToString()
        {
            return BitwuzlaNative.bitwuzla_sort_to_string(native);
        }

        public override int GetHashCode()
        {
            return (int)BitwuzlaNative.bitwuzla_sort_hash(native);
        }

        public void Dispose()
        {
            // BitwuzlaSort is ref-counted? C API says bitwuzla_sort_release but generated code has Dispose calling delete.
            // Checkgenerated/BitwuzlaSort.cs. Usually SWIG handles deletion. 
            // If we wrap it, we don't necessarily own it unless we bump ref count.
            // For now, assuming standard SWIG wrapper behavior.
        }

        public static implicit operator BitwuzlaSort(Sort sort) => sort.native;
        public static implicit operator Sort(BitwuzlaSort native) => new Sort(native);
    }

    /// <summary>
    /// High-level wrapper for a Bitwuzla Term.
    /// </summary>
    public class Term : IDisposable
    {
        internal readonly BitwuzlaTerm native;

        public Term(BitwuzlaTerm native)
        {
            this.native = native;
        }

        public BitwuzlaKind Kind => BitwuzlaNative.bitwuzla_term_get_kind(native);
        public Sort Sort => new Sort(BitwuzlaNative.bitwuzla_term_get_sort(native));

        public bool IsConst => BitwuzlaNative.bitwuzla_term_is_const(native);
        public bool IsVar => BitwuzlaNative.bitwuzla_term_is_var(native);
        public bool IsValue => BitwuzlaNative.bitwuzla_term_is_value(native);
        public bool IsBvValue => BitwuzlaNative.bitwuzla_term_is_bv_value(native);
        public bool IsTrue => BitwuzlaNative.bitwuzla_term_is_true(native);
        public bool IsFalse => BitwuzlaNative.bitwuzla_term_is_false(native);

        public string Symbol => BitwuzlaNative.bitwuzla_term_get_symbol(native);

        public override string ToString() => BitwuzlaNative.bitwuzla_term_to_string(native);

        public override int GetHashCode() => (int)BitwuzlaNative.bitwuzla_term_hash(native);

        public void Dispose()
        {
            // SWIG wrapper manages native memory
        }

        public static implicit operator BitwuzlaTerm(Term term) => term.native;
        public static implicit operator Term(BitwuzlaTerm native) => new Term(native);

        // Helper to lift C# primitives to Terms using the context of an existing term
        private static Term Lift(Term context, long value) => context.Manager.MkBvValue(context.Sort, (ulong)value);
        private static Term Lift(Term context, ulong value) => context.Manager.MkBvValue(context.Sort, value);
        private static Term Lift(Term context, bool value) => value ? context.Manager.MkTrue() : context.Manager.MkFalse();

        // Operators
        public static Term operator ~(Term t)
        {
            if (t.Sort.IsBv)
                return t.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_NOT, t);
            return t.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_NOT, t);
        }

        public static Term operator &(Term a, Term b)
        {
            if (a.Sort.IsBool && b.Sort.IsBool) return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_AND, a, b);
            return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_AND, a, b);
        }
        public static Term operator |(Term a, Term b)
        {
            if (a.Sort.IsBool && b.Sort.IsBool) return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_OR, a, b);
            return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_OR, a, b);
        }
        public static Term operator ^(Term a, Term b)
        {
            if (a.Sort.IsBool && b.Sort.IsBool) return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_XOR, a, b);
            return a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_XOR, a, b);
        }

        public static Term operator +(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_ADD, a, b);
        public static Term operator -(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_SUB, a, b);
        public static Term operator *(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_MUL, a, b);
        public static Term operator <<(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_SHL, a, b);
        public static Term operator >>(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_SHR, a, b);
        public static Term operator >>>(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_ASHR, a, b);
        public static Term operator /(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_UDIV, a, b);
        public static Term operator %(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_UREM, a, b);
        public static Term operator -(Term t) => t.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_NEG, t);

        //public static bool operator ==(Term a, object b) => a.Equals(b);
        //public static bool operator !=(Term a, object b) => a.Equals(b);
        public static Term operator ==(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_EQUAL, a, b);
        public static Term operator !=(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_DISTINCT, a, b);
        public static Term operator >(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_UGT, a, b);
        public static Term operator <(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_ULT, a, b);
        public static Term operator >=(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_UGE, a, b);
        public static Term operator <=(Term a, Term b) => a.Manager.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_ULE, a, b);


        // Integer/Long Overloads
        public static Term operator &(Term a, long b) => a & Lift(a, b);
        public static Term operator &(long a, Term b) => Lift(b, a) & b;
        public static Term operator |(Term a, long b) => a | Lift(a, b);
        public static Term operator |(long a, Term b) => Lift(b, a) | b;
        public static Term operator ^(Term a, long b) => a ^ Lift(a, b);
        public static Term operator ^(long a, Term b) => Lift(b, a) ^ b;
        public static Term operator +(Term a, long b) => a + Lift(a, b);
        public static Term operator +(long a, Term b) => Lift(b, a) + b;
        public static Term operator -(Term a, long b) => a - Lift(a, b);
        public static Term operator -(long a, Term b) => Lift(b, a) - b;
        public static Term operator *(Term a, long b) => a * Lift(a, b);
        public static Term operator *(long a, Term b) => Lift(b, a) * b;

        public static Term operator ==(Term a, long b) => a == Lift(a, b);
        public static Term operator ==(long a, Term b) => Lift(b, a) == b;
        public static Term operator !=(Term a, long b) => a != Lift(a, b);
        public static Term operator !=(long a, Term b) => Lift(b, a) != b;

        // Ulong Overloads
        public static Term operator &(Term a, ulong b) => a & Lift(a, b);
        public static Term operator &(ulong a, Term b) => Lift(b, a) & b;
        public static Term operator |(Term a, ulong b) => a | Lift(a, b);
        public static Term operator |(ulong a, Term b) => Lift(b, a) | b;
        public static Term operator ^(Term a, ulong b) => a ^ Lift(a, b);
        public static Term operator ^(ulong a, Term b) => Lift(b, a) ^ b;
        public static Term operator +(Term a, ulong b) => a + Lift(a, b);
        public static Term operator +(ulong a, Term b) => Lift(b, a) + b;
        public static Term operator -(Term a, ulong b) => a - Lift(a, b);
        public static Term operator -(ulong a, Term b) => Lift(b, a) - b;
        public static Term operator *(Term a, ulong b) => a * Lift(a, b);
        public static Term operator *(ulong a, Term b) => Lift(b, a) * b;
        public static Term operator >>(Term a, ulong b) => a >> Lift(a, b);

        public static Term operator ==(Term a, ulong b) => a == Lift(a, b);
        public static Term operator ==(ulong a, Term b) => Lift(b, a) == b;
        public static Term operator !=(Term a, ulong b) => a != Lift(a, b);
        public static Term operator !=(ulong a, Term b) => Lift(b, a) != b;
        public static Term operator >(Term a, ulong b) => a > Lift(a, b);
        public static Term operator >(ulong a, Term b) => Lift(b, a) > b;
        public static Term operator <(Term a, ulong b) => a < Lift(a, b);
        public static Term operator <(ulong a, Term b) => Lift(b, a) < b;
        public static Term operator >=(Term a, ulong b) => a >= Lift(a, b);
        public static Term operator >=(ulong a, Term b) => Lift(b, a) >= b;
        public static Term operator <=(Term a, ulong b) => a <= Lift(a, b);
        public static Term operator <=(ulong a, Term b) => Lift(b, a) <= b;

        // Bool Overloads
        public static Term operator &(Term a, bool b) => a & Lift(a, b);
        public static Term operator &(bool a, Term b) => Lift(b, a) & b;
        public static Term operator |(Term a, bool b) => a | Lift(a, b);
        public static Term operator |(bool a, Term b) => Lift(b, a) | b;
        public static Term operator ^(Term a, bool b) => a ^ Lift(a, b);
        public static Term operator ^(bool a, Term b) => Lift(b, a) ^ b;

        public static Term operator ==(Term a, bool b) => a == Lift(a, b);
        public static Term operator ==(bool a, Term b) => Lift(b, a) == b;
        public static Term operator !=(Term a, bool b) => a != Lift(a, b);
        public static Term operator !=(bool a, Term b) => Lift(b, a) != b;


        public TermManager Manager { get; internal set; }
    }

    /// <summary>
    /// High-level wrapper for Bitwuzla Term Manager.
    /// </summary>
    public class TermManager : IDisposable
    {
        private static readonly System.Reflection.ConstructorInfo bitwuzlaTermCtor = typeof(BitwuzlaTerm).GetConstructor(
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance,
            null,
            new Type[] { typeof(nint), typeof(bool) },
            null);

        internal readonly BitwuzlaTermManager native;

        public TermManager()
        {
            native = BitwuzlaNative.bitwuzla_term_manager_new();
        }

        public void Dispose()
        {
            BitwuzlaNative.bitwuzla_term_manager_delete(native);
        }

        public Sort MkBoolSort() => new Sort(BitwuzlaNative.bitwuzla_mk_bool_sort(native));
        public Sort MkBvSort(ulong size) => new Sort(BitwuzlaNative.bitwuzla_mk_bv_sort(native, size));
        public Sort MkArraySort(Sort index, Sort element)
            => new Sort(BitwuzlaNative.bitwuzla_mk_array_sort(native, index, element));

        public Term MkTrue() => Wrap(BitwuzlaNative.bitwuzla_mk_true(native));
        public Term MkFalse() => Wrap(BitwuzlaNative.bitwuzla_mk_false(native));
        public Term MkBvZero(Sort sort) => Wrap(BitwuzlaNative.bitwuzla_mk_bv_zero(native, sort));
        public Term MkBvOne(Sort sort) => Wrap(BitwuzlaNative.bitwuzla_mk_bv_one(native, sort));
        public Term MkBvMinSigned(Sort sort) => Wrap(BitwuzlaNative.bitwuzla_mk_bv_min_signed(native, sort));
        public Term MkBvMaxSigned(Sort sort) => Wrap(BitwuzlaNative.bitwuzla_mk_bv_max_signed(native, sort));

        public Term MkBvValue(Sort sort, ulong value)
            => Wrap(BitwuzlaNative.bitwuzla_mk_bv_value_uint64(native, sort, value));

        public Term MkBvValue(ulong value, ulong size)
            => Wrap(MkBvValue(MkBvSort(size), value));

        public Term MkBvValue(long value, ulong size)
            => Wrap(MkBvValue(MkBvSort(size), value));

        public Term MkBvValue(Sort sort, long value)
            => Wrap(BitwuzlaNative.bitwuzla_mk_bv_value_int64(native, sort, value));

        public Term MkConst(Sort sort, string symbol = null)
           => Wrap(BitwuzlaNative.bitwuzla_mk_const(native, sort, symbol));

        public Term MkBvConst(string name, ulong width)
            => Wrap(MkConst(MkBvSort(width), name));

        public Term MkBvConst(string name, int width)
           => Wrap(MkConst(MkBvSort((ulong)width), name));

        public Term MkBoolConst(string name)
         => Wrap(MkConst(MkBoolSort(), name));

        public Term MkVar(Sort sort, string symbol = null)
           => Wrap(BitwuzlaNative.bitwuzla_mk_var(native, sort, symbol));

        public Term MkIte(params Term[] children)
        {
            return MkTerm(BitwuzlaKind.BITWUZLA_KIND_ITE, children);
        }

        public Term MkZext(uint by, Term child)
        {
            if (by > 64)
                throw new InvalidOperationException("Probably overflowed");

            return Wrap(BitwuzlaNative.bitwuzla_mk_term1_indexed1(this, BitwuzlaKind.BITWUZLA_KIND_BV_ZERO_EXTEND, child, by));
        }

        public Term MkExtract(uint high, uint low, Term child)
        {
            return Wrap(BitwuzlaNative.bitwuzla_mk_term1_indexed2(this, BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT, child, high, low));
        }


        public Term MkImplies(params Term[] children)
        {
            return MkTerm(BitwuzlaKind.BITWUZLA_KIND_IMPLIES, children);
        }


        public unsafe Term MkTerm(BitwuzlaKind kind, params Term[] children)
        {
            if (children == null || children.Length == 0)
                throw new ArgumentException("At least one child required", nameof(children));

            int len = children.Length;
            nint* ptrs = stackalloc nint[len];
            for (int i = 0; i < len; i++)
            {
                ptrs[i] = BitwuzlaTerm.getCPtr(children[i].native).Handle;
            }

            return Wrap(BitwuzlaNative.bitwuzla_mk_term(native, kind, (uint)len, ptrs));
        }

        public unsafe Term MkTerm(BitwuzlaKind kind, IEnumerable<Term> children)
        {
            return MkTerm(kind, children.ToArray());
        }

        public ulong GetIntegerValue(Term term)
        {
            var s = BitwuzlaNative.bitwuzla_term_to_string_fmt(term, 10);

            s = s.Replace("(", "").Replace(")", "");

            var split = s.Split(" ", StringSplitOptions.RemoveEmptyEntries);
            if (split.Length != 3 || split[0] != "_" || !split[1].StartsWith("bv"))
                throw new InvalidOperationException();

            var uStr = split[1].Substring(2);

            return ulong.Parse(uStr);
        }

        public bool GetBoolValue(Term term)
        {
            var s = BitwuzlaNative.bitwuzla_term_to_string_fmt(term, 10);
            return bool.Parse(s);
        }

        public unsafe void SubstituteTerms(Term[] terms, Term[] from, Term[] to)
        {
            if (terms == null || terms.Length == 0) return;
            if (from == null || to == null) return;
            if (from.Length != to.Length) throw new ArgumentException("Substitution map arrays must be of same length");

            int termsLen = terms.Length;
            int mapLen = from.Length;

            if (mapLen == 0) return;

            nint[] termHandles = new nint[termsLen];
            nint[] keyHandles = new nint[mapLen];
            nint[] valHandles = new nint[mapLen];

            for (int i = 0; i < termsLen; i++)
            {
                termHandles[i] = BitwuzlaTerm.getCPtr(terms[i].native).Handle;
            }

            for (int i = 0; i < mapLen; i++)
            {
                keyHandles[i] = BitwuzlaTerm.getCPtr(from[i].native).Handle;
                valHandles[i] = BitwuzlaTerm.getCPtr(to[i].native).Handle;
            }

            fixed (nint* tPtr = termHandles)
            fixed (nint* kPtr = keyHandles)
            fixed (nint* vPtr = valHandles)
            {
                BitwuzlaNative.bitwuzla_substitute_terms((uint)termsLen, tPtr, (uint)mapLen, kPtr, vPtr);
            }

            for (int i = 0; i < termsLen; i++)
            {
                var newPtr = termHandles[i];
                terms[i] = Wrap((BitwuzlaTerm)bitwuzlaTermCtor.Invoke(new object[] { newPtr, true }));
            }
        }

        public unsafe Term SubstituteTerm(Term term, Term[] from, Term[] to)
        {
            if (from == null || to == null) return term;
            if (from.Length != to.Length) throw new ArgumentException("Substitution map arrays must be of same length");

            int mapSize = from.Length;
            if (mapSize == 0) return term;

            nint[] keys = new nint[mapSize];
            nint[] values = new nint[mapSize];

            for (int i = 0; i < mapSize; i++)
            {
                keys[i] = BitwuzlaTerm.getCPtr(from[i].native).Handle;
                values[i] = BitwuzlaTerm.getCPtr(to[i].native).Handle;
            }

            fixed (nint* k = keys)
            fixed (nint* v = values)
            {
                return Wrap(BitwuzlaNative.bitwuzla_substitute_term(term.native, (uint)mapSize, k, v));
            }
        }

        public unsafe void SubstituteTerms(Term[] terms, Dictionary<Term, Term> map)
        {
            if (terms == null || terms.Length == 0) return;
            if (map == null || map.Count == 0) return;

            int termsLen = terms.Length;
            int mapLen = map.Count;

            nint[] termHandles = new nint[termsLen];
            nint[] keyHandles = new nint[mapLen];
            nint[] valHandles = new nint[mapLen];

            for (int i = 0; i < termsLen; i++)
            {
                termHandles[i] = BitwuzlaTerm.getCPtr(terms[i].native).Handle;
            }

            int j = 0;
            foreach (var kvp in map)
            {
                keyHandles[j] = BitwuzlaTerm.getCPtr(kvp.Key.native).Handle;
                valHandles[j] = BitwuzlaTerm.getCPtr(kvp.Value.native).Handle;
                j++;
            }

            fixed (nint* tPtr = termHandles)
            fixed (nint* kPtr = keyHandles)
            fixed (nint* vPtr = valHandles)
            {
                BitwuzlaNative.bitwuzla_substitute_terms((uint)termsLen, tPtr, (uint)mapLen, kPtr, vPtr);
            }

            for (int i = 0; i < termsLen; i++)
            {
                var newPtr = termHandles[i];
                terms[i] = Wrap((BitwuzlaTerm)bitwuzlaTermCtor.Invoke(new object[] { newPtr, true }));
            }
        }

        private Term Wrap(BitwuzlaTerm t)
        {
            return new Term(t) { Manager = this };
        }

        public static implicit operator BitwuzlaTermManager(TermManager tm) => tm.native;
    }

    /// <summary>
    /// High-level wrapper for the Bitwuzla Solver.
    /// </summary>
    public class BvSolver : IDisposable
    {
        private readonly BitwuzlaSolver native;
        private readonly TermManager tm;

        public BvSolver(TermManager tm, Options options = null)
        {
            this.tm = tm;
            native = BitwuzlaNative.bitwuzla_new(tm.native, options?.native);
        }

        public void ConfigureTerminator(nint terminatorState)
        {
            // TODO
        }

        public void Push(ulong nlevels = 1)
            => BitwuzlaNative.bitwuzla_push(native, nlevels);

        public void Pop(ulong nlevels = 1)
            => BitwuzlaNative.bitwuzla_pop(native, nlevels);

        public void Assert(Term term)
            => BitwuzlaNative.bitwuzla_assert(native, term.native);

        public Result CheckSat()
            => (Result)BitwuzlaNative.bitwuzla_check_sat(native);

        public unsafe Result CheckSatAssuming(params Term[] assumptions)
        {
            if (assumptions == null || assumptions.Length == 0)
                return (Result)BitwuzlaNative.bitwuzla_check_sat_assuming(native, 0, null);

            int len = assumptions.Length;
            nint* ptrs = stackalloc nint[len];
            for (int i = 0; i < len; i++)
            {
                ptrs[i] = BitwuzlaTerm.getCPtr(assumptions[i].native).Handle;
            }
            return (Result)BitwuzlaNative.bitwuzla_check_sat_assuming(native, (uint)len, ptrs);
        }

        public unsafe List<Term> GetUnsatCore()
        {
            nuint size;
            var ptr = BitwuzlaNative.bitwuzla_get_unsat_core(native, &size);

            var result = new List<Term>();
            if (size == 0 || ptr.swigCPtr.Handle == nint.Zero)
                return result;

            // Access the internal SWIG constructor for BitwuzlaTerm from the IntPtr
            var ctor = typeof(BitwuzlaTerm).GetConstructor(
                System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance,
                null,
                new Type[] { typeof(nint), typeof(bool) },
                null);

            var items = (nint*)ptr.swigCPtr.Handle;
            for (ulong i = 0; i < size; i++)
            {
                var termPtr = items[i];
                // Create the BitwuzlaTerm wrapper (ownsMemory=false)
                var term = (BitwuzlaTerm)ctor.Invoke(new object[] { termPtr, false });
                result.Add(new Term(term) { Manager = tm });
            }

            return result;
        }

        public Term GetValue(Term term)
            => new Term(BitwuzlaNative.bitwuzla_get_value(native, term.native)) { Manager = tm };

        public void Simplify()
            => BitwuzlaNative.bitwuzla_simplify(native);

        public void Write()
        {
            var handle = NativeMethods.fopen("\\\\wsl.localhost\\Ubuntu-22.04\\home\\colton\\bitwuzla_linux_build\\bitwuzla\\build\\src\\main\\your_problem.smt2", "w");
            BitwuzlaNative.bitwuzla_print_formula(native, "smt2", new SWIGTYPE_p_FILE(handle, true), 10);

            NativeMethods.fclose(handle);

        }

        public void PrintModel()
        {
            // BitwuzlaNative.print
        }

        public void Dispose()
        {
            BitwuzlaNative.bitwuzla_delete(native);
        }

        public static class NativeMethods
        {
            // Import the native C functions
            [DllImport("msvcrt.dll", CallingConvention = CallingConvention.Cdecl, SetLastError = true)]
            public static extern nint fopen(string filename, string mode);

            [DllImport("msvcrt.dll", CallingConvention = CallingConvention.Cdecl, SetLastError = true)]
            public static extern int fclose(nint stream);

            // If needed, import the function from the external DLL that takes the FILE*
            // [DllImport("YourNativeLibrary.dll", CallingConvention = CallingConvention.Cdecl)]
            // public static extern void ProcessFile(IntPtr fileHandle);
        }
    }
}
