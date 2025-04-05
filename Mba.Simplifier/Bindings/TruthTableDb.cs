using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using static Mba.Simplifier.Bindings.AstCtx;

namespace Mba.Simplifier.Bindings
{
    public struct OpaqueTruthTableDb { }

    public class TruthTableDb
    {
        private nint handle;

        public TruthTableDb(nint handle)
        {
            this.handle = handle;
        }

        public unsafe TruthTableDb()
        {
            handle = (nint)Api.CreateTruthTableDb();
        }

        public unsafe AstIdx GetBoolean(AstCtx ctx, uint varCount, List<AstIdx> vars, ulong idx)
        {
            var span = CollectionsMarshal.AsSpan(vars);
            fixed (AstIdx* arrPtr = &span[0])
            {
                return Api.GetTruthTableDbEntry(this, ctx, varCount, arrPtr, idx);
            }
        }

        public unsafe uint GetBooleanCost(uint varCount, ulong idx)
        {
            return Api.GetTruthTableDbEntryCost(this,varCount, idx);
        }

        public unsafe static implicit operator OpaqueTruthTableDb*(TruthTableDb ctx) => (OpaqueTruthTableDb*)ctx.handle;

        public unsafe static implicit operator TruthTableDb(OpaqueTruthTableDb* ctx) => new TruthTableDb((nint)ctx);

        protected static class Api
        {
            [DllImport("eq_sat")]
            public unsafe static extern OpaqueTruthTableDb* CreateTruthTableDb();

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx GetTruthTableDbEntry(OpaqueTruthTableDb* db, OpaqueAstCtx* ctx, uint varCount, AstIdx* variableArray, ulong idx);

            [DllImport("eq_sat")]
            public unsafe static extern uint GetTruthTableDbEntryCost(OpaqueTruthTableDb* db, uint varCount, ulong idx);
        }
    }
}
