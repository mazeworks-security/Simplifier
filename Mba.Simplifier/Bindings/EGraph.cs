using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public struct OpaqueEGraph { }

    public class EGraph
    {
        private readonly nint handle;

        public EGraph(nint handle)
        {
            this.handle = handle;
        }

        public unsafe EGraph()
        {
            handle = (nint)Api.CreateEGraph();
        }

        public unsafe AstIdx AddFromContext(AstCtx ctx, AstIdx idx)
            => Api.EGraphAddFromContext(this, ctx, idx);

        public unsafe void Run(ulong msLimit, ulong iterLimit)
            => Api.EGraphRun(this, msLimit, iterLimit);

        public unsafe IReadOnlyList<AstIdx> GetClasses()
        {
            ulong len = 0;
            var ptr = Api.EGraphGetClasses(this, &len);
            var vec = new List<AstIdx>();
            for(int i = 0; i < (int)len; i++)
            {
                // Get a ptr to the elem at this idx.
                var pItem = &ptr[i];

                // Push the variable.
                var value = *pItem;
                vec.Add(value);
            }

            return vec;
        }


        public unsafe IReadOnlyList<(AstIdx eclass, AstIdx extracted)> ExtractAll(AstCtx ctx)
        {
            ulong len = 0;
            var ptr = Api.EGraphExtractAll(this, ctx, &len);
            var vec = new List<(AstIdx eclass, AstIdx extracted)>();
            for (int i = 0; i < (int)len; i += 2)
            {
                // Get a ptr to the elem at this idx.
                var pItem = &ptr[i];

                // Push the variable.
                var eclass = *pItem;
                var extracted = pItem[1];
                vec.Add((eclass, extracted));
            }

            return vec;
        }

        public unsafe AstIdx Extract(AstCtx ctx, AstIdx eclass)
            => Api.EGraphExtract(this, ctx, eclass);

        public unsafe void Union(AstIdx a, AstIdx b)
            => Api.EGraphUnion(this, a, b);

        public unsafe void Rebuild() => Api.EGraphRebuild(this);

        public unsafe static implicit operator OpaqueEGraph*(EGraph egraph) => (OpaqueEGraph*)egraph.handle;

        public unsafe static implicit operator EGraph(OpaqueEGraph* egraph) => new EGraph((nint)egraph);

        private static class Api
        {
            [DllImport("eq_sat")]
            public unsafe static extern OpaqueEGraph* CreateEGraph();

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx EGraphAddFromContext(OpaqueEGraph* egraph, OpaqueAstCtx* ctx, AstIdx idx);

            [DllImport("eq_sat")]
            public unsafe static extern void EGraphRun(OpaqueEGraph* egraph, ulong msLimit, ulong iterLimit);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx* EGraphGetClasses(OpaqueEGraph* egraph, ulong* outLen);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx EGraphExtract(OpaqueEGraph* egraph, OpaqueAstCtx* ctx, AstIdx eclass);

            [DllImport("eq_sat")]
            public unsafe static extern AstIdx* EGraphExtractAll(OpaqueEGraph* egraph, OpaqueAstCtx* ctx, ulong* outLen);

            [DllImport("eq_sat")]
            public unsafe static extern void EGraphUnion(OpaqueEGraph* egraph, AstIdx a, AstIdx b);

            [DllImport("eq_sat")]
            public unsafe static extern void EGraphRebuild(OpaqueEGraph* egraph);

        }
    }
}
