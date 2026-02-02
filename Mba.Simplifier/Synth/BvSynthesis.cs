using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synth
{
    public class BvSynthesis
    {
        private readonly AstCtx mbaCtx;
        private readonly AstIdx mbaIdx;
        private TermManager ctx = new();

        public BvSynthesis(AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
        }

        public void Run()
        {
            var x = ctx.MkBvConst(8, "x");
            Debugger.Break();
        }
    }
}
