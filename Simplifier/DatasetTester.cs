using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Simplifier
{
    public static class DatasetTester
    {
        public static void Run()
        {
            var lines = File.ReadLines("C:\\Users\\colton\\source\\repos\\mba-database\\real-world-nonlinear.txt");
            var beforeAndAfter = lines.Select(x => (x.Split(",")[0], x.Split(",")[1])).ToList();

            var ctx = new AstCtx();
            AstIdx.ctx = ctx;
            foreach (var (strBefore, strAfter) in beforeAndAfter)
            {

                var before = RustAstParser.Parse(ctx, strBefore, uint.MaxValue);
                var after = RustAstParser.Parse(ctx, strAfter, uint.MaxValue);

                var cls = ctx.GetClass(before);
                var clsAfter = ctx.GetClass(after);

                var generalSimplifier = new GeneralSimplifier(ctx);
                var simplified = generalSimplifier.SimplifyGeneral(before);


                var r = LinearSimplifier.Run(ctx.GetWidth(before), ctx, before, false, true);
                var rClass = ctx.GetClass(r);
                if (ctx.GetClass(after) != ctx.GetClass(simplified))
                    Debugger.Break();
                //if (ctx.GetClass(before) == AstClassification.Nonlinear)
                //    Debugger.Break();
                //if (ctx.GetClass(simplified) != AstClassification.Nonlinear || !ctx.IsConstant(r)))
                //    continue;

                //Debugger.Break();
            }

            Debugger.Break();

        }
    }
}
