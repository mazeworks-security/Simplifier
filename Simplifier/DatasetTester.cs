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
            foreach (var (strBefore_, strAfter) in beforeAndAfter)
            {
                var strBefore = strBefore_;
                if (strBefore != "((((((((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))^(213:i64|(-214:i64&RSI:i64)))*2199023256422:i64)+(((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))&(~((213:i64&RSI:i64)|(-214:i64^(-214:i64&RSI:i64)))))*7378699388702425784:i64))+(((((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))&RSI:i64)^-1:i64)|213:i64)*-7378698289190797573:i64))+(7378697189679169362:i64*(~(5:i64&RSI:i64))))+(((-1:i64*(~((-209:i64&RSI:i64)|(208:i64^(208:i64&RSI:i64)))))+((4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))|RSI:i64))*3689348594839584681:i64))+((((-9223372036854775808:i64^((-9223372036854775803:i64&RSI:i64)|(9223372036854775802:i64^(9223372036854775802:i64&RSI:i64))))+(0:i64+(((-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))&RSI:i64)*-1:i64)))+(0:i64+(((4040198467629586909:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))&(~RSI:i64))*-1:i64)))*3689349694351212892:i64))")
                    continue;

                //strBefore = "(228698418667888:i64+((((((((3689349694351212892:i64*(4611686018427387690:i64&RSI:i64))+(3689348594839584681:i64*(5:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(691752243057131259:i64*(208:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(-3689348594839584681:i64*(5:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(4611686018427387690:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-691754442080387681:i64*(208:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(RSI:i64&(-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))))))";

                strBefore = "(228698418667888:i64+((((3689349694351212892:i64*(4611686018427387690:i64&RSI:i64))+(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(-3689349694351212892:i64*(4611686018427387690:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(RSI:i64&(-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))))))";

                var before = RustAstParser.Parse(ctx, strBefore, uint.MaxValue);
                var after = RustAstParser.Parse(ctx, strAfter, uint.MaxValue);

                var cls = ctx.GetClass(before);
                var clsAfter = ctx.GetClass(after);

                var generalSimplifier = new GeneralSimplifier(ctx);
                var simplified = generalSimplifier.SimplifyGeneral(before);
                for(int i = 0; i < 5; i++)
                    simplified = generalSimplifier.SimplifyGeneral(simplified);

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
