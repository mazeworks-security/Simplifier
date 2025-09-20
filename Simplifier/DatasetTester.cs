using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection.Metadata;
using System.Text;
using System.Threading.Tasks;

namespace Simplifier
{
    public static class DatasetTester
    {
        public static void Run()
        {
            Console.WriteLine("     ");
            var lines = File.ReadLines("C:\\Users\\colton\\source\\repos\\mba-database\\real-world-nonlinear-full.txt");
            var beforeAndAfter = lines.Select(x => (x.Split(",")[0], x.Split(",")[1])).ToList();

            var ctx = new AstCtx();
            AstIdx.ctx = ctx;

            var asts = beforeAndAfter.Select(x => (RustAstParser.Parse(ctx, x.Item1, 64), RustAstParser.Parse(ctx, x.Item2, 64))).ToList();


            Parallel.ForEach(asts, x =>
            {

                ProbableEquivalenceChecker.ProbablyEquivalentZ3(ctx, x.Item1, x.Item2);
            }
            );

            foreach(var (before, after) in asts)
            {
                ProbableEquivalenceChecker.ProbablyEquivalentZ3(ctx, before, after);
            }

            Debugger.Break();

            foreach (var (strBefore_, strAfter) in beforeAndAfter)
            {
                var strBefore = strBefore_;

                //if (strBefore != "((((((((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))^(213:i64|(-214:i64&RSI:i64)))*2199023256422:i64)+(((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))&(~((213:i64&RSI:i64)|(-214:i64^(-214:i64&RSI:i64)))))*7378699388702425784:i64))+(((((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))&RSI:i64)^-1:i64)|213:i64)*-7378698289190797573:i64))+(7378697189679169362:i64*(~(5:i64&RSI:i64))))+(((-1:i64*(~((-209:i64&RSI:i64)|(208:i64^(208:i64&RSI:i64)))))+((4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))|RSI:i64))*3689348594839584681:i64))+((((-9223372036854775808:i64^((-9223372036854775803:i64&RSI:i64)|(9223372036854775802:i64^(9223372036854775802:i64&RSI:i64))))+(0:i64+(((-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))&RSI:i64)*-1:i64)))+(0:i64+(((4040198467629586909:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))&(~RSI:i64))*-1:i64)))*3689349694351212892:i64))")
                //    continue;


                //strBefore = "(-3689349694351212892*(4611686018427387690&(RSI&(4040198467629586696+(1099511628211*(5292288&RBX))))))+(-3689349694351212892*(RSI&(-4040198467629586910+(72056494526299725*(5292288&RBX)))))";

                //strBefore = "(7610965373738707464:i64+((((956575116354345:i64*(5292288:i64&RBX:i64))+(3689349694351212892:i64*(4611686018427387690:i64&RSI:i64)))+(-3689349694351212892:i64*(4611686018427387690:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(RSI:i64&(-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))))))";

                // strBefore = "(-3689349694351212892*(4611686018427387690&(RSI&(4040198467629586696+(1099511628211*(5292288&RBX))))))+(-3689349694351212892*(RSI&(-4040198467629586910+(72056494526299725*(5292288&RBX)))))";

                //strBefore = "(228698418667888:i64+((((((((3689349694351212892:i64*(4611686018427387690:i64&RSI:i64))+(3689348594839584681:i64*(5:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(691752243057131259:i64*(208:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(-3689348594839584681:i64*(5:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(4611686018427387690:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-691754442080387681:i64*(208:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(RSI:i64&(-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))))))";

                //strBefore = "(228698418667888:i64+((((3689349694351212892:i64*(4611686018427387690:i64&RSI:i64))+(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64))))))+(-3689349694351212892:i64*(4611686018427387690:i64&(RSI:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))))+(-3689349694351212892:i64*(RSI:i64&(-4040198467629586910:i64+(72056494526299725:i64*(5292288:i64&RBX:i64)))))))";

                //strBefore = "(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))";

                //strBefore = "-214&((4040198467629586696+(1099511628211*(5292288&RBX))))";

                //strBefore = "(1099511628211:i64*(-214:i64&(4040198467629586696:i64+(1099511628211:i64*(5292288:i64&RBX:i64)))))";

                //strBefore = "(-3689349694351212892*(4611686018427387690&(RSI&(4040198467629586696+(1099511628211*(5292288&RBX))))))+(-3689349694351212892*(RSI&(-4040198467629586910+(72056494526299725*(5292288&RBX)))))";

                //if (strBefore != "(((-433557024052896108:i64+(46702856230664876:i64*(5292288:i64&RBX:i64)))+((((0:i64+((((7610965373738707464:i64+(956575116354345:i64*(5292288:i64&RBX:i64)))|5370260760:i64)&-125:i64)*-1:i64))+((-7610965373738707465:i64+(71101018921573591:i64*(5292288:i64&RBX:i64)))^5370260736:i64))+(-7610965373738707565:i64+(71101018921573591:i64*(5292288:i64&RBX:i64))))*2199023256422:i64))+((((7610965373738707572:i64+(956575116354345:i64*(5292288:i64&RBX:i64)))^5370260760:i64)+0:i64)*3298534884633:i64))")
                //    continue;
                //strBefore = "(((-433557024052896108:i64+(46702856230664876:i64*(5292288:i64&RBX:i64)))+((((0:i64+((((7610965373738707464:i64+(956575116354345:i64*(5292288:i64&RBX:i64)))|5370260760:i64)&-125:i64)*-1:i64))+((-7610965373738707465:i64+(71101018921573591:i64*(5292288:i64&RBX:i64)))^5370260736:i64))+(-7610965373738707565:i64+(71101018921573591:i64*(5292288:i64&RBX:i64))))*2199023256422:i64))+((((7610965373738707572:i64+(956575116354345:i64*(5292288:i64&RBX:i64)))^5370260760:i64)+0:i64)*3298534884633:i64))";

                //strBefore = "(2342386684228996530:i64+((((23351428115332438:i64*(5292288:i64&RBX:i64))+(1099511628211:i64*(-5370260861:i64&(7610965373738707456:i64+(956575116354345:i64*(5292288:i64&RBX:i64))))))+(-3298534884633:i64*(5370260744:i64&(7610965373738707456:i64+(956575116354345:i64*(5292288:i64&RBX:i64))))))+(2199023256422:i64*(5370260736:i64^(-7610965373738707465:i64+(71101018921573591:i64*(5292288:i64&RBX:i64)))))))";

                //strBefore = "((1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64)))&-214:i64)";
                //strBefore = "(-214:i64&(1099511628211:i64*(659114373011020351:i64|(5292288:i64&RBX:i64))))";

                var before = RustAstParser.Parse(ctx, strBefore, 64);



                var after = RustAstParser.Parse(ctx, strAfter, 64);

                

                // if (ctx.GetAstString(before) != "((~(-72056494526299725:i64*(5631088361628047935:i64|(5292288:i64&RBX:i64))))&213:i64)")
                //    continue;



                var cls = ctx.GetClass(before);
                var clsAfter = ctx.GetClass(after);

                var generalSimplifier = new GeneralSimplifier(ctx);
                var simplified = generalSimplifier.SimplifyGeneral(before);
                for (int i = 0; i < 10; i++)
                {
                    generalSimplifier = new(ctx);
                    simplified = generalSimplifier.SimplifyGeneral(simplified);
                }

                var kb = ctx.GetKnownBits(simplified);
                var kb2 = ctx.GetKnownBits(before);
                Console.WriteLine(kb.ToString() == kb2.ToString());

                var r = LinearSimplifier.Run(ctx.GetWidth(before), ctx, before, false, true);
                var r2 = LinearSimplifier.Run(ctx.GetWidth(simplified), ctx, simplified, false, true);
                if (r != r2)
                    Debugger.Break();
                var rClass = ctx.GetClass(r);
                var simplifiedClass = ctx.GetClass(simplified);
                if (ctx.GetClass(after) != simplifiedClass)
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
