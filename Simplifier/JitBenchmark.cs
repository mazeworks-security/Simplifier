using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Simplifier
{
    public class JitBenchmark
    {
        public static void Run()
        {
            var bc = new JitBenchmark();
            while (true)
            {
                bc.Benchmark3();
            }
        }

        private readonly AstCtx ctx = new();

        private readonly AstIdx idx;

        private JitBenchmark()
        {
            AstIdx.ctx = ctx;
            var inputText = "                (((-1099511628211:i64*((uns173:i64&(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))|(uns174:i64&(~(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))))))+(uns175:i64*(-2:i64+(-1:i64*uns174:i64))))+(2199023256422:i64*((((-1:i64*(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))+(-1:i64*uns173:i64))+(2:i64*((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns173:i64)))+((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns174:i64))))";

            //inputText = "x+y";

            //inputText = "x*x*x";

            //inputText = "a + b + c";

            //inputText = "(x+y) * (x+y)";

            //inputText = "x + x";

            ///inputText = "((2 * (x & 0x7FFFFFFFFF0)) - 0x100000000350 + 0x178) + (x+y)";

            // breaks:
            //inputText = "(((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))";
            //inputText = "(2 * (x & 0x7FFFFFFFFF0)) - 0x100000000350 + 0x178";
            //inputText = "x + y";

            // Minimal repro
            //inputText = "((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))";

            //inputText = "(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64))";

            //inputText = "(8275699730240514659:i64*(((v1:i32&(v2:i16 zx i32)) zx i64)^((((v0:i8 zx i64)&(v1:i32 zx i64))&(v2:i16 zx i64))&v3:i64)))";
            //inputText = "(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))";
            idx = RustAstParser.Parse(ctx, inputText, 64);
        }

        private void Benchmark()
        {
            var variables = ctx.CollectVariables(idx);
            for (int i = 0; i < 1000; i++)
            {
                var jit = new Amd64OptimizingJit(ctx);
                jit.Compile(idx, variables, MultibitSiMBA.JitPage.Value, false);
            }

            var sw = Stopwatch.StartNew();
            int limit = 10000;

            for (int i = 0; i < limit; i++)
            {
                var jit = new Amd64OptimizingJit(ctx);
                jit.Compile(idx, variables, MultibitSiMBA.JitPage.Value, false);
            }

            sw.Stop();
            Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to jit {limit} asts");
        }

        private void Benchmark3()
        {
            var variables = ctx.CollectVariables(idx).ToArray();
            while (true)
            {
                var sw = Stopwatch.StartNew();
                ctx.CompileBenchmark(idx, ulong.MaxValue, variables, MultibitSiMBA.JitPage.Value);
                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to compile");
            }
        }

        private void Benchmark2()
        {
            var variables = ctx.CollectVariables(idx).ToArray();
            var w = ctx.GetWidth(idx);
            var mask = ModuloReducer.GetMask(w);

            for (int i = 0; i < 1000; i++)
            {
                ctx.Compile(idx, mask, variables, MultibitSiMBA.JitPage.Value);
            }

            var sw = Stopwatch.StartNew();
            int limit = 10000;
            for (int i = 0; i < limit; i++)
            {
                ctx.Compile(idx, mask, variables, MultibitSiMBA.JitPage.Value);
            }
            sw.Stop();
            Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to jit {limit} MBAs");


            /*
            long numMs = 0;
            int count = 0;
            while (true)
            {
                var sw = Stopwatch.StartNew();
                int limit = 1;


                for (int i = 0; i < limit; i++)
                {
                    ctx.CompileNew(idx, mask, variables, MultibitSiMBA.JitPage.Value);
                }

                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to jit {limit} asts");
                numMs += sw.ElapsedMilliseconds;
                count++;

                if (count % 10 == 0)
                {

                }
            }
            */
        }
    }
}
