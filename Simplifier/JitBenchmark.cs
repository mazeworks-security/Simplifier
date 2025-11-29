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
                bc.Benchmark();
            }
        }

        private readonly AstCtx ctx = new();

        private readonly AstIdx idx;

        private JitBenchmark()
        {
            AstIdx.ctx = ctx;
            var inputText = "                 (((-1099511628211:i64*((uns173:i64&(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))|(uns174:i64&(~(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))))))+(uns175:i64*(-2:i64+(-1:i64*uns174:i64))))+(2199023256422:i64*((((-1:i64*(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))+(-1:i64*uns173:i64))+(2:i64*((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns173:i64)))+((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns174:i64))))";

            //inputText = "(a+b) + (a+b)";

           // inputText = "a+(b+c)";

            //inputText = "34234*(a+b) + 454533433*(c|d)";

            inputText = " 10007043139036883030*((v0&v1)|(v0&v2&v4)|(v0&v2&~v3)|(v1&~v2&~v4)|(v0&~v3&~v4)|(~v2&~v3&~v4)|(~v1&v2&v3&v4)) + 14553531039321956558*((v0&v3&v4)|(~v1&v4)|(v0&~v1&v2)|(v0&~v2&v4)|(~v0&~v3&v4)|(~v2&~v3&v4)|(~v0&v2&v4)|(~v0&v2&~v3)|(v2&v3&v4)|(~v1&v2&~v3)|(~v0&v1&~v2&v3&~v4)) + 172617393219736364*((v0&v2&v3&~v4)|(v0&v1&v3&~v4)|(~v0&v1&~v2&v4)|(~v0&v1&~v2&~v3)|(v0&~v3&v4)|(v0&~v1&~v2&v4)|(v0&~v1&~v2&~v3)|(v0&v1&v2&v4)|(~v0&~v1&v2&v3&v4)|(v1&~v3&v4)|(v0&v1&v2&v3)|(~v0&~v1&v2&~v3&~v4)) + 18400744130898817913*((v2&v3)|(v0&v1&v4)|(v0&v1&v3)|(v0&~v3&v4)|(v0&v1&~v2)|(v2&v4)|(~v0&~v1&v4)|(~v1&~v3&v4)|(v0&v3&~v4)|(~v0&~v1&~v2&~v3)) + 12973446298554413047*((~v0&~v1)|(~v0&~v2&v3)|(~v2&v3&~v4)|(v0&v1&v3&~v4)|(~v1&~v2&v3)|(~v0&v2&~v3&~v4)) + 6889222648871126418*((v0&~v1&v2&v4)|(~v0&v1&~v2&v4)|(v0&~v1&~v3&v4)|(v1&~v2&v3)|(v0&~v2&v3&~v4)|(~v1&v2&~v3&v4)|(~v0&~v1&v2&~v3)|(v0&v1&~v2&~v4)|(~v0&v2&~v3&~v4)|(~v0&~v1&~v3&~v4)) + 10054566868303552552*((v2&v3&v4)|(~v1&v3&v4)|(v1&v2&v3)|(~v0&v2&v3)|(~v0&~v2&~v3)|(v0&~v1&v2&v4)|(v0&~v1&v2&~v3)|(v1&~v2&~v3)) + 4321622017109792814*((v0&~v2&v3)|(~v0&v1&v2)|(~v1&~v2&v3)|(v0&v3&v4)|(~v0&~v3&~v4)|(v1&v2&v3&v4)|(~v1&v2&~v3&~v4)) + 9671738531447837690*((~v0&v2&v3&v4)|(~v0&v1&v2&v3)|(~v0&v1&v2&~v4)|(v1&v2&v3&v4)|(~v1&~v2&~v3&v4)|(~v0&v1&~v3&~v4)|(v0&~v1&v2&v3&~v4)|(~v0&~v2&~v3&v4)|(v0&v1&~v2&v3&~v4)|(~v0&v1&v3&v4)|(~v0&v1&~v2&v4)|(~v0&v1&~v2&~v3)|(~v0&~v1&~v2&v3&~v4)) + 14627705691435396212*((v0&v1&v3)|(~v0&v1&v4)|(v1&~v2&v4)|(v0&~v1&v2&v4)|(v3&v4)|(v0&~v2&v3)|(~v0&v1&v2&~v3)|(~v1&~v2&v3)|(~v0&v2&~v3&~v4)|(v0&~v1&~v2&~v4)) + 9987377089676046899*((v1&~v2&v3&v4)|(~v0&v1&~v2&v3)|(~v0&~v1&~v3&v4)|(v0&v1&v2&v4)|(~v0&~v1&~v2&~v3)|(v0&v1&v3&v4)|(~v0&v1&v2&~v3&~v4)|(v0&~v1&v2&~v3&~v4)|(~v0&~v1&v2&v3&~v4)|(v0&v1&~v2&~v3&~v4)) + 17813789769476130022*((v0&~v2&~v3)|(~v0&~v1&~v3)|(~v0&~v1&~v2)|(~v1&~v2&~v3)|(v0&v1&~v3&v4)|(~v2&~v3&~v4)|(~v0&v2&~v3&v4)|(v0&~v1&v2&v3&v4)|(~v1&~v3&~v4)|(v1&v2&~v3&v4)|(v0&v1&v2&v3&~v4)) + 14976100545088856652*((v2&v3&~v4)|(~v1&~v3&v4)|(v1&~v2&v3&v4)|(~v0&~v1&~v2&v4)|(~v0&~v2&v3&v4)|(v0&~v2&~v3)|(v0&~v1&v2&~v4)|(~v0&v1&v2&~v4)|(~v0&v1&v2&~v3)|(v0&~v1&~v3)|(~v0&v2&~v3&v4)|(~v2&~v3&~v4)|(v0&v1&~v2&v4)|(v0&v1&v2&v3)) + 16389632358196193615*((v1&v3&v4)|(v0&v1&v3)|(v2&v3&v4)|(~v0&v1&v4)|(v1&~v2&v4)|(v0&~v1&v4)|(v0&~v2&v4)|(v1&~v2&v3)|(~v0&v1&~v2)|(v0&~v1&v2&~v3)|(v0&v3&v4)|(~v0&~v2&v3&~v4)) + 16593870877065282714*((~v1&v3&v4)|(~v1&v2&v3)|(~v0&v1&~v2)|(v1&~v2&~v3&v4)|(~v0&~v1&v2&~v4)|(~v0&v3&v4)|(v0&~v1&v3)|(v0&~v1&~v2&~v4)|(~v0&~v1&~v3&~v4)|(v2&v3&v4)) + 4096367517254474779*((v0&~v2&v4)|(v1&~v3&~v4)|(v0&v1&v3&v4)|(~v0&v2&v3&~v4)|(~v0&v1&~v4)|(~v0&v1&v2&~v3)|(v0&v1&~v2&~v3)|(v0&~v1&~v3&v4)|(~v1&~v2&~v3&v4)) + 5065372982172802889*((v0&v3&v4)|(v1&v2&v3&v4)|(~v0&v1&v2&v3)|(~v0&v1&v2&~v4)|(v1&v2&~v3&~v4)|(~v0&~v2&~v3&v4)|(~v0&~v1&v2&~v3)|(~v0&v2&~v3&~v4)|(v0&~v1&v3)|(~v0&~v1&~v3&v4)|(v0&~v1&~v2&~v4)) + 14531686691201963859*((v0&v2&v4)|(v0&~v1&v2)|(~v1&v2&v3&v4)|(v1&v2&~v3&v4)|(v0&v1&v4)|(v0&~v1&v3&~v4)|(~v0&v1&v2&v3&~v4)) + 5021643378913866172*((~v0&v2&~v4)|(v0&~v2&~v3&v4)|(~v0&~v1&~v3&~v4)|(v0&~v1&~v2&~v3)|(v0&~v1&~v2&~v4)|(v1&v2&~v3&~v4)|(v1&~v2&~v3&v4)|(~v1&v2&v3&v4)|(~v1&~v2&~v3&~v4)|(v0&~v1&~v3&v4)|(~v0&~v1&v2&v3)|(~v0&~v1&v3&v4)|(v0&~v1&v2&v4)|(v0&v2&v3&v4)) + 5730572244094584490*((~v0&v1&v2&~v3&~v4)|(v0&v3&v4)|(v0&v2&v3)|(~v0&~v1&~v2&~v3)|(v0&~v2&~v3&~v4)|(~v0&~v2&v3&~v4)|(~v0&~v1&~v3&v4)|(v0&~v1&v3)|(v0&v1&~v2&~v3)|(v0&v1&~v2&v4)|(~v0&v1&~v2&v3)|(v0&~v1&v2&v4)|(v1&v3&v4)|(~v1&v2&~v3&v4)|(~v1&~v2&~v4)|(~v1&v3&~v4)) + 12206460146727066172*((~v0&v1&v2)|(v0&~v1&v2&v4)|(v1&v2&v3&~v4)|(~v0&v1&~v3&v4)|(v0&~v1&~v3&v4)|(v0&~v2&~v3&~v4)|(v0&~v1&~v2&~v3)|(~v0&~v1&~v3&~v4)|(~v0&v2&~v4)|(~v1&~v2&~v3&~v4)|(v0&v1&~v2&v3&v4)|(~v0&v1&v3&~v4)|(~v0&~v1&~v2&v3&v4)) + 3849125494712834494*((~v1&v2&v4)|(v2&~v3&v4)|(v1&~v3&v4)|(v0&~v1&v2)|(v1&v2&v3&~v4)|(v0&v2&v3&~v4)|(~v0&v1&~v2&v4)|(~v0&~v1&~v2&~v3&~v4)) + 16486285417223371074*((v0&v1)|(v1&~v2&~v3)|(v1&~v3&~v4)|(v1&~v2&v4)|(v0&v2&~v3&v4)|(v0&~v2&v3)|(~v0&~v2&~v3&v4)|(~v1&~v2&v3&~v4)) + 14457982469806464123*((v0&v2&~v3&~v4)|(~v1&~v2&v3&~v4)|(v1&~v2&~v3&~v4)|(~v0&~v2&~v4)|(~v1&~v2&~v3&v4)|(v0&~v1&~v3&v4)|(v0&v1&~v3&~v4)|(v0&~v1&v2&~v3)|(~v0&v1&v3&~v4)|(~v0&v1&v2&~v3&v4)|(~v0&~v1&v3&v4)|(v0&v1&v2&~v4)) + 17725768091447676268*((~v0&~v1&v2)|(~v1&v2&~v3)|(v0&v1&~v2&v3)|(~v0&~v1&~v3&v4)|(v0&~v1&~v3&~v4)|(v0&v2&~v3)|(~v0&v1&~v2&~v3&~v4)) + 11547284443345863073*((~v2&v3&~v4)|(~v1&v2&~v3)|(~v0&~v1&~v2)|(~v0&v3&~v4)|(~v0&~v1&~v3)|(~v1&~v3&v4)|(~v0&~v1&~v4)|(~v0&~v2&~v4)|(v1&v2&v3&v4)|(~v0&v1&v2&v3)|(v1&~v2&~v4)|(v0&~v2&~v3&v4)) + 3831402528752184989*((v0&v1&~v2&~v4)|(~v0&v1&~v3&~v4)|(v0&v2&~v3&v4)|(v1&~v2&~v3&~v4)|(~v0&~v1&~v2&~v4)|(~v0&~v2&~v3&~v4)|(v0&~v1&~v3&v4)|(~v0&~v1&v2&v3&v4)|(v1&v2&~v3&v4)|(~v0&v1&v2&~v3)|(~v0&v1&~v2&v3&v4)) + 1275746746524630163*((v0&~v1&~v3&v4)|(v0&~v1&v2&v4)|(v0&~v1&v2&~v3)|(~v0&~v1&~v2&v3)|(~v0&~v2&v3&~v4)|(~v0&v1&v2&v3&v4)|(v0&v1&~v2&v3&v4)|(~v0&v1&~v2&~v3&v4)|(~v0&~v1&~v2&~v4)|(v0&v1&~v2&~v3&~v4)) + 926513298982668131*((~v0&v1&~v2&~v3&~v4)|(v0&~v1&~v2&v3)|(v0&~v1&~v2&~v4)|(~v0&v2&~v3&v4)|(~v1&~v2&v3&v4)|(v0&~v2&v3&v4)|(~v0&~v1&v2&~v3)|(v1&v2&v3&~v4)|(v0&v1&v2&~v3)|(v0&v1&v2&~v4)|(v0&v1&~v3&v4)|(v0&v1&~v2&v4)|(~v0&~v1&v4)) + 14716433015540759842*((v1&~v2&v4)|(~v2&v3&v4)|(v0&~v2&v4)|(v0&~v3&v4)|(~v1&v2&~v3)|(~v0&~v3&~v4)|(v0&~v1&v4)|(v0&v2&v3&~v4)|(v0&~v1&v2)|(v0&v1&~v2&v3)|(~v0&v1&v3&v4)) + 10865415571201427848*((v2&v3&v4)|(v1&v2&v4)|(~v0&v1&v3&v4)|(v0&~v1&v3&v4)|(v0&v2&v3)|(v0&v1&~v3&v4)|(~v0&v2&v4)|(~v0&v2&~v3)|(~v0&v1&~v2&~v4)) + 8259750958305912197*((~v2&~v3&~v4)|(v0&v1&v2&v4)|(v0&v1&v2&v3)|(v0&v2&~v3&v4)|(v0&v1&v3&~v4)|(~v0&~v1&v2&v3)|(v0&~v1&v2&~v3)|(v0&v1&~v2&~v4)|(v0&~v1&~v3&~v4)|(~v0&v1&~v2&v3&v4))";


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

            var j = new Amd64OptimizingJit(ctx);
            j.Compile(idx, variables, MultibitSiMBA.JitPage.Value, false);
            Debugger.Break();

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

        private unsafe void Benchmark2()
        {
            var variables = ctx.CollectVariables(idx).ToArray();
            var w = ctx.GetWidth(idx);
            var mask = ModuloReducer.GetMask(w);

            List<byte> bytes = new();
            //var len = (int)ctx.Compile(idx, mask, variables, MultibitSiMBA.JitPage.Value);
            var jit = new Amd64OptimizingJit(ctx);
            var len = (int)jit.Compile(idx, variables.ToList(), MultibitSiMBA.JitPage.Value, false);

            var p = (byte*)MultibitSiMBA.JitPage.Value;
            for (int i = 0; i < len; i++)
            {
                bytes.Add(p[i]);
            }

            File.WriteAllBytes("bytes.bin", bytes.ToArray());
            Debugger.Break();
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
            Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to jit {limit} MBAs ");


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
