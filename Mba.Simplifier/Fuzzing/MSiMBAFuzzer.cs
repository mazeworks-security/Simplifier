using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Transactions;

namespace Mba.Simplifier.Fuzzing
{
    public class MSiMBAFuzzer
    {
        private readonly SeededRandom rand = new();

        private readonly AstCtx ctx = new();

        public static void Run()
        {
            var sharpPtr = JitUtils.AllocateExecutablePage(1000);
            var fuzzer = new MSiMBAFuzzer();
            var ctx = fuzzer.ctx;
            AstIdx.ctx = fuzzer.ctx;

            //fuzzer.BenchAllocs();

            // Simplify the expression using MSiMBA
            //var fCase2 = fuzzer.GetFuzzCase();
            string inputText = "(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((13716790784261793:i64*(1024:i64&v0:i64))+(2569773508279186:i64*(2048:i64&v0:i64)))+(854931267102023:i64*(4096:i64&v0:i64)))+(642443377069797:i64*(1152921504606855168:i64&v0:i64)))+(147:i64*(36028797018963968:i64&v0:i64)))+(321221688534899:i64*(16384:i64&v0:i64)))+(80305422133725:i64*(65536:i64&v0:i64)))+(32409689095277:i64*(131072:i64&v0:i64)))+(20076355533432:i64*(262144:i64&v0:i64)))+(10038177766716:i64*(524288:i64&v0:i64)))+(14868252956188:i64*(1048576:i64&v0:i64)))+(41116376132466962:i64*(128:i64&v0:i64)))+(36662153:i64*(-9223372019674906624:i64&v0:i64)))+(1680457161042:i64*(8388608:i64&v0:i64)))+(313693055210:i64*(16777216:i64&v0:i64)))+(110405950451:i64*(33554432:i64&v0:i64)))+(78423263803:i64*(67108864:i64&v0:i64)))+(39211631902:i64*(134217728:i64&v0:i64)))+(41884715533:i64*(268435456:i64&v0:i64)))+(9802907976:i64*(576460752840294400:i64&v0:i64)))+(4901453988:i64*(1073741824:i64&v0:i64)))+(7549757392:i64*(2147483648:i64&v0:i64)))+(1225363497:i64*(4294967296:i64&v0:i64)))+(1416744851:i64*(2305843017803628544:i64&v0:i64)))+(1254772220840:i64*(4194304:i64&v0:i64)))+(841939291338179:i64*(512:i64&v0:i64)))+(11267:i64*(562949953421312:i64&v0:i64)))+(37049344:i64*(137438953472:i64&v0:i64)))+(19146305:i64*(274877906944:i64&v0:i64)))+(9573153:i64*(549755813888:i64&v0:i64)))+(4786577:i64*(288231475663339520:i64&v0:i64)))+(1150023:i64*(2199023255552:i64&v0:i64)))+(4147683:i64*(4398046511104:i64&v0:i64)))+(598323:i64*(8796093022208:i64&v0:i64)))+(104472:i64*(17592186044416:i64&v0:i64)))+(149581:i64*(35184372088832:i64&v0:i64)))+(142245:i64*(144185556820033536:i64&v0:i64)))+(37396:i64*(140737488355328:i64&v0:i64)))+(75341953:i64*(68719476736:i64&v0:i64)))+(4675:i64*(1125899906842624:i64&v0:i64)))+(4256:i64*(2251799813685248:i64&v0:i64)))+(3087:i64*(4503599627370496:i64&v0:i64)))+(455:i64*(9007199254740992:i64&v0:i64)))+(163:i64*(18014398509481984:i64&v0:i64)))+(293605310651192:i64*(32768:i64&v0:i64)))+(74:i64*(72057594037927936:i64&v0:i64)))+(20616:i64*(281474976710656:i64&v0:i64)))+(153170438:i64*(34359738368:i64&v0:i64)))+(2509544441679:i64*(2097152:i64&v0:i64)))+(11121033324454919:i64*(256:i64&v0:i64)))+(20558188066233481:i64*(256:i64&v1:i64)))+(10279094033116741:i64*(512:i64&v1:i64)))+(5139547016558371:i64*(1024:i64&v1:i64)))+(2569773508279186:i64*(2048:i64&v1:i64)))+(74:i64*(72057594037927936:i64&v1:i64)))+(147:i64*(324259173170675712:i64&v1:i64)))+(321221688534899:i64*(16384:i64&v1:i64)))+(160610844267450:i64*(32768:i64&v1:i64)))+(80305422133725:i64*(65536:i64&v1:i64)))+(40152711066863:i64*(131072:i64&v1:i64)))+(20076355533432:i64*(262144:i64&v1:i64)))+(164465504529867848:i64*(32:i64&v1:i64)))+(5019088883358:i64*(1048576:i64&v1:i64)))+(612681749:i64*(-8070450523657994240:i64&v1:i64)))+(1254772220840:i64*(4194304:i64&v1:i64)))+(627386110420:i64*(8388608:i64&v1:i64)))+(313693055210:i64*(576460752320200704:i64&v1:i64)))+(156846527605:i64*(33554432:i64&v1:i64)))+(78423263803:i64*(2305843009280802816:i64&v1:i64)))+(39211631902:i64*(134217728:i64&v1:i64)))+(19605815951:i64*(268435456:i64&v1:i64)))+(9802907976:i64*(536870912:i64&v1:i64)))+(4901453988:i64*(1073741824:i64&v1:i64)))+(2450726994:i64*(4611686020574871552:i64&v1:i64)))+(1225363497:i64*(4294967296:i64&v1:i64)))+(2509544441679:i64*(2097152:i64&v1:i64)))+(41116376132466962:i64*(128:i64&v1:i64)))+(37396:i64*(140737488355328:i64&v1:i64)))+(76585219:i64*(68719476736:i64&v1:i64)))+(38292610:i64*(137438953472:i64&v1:i64)))+(19146305:i64*(274877906944:i64&v1:i64)))+(9573153:i64*(549755813888:i64&v1:i64)))+(4786577:i64*(1099511627776:i64&v1:i64)))+(2393289:i64*(2199023255552:i64&v1:i64)))+(1196645:i64*(4398046511104:i64&v1:i64)))+(598323:i64*(8796093022208:i64&v1:i64)))+(299162:i64*(17592186044416:i64&v1:i64)))+(149581:i64*(35184372088832:i64&v1:i64)))+(74791:i64*(70368744177664:i64&v1:i64)))+(153170438:i64*(34359738368:i64&v1:i64)))+(18698:i64*(281474976710656:i64&v1:i64)))+(4675:i64*(1125899906842624:i64&v1:i64)))+(2338:i64*(2251799813685248:i64&v1:i64)))+(1169:i64*(4503599627370496:i64&v1:i64)))+(585:i64*(9007199254740992:i64&v1:i64)))+(293:i64*(162129586585337856:i64&v1:i64)))+(642443377069797:i64*(8192:i64&v1:i64)))+(1284886754139593:i64*(4096:i64&v1:i64)))+(9349:i64*(562949953421312:i64&v1:i64)))+(306340875:i64*(17179869184:i64&v1:i64)))+(10038177766716:i64*(524288:i64&v1:i64)))+(82232752264933924:i64*(64:i64&v1:i64)))+(-10279094033116740:i64*(512:i64&(v0:i64&v1:i64))))+(-5139547016558370:i64*(1024:i64&(v0:i64&v1:i64))))+(-2569773508279185:i64*(2048:i64&(v0:i64&v1:i64))))+(-1284886754139592:i64*(4096:i64&(v0:i64&v1:i64))))+(-146:i64*(324259173170675712:i64&(v0:i64&v1:i64))))+(-642443377069796:i64*(8192:i64&(v0:i64&v1:i64))))+(-160610844267449:i64*(32768:i64&(v0:i64&v1:i64))))+(-80305422133724:i64*(65536:i64&(v0:i64&v1:i64))))+(-40152711066862:i64*(131072:i64&(v0:i64&v1:i64))))+(-20076355533431:i64*(262144:i64&(v0:i64&v1:i64))))+(-10038177766715:i64*(524288:i64&(v0:i64&v1:i64))))+(-164465504529867848:i64*(32:i64&(v0:i64&v1:i64))))+(-612681748:i64*(1152921513196781568:i64&(v0:i64&v1:i64))))+(-1254772220839:i64*(4194304:i64&(v0:i64&v1:i64))))+(-627386110419:i64*(8388608:i64&(v0:i64&v1:i64))))+(-313693055209:i64*(576460752320200704:i64&(v0:i64&v1:i64))))+(-156846527604:i64*(33554432:i64&(v0:i64&v1:i64))))+(-78423263802:i64*(-6917529027573972992:i64&(v0:i64&v1:i64))))+(-39211631901:i64*(134217728:i64&(v0:i64&v1:i64))))+(-19605815950:i64*(268435456:i64&(v0:i64&v1:i64))))+(-9802907975:i64*(536870912:i64&(v0:i64&v1:i64))))+(-4901453987:i64*(1073741824:i64&(v0:i64&v1:i64))))+(-2450726993:i64*(4611686020574871552:i64&(v0:i64&v1:i64))))+(-1225363496:i64*(4294967296:i64&(v0:i64&v1:i64))))+(-2509544441678:i64*(2097152:i64&(v0:i64&v1:i64))))+(-20558188066233480:i64*(256:i64&(v0:i64&v1:i64))))+(-37395:i64*(140737488355328:i64&(v0:i64&v1:i64))))+(-76585218:i64*(68719476736:i64&(v0:i64&v1:i64))))+(-38292609:i64*(137438953472:i64&(v0:i64&v1:i64))))+(-19146304:i64*(274877906944:i64&(v0:i64&v1:i64))))+(-9573152:i64*(549755813888:i64&(v0:i64&v1:i64))))+(-4786576:i64*(1099511627776:i64&(v0:i64&v1:i64))))+(-2393288:i64*(2199023255552:i64&(v0:i64&v1:i64))))+(-1196644:i64*(4398046511104:i64&(v0:i64&v1:i64))))+(-598322:i64*(8796093022208:i64&(v0:i64&v1:i64))))+(-299161:i64*(17592186044416:i64&(v0:i64&v1:i64))))+(-149580:i64*(35184372088832:i64&(v0:i64&v1:i64))))+(-74790:i64*(70368744177664:i64&(v0:i64&v1:i64))))+(-153170437:i64*(34359738368:i64&(v0:i64&v1:i64))))+(-9348:i64*(562949953421312:i64&(v0:i64&v1:i64))))+(-4674:i64*(1125899906842624:i64&(v0:i64&v1:i64))))+(-2337:i64*(2251799813685248:i64&(v0:i64&v1:i64))))+(-1168:i64*(4503599627370496:i64&(v0:i64&v1:i64))))+(-584:i64*(9007199254740992:i64&(v0:i64&v1:i64))))+(-292:i64*(18014398509481984:i64&(v0:i64&v1:i64))))+(-321221688534898:i64*(16384:i64&(v0:i64&v1:i64))))+(-73:i64*(72057594037927936:i64&(v0:i64&v1:i64))))+(-18697:i64*(281474976710656:i64&(v0:i64&v1:i64))))+(-306340874:i64*(17179869184:i64&(v0:i64&v1:i64))))+(-5019088883357:i64*(1048576:i64&(v0:i64&v1:i64))))+(-82232752264933924:i64*(144115188075856064:i64&(v0:i64&v1:i64))))";
            inputText = "((((((((((((((((((((44:i16*(256:i16&v0:i16))+(22:i16*(512:i16&v0:i16)))+(11:i16*(1024:i16&v0:i16)))+(6:i16*(2048:i16&v0:i16)))+(2:i16*(12288:i16&v0:i16)))+(-12288:i16&v0:i16))+(44:i16*(256:i16&v1:i16)))+(22:i16*(512:i16&v1:i16)))+(11:i16*(1024:i16&v1:i16)))+(6:i16*(2048:i16&v1:i16)))+(2:i16*(12288:i16&v1:i16)))+(-12288:i16&v1:i16))+(88:i16*(128:i16&(v0:i16&v1:i16))))+(221567343985614:i16*(256:i16&(v0:i16&v1:i16))))+(-21:i16*(512:i16&(v0:i16&v1:i16))))+(-10:i16*(1024:i16&(v0:i16&v1:i16))))+(221567343985652:i16*(2048:i16&(v0:i16&v1:i16))))+(-2:i16*(4096:i16&(v0:i16&v1:i16))))+(-1:i16*(-9223372036854767616:i16&(v0:i16&v1:i16))))+(221567343985657:i16*(5218521314454437888:i16&(v0:i16&v1:i16))))";

            inputText = "          18446744066237678246*~(x|5148131303079159687) + 18446744069973614931*(5148131303079159687^~(~x&(~y&5148131303079159687))) + 14943697366*~(x|~y) + 18446744069973614931*~(x^(y^5148131303079159687)) + 18446744069973614931*~(~x|(y^5148131303079159687)) + 18446744069973614931*((x|~y)&(x^(y^5148131303079159687))) + 14943697366*(x|~y) + 18446744066237678246*(5148131303079159687|(x&y))";

            inputText = " 16689911286994657724*((((x^y)&~(x^z))&~t)|((y^~(x&(y^z)))&t)) + 15811494930996577628*((((x&y)^(y|~z))&~t)|((~(x&~y)&(y^z))&t)) + 14933078530167257312*(((y^(~x|(y&z)))&~t)|(((x^y)&~(x^z))&t)) + 13176245769603920215*(((z^(x|y))&~t)|(~(~x|(y&z))&t)) + 18446744062501741561*(((z^(x|(~y|z)))&~t)|((z^~(x&(~y&z)))&t)) + 4392081940635677935*(((y^(~x|(y|z)))&~t)|((z^~(x&(~y&z)))&t)) + 14933078530167257312*((~(x|~z)&~t)|((y^(x|(~y|z)))&t)) + 4392081940635677935*((((x|y)&(y^z))&~t)|(~(y&z)&t)) + 10540996623155009542*(((x^(~y&z))&~t)|((~(x&y)&~(y^z))&t)) + 6148914697463078347*(((y^(x|(y|z)))&~t)|(~(x|~z)&t)) + 9662580211117879171*(((y^(x|(~y|z)))&~t)|(((x^y)|(x^z))&t)) + 7905747454290478759*((y&~z)|x) + 4392081918220057825*((((x&~y)|~(x^(y^z)))&~t)|(~(y^z)&t)) + 14054662140545747051*(((x|z)&~t)|(~(x&~y)&t)) + 6148914704934951717*(((y^~(~x&(y|z)))&~t)|((y|(x^z))&t)) + 4392081929427867880*(((x^(~y&z))&~t)|((z|~(x|y))&t))";

            inputText = " 10007043139036883030*((v0&v1)|(v0&v2&v4)|(v0&v2&~v3)|(v1&~v2&~v4)|(v0&~v3&~v4)|(~v2&~v3&~v4)|(~v1&v2&v3&v4)) + 14553531039321956558*((v0&v3&v4)|(~v1&v4)|(v0&~v1&v2)|(v0&~v2&v4)|(~v0&~v3&v4)|(~v2&~v3&v4)|(~v0&v2&v4)|(~v0&v2&~v3)|(v2&v3&v4)|(~v1&v2&~v3)|(~v0&v1&~v2&v3&~v4)) + 172617393219736364*((v0&v2&v3&~v4)|(v0&v1&v3&~v4)|(~v0&v1&~v2&v4)|(~v0&v1&~v2&~v3)|(v0&~v3&v4)|(v0&~v1&~v2&v4)|(v0&~v1&~v2&~v3)|(v0&v1&v2&v4)|(~v0&~v1&v2&v3&v4)|(v1&~v3&v4)|(v0&v1&v2&v3)|(~v0&~v1&v2&~v3&~v4)) + 18400744130898817913*((v2&v3)|(v0&v1&v4)|(v0&v1&v3)|(v0&~v3&v4)|(v0&v1&~v2)|(v2&v4)|(~v0&~v1&v4)|(~v1&~v3&v4)|(v0&v3&~v4)|(~v0&~v1&~v2&~v3)) + 12973446298554413047*((~v0&~v1)|(~v0&~v2&v3)|(~v2&v3&~v4)|(v0&v1&v3&~v4)|(~v1&~v2&v3)|(~v0&v2&~v3&~v4)) + 6889222648871126418*((v0&~v1&v2&v4)|(~v0&v1&~v2&v4)|(v0&~v1&~v3&v4)|(v1&~v2&v3)|(v0&~v2&v3&~v4)|(~v1&v2&~v3&v4)|(~v0&~v1&v2&~v3)|(v0&v1&~v2&~v4)|(~v0&v2&~v3&~v4)|(~v0&~v1&~v3&~v4)) + 10054566868303552552*((v2&v3&v4)|(~v1&v3&v4)|(v1&v2&v3)|(~v0&v2&v3)|(~v0&~v2&~v3)|(v0&~v1&v2&v4)|(v0&~v1&v2&~v3)|(v1&~v2&~v3)) + 4321622017109792814*((v0&~v2&v3)|(~v0&v1&v2)|(~v1&~v2&v3)|(v0&v3&v4)|(~v0&~v3&~v4)|(v1&v2&v3&v4)|(~v1&v2&~v3&~v4)) + 9671738531447837690*((~v0&v2&v3&v4)|(~v0&v1&v2&v3)|(~v0&v1&v2&~v4)|(v1&v2&v3&v4)|(~v1&~v2&~v3&v4)|(~v0&v1&~v3&~v4)|(v0&~v1&v2&v3&~v4)|(~v0&~v2&~v3&v4)|(v0&v1&~v2&v3&~v4)|(~v0&v1&v3&v4)|(~v0&v1&~v2&v4)|(~v0&v1&~v2&~v3)|(~v0&~v1&~v2&v3&~v4)) + 14627705691435396212*((v0&v1&v3)|(~v0&v1&v4)|(v1&~v2&v4)|(v0&~v1&v2&v4)|(v3&v4)|(v0&~v2&v3)|(~v0&v1&v2&~v3)|(~v1&~v2&v3)|(~v0&v2&~v3&~v4)|(v0&~v1&~v2&~v4)) + 9987377089676046899*((v1&~v2&v3&v4)|(~v0&v1&~v2&v3)|(~v0&~v1&~v3&v4)|(v0&v1&v2&v4)|(~v0&~v1&~v2&~v3)|(v0&v1&v3&v4)|(~v0&v1&v2&~v3&~v4)|(v0&~v1&v2&~v3&~v4)|(~v0&~v1&v2&v3&~v4)|(v0&v1&~v2&~v3&~v4)) + 17813789769476130022*((v0&~v2&~v3)|(~v0&~v1&~v3)|(~v0&~v1&~v2)|(~v1&~v2&~v3)|(v0&v1&~v3&v4)|(~v2&~v3&~v4)|(~v0&v2&~v3&v4)|(v0&~v1&v2&v3&v4)|(~v1&~v3&~v4)|(v1&v2&~v3&v4)|(v0&v1&v2&v3&~v4)) + 14976100545088856652*((v2&v3&~v4)|(~v1&~v3&v4)|(v1&~v2&v3&v4)|(~v0&~v1&~v2&v4)|(~v0&~v2&v3&v4)|(v0&~v2&~v3)|(v0&~v1&v2&~v4)|(~v0&v1&v2&~v4)|(~v0&v1&v2&~v3)|(v0&~v1&~v3)|(~v0&v2&~v3&v4)|(~v2&~v3&~v4)|(v0&v1&~v2&v4)|(v0&v1&v2&v3)) + 16389632358196193615*((v1&v3&v4)|(v0&v1&v3)|(v2&v3&v4)|(~v0&v1&v4)|(v1&~v2&v4)|(v0&~v1&v4)|(v0&~v2&v4)|(v1&~v2&v3)|(~v0&v1&~v2)|(v0&~v1&v2&~v3)|(v0&v3&v4)|(~v0&~v2&v3&~v4)) + 16593870877065282714*((~v1&v3&v4)|(~v1&v2&v3)|(~v0&v1&~v2)|(v1&~v2&~v3&v4)|(~v0&~v1&v2&~v4)|(~v0&v3&v4)|(v0&~v1&v3)|(v0&~v1&~v2&~v4)|(~v0&~v1&~v3&~v4)|(v2&v3&v4)) + 4096367517254474779*((v0&~v2&v4)|(v1&~v3&~v4)|(v0&v1&v3&v4)|(~v0&v2&v3&~v4)|(~v0&v1&~v4)|(~v0&v1&v2&~v3)|(v0&v1&~v2&~v3)|(v0&~v1&~v3&v4)|(~v1&~v2&~v3&v4)) + 5065372982172802889*((v0&v3&v4)|(v1&v2&v3&v4)|(~v0&v1&v2&v3)|(~v0&v1&v2&~v4)|(v1&v2&~v3&~v4)|(~v0&~v2&~v3&v4)|(~v0&~v1&v2&~v3)|(~v0&v2&~v3&~v4)|(v0&~v1&v3)|(~v0&~v1&~v3&v4)|(v0&~v1&~v2&~v4)) + 14531686691201963859*((v0&v2&v4)|(v0&~v1&v2)|(~v1&v2&v3&v4)|(v1&v2&~v3&v4)|(v0&v1&v4)|(v0&~v1&v3&~v4)|(~v0&v1&v2&v3&~v4)) + 5021643378913866172*((~v0&v2&~v4)|(v0&~v2&~v3&v4)|(~v0&~v1&~v3&~v4)|(v0&~v1&~v2&~v3)|(v0&~v1&~v2&~v4)|(v1&v2&~v3&~v4)|(v1&~v2&~v3&v4)|(~v1&v2&v3&v4)|(~v1&~v2&~v3&~v4)|(v0&~v1&~v3&v4)|(~v0&~v1&v2&v3)|(~v0&~v1&v3&v4)|(v0&~v1&v2&v4)|(v0&v2&v3&v4)) + 5730572244094584490*((~v0&v1&v2&~v3&~v4)|(v0&v3&v4)|(v0&v2&v3)|(~v0&~v1&~v2&~v3)|(v0&~v2&~v3&~v4)|(~v0&~v2&v3&~v4)|(~v0&~v1&~v3&v4)|(v0&~v1&v3)|(v0&v1&~v2&~v3)|(v0&v1&~v2&v4)|(~v0&v1&~v2&v3)|(v0&~v1&v2&v4)|(v1&v3&v4)|(~v1&v2&~v3&v4)|(~v1&~v2&~v4)|(~v1&v3&~v4)) + 12206460146727066172*((~v0&v1&v2)|(v0&~v1&v2&v4)|(v1&v2&v3&~v4)|(~v0&v1&~v3&v4)|(v0&~v1&~v3&v4)|(v0&~v2&~v3&~v4)|(v0&~v1&~v2&~v3)|(~v0&~v1&~v3&~v4)|(~v0&v2&~v4)|(~v1&~v2&~v3&~v4)|(v0&v1&~v2&v3&v4)|(~v0&v1&v3&~v4)|(~v0&~v1&~v2&v3&v4)) + 3849125494712834494*((~v1&v2&v4)|(v2&~v3&v4)|(v1&~v3&v4)|(v0&~v1&v2)|(v1&v2&v3&~v4)|(v0&v2&v3&~v4)|(~v0&v1&~v2&v4)|(~v0&~v1&~v2&~v3&~v4)) + 16486285417223371074*((v0&v1)|(v1&~v2&~v3)|(v1&~v3&~v4)|(v1&~v2&v4)|(v0&v2&~v3&v4)|(v0&~v2&v3)|(~v0&~v2&~v3&v4)|(~v1&~v2&v3&~v4)) + 14457982469806464123*((v0&v2&~v3&~v4)|(~v1&~v2&v3&~v4)|(v1&~v2&~v3&~v4)|(~v0&~v2&~v4)|(~v1&~v2&~v3&v4)|(v0&~v1&~v3&v4)|(v0&v1&~v3&~v4)|(v0&~v1&v2&~v3)|(~v0&v1&v3&~v4)|(~v0&v1&v2&~v3&v4)|(~v0&~v1&v3&v4)|(v0&v1&v2&~v4)) + 17725768091447676268*((~v0&~v1&v2)|(~v1&v2&~v3)|(v0&v1&~v2&v3)|(~v0&~v1&~v3&v4)|(v0&~v1&~v3&~v4)|(v0&v2&~v3)|(~v0&v1&~v2&~v3&~v4)) + 11547284443345863073*((~v2&v3&~v4)|(~v1&v2&~v3)|(~v0&~v1&~v2)|(~v0&v3&~v4)|(~v0&~v1&~v3)|(~v1&~v3&v4)|(~v0&~v1&~v4)|(~v0&~v2&~v4)|(v1&v2&v3&v4)|(~v0&v1&v2&v3)|(v1&~v2&~v4)|(v0&~v2&~v3&v4)) + 3831402528752184989*((v0&v1&~v2&~v4)|(~v0&v1&~v3&~v4)|(v0&v2&~v3&v4)|(v1&~v2&~v3&~v4)|(~v0&~v1&~v2&~v4)|(~v0&~v2&~v3&~v4)|(v0&~v1&~v3&v4)|(~v0&~v1&v2&v3&v4)|(v1&v2&~v3&v4)|(~v0&v1&v2&~v3)|(~v0&v1&~v2&v3&v4)) + 1275746746524630163*((v0&~v1&~v3&v4)|(v0&~v1&v2&v4)|(v0&~v1&v2&~v3)|(~v0&~v1&~v2&v3)|(~v0&~v2&v3&~v4)|(~v0&v1&v2&v3&v4)|(v0&v1&~v2&v3&v4)|(~v0&v1&~v2&~v3&v4)|(~v0&~v1&~v2&~v4)|(v0&v1&~v2&~v3&~v4)) + 926513298982668131*((~v0&v1&~v2&~v3&~v4)|(v0&~v1&~v2&v3)|(v0&~v1&~v2&~v4)|(~v0&v2&~v3&v4)|(~v1&~v2&v3&v4)|(v0&~v2&v3&v4)|(~v0&~v1&v2&~v3)|(v1&v2&v3&~v4)|(v0&v1&v2&~v3)|(v0&v1&v2&~v4)|(v0&v1&~v3&v4)|(v0&v1&~v2&v4)|(~v0&~v1&v4)) + 14716433015540759842*((v1&~v2&v4)|(~v2&v3&v4)|(v0&~v2&v4)|(v0&~v3&v4)|(~v1&v2&~v3)|(~v0&~v3&~v4)|(v0&~v1&v4)|(v0&v2&v3&~v4)|(v0&~v1&v2)|(v0&v1&~v2&v3)|(~v0&v1&v3&v4)) + 10865415571201427848*((v2&v3&v4)|(v1&v2&v4)|(~v0&v1&v3&v4)|(v0&~v1&v3&v4)|(v0&v2&v3)|(v0&v1&~v3&v4)|(~v0&v2&v4)|(~v0&v2&~v3)|(~v0&v1&~v2&~v4)) + 8259750958305912197*((~v2&~v3&~v4)|(v0&v1&v2&v4)|(v0&v1&v2&v3)|(v0&v2&~v3&v4)|(v0&v1&v3&~v4)|(~v0&~v1&v2&v3)|(v0&~v1&v2&~v3)|(v0&v1&~v2&~v4)|(v0&~v1&~v3&~v4)|(~v0&v1&~v2&v3&v4))";

            //inputText = "2*x";

            var fCase2 = RustAstParser.Parse(ctx, inputText, 64);
            var fr = LinearSimplifier.Run(ctx.GetWidth(fCase2), fuzzer.ctx, fCase2, false, true);

            var pagePtr = MultibitSiMBA.JitPage.Value;


            Console.WriteLine("Done");
            Console.WriteLine($"{ctx.GetAstString(fCase2)} => {ctx.GetAstString(fr)}");

            var vs = ctx.CollectVariables(fCase2);

            
            while(true)
            {
                var s = Stopwatch.StartNew();
                int limit = 200000;
                for (int i = 0; i < limit; i++)
                {
                    var resulttt = LinearSimplifier.Run(ctx.GetWidth(fCase2), fuzzer.ctx, fCase2, false, false, variables: vs);
                }

                s.Stop();
                Console.WriteLine($"Took {s.ElapsedMilliseconds}ms to process {limit} MBAs ");
            }
            

            for (int i = 0; i < 1000000; i++)
            {
                // Simplify the expression using MSiMBA
                var fCase = fuzzer.GetFuzzCase();
                var result = LinearSimplifier.Run(ctx.GetWidth(fCase), fuzzer.ctx, fCase, false, true);
                Console.WriteLine($"{fuzzer.ctx.GetAstString(fCase)}\n=>\n{fuzzer.ctx.GetAstString(result)}\n    \n");

                // Skip if the expression simplifies to a constant
                var variables = ctx.CollectVariables(fCase);

                if (variables.Count == 0)
                    continue;

                // Verify that both expressions are equivalent. Fuzz both JITs by using the old/new jit for the input and result.
                bool multiBit = true;
                var numCombinations = (ulong)Math.Pow(2, variables.Count);
                var w = ctx.GetWidth(fCase);
                var vec1 = LinearSimplifier.JitResultVector(ctx, w, (ulong)ModuloReducer.GetMask(w), variables, fCase, multiBit, numCombinations);
                var vec2 = LinearSimplifier.JitResultVectorOld(ctx, w, (ulong)ModuloReducer.GetMask(w), variables, result, multiBit, numCombinations);
                if(!vec1.SequenceEqual(vec2))
                    throw new InvalidOperationException("Mismatch");
            }
        }

        private void BenchAllocs()
        {
            while(true)
            {
                ctx.Clear();
                var seed = rand.GetRandUlong();
                var sw = Stopwatch.StartNew();
                ctx.Benchmark(seed);
                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms to generate 10,000,000 constants   ");
            }
        }

        // Expression can either be purely linear(with zext/trunc which is technically semi-linear), or classically semi-linear
        // Pick output expression size(e.g. 8, 16, 32, 64)
        // Pick N variables of random size
        // TODO: Truncation.. for now, assert that the variable sizes must be less than or equal to the size of the output expression
        private AstIdx GetFuzzCase()
        {
            // Clear the ast context
            ctx.Clear();

            // Pick the width of the output expression...
            int outputWidth = rand.Next(0, 4) switch
            {
                0 => 8,
                1 => 16,
                2 => 32,
                3 => 64,
            };

            // Pick between 2 and 5 variables of random sizes
            var numVars = rand.Next(2, 5);
            var variables = new List<AstIdx>();
            for (int i = 0; i < numVars; i++)
            {
                variables.Add(ctx.Symbol($"v{i}", (byte)ChooseVarWidth(outputWidth)));
            }

            // Chose between 2 and 5 terms
            //var termCount = rand.Next(2, 6);
            var termCount = 1;
            List<AstIdx> terms = new();
            for(int i = 0; i < termCount; i++)
            {
                var term = GetTerm(outputWidth, variables);
                terms.Add(term);
            }

            var result = ctx.Add(terms);
            return result;
        }

        // Choose an aligned width that is less than or equal to the size of the output register
        private int ChooseVarWidth(int outputWidth)
        {
            var choices = new int[] { 8, 16, 32, 64 };
            return choices[rand.Next(0, choices.Length)];
        }

        // Compute a random semi-linear bitwise term
        // We output booleans in algebraic form because it's more convenient to generate 
        private AstIdx GetTerm(int outputWidth, List<AstIdx> variables)
        {
            // Compute a list of variable conjunctions, e.g. [(a&b&c), (b&c), (a)]
            var conjCount = rand.GetRandUshort(1, 4);
            HashSet<ulong> conjMasks = new();
            for (int i = 0; i < conjCount; i++)
            {
                // Get a unique conjunction.
                while (true)
                {
                    var conj = GetRandConjMask(variables.Count);
                    if (conj == 0)
                        continue;
                    // Skip if we've already used this conjunction.
                    if (conjMasks.Contains(conj))
                        continue;

                    conjMasks.Add(conj);
                    break;
                }
            }

            // Build an AST for the variable conjunction, inserting zero extensions where necessary.
            List<AstIdx> conjs = new();
            foreach(var conjMask in conjMasks)
            {
                var minWidth = GetConjMinWidth(conjMask, variables);
                var extendedVars = variables.Select(x => ChangeWidth(x, ctx.GetWidth(x), minWidth)).ToList();
                var conj = LinearSimplifier.ConjunctionFromVarMask(ctx, extendedVars, 1, conjMask);
                conjs.Add(ChangeWidth(conj, ctx.GetWidth(conj), (uint)outputWidth));
            }

            // XOR all of the conjunctions together
            return ctx.Mul(ctx.Constant(rand.GetRandUlong(), (byte)outputWidth), ctx.Xor(conjs));
        }

        private AstIdx ChangeWidth(AstIdx idx, uint from, uint to)
        {
            if (from == to)
                return idx;
            if (from < to)
                return ctx.Zext(idx, (byte)to);
            else
                return ctx.Trunc(idx, (byte)to);
        }

        private ulong GetRandConjMask(int varCount)
        {
            return rand.GetRandUlong(0, (1ul << varCount));
        }

        private byte GetConjMinWidth(ulong conj, List<AstIdx> variables)
        {
            // Compute a minimal width that all variables must be extended to.
            byte minWidth = 0;
            for (ushort i = 0; i < variables.Count; i++)
            {
                // Skip if this variable is not demanded.
                if (((1ul << i) & conj) == 0)
                    continue;

                var w = ctx.GetWidth(variables[i]);
                if (w > minWidth)
                    minWidth = w;
            }

            return minWidth;
        }
    }
}
