using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.DSL;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Minimization;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using Simplifier;
using System.ComponentModel;
using System.Diagnostics;

bool printUsage = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = true;
string inputText = null;

//DatasetTester.Run();


inputText = "((((1:i32&((uns17:i8 zx i32)&(~uns18:i32)))|(4294964010:i32&(~((uns17:i8 zx i32)|(~uns18:i32)))))|(4294964011:i32&((uns17:i8 zx i32)&uns18:i32)))|(4:i32*(1:i32&(uns19:i8 zx i32))))";

inputText = "((2041933603239772578:i64+((((((((((((((((-27487790705275:i64*uns121:i64)+(-9223358842715237276:i64*(-860922984064492326:i64&uns121:i64)))+(9223354444668724432:i64*uns131:i64))+(-9223350046622211588:i64*(860922984064492325:i64&uns131:i64)))+(-8796093025688:i64*uns132:i64))+(4398046512844:i64*uns34:i64))+(17592186051376:i64*uns65:i64))+(-3298534884633:i64*uns91:i64))+(9223367638808262964:i64*(8362449052790283482:i64&uns91:i64)))+(13194139538532:i64*(860922984064492325:i64&(uns121:i64&uns130:i64))))+(14293651166743:i64*(-3750763034362895579:i64&(uns121:i64&uns67:i64))))+(4398046512844:i64*(uns130:i64&uns133:i64)))+(-8796093025688:i64*(1444920025149201626:i64&(uns130:i64&uns91:i64))))+(-4398046512844:i64*(uns131:i64&uns133:i64)))+(-9223350046622211588:i64*(3750763034362895578:i64&(uns131:i64&uns91:i64))))+(-9895604653899:i64*((uns121:i64&uns130:i64)&uns91:i64))))+(3062923494603851298:i64+(((((((-9895604653899:i64*uns130:i64)+(9895604653899:i64*(-3750763034362895579:i64&uns131:i64)))+(9895604653899:i64*(3750763034362895578:i64&uns17:i64)))+(-9895604653899:i64*(-3750763034362895579:i64&(uns121:i64&uns131:i64))))+(9895604653899:i64*(uns130:i64&uns134:i64)))+(-9895604653899:i64*(uns131:i64&uns134:i64)))+(9895604653899:i64*(-3750763034362895579:i64&(uns131:i64&uns91:i64))))))";

inputText = "((-1:i64*(~((((8614007388540201639:i64+(((((6919028725695267695:i64*(183:i64&uns16:i64))+(2304343311159508113:i64*(72:i64&uns16:i64)))+(8796093025688:i64*uns22:i64))+(-8796093025688:i64*((5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))+(-8796093025688:i64*((-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64))))&((~uns4:i64)^(((((~uns4:i64)&((167:i16+(((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))&((11175:i16+(((((52335:i16*(183:i16&(uns16:i64 tr i16)))+(5265:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))|(((~uns4:i64)&((167:i16+(((((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))&((11175:i16+(((((52335:i16*(183:i16&(uns16:i64 tr i16)))+(5265:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64)))&uns16:i64)))|(255:i64&(uns16:i64&((((~uns4:i64)&(~((167:i16+(((((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64)))&(~((167:i16+(((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64)))&(~(8614007388540201639:i64+(((((6919028725695267695:i64*(183:i64&uns16:i64))+(2304343311159508113:i64*(72:i64&uns16:i64)))+(8796093025688:i64*uns22:i64))+(-8796093025688:i64*((5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))+(-8796093025688:i64*((-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))))))))|(-256:i64&(((uns16:i64&(8614007388540201639:i64+(((((6919028725695267695:i64*(183:i64&uns16:i64))+(2304343311159508113:i64*(72:i64&uns16:i64)))+(8796093025688:i64*uns22:i64))+(-8796093025688:i64*((5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))+(-8796093025688:i64*((-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))))&((11175:i16+(((((52335:i16*(183:i16&(uns16:i64 tr i16)))+(5265:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))&(((~uns4:i64)&((167:i16+(((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))|((~uns4:i64)&((167:i16+(((((111:i16*(183:i16&(uns16:i64 tr i16)))+(145:i16*(72:i16&(uns16:i64 tr i16))))+(256:i16*(uns22:i64 tr i16)))+(104:i16*((65451:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))+(65432:i16*((171:i16*(~((183:i16&(uns16:i64 tr i16))|(72:i16^(72:i16&(uns16:i64 tr i16))))))&(uns22:i64 tr i16))))) zx i64))))))))+(-1:i64*(((~uns16:i64)&(8614011786586714483:i64+(((((((4398046512844:i64*(5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64))))))+(4398046512844:i64*(-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))))+(6919028725695267695:i64*(183:i64&uns16:i64)))+(2304343311159508113:i64*(72:i64&uns16:i64)))+(8796093025688:i64*uns22:i64))+(-8796093025688:i64*((5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))+(-8796093025688:i64*((-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))))|(uns4:i64&(8614011786586714483:i64+(((((((4398046512844:i64*(5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64))))))+(4398046512844:i64*(-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))))+(6919028725695267695:i64*(183:i64&uns16:i64)))+(2304343311159508113:i64*(72:i64&uns16:i64)))+(8796093025688:i64*uns22:i64))+(-8796093025688:i64*((5156503906449953109:i64+(-624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64)))+(-8796093025688:i64*((-5156503906449953110:i64+(624165263380053675:i64*((183:i64&uns16:i64)|(72:i64^(72:i64&uns16:i64)))))&uns22:i64))))))))";

inputText = "(((-1099511628211:i64*((uns173:i64&(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))|(uns174:i64&(~(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))))))+(uns175:i64*(-2:i64+(-1:i64*uns174:i64))))+(2199023256422:i64*((((-1:i64*(-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64)))))))+(-1:i64*uns173:i64))+(2:i64*((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns173:i64)))+((-46179488384862:i64+(((((((((((((((((((((-3298534884633:i64*uns158:i64)+(8796093025688:i64*uns159:i64))+(-4398046512844:i64*uns160:i64))+(-4398046512844:i64*(uns158:i64&uns159:i64)))+(17592186051376:i64*(uns159:i64&uns160:i64)))+(-19791209307798:i64*(uns159:i64&uns162:i64)))+(-21990232564220:i64*(uns159:i64&uns165:i64)))+(-13194139538532:i64*(uns160:i64&uns167:i64)))+(-14293651166743:i64*(uns167:i64&uns168:i64)))+(-8796093025688:i64*((uns158:i64&uns159:i64)&uns164:i64)))+(21990232564220:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns164:i64)&uns167:i64)))+(-13194139538532:i64*((uns159:i64&uns160:i64)&uns164:i64)))+(13194139538532:i64*((uns160:i64&uns164:i64)&uns167:i64)))+(-8796093025688:i64*uns166:i64))+(-4398046512844:i64*uns163:i64))+(-17592186051376:i64*uns161:i64))+(-4398046512844:i64*((uns169:i64&(~uns164:i64))|((~uns169:i64)&(~uns165:i64)))))+(-9895604653899:i64*(~uns171:i64)))+(9895604653899:i64+((((9895604653899:i64*(uns158:i64&uns165:i64))+(9895604653899:i64*(uns160:i64&uns165:i64)))+(-9895604653899:i64*((uns158:i64&uns159:i64)&uns165:i64)))+(-9895604653899:i64*((uns160:i64&uns165:i64)&uns167:i64)))))+(9895604653899:i64*(((~uns170:i64)&(~uns164:i64))|(uns170:i64&(~uns165:i64))))))&uns174:i64))))";

inputText = "(2374945116151681 + 1152921504606846706*(x&8796093022192)) + (-2383741209174193 + 271*(x&8796093022192))";

inputText = "(3*(x&0x7FFFFFFFFF0) - 0x180000000490) - 0x100000000350 + 0x178";

inputText = "(-43980465112680+(3*(-8796093022208|(8796093022192&(x&~15)))))";

inputText = "((0xFFFFFFFFFFFFFE71 * ~(~a4 & (0x8000000023F - (a1 & 0x7FFFFFFFFF0)))) + (~a4 & (v37 + 0x570)) - ((~a4 & (v37 + 0x570)) | a4 & (0x8000000023F - (a1 & 0x7FFFFFFFFF0)))) + (0xFFFFFFFFFFFFFE70 * (~a4 & (0x8000000023F - (a1 & 0x7FFFFFFFFF0))))";

inputText = "((2 * (a1 & 0x7FFFFFFFFF0)) - 0x100000000350 + 0x178)";

inputText = " (2 * (x & 0x7FFFFFFFFF0)) - 0x100000000350 + 0x178";

var printHelp = () =>
{
    Console.WriteLine("Usage: Simplifier.exe");
    Console.WriteLine("Command line input not preceded by the option indicators below are considered to be input expressions. Only one input expression is accepted.");
    Console.WriteLine("Command line options:");
    Console.WriteLine("    -h:        print usage");
    Console.WriteLine("    -b:        specify the bit number of variables (default is 64)");
    Console.WriteLine("    -z:        enable a check for valid simplification using Z3");
    Console.WriteLine("    -e:        enable equality saturation based simplification");
};

for (int i = 0; i < args.Length; i++)
{
    var arg = args[i];
    switch (arg)
    {
        case "-h":
            printUsage = true;
            break;
        case "-b":  
            bitWidth = uint.Parse(args[i + 1]);
            i++;
            break;
        case "-z":
            proveEquivalence = true;
            break;
        case "-e":
            useEqsat = true;
            break;
        default:
            if (inputText != null)
                throw new ArgumentException($"Found more than one expression argument. Received both {inputText} and {args[i]}");
            inputText = args[i];
            break;
    }
}

if (inputText == null || printUsage)
{
    printHelp();
    return;
}

// For now we only support integer widths of up to 64 bits.
const int maxWidth = 64;
if (bitWidth > maxWidth)
    throw new InvalidOperationException($"Received bit width {bitWidth}, which is greater than the max width {maxWidth}");

var ctx = new AstCtx();
AstIdx.ctx = ctx;
var id = RustAstParser.Parse(ctx, inputText, bitWidth);

Console.WriteLine($"\nExpression: {ctx.GetAstString(id)}\n\n\n");

Console.WriteLine(DagFormatter.Format(ctx, id));


var bx = LinearSimplifier.Run(bitWidth, ctx, id, false, true);

while(false)
{
    var simplifier = new GeneralSimplifier(ctx);

    var sw = Stopwatch.StartNew();
    var r = simplifier.SimplifyGeneral(id);
    sw.Stop();
    Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms");
}

var input = id;
id = ctx.RecursiveSimplify(id);
for (int i = 0; i < 3; i++)
{
    // Apply our simplification procedure.
    var simplifier = new GeneralSimplifier(ctx);
    // Run the simplification pipeline.
    id = simplifier.SimplifyGeneral(id);
    // Try to expand and reduce the polynomial parts(if any exist).
    if(ctx.GetHasPoly(id))
        id = simplifier.ExpandReduce(id);

    if (!useEqsat)
        continue;
    if (bitWidth != 64)
        throw new InvalidOperationException($"Equality saturation is only supported for 64-bit expressions");

    // Apply equality saturation.
    ulong timeout = 2000;
    Console.WriteLine($"Running equality saturation with {timeout}ms timeout...");
    var ast = AstParser.Parse(ctx.GetAstString(id), bitWidth);
    var egg = EqualitySaturation.Run(ast, timeout);
    id = RustAstParser.Parse(ctx, egg.ToString(), bitWidth);

    // Apply term rewriting.
    id = ctx.RecursiveSimplify(id);
    Console.WriteLine($"Eqsat run {i} yielded: {ctx.GetAstString(id)}\n\n");
}

Console.WriteLine($"Simplified to: {ctx.GetAstString(id)}\n\nwith cost: {ctx.GetCost(id)}");

if (!proveEquivalence)
    return;

var z3Ctx = new Context();
var translator = new Z3Translator(ctx, z3Ctx);
var before = translator.Translate(input);
var after = translator.Translate(id);
var solver = z3Ctx.MkSolver("QF_BV");

// Set the maximum timeout to 10 seconds.
var p = z3Ctx.MkParams();
uint solverLimit = 10000;
p.Add("timeout", solverLimit);
solver.Parameters = p;

Console.WriteLine("Proving equivalence...\n");
solver.Add(z3Ctx.MkNot(z3Ctx.MkEq(before, after)));
var check = solver.Check();

var printModel = (Model model) =>
{
    var values = model.Consts.Select(x => $"{x.Key.Name} = {(long)ulong.Parse(model.Eval(x.Value).ToString())}");
    return $"[{String.Join(", ", values)}]";
};

if (check == Status.UNSATISFIABLE)
    Console.WriteLine("Expressions are equivalent.");
else if (check == Status.SATISFIABLE)
    Console.WriteLine($"Expressions are not equivalent. Counterexample:\n{printModel(solver.Model)}");
else
    Console.WriteLine($"Solver timed out - expressions are probably equivalent. Could not find counterexample within {solverLimit}ms");