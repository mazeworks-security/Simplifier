using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using System.ComponentModel;

bool printUsage = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = false;
string inputText = null;

//inputText = "33*(255&(((1111^x)&y)))";

inputText = "4534434534355345*((((1111^x)&y)))";

// inputText = "546776870978778*(a|4534545345534&b&435345435543453&c|8889879798)";
//inputText = "17*((a&b)^5)";

//inputText = "17*((a^5)&(b^3))";
//inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590)))";
//inputText = "4534434534355345*(1010101|(((((1111^x)&y)))))";
inputText = "0xA96AAABCE6AAAAAA*((a&b)^453457888900)";
inputText = "17*(((a^5)|(b^3))^8)";

inputText = "17*(((a^5)|(b^8))^67567567)";
inputText = "17*(((a^5)|(b^5))^67567567)";
inputText = "17*(((a^5)|(b^3))^67567567)";
inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590)))";
//inputText = "17*(((a^5)|(b^3)))";
//inputText = "17*(((a^5)|(b^3))^8)";

inputText = "17*(a^5)";
inputText = "17*(((a^5)|(b^3))^67567567)";
inputText = "17*(((a^111)|(b^201))^207)";

inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0xA96AAABCE6AAAAAA*((a&b)^453457888900)";


inputText = "17*(((a^5)&(b^3))^8)";

inputText = "17*(a^5)";

inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0*((a&b)^453457888900)";

inputText = "565468546586356689456889*((a|b|c)|11111)";

inputText = "-32434294320249392343249042308*(((a|b|c)^101010101010101010101010101)|0x8023E2D0E5214295)";

//inputText = "546776870978778*((a|4534545345534&(b^(c|d|e|f^5454))&435345435543453&c|8889879798)|((a|(b^(c|d|e|f^5454))&5564456546)^56456654|(5645665&(b^(c|d|e|f^5454))&c^76878889)|(65655656^a&688768&c|(6545654&(b^(c|d|e|f^5454))))|(a^((b^(c|d|e|f^5454))|4554453)^c^6706767590))) + 0*((a&(b^(c|d|e|f^5454)))^453457888900)";

//inputText = "9453443545356765778657658*(43534543453435435435^(a|b))";
//inputText = "7876788766782324334*(45435435453|(a^b^c^234234324234234)|(a&b&~c^909908890809))";

//inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590)))";
//inputText = "1252134335260001084*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0";

//inputText = "455434453543*((a&b&234234)|4534435453)";
//inputText = "17*(((a^5)|(b^3))^8)";
//inputText = "17*(((a^111)|(b^201))^207)";

//inputText = "8*((a^7763425967556079)|((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))))";

//inputText = "0x2D2344BB * (0xE290CB9D * (0x7D4AB29F * (0xA8902D4B - 0x933CDDE7 * (0xF8E74B09 * (0x1F71BE11 * (0x313FF247 * (0xA4554C1F * INPUT - 0x4C98BAA7) + 0xED7F68A) + 0x3390A057) * (0xFD516D86 * (((((0xF2EF57E5 - 0x515C410E * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E)) & 0xA4EA738E) + 0x28AE2087 * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E) + 0x459DC2E6) - 0x118AA8A0) | 0xAD8AC638) + 0x157493D * (((0xF2EF57E5 - 0x515C410E * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E)) & 0xA4EA738E) + 0x28AE2087 * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E) + 0x459DC2E6) - 0x2637E405) - 0x4402F300)) - 0x7B719407) * (0x10C2AAF6 * (((((0xF2EF57E5 - 0x515C410E * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E)) & 0xA4EA738E) + 0x28AE2087 * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E) + 0x459DC2E6) - 0x118AA8A0) | 0xAD8AC638) + 0x779EAA85 * (((0xF2EF57E5 - 0x515C410E * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E)) & 0xA4EA738E) + 0x28AE2087 * (0xD589278B * (0xA4554C1F * INPUT - 0x4C98BAA7) - 0x10B3DE7E) + 0x459DC2E6) - 0x6C185A8D) - 0x31566FCB) - 0x1FA0AEBA";

//inputText = "(3905469437+((4206101778+((3027720224+(3437579321*INPUT))*(906225632+(((4096966087*INPUT)+(4249972102*(1383414215&(2968652697+((872934227*INPUT)+(2766828430&(4180768063+(2549098842*INPUT))))))))+(22497597*(2766828430&(4180768063+(2549098842*INPUT))))))))*(3388525280+(((480010271*INPUT)+(281193206*(1383414215&(2968652697+((872934227*INPUT)+(2766828430&(4180768063+(2549098842*INPUT))))))))+(4154370693*(2766828430&(4180768063+(2549098842*INPUT))))))))";
//inputText = "17*(((a^5)|(b^3))^67567567)"; // Triggers edge case, maximal value or minimal value will not work
//inputText = "17*~(a&11111)";

//inputText = "17*((a|b|c)^5)";

//inputText = "(2^(2&(a&(~b)))) + (2^(2&((~a)&b)))";

//inputText = "127*(a&b&2) + 127*((~a&b)&2)";

//inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0xA96AAABCE6AAAAAA*((x&y)^453457888900)";
//inputText = "7876788766782324334*(45435435453|(a^b^c^234234324234234)|(a&b&~c^909908890809))";

//inputText = "43545435*(x^111111)";
//inputText = "1252134335260001084*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0";


//inputText = "5445645*(((x&111111)^7656657567)|101010)";
//inputText = "8*((a^7763425967556079)|((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))))";
//inputText = "17*(((a^5)|(b^3))^8)";
//inputText = "17*(((a^111)|(b^201))^207)";
//inputText = "17*(((a^111)|(b^201))^207)";

//inputText = "0xA96AAABCE6AAAAAA*((a&b)^453457888900)";

//inputText = "45455434545345345*((a|b|c|4543534435)^(687877678878787&a^b^c))";


//inputText = "-234234*((a|b|c|4543534435)^(687877678878787&a^b^c))";
//inputText = "1252134335260001084*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0";

//inputText = "17*(a^5)";


//inputText = "8*((a^7763425967556079)|((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))))";
//inputText = "17*(((a^111)|(b^201))^207)";

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
var id = RustAstParser.Parse(ctx, inputText, bitWidth);

Console.WriteLine($"\nExpression: {ctx.GetAstString(id)}\n\n");

var res = LinearSimplifier.Run(bitWidth, ctx, id, false, true);
Console.WriteLine(ctx.GetAstString(res));
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

// TODO: Prove equivalence.
Console.WriteLine($"Simplified to: {ctx.GetAstString(id)}\n\nwith cost: {ctx.GetCost(id)} ");