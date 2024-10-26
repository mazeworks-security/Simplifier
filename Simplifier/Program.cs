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

inputText = "7876788766782324334*(45435435453|(a^b^c^234234324234234)|(a&b&~c^909908890809))";

//inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590)))";
//inputText = "546776870978778*((a|4534545345534&b&435345435543453&c|8889879798)|((a|b&5564456546)^56456654|(5645665&b&c^76878889)|(65655656^a&688768&c|(6545654&b))|(a^(b|4554453)^c^6706767590))) + 0xA96AAABCE6AAAAAA*((a&b)^453457888900)";
//inputText = "17*~(a&11111)";
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

LinearSimplifier.Run(bitWidth, ctx, id, false, true);

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