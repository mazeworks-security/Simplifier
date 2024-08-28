using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;

bool printUsage = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = false;
string inputText = null;

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

for (int i = 0; i < 5; i++)
{
    // Apply our simplification procedure.
    id = GeneralSimplifier.Simplify(ctx, id);
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