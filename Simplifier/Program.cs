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
using System.ComponentModel;
using System.Diagnostics;

bool printUsage = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = true;
string inputText = "a|b|c";

inputText = "b|(a^c)";

inputText = "(((uns19:i8*4:i8)&4:i8) zx i32)";

inputText = "((((1:i32&((uns17:i8 zx i32)&(~uns18:i32)))|(4294964010:i32&(~((uns17:i8 zx i32)|(~uns18:i32)))))|(4294964011:i32&((uns17:i8 zx i32)&uns18:i32)))|(4:i32*(1:i32&(uns19:i8 zx i32))))";

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