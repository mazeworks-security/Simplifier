using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.DSL;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.LinEq;
using Mba.Simplifier.Minimization;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System.ComponentModel;
using System.Diagnostics;

bool printUsage = false;
bool onlyLinear = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = false;
string inputText = null;


//Debugger.Break();

//PolyInverter.InterpolateMvExample();

inputText = " -x**63 + 64*x**62 - 2016*x**61 + 41664*x**60 - 635376*x**59 + 7624512*x**58 - 74974368*x**57 + 621216192*x**56 - 4426165368*x**55 + 27540584512*x**54 - 151473214816*x**53 + 743595781824*x**52 - 3284214703056*x**51 + 13136858812224*x**50 - 47855699958816*x**49 + 159518999862720*x**48 - 488526937079580*x**47 + 1379370175283520*x**46 - 3601688791018080*x**45 + 8719878125622720*x**44 - 19619725782651120*x**43 + 41107996877935680*x**42 - 80347448443237920*x**41 + 146721427591999680*x**40 - 250649105469666120*x**39 + 401038568751465792*x**38 - 601557853127198688*x**37 + 846636978475316672*x**36 - 1118770292985239888*x**35 + 1388818294740297792*x**34 - 1620288010530347424*x**33 + 1777090076065542336*x**32 - 1832624140942590534*x**31 + 1777090076065542336*x**30 - 1620288010530347424*x**29 + 1388818294740297792*x**28 - 1118770292985239888*x**27 + 846636978475316672*x**26 - 601557853127198688*x**25 + 401038568751465792*x**24 - 250649105469666120*x**23 + 146721427591999680*x**22 - 80347448443237920*x**21 + 41107996877935680*x**20 - 19619725782651120*x**19 + 8719878125622720*x**18 - 3601688791018080*x**17 + 1379370175283520*x**16 - 488526937079580*x**15 + 159518999862720*x**14 - 47855699958816*x**13 + 13136858812224*x**12 - 3284214703056*x**11 + 743595781824*x**10 - 151473214816*x**9 + 27540584512*x**8 - 4426165368*x**7 + 621216192*x**6 - 74974368*x**5 + 7624512*x**4 - 635376*x**3 + 41664*x**2 - 2016*x + 64";

inputText = "205*x*x*x*x*x*x*x";

inputText = "64 + 224*x + 64*x*x + 212*x*x*x*x*x + 205*x*x*x*x*x*x*x";

inputText = "64 + 224*x + 64*x*x";

inputText = "1*x";

inputText = " -x**63 + 64*x**62 - 2016*x**61 + 41664*x**60 - 635376*x**59 + 7624512*x**58 - 74974368*x**57 + 621216192*x**56 - 4426165368*x**55 + 27540584512*x**54 - 151473214816*x**53 + 743595781824*x**52 - 3284214703056*x**51 + 13136858812224*x**50 - 47855699958816*x**49 + 159518999862720*x**48 - 488526937079580*x**47 + 1379370175283520*x**46 - 3601688791018080*x**45 + 8719878125622720*x**44 - 19619725782651120*x**43 + 41107996877935680*x**42 - 80347448443237920*x**41 + 146721427591999680*x**40 - 250649105469666120*x**39 + 401038568751465792*x**38 - 601557853127198688*x**37 + 846636978475316672*x**36 - 1118770292985239888*x**35 + 1388818294740297792*x**34 - 1620288010530347424*x**33 + 1777090076065542336*x**32 - 1832624140942590534*x**31 + 1777090076065542336*x**30 - 1620288010530347424*x**29 + 1388818294740297792*x**28 - 1118770292985239888*x**27 + 846636978475316672*x**26 - 601557853127198688*x**25 + 401038568751465792*x**24 - 250649105469666120*x**23 + 146721427591999680*x**22 - 80347448443237920*x**21 + 41107996877935680*x**20 - 19619725782651120*x**19 + 8719878125622720*x**18 - 3601688791018080*x**17 + 1379370175283520*x**16 - 488526937079580*x**15 + 159518999862720*x**14 - 47855699958816*x**13 + 13136858812224*x**12 - 3284214703056*x**11 + 743595781824*x**10 - 151473214816*x**9 + 27540584512*x**8 - 4426165368*x**7 + 621216192*x**6 - 74974368*x**5 + 7624512*x**4 - 635376*x**3 + 41664*x**2 - 2016*x + 64";




//PolyInverter.Hello();

//inputText = " (64:i8+((((224:i8*x:i8)+(64:i8*(x:i8**2:i8)))+(212:i8*(x:i8**5:i8)))+(205:i8*(x:i8**7:i8))))";

// NewtonInterpolation.MvNewtonNew();

NewtonInterpolation.NewClassic();

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
        case "-l":
            onlyLinear = true;
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

// Run only the linear simplifier if requested
if (onlyLinear)
{
    id = LinearSimplifier.Run(bitWidth, ctx, input, false, true);
    goto done;
}

id = ctx.RecursiveSimplify(id);
for (int i = 0; i < 3; i++)
{
    // Apply our simplification procedure.
    var simplifier = new GeneralSimplifier(ctx);
    // Run the simplification pipeline.
    id = simplifier.SimplifyGeneral(id);
    // Try to expand and reduce the polynomial parts(if any exist).
    if (ctx.GetHasPoly(id))
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

done:
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