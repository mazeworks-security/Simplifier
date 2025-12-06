using Mba.Ast;
using Mba.Common.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Parsing;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public class NewEggBackend
    {
        IReadOnlyList<DslFunction> dslFunctions;

        IReadOnlyList<DslRule> dslRules;

        private IReadOnlyDictionary<string, DslFunction> nameToFunc;

        public NewEggBackend(Dsl dsl)
        {
            dslFunctions = dsl.FunctionGroups.Single().Functions;
            dslRules = dsl.RuleGroups.Single().Rules;
            nameToFunc = dslFunctions.ToDictionary(x => x.Name, x => x);
        }

        public void Generate()
        {
            InlineFunctions();
        }

        private void InlineFunctions()
        {
            foreach(var dslFunction in dslFunctions)
            {
                // Skip bodyless functions.
                if (dslFunction.IsBuiltin)
                    continue;

                Func<AstNode, AstNode> clonePred = (AstNode node) =>
                {
                    // Skip if this is not an intrinsic call.
                    if (node is not IntrinsicCallNode intrinsicCall)
                        return null;

                    // Skip if the call cannot be inlined
                    var callTarget = nameToFunc[intrinsicCall.Name];
                    if (callTarget.IsBuiltin)
                    {
                        return new IntrinsicCallNode(intrinsicCall.Name, callTarget.ReturnType.Width, intrinsicCall.Children.Select(x => AstCloner.Clone(x, clonePred)).ToList());
                    }

                    // Otherwise the call can be inlined.
                    Dictionary<string, AstNode> varToReplacement = new();
                    for(int i = 0; i < callTarget.Arguments.Count; i++)
                    {
                        var arg = callTarget.Arguments[i];
                        varToReplacement[arg.Name] = intrinsicCall.Children[i];
                    }

                    var inlined = AstCloner.ReplaceVars(callTarget.Body, varToReplacement);

                    return inlined;
                };

                var newBody = AstCloner.Clone(dslFunction.Body, clonePred);
                var s = newBody.ToString();
                Debugger.Break();

            }
        }
    }
}
