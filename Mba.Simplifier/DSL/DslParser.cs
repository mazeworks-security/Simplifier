using Mba.Ast;
using Mba.Common.Parsing;
using Mba.Parsing;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public static class DslParser
    {
        public static Dsl ParseDsl(string fileContents)
            => (Dsl)AstParser.ParseDsl(fileContents, 64, new(), new (), new ());
    }
}