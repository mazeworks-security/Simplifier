using Mba.Ast;
using Mba.Common.Interop;
using Mba.Common.Utility;
using Mba.Interop;
using Mba.Parsing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public static class EqualitySaturation
    {
        public static unsafe AstNode Run(AstNode input, ulong ms)
        {
            var str = EggFormatter.FormatAst(input);
            var outStr = StringMarshaler.AcquireString(Api.SimplifyViaEqsat(new MarshaledString(str), ms));
            var output = EggExpressionParser.Parse(outStr, input.BitSize);
            return output;
        }

        protected static class Api
        {
            [DllImport("eq_sat")]
            public unsafe static extern sbyte* SimplifyViaEqsat(sbyte* pStr, ulong ms);
        }
    }
}
