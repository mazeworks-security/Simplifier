using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public struct AstIdx
    {
        public uint Idx;

        public AstIdx(uint idx)
        {
            Idx = idx;
        }

        public override string ToString()
        {
            if (ctx == null)
                return Idx.ToString();
            return ctx.GetAstString(Idx);
        }

        public override int GetHashCode()
        {
            return Idx.GetHashCode();
        }

        public unsafe static implicit operator uint(AstIdx reg) => reg.Idx;

        public unsafe static implicit operator AstIdx(uint reg) => new AstIdx(reg);

        // This is a hack to allow viewing AST nodes in the debugger.
        public static AstCtx ctx;
    }
}
