using Mba.Ast;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Utility
{
    public class RustAstParser
    {
        private readonly AstCtx ctx;

        private readonly string input;

        private readonly byte bitWidth;

        public static AstIdx Parse(AstCtx ctx, string input, uint bitWidth)
            => new RustAstParser(ctx, input, bitWidth).Parse();

        private RustAstParser(AstCtx ctx, string input, uint bitSize)
        {
            this.ctx = ctx;
            this.input = input;
            this.bitWidth = (byte)bitSize;
        }

        private AstIdx Parse()
        {
            // For now we just reuse MSiMBA's ast parser and translate the result.
            var ast = AstParser.Parse(input, bitWidth);
            return Convert(ast);
        }

        public AstIdx Convert(AstNode node)
        {
            var binop = (AstOp op) => ctx.Binop(op, Convert(node.Children[0]), Convert(node.Children[1]));

            return node.Kind switch
            {
                AstKind.Const => ctx.Constant((ulong)(node as ConstNode).Value, node.BitSize),
                AstKind.Var => ctx.Symbol((node as VarNode).Name, (byte)node.BitSize),
                AstKind.Add => binop(AstOp.Add),
                AstKind.Power => binop(AstOp.Pow),
                AstKind.Mul => binop(AstOp.Mul),
                AstKind.And => binop(AstOp.And),
                AstKind.Or => binop(AstOp.Or),
                AstKind.Xor => binop(AstOp.Xor),
                AstKind.Neg => ctx.Neg(Convert(node.Children[0])),
                AstKind.Lshr => binop(AstOp.Lshr),
                AstKind.Zext => ctx.Zext(Convert(node.Children[0]), (byte)node.BitSize),
                AstKind.Trunc => ctx.Trunc(Convert(node.Children[0]), (byte)node.BitSize),
                _ => throw new InvalidOperationException($"Ast kind {node.Kind} is not supported!")
            };
        }
    }
}
