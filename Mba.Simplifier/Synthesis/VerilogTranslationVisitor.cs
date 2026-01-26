using Antlr4.Runtime.Misc;
using Mba.Common.Parsing;
using Mba.Simplifier.Bindings;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Security.Cryptography.X509Certificates;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public class VerilogTranslationVisitor : VerilogBaseVisitor<AstIdx?>
    {
        private readonly AstCtx ctx;

        private Dictionary<string, AstIdx> inputs = new();

        public Dictionary<string, AstIdx?[]> outputs = new();

        private Dictionary<string, AstIdx> wireAssignments = new();


        public VerilogTranslationVisitor(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public override AstIdx? VisitDecl([NotNull] VerilogParser.DeclContext context)
        {
            // Skip wire declarations
            if (context.WIRE() != null)
                return base.VisitDecl(context);

            var range = context.range();
            var rangeEnd = ParseNumber(range.number()[0]);
            var rangeBegin = ParseNumber(range.number()[1]);
            if (rangeBegin != 0)
                throw new InvalidOperationException($"Invalid range {range.GetText()}");

            var name = context.idList().identifier().Single().GetText();
            var width = (rangeEnd + 1);
            var symbol = ctx.Symbol(name, (byte)width);
            bool isInput = context.INPUT() != null;
            if (isInput)
                inputs.Add(name, symbol);
            else
                outputs.Add(name, new AstIdx?[width]);

            return base.VisitDecl(context);
        }

        public override AstIdx? VisitAssignStmt([NotNull] VerilogParser.AssignStmtContext context)
        {
            var name = context.lhs().identifier().GetText();
            var bitSelect = context.lhs().bitSelect();
            var assignment = Visit(context.expression());
            if (bitSelect == null)
            {
                wireAssignments[name] = assignment.Value;
                return null;
            }

            // Otherwise assume this is an assignment to a specific bit of an output variable
            if (!outputs.ContainsKey(name))
                throw new InvalidOperationException($"Cannot assign range to non-output!");

            var index = (int)ParseNumber(bitSelect.number());
            outputs[name][index] = assignment;
            return null;
        }

        public override AstIdx? VisitParenthesizedExpression([NotNull] VerilogParser.ParenthesizedExpressionContext context)
        {
            return Visit(context.expression());
        }

        public override AstIdx? VisitAndExpression([NotNull] VerilogParser.AndExpressionContext context)
        {
            var op0 = Visit(context.expression()[0]);
            var op1 = Visit(context.expression()[1]);
            return ctx.And(op0.Value, op1.Value);
        }

        public override AstIdx? VisitOrExpression([NotNull] VerilogParser.OrExpressionContext context)
        {
            var op0 = Visit(context.expression()[0]);
            var op1 = Visit(context.expression()[1]);
            return ctx.Or(op0.Value, op1.Value);
        }

        public override AstIdx? VisitXorExpression([NotNull] VerilogParser.XorExpressionContext context)
        {
            var op0 = Visit(context.expression()[0]);
            var op1 = Visit(context.expression()[1]);
            return ctx.Xor(op0.Value, op1.Value);
        }

        public override AstIdx? VisitNegExpression([NotNull] VerilogParser.NegExpressionContext context)
        {
            var op0 = Visit(context.expression());
            var neg = ctx.Neg(op0.Value);

            var w = ctx.GetWidth(neg);
            // neg = ctx.And(ctx.Constant(1, w), neg);
            return neg;
        }

        public override AstIdx? VisitLhsExpression([NotNull] VerilogParser.LhsExpressionContext context)
        {
            var name = context.lhs().identifier().GetText();
            var bitSelect = context.lhs().bitSelect();
            if (bitSelect == null)
                return wireAssignments[name];

            var index = (byte)ParseNumber(bitSelect.number());

            // Shift the selected bit to the 0th index
            var symbol = inputs[name];
            var w = ctx.GetWidth(symbol);
            //var output = ctx.Lshr(symbol, ctx.Constant((ulong)index, w));

            //output = ctx.And(ctx.Constant(1, w), output);
            var output = ctx.Extract(symbol, index, index);
            return output;
        }


        private static ulong ParseNumber(VerilogParser.NumberContext context)
        {
            return ulong.Parse(context.GetText());
        }


    }
}
