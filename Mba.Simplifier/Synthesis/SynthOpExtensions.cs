using Mba.Simplifier.Synth;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public static class SynthOpExtensions
    {
        public static bool IsCommutative(this SynthOpc opc)
        {
            return opc switch
            {
                SynthOpc.And or SynthOpc.Or or SynthOpc.Xor or SynthOpc.Add or SynthOpc.Mul => true,
                SynthOpc.Not or SynthOpc.Sub or SynthOpc.Lshr or SynthOpc.Ashr or SynthOpc.Shl or SynthOpc.TruthTable or SynthOpc.Constant => false,
                _ => throw new NotImplementedException(),
            };
        }


        public static bool IsIdempotent(this SynthOpc opc)
        {
            return opc switch
            {
                SynthOpc.And or SynthOpc.Xor or SynthOpc.Or or SynthOpc.Sub => true,
                _ => false,
            };
        }

        public static int GetOperandCount(this SynthOpc opc)
        {
            return opc switch
            {
                SynthOpc.And or SynthOpc.Or or SynthOpc.Xor or SynthOpc.Add or SynthOpc.Sub or SynthOpc.Mul => 2,
                SynthOpc.Not => 1,
                SynthOpc.Lshr or SynthOpc.Ashr or SynthOpc.Shl => 2, 
                SynthOpc.TruthTable => 2,
                SynthOpc.Constant => 0,
            };
        }

        public static int GetCost(this SynthOpc opc)
        {
            //return opc == SynthOpc.Mul ? 1 : 0;

            return opc switch
            {
                SynthOpc.And => 1,
                SynthOpc.Or => 1,
                SynthOpc.Xor => 1,
                SynthOpc.Not => 1,
                SynthOpc.Add => 1,
                SynthOpc.Sub => 1,
                SynthOpc.Mul => 3,
                SynthOpc.Lshr => 1,
                SynthOpc.TruthTable => 1,
                SynthOpc.Constant => 0,
            };
        }
    }
}
