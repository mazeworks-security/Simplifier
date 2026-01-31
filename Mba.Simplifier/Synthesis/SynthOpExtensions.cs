using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public static class SynthOpExtensions
    {
        public static bool IsAssociative(this SynthOpc opc)
        {
            return opc switch
            {
                SynthOpc.And or SynthOpc.Or or SynthOpc.Xor or SynthOpc.Add or SynthOpc.Mul => true,
                _ => false,
            };
        }


        public static bool IsIdempotent(this SynthOpc opc)
        {
            return opc switch
            {
                SynthOpc.And or SynthOpc.Xor or SynthOpc.Xor => true,
                _ => false,
            };
        }
    }
}
