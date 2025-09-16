using Mba.Common.Interop;
using Mba.Interop;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public struct OpaqueOptimal5Db { }

    [StructLayout(LayoutKind.Explicit)]
    public unsafe struct GateVecFast
    {
        // 24 bytes = 12 gates
        [FieldOffset(0)]
        public fixed ushort Gates[12]; 
        [FieldOffset(24)]
        // Between 0 and 12, inclusive
        public byte NumGates;
        [FieldOffset(25)]
        public byte Output;
    }

    public unsafe class Optimal5
    {
        private OpaqueOptimal5Db* handle;

        public static readonly Optimal5 Instance = new();

        private unsafe Optimal5()
        {
            handle = Api.GetOptimal5Db(new MarshaledString("knuth5.dat"));
        }

        public unsafe GateVecFast Lookup(uint truthTable)
        {
            GateVecFast gv;
            Api.LookupOptimal5(this, truthTable, &gv);
            return gv;
        }

        public unsafe void PrintGatevec(GateVecFast gatevec)
        {
            Api.PrintGatevec(&gatevec);
        }

        public unsafe static implicit operator OpaqueOptimal5Db*(Optimal5 ctx) => (OpaqueOptimal5Db*)ctx.handle;

        protected static class Api
        {
            [DllImport("Mba.FFI")]
            public unsafe static extern OpaqueOptimal5Db* GetOptimal5Db(sbyte* databasePath);

            [DllImport("Mba.FFI")]
            public unsafe static extern void LookupOptimal5(OpaqueOptimal5Db* db, uint truthTable, GateVecFast* output);

            [DllImport("Mba.FFI")]
            public unsafe static extern void PrintGatevec( GateVecFast* output);
        }
    }
}
