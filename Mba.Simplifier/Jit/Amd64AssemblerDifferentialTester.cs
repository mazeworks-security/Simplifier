using Iced.Intel;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;
using static Iced.Intel.AssemblerRegisters;

namespace Mba.Simplifier.Jit
{
    public unsafe class Amd64AssemblerDifferentialTester
    {
        private readonly Random rand = new();

        private readonly Register[] registers =
        {
            Register.RAX, Register.RCX, Register.RDX, Register.RBX,
            Register.RSI, Register.RDI, Register.RSP, Register.RBP,
            Register.R8,Register.R9, Register.R10, Register.R11,
            Register.R12, Register.R13, Register.R14, Register.R15
        };

        private readonly IcedAmd64Assembler icedAssembler;

        private readonly FastAmd64Assembler fastAssembler;

        public unsafe Amd64AssemblerDifferentialTester(byte* buffer)
        {
            fastAssembler = new FastAmd64Assembler(buffer);
            icedAssembler = new IcedAmd64Assembler(new Assembler(64));
        }

        public static void Test()
        {
            var buffer = new byte[64 * 4096];
            fixed(byte* p = buffer) 
            {
                new Amd64AssemblerDifferentialTester(p).Run();
            }
        }

        public void Run()
        {
            for (int i = 0; i < registers.Length; i++)
            {
                DiffRegInsts(registers[i]);
                for (int j = i + 1; j < registers.Length; j++)
                    DiffRegRegInsts(registers[i], registers[j]);
            }
        }

        private void DiffRegInsts(Register reg1)
        {
            Diff(nameof(IAmd64Assembler.PushReg), reg1);
            Diff(nameof(IAmd64Assembler.PopReg), reg1);
            Diff(nameof(IAmd64Assembler.NotReg), reg1);
            Diff(nameof(IAmd64Assembler.ShlRegCl), reg1);
            Diff(nameof(IAmd64Assembler.ShrRegCl), reg1);
            Diff(nameof(IAmd64Assembler.CallReg), reg1);

            // Diff reg, constant instants
            for (int _ = 0; _ < 100; _++)
            {
                var c = (ulong)rand.NextInt64();
                c |= rand.Next(0, 2) == 0 ? 0 : (1ul << 63);

                Diff(nameof(IAmd64Assembler.MovabsRegImm64), reg1, c);
                Diff(nameof(IAmd64Assembler.AddRegImm32), reg1, (uint)c);
                Diff(nameof(IAmd64Assembler.SubRegImm32), reg1, (uint)c);
                Diff(nameof(IAmd64Assembler.AndRegImm32), reg1, (uint)c);
                Diff(nameof(IAmd64Assembler.ShrRegImm8), reg1, (byte)c);
                if (reg1 != rsp)
                    Diff(nameof(IAmd64Assembler.PushMem64), reg1, (int)c);
            }
        }

        private void DiffRegRegInsts(Register reg1, Register reg2)
        {
            // Diff reg, reg insts
            Diff(nameof(IAmd64Assembler.MovRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.MovRegReg), reg2, reg1);
            Diff(nameof(IAmd64Assembler.AddRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.AddRegReg), reg2, reg1);
            Diff(nameof(IAmd64Assembler.AndRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.AndRegReg), reg2, reg1);
            Diff(nameof(IAmd64Assembler.OrRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.OrRegReg), reg2, reg1);
            Diff(nameof(IAmd64Assembler.XorRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.XorRegReg), reg2, reg1);
            Diff(nameof(IAmd64Assembler.ImulRegReg), reg1, reg2);
            Diff(nameof(IAmd64Assembler.ImulRegReg), reg2, reg1);

            // Diff reg, reg, constant insts
            for (int _ = 0; _ < 100; _++)
            {
                var c = rand.NextInt64();
                Diff(nameof(IAmd64Assembler.MovMem64Reg), reg1, (int)c, reg2);
                Diff(nameof(IAmd64Assembler.MovMem64Reg), reg2, (int)c, reg1);
                Diff(nameof(IAmd64Assembler.MovRegMem64), reg1, reg2, (int)c);
                Diff(nameof(IAmd64Assembler.MovRegMem64), reg2, reg1, (int)c);
                Diff(nameof(IAmd64Assembler.AndMem64Reg), reg1, (int)c, reg2);
                Diff(nameof(IAmd64Assembler.AndMem64Reg), reg2, (int)c, reg1);
            }
        }

        private void Diff(string methodName, params object[] args)
        {
            // Assemble the instruction using both assemblers
            var method = typeof(IAmd64Assembler).GetMethod(methodName, BindingFlags.Public | BindingFlags.Instance);
            method.Invoke(icedAssembler, args);
            method.Invoke(fastAssembler, args);

            // Throw if they are not equivalent
            Compare();

            // Reset the internal state of both assemblers
            icedAssembler.Reset();
            fastAssembler.Reset();
        }

        private void Compare()
        {
            var icedInsts = icedAssembler.GetInstructions();
            var icedBytes = icedAssembler.GetBytes();
            var ourInsts = fastAssembler.GetInstructions();
            var ourBytes = fastAssembler.GetBytes();

            if (icedInsts.Count == 0 || icedBytes.Count == 0 || icedInsts.Count != ourInsts.Count)
                throw new InvalidOperationException();

            // Check if our instructions resolve to the same string
            bool valid = ourInsts.Single().ToString() == icedInsts.Single().ToString();
            if (!icedInsts.SequenceEqual(ourInsts) && !valid)
            {
                throw new InvalidOperationException($"Instruction {icedInsts.Single()} and {ourInsts.Single()} not equivalent!");
            }
        }

    }
}
