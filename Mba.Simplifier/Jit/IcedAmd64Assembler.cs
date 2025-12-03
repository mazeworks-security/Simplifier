using Iced.Intel;
using Mba.Common.MSiMBA;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using static Iced.Intel.AssemblerRegisters;

namespace Mba.Simplifier.Jit
{
    public class IcedAmd64Assembler : IAmd64Assembler
    {
        private readonly Assembler assembler;

        public IcedAmd64Assembler(Assembler assembler)
        {
            this.assembler = assembler;
        }

        public List<byte> GetBytes()
        {
            return JitUtils.EncodeInstructions(GetInstructions(), 0, out ulong endRip).ToList();
        }

        public List<Instruction> GetInstructions()
        {
            return assembler.Instructions.ToList();
        }

        public void PushReg(Register reg)
        {
            assembler.push(Reg.Conv(reg));
        }

        public void PopReg(Register reg)
        {
            assembler.pop(Reg.Conv(reg));
        }

        public void MovRegReg(Register reg1, Register reg2)
        {
            assembler.mov(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void MovMem64Reg(Register baseReg, int offset, Register srcReg)
        {
            assembler.mov(__qword_ptr[Reg.Conv(baseReg) + offset], Reg.Conv(srcReg));
        }

        public void MovRegMem64(Register dstReg, Register baseReg, int offset)
        {
            assembler.mov(Reg.Conv(dstReg), __qword_ptr[Reg.Conv(baseReg) + offset]);
        }

        public void MovabsRegImm64(Register reg1, ulong imm)
        {
            assembler.mov(Reg.Conv(reg1), imm);
        }

        public void AddRegReg(Register reg1, Register reg2)
        {
            assembler.add(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void AddRegImm32(Register reg1, uint imm32)
        {
            assembler.add(Reg.Conv(reg1), (int)imm32);
        }

        public void SubRegImm32(Register reg1, uint imm32)
        {
            assembler.sub(Reg.Conv(reg1), (int)imm32);
        }

        public void ImulRegReg(Register reg1, Register reg2)
        {
            assembler.imul(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void AndRegReg(Register reg1, Register reg2)
        {
            assembler.and(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void AndRegImm32(Register reg1, uint imm32)
        {
            assembler.and(Reg.Conv(reg1), (int)imm32);
        }

        public void AndMem64Reg(Register baseReg, int offset, Register srcReg)
        {
            assembler.and(__qword_ptr[Reg.Conv(baseReg) + offset], Reg.Conv(srcReg));
        }

        public void OrRegReg(Register reg1, Register reg2)
        {
            assembler.or(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void XorRegReg(Register reg1, Register reg2)
        {
            assembler.xor(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void NotReg(Register reg1)
        {
            assembler.not(Reg.Conv(reg1));
        }

        public void ShlRegCl(Register reg1)
        {
            assembler.shl(Reg.Conv(reg1), cl);
        }

        public void ShrRegCl(Register reg1)
        {
            assembler.shr(Reg.Conv(reg1), cl);
        }

        public void ShrRegImm8(Register reg, byte imm8)
        {
            assembler.shr(Reg.Conv(reg), imm8);
        }

        public void CmpRegReg(Register reg1, Register reg2)
        {
            assembler.cmp(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void TestRegReg(Register reg1, Register reg2)
        {
            assembler.test(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void CmoveRegReg(Register reg1, Register reg2)
        {
            assembler.cmove(Reg.Conv(reg1), Reg.Conv(reg2));
        }

        public void SeteReg(Register reg1)
        {
            assembler.sete(Reg.Conv8(reg1));
        }

        public void SetneReg(Register reg1)
        {
            assembler.setne(Reg.Conv8(reg1));
        }

        public void SetaReg(Register reg1)
        {
            assembler.seta(Reg.Conv8(reg1));
        }

        public void SetbReg(Register reg1)
        {
            assembler.setb(Reg.Conv8(reg1));
        }

        public void CallReg(Register reg1)
        {
            assembler.call(Reg.Conv(reg1));
        }

        public void Ret()
        {
            assembler.ret();
        }

        public void Reset()
        {
            assembler.Reset();
        }

        public void PushMem64(Register baseReg, int offset)
        {
            assembler.push(__qword_ptr[Reg.Conv(baseReg) + offset]);
        }
    }
}
