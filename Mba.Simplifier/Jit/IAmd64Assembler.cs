using Iced.Intel;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Jit
{
    public interface IAmd64Assembler
    {
        public void PushReg(Register reg);

        public void PushMem64(Register baseReg, int offset);

        public void PopReg(Register reg);

        public void MovRegReg(Register reg1, Register reg2);

        public void MovRegMem64(Register dstReg, Register baseReg, int offset);

        public void MovMem64Reg(Register baseReg, int offset, Register srcReg);

        public void MovabsRegImm64(Register reg1, ulong imm);

        public void AddRegReg(Register reg1, Register reg2);

        public void AddRegImm32(Register reg1, uint imm32);

        public void SubRegImm32(Register reg1, uint imm32);

        public void ImulRegReg(Register reg1, Register reg2);

        public void AndRegReg(Register reg1, Register reg2);

        public void AndRegImm32(Register reg1, uint imm);

        public void AndMem64Reg(Register baseReg, int offset, Register srcReg);

        public void OrRegReg(Register reg1, Register reg2);

        public void XorRegReg(Register reg1, Register reg2);

        public void NotReg(Register reg1);

        public void ShlRegCl(Register reg);

        public void ShrRegCl(Register reg1);

        public void ShrRegImm8(Register reg, byte imm8);

        public void CmpRegReg(Register reg1, Register reg2);

        public void TestRegReg(Register reg1, Register reg2);

        public void CmoveRegReg(Register reg1, Register reg2);

        public void SeteReg(Register reg1);

        public void SetneReg(Register reg1);

        public void SetaReg(Register reg1);

        public void SetbReg(Register reg1);

        public void CallReg(Register reg1);

        public void Ret();

        public List<Instruction> GetInstructions();

        public List<byte> GetBytes();

        public void Reset();
    }
}
