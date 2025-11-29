using Iced.Intel;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Interpreter;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.Arm;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Jit
{
    unsafe ref struct StackBuffer
    {
        public byte* Ptr;

        public uint Offset;

        public StackBuffer(byte* ptr)
        {
            this.Ptr = ptr;
        }

        public void PushU8(byte value)
        {
            Ptr[Offset++] = value;
        }

        public void PushI32(int value)
            => PushU32((uint)value);

        public void PushU32(uint value)
        {
            *(uint*)&Ptr[Offset] = value;
            Offset += 4;
        }

        public void PushU64(ulong value)
        {
            *(ulong*)&Ptr[Offset] = value;
            Offset += 8;
        }
    }

    public unsafe class FastAmd64Assembler : IAmd64Assembler
    {
        public byte* start;

        public byte* ptr;

        public int offset = 0;

        public List<Instruction> Instructions => GetInstructions();

        public FastAmd64Assembler(byte* ptr)
        {
            start = ptr;
            this.ptr = ptr;
        }

        private unsafe void EmitBytes(params byte[] bytes)
        {
            fixed(byte* p = &bytes[0])
            {
                Memcpy(ptr, p, (uint)bytes.Length);
            }

            ptr += bytes.Length;
        }

        private void EmitBuffer(StackBuffer buffer)
        {
            Memcpy(ptr, buffer.Ptr, buffer.Offset);
            ptr += buffer.Offset;
        }

        private void Memcpy(void* destination, void* source, uint byteCount)
        {
            Unsafe.CopyBlockUnaligned(destination, source, byteCount);
        }

        public void PushReg(Register reg)
        {
            if (reg >= Register.RAX && reg <= Register.RDI)
            {
                byte opcode = (byte)(0x50 + GetRegisterCode(reg));
                EmitBytes(opcode);
                return;
            }

            if (reg >= Register.R8 && reg <= Register.R15)
            {
                byte rex = 0x41;
                byte opcode = (byte)(0x50 + (int)reg - (int)Register.R8);
                EmitBytes(rex, opcode);
                return;
            }

            throw new ArgumentException("Invalid register for PUSH instruction.");
            
        }
        // push qword ptr [baseReg+offset]
        public void PushMem64(Register baseReg, int offset)
        {
            byte* p = stackalloc byte[8];
            var arr = new StackBuffer(ptr);

            if (IsExtended(baseReg))
            {
                byte rex = 0x49;
                arr.PushU8(rex);
            }

            byte opcode = 0xFF;
            byte modrm = (byte)(0x80 | (0x06 << 3) | (GetRegisterCode(baseReg) & 0x07));
            arr.PushU8(opcode);
            arr.PushU8(modrm);

            if (baseReg == Register.RSP || baseReg == Register.R12)
            {
                byte sib = (byte)(0x00 | (0x04 << 3) | (GetRegisterCode(baseReg) & 0x07));
                arr.PushU8(sib); 
            }

            arr.PushI32(offset);

            EmitBuffer(arr);
        }

        public void PopReg(Register reg)
        {
            if (reg >= Register.RAX && reg <= Register.RDI)
            {
                byte opcode = (byte)(0x58 + GetRegisterCode(reg));
                EmitBytes(opcode);
                return;
            }

            if (reg >= Register.R8 && reg <= Register.R15)
            {
                byte rex = 0x41;
                byte opcode = (byte)(0x58 + GetRegisterCode(reg) - 8);
                EmitBytes(rex, opcode);
                return;
            }

            throw new ArgumentException($"Cannot pop {reg}");
            
        }

        public void OpcodeRegReg(byte opcode, Register reg1, Register reg2)
        {
            byte rex = 0x48; 
            if (IsExtended(reg1)) rex |= 0x01; 
            if (IsExtended(reg2)) rex |= 0x04;

            byte modrm = (byte)(0xC0 | ((GetRegisterCode(reg2) & 0x07) << 3) | (GetRegisterCode(reg1) & 0x07));
            EmitBytes(rex, opcode, modrm);
        }

        public void MovRegReg(Register reg1, Register reg2)
            => OpcodeRegReg(0x89, reg1, reg2);

        public void MovRegMem64(Register dstReg, Register baseReg, int offset)
        {
            byte* p = stackalloc byte[8];
            var arr = new StackBuffer(ptr);

            byte rex = 0x48; 
            if (IsExtended(dstReg)) rex |= 0x04;
            if (IsExtended(baseReg)) rex |= 0x01; 

            byte opcode = 0x8B;
            byte modrm = (byte)(0x80 | ((GetRegisterCode(dstReg) & 0x07) << 3) | (GetRegisterCode(baseReg) & 0x07));

            arr.PushU8(rex);
            arr.PushU8(opcode);
            arr.PushU8(modrm);

            if (baseReg == Register.RSP || baseReg == Register.R12)
            {
                byte sib = (byte)(0x00 | (0x04 << 3) | (GetRegisterCode(baseReg) & 0x07));
                arr.PushU8(sib);
            }

            arr.PushI32(offset);

            EmitBuffer(arr);
        }

        // mov qword ptr [baseReg + offset], srcReg
        public void MovMem64Reg(Register baseReg, int offset, Register srcReg)
        {
            byte* p = stackalloc byte[8];
            var arr = new StackBuffer(ptr);

            byte rex = 0x48; 
            if (IsExtended(srcReg)) rex |= 0x04; 
            if (IsExtended(baseReg)) rex |= 0x01; 

            byte opcode = 0x89;
            byte modrm = (byte)(0x80 | ((GetRegisterCode(srcReg) & 0x07) << 3) | (GetRegisterCode(baseReg) & 0x07));

            arr.PushU8(rex);
            arr.PushU8(opcode);
            arr.PushU8(modrm);

            if (baseReg == Register.RSP || baseReg == Register.R12)
            {
                byte sib = (byte)(0x00 | (0x04 << 3) | (GetRegisterCode(baseReg) & 0x07));
                arr.PushU8(sib);
            }

            arr.PushI32(offset);
            EmitBuffer(arr);
        }

        public void MovabsRegImm64(Register reg1, ulong imm64)
        {
            byte rex = 0x48;
            if (IsExtended(reg1)) rex |= 0x01;

            var cond = (reg1 >= Register.RAX && reg1 <= Register.RDI);
            byte opcode = (byte)(0xB8 + (cond ? GetRegisterCode(reg1) : GetRegisterCode(reg1) - 8));

            byte* p = stackalloc byte[10];
            var arr = new StackBuffer(ptr);
            arr.PushU8(rex);
            arr.PushU8(opcode);
            arr.PushU64(imm64);

            EmitBuffer(arr);
        }

        public void AddRegReg(Register reg1, Register reg2)
        {
            OpcodeRegReg(0x01, reg1, reg2);
        }

        public void AddRegImm32(Register reg1, uint imm32)
            => OpcRegImm(0x00, reg1, imm32);

        public void SubRegImm32(Register reg1, uint imm32)
            => OpcRegImm(0x05, reg1, imm32);

        public void OpcRegImm(byte mask, Register reg1, uint imm32)
        {
            byte rex = 0x48;
            if (IsExtended(reg1)) rex |= 0x01;

            byte opcode = 0x81;
            byte modrm = (byte)(0xC0 | (mask << 3) | (GetRegisterCode(reg1) & 0x07));

            byte* p = stackalloc byte[7];
            var arr = new StackBuffer(ptr);
            arr.PushU8(rex);
            arr.PushU8(opcode);
            arr.PushU8(modrm);
            arr.PushU32(imm32);

            EmitBuffer(arr);
        }

        public void ImulRegReg(Register reg1, Register reg2)
        {
            byte rex = 0x48;
            if (IsExtended(reg1)) rex |= 0x04;
            if (IsExtended(reg2)) rex |= 0x01;

            byte opcode1 = 0x0F;
            byte opcode2 = 0xAF;
            byte modrm = (byte)(0xC0 | ((GetRegisterCode(reg1) & 0x07) << 3) | (GetRegisterCode(reg2) & 0x07));
            EmitBytes(rex, opcode1, opcode2, modrm);
        }

        public void AndRegReg(Register reg1, Register reg2)
            => OpcodeRegReg(0x21, reg1, reg2);

        public void AndRegImm32(Register reg1, uint imm32)
            => OpcRegImm(0x04, reg1, imm32);

        public void AndMem64Reg(Register baseReg, int offset, Register srcReg)
        {
            byte rex = 0x48; 
            if (IsExtended(srcReg)) rex |= 0x04; 
            if (IsExtended(baseReg)) rex |= 0x01;

            byte opcode = 0x21;
            byte modrm = (byte)(0x80 | ((GetRegisterCode(srcReg) & 0x07) << 3) | (GetRegisterCode(baseReg) & 0x07));

            byte* p = stackalloc byte[8];
            var arr = new StackBuffer(ptr);
            arr.PushU8(rex);
            arr.PushU8(opcode);
            arr.PushU8(modrm);


            if (baseReg == Register.RSP || baseReg == Register.R12)
            {
                byte sib = (byte)(0x00 | (0x04 << 3) | (GetRegisterCode(baseReg) & 0x07));
                arr.PushU8(sib);
            }

            arr.PushI32(offset);

            EmitBuffer(arr);
        }

        public void OrRegReg(Register reg1, Register reg2)
            => OpcodeRegReg(0x09, reg1, reg2);

        public void XorRegReg(Register reg1, Register reg2)
            => OpcodeRegReg(0x31, reg1, reg2);

        public void NotReg(Register reg1)
        {
            byte rex = 0x48;
            if (IsExtended(reg1)) rex |= 0x01;

            byte opcode = 0xF7;
            byte modrm = (byte)(0xC0 | (0x02 << 3) | (GetRegisterCode(reg1) & 0x07));
            EmitBytes(rex, opcode, modrm);
        }

        public void ShlRegCl(Register reg)
            => ShiftRegCl(true, reg);

        public void ShrRegCl(Register reg)
            => ShiftRegCl(false, reg);

        public void ShiftRegCl(bool shl, Register reg)
        {
            byte rex = 0x48;
            if (IsExtended(reg)) rex |= 0x01;

            byte opcode = 0xD3;
            var m1 = shl ? 0x04 : 0x05;
            byte modrm = (byte)(0xC0 | (m1 << 3) | (GetRegisterCode(reg) & 0x07));
            EmitBytes(rex, opcode, modrm);
        }

        public void ShrRegImm8(Register reg, byte imm8)
        {
            byte rex = 0x48;
            if (IsExtended(reg)) rex |= 0x01;

            byte opcode = 0xC1;
            byte modrm = (byte)(0xC0 | (0x05 << 3) | (GetRegisterCode(reg) & 0x07));
            EmitBytes(rex, opcode, modrm, imm8);
        }

        public void CallReg(Register reg1)
        {
            byte rex = 0x00;
            if (IsExtended(reg1))
                rex = 0x41;

            byte opcode = 0xFF;
            byte modrm = (byte)(0xC0 | (0x02 << 3) | (GetRegisterCode(reg1) & 0x07));
            if (rex != 0)
                EmitBytes(rex, opcode, modrm);
            else
                EmitBytes(opcode, modrm);
        }

        public void Ret()
            => EmitBytes(0xC3);

        private bool IsExtended(Register reg)
            => reg >= Register.R8 && reg <= Register.R15;

        private uint GetRegisterCode(Register reg)
            => (uint)reg - (uint)Register.RAX;

        public List<Instruction> GetInstructions()
        {
            var ourBytes = GetBytes().ToArray();
            var codeReader = new ByteArrayCodeReader(ourBytes);
            var decoder = Iced.Intel.Decoder.Create(64, codeReader);
            decoder.IP = 0;

            var insts = new List<Instruction>();
            while (true)
            {
                insts.Add(decoder.Decode());
                if (codeReader.Position >= ourBytes.Length)
                    break;
            }

            return insts;
        }

        public List<byte> GetBytes()
        {
            var len = (ulong)ptr - (ulong)start;
            var output = new List<byte>();
            for (ulong i = 0; i < len; i++)
                output.Add(start[i]);

            return output;
        }

        public void Reset()
            => ptr = start;
    }

    public static class Reg
    {
        public static AssemblerRegister64 Conv(Register reg)
        {
            return reg switch
            {
                Register.RCX => AssemblerRegisters.rcx,
                Register.RDX => AssemblerRegisters.rdx,
                Register.RBX => AssemblerRegisters.rbx,
                Register.RDI => AssemblerRegisters.rdi,
                Register.RAX => AssemblerRegisters.rax,
                Register.RSI => AssemblerRegisters.rsi,
                Register.R8 => AssemblerRegisters.r8,
                Register.R9 => AssemblerRegisters.r9,
                Register.R10 => AssemblerRegisters.r10,
                Register.R11 => AssemblerRegisters.r11,
                Register.R12 => AssemblerRegisters.r12,
                Register.R13 => AssemblerRegisters.r13,
                Register.R14 => AssemblerRegisters.r14,
                Register.R15 => AssemblerRegisters.r15,
                Register.RBP => AssemblerRegisters.rbp,
                Register.RSP => AssemblerRegisters.rsp,
                _ => throw new InvalidOperationException()
            };
        }
    }
}
