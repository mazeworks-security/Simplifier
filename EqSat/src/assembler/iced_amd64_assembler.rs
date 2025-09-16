use crate::assembler::amd64_assembler::IAmd64Assembler;
use iced_x86::code_asm::*;
use iced_x86::Instruction;
use iced_x86::Register;

/// x86-64 assembler implementation using the iced-x86 library
pub struct IcedAmd64Assembler {
    assembler: CodeAssembler,
}

impl IcedAmd64Assembler {
    pub fn new() -> Result<Self, IcedError> {
        Ok(Self {
            assembler: CodeAssembler::new(64)?,
        })
    }

    fn conv(reg: Register) -> AsmRegister64 {
        match reg {
            Register::RAX => rax,
            Register::RCX => rcx,
            Register::RDX => rdx,
            Register::RBX => rbx,
            Register::RSP => rsp,
            Register::RBP => rbp,
            Register::RSI => rsi,
            Register::RDI => rdi,
            Register::R8 => r8,
            Register::R9 => r9,
            Register::R10 => r10,
            Register::R11 => r11,
            Register::R12 => r12,
            Register::R13 => r13,
            Register::R14 => r14,
            Register::R15 => r15,
            _ => panic!("Unsupported register"),
        }
    }
}

impl IAmd64Assembler for IcedAmd64Assembler {
    fn push_reg(&mut self, reg: Register) {
        self.assembler.push(Self::conv(reg)).unwrap();
    }

    fn push_mem64(&mut self, base_reg: Register, offset: i32) {
        self.assembler
            .push(qword_ptr(Self::conv(base_reg) + offset))
            .unwrap();
    }

    fn pop_reg(&mut self, reg: Register) {
        self.assembler.pop(Self::conv(reg)).unwrap();
    }

    fn mov_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .mov(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn mov_reg_mem64(&mut self, dst_reg: Register, base_reg: Register, offset: i32) {
        self.assembler
            .mov(
                Self::conv(dst_reg),
                qword_ptr(Self::conv(base_reg) + offset),
            )
            .unwrap();
    }

    fn mov_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register) {
        self.assembler
            .mov(
                qword_ptr(Self::conv(base_reg) + offset),
                Self::conv(src_reg),
            )
            .unwrap();
    }

    fn movabs_reg_imm64(&mut self, reg: Register, imm: u64) {
        self.assembler.mov(Self::conv(reg), imm).unwrap();
    }

    fn add_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .add(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn add_reg_imm32(&mut self, reg: Register, imm32: u32) {
        self.assembler.add(Self::conv(reg), imm32 as i32).unwrap();
    }

    fn sub_reg_imm32(&mut self, reg: Register, imm32: u32) {
        self.assembler.sub(Self::conv(reg), imm32 as i32).unwrap();
    }

    fn imul_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .imul_2(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn and_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .and(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn and_reg_imm32(&mut self, reg: Register, imm: u32) {
        self.assembler.and(Self::conv(reg), imm as i32).unwrap();
    }

    fn and_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register) {
        self.assembler
            .and(
                qword_ptr(Self::conv(base_reg) + offset),
                Self::conv(src_reg),
            )
            .unwrap();
    }

    fn or_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .or(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn xor_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.assembler
            .xor(Self::conv(reg1), Self::conv(reg2))
            .unwrap();
    }

    fn not_reg(&mut self, reg: Register) {
        self.assembler.not(Self::conv(reg)).unwrap();
    }

    fn shl_reg_cl(&mut self, reg: Register) {
        self.assembler.shl(Self::conv(reg), cl).unwrap();
    }

    fn shr_reg_cl(&mut self, reg: Register) {
        self.assembler.shr(Self::conv(reg), cl).unwrap();
    }

    fn shr_reg_imm8(&mut self, reg: Register, imm8: u8) {
        self.assembler.shr(Self::conv(reg), imm8 as u32).unwrap();
    }

    fn call_reg(&mut self, reg: Register) {
        self.assembler.call(Self::conv(reg)).unwrap();
    }

    fn ret(&mut self) {
        self.assembler.ret().unwrap();
    }

    fn get_instructions(&mut self) -> Vec<Instruction> {
        self.assembler.instructions().to_vec()
    }

    fn get_bytes(&mut self) -> Vec<u8> {
        self.assembler.assemble(0).unwrap()
    }

    fn reset(&mut self) {
        self.assembler.reset();
    }
}
