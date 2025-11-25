use iced_x86::code_asm::*;
use iced_x86::{Instruction, Register};
use rand::Rng;
use std::fmt::Write;
use std::hint::unreachable_unchecked;
use std::time::Instant;

use crate::assembler::amd64_assembler::IAmd64Assembler;

// Wrapper around a stack-allocated byte buffer for building instruction byte sequences
pub struct StackBuffer<'a> {
    pub arr: &'a mut [u8],
    pub offset: usize,
}

impl StackBuffer<'_> {
    fn push<T>(&mut self, v: T) {
        unsafe {
            let ptr = self.arr.as_mut_ptr().add(self.offset) as *mut T;
            *ptr = v;
        }

        self.offset += std::mem::size_of::<T>();
    }

    fn pop<T: Copy>(&mut self) -> T {
        self.offset -= std::mem::size_of::<T>();

        unsafe {
            let ptr = self.arr.as_mut_ptr().add(self.offset) as *mut T;
            *ptr
        }
    }

    fn push_u8(&mut self, byte: u8) {
        unsafe {
            *self.arr.get_unchecked_mut(self.offset) = byte;
        }

        self.offset += 1;
    }

    fn push_i32(&mut self, byte: i32) {
        unsafe {
            let ptr = self.arr.as_mut_ptr().add(self.offset) as *mut i32;
            *ptr = byte;
        }

        self.offset += 4;
    }

    fn push_u32(&mut self, byte: u32) {
        unsafe {
            let ptr = self.arr.as_mut_ptr().add(self.offset) as *mut u32;
            *ptr = byte;
        }

        self.offset += 4;
    }

    fn push_u64(&mut self, byte: u64) {
        unsafe {
            let ptr = self.arr.as_mut_ptr().add(self.offset) as *mut u64;
            *ptr = byte;
        }

        self.offset += 8;
    }
}

pub struct FastAmd64Assembler {
    pub p: *mut u8,
    pub offset: usize,
}

impl FastAmd64Assembler {
    pub fn new(buffer: *mut u8) -> Self {
        FastAmd64Assembler {
            p: buffer,
            offset: 0,
        }
    }

    fn emit_bytes(&mut self, data: &[u8]) {
        unsafe {
            std::ptr::copy_nonoverlapping(data.as_ptr(), self.p.add(self.offset), data.len());
        }

        self.offset += data.len();
    }

    fn emit_buffer(&mut self, buffer: &StackBuffer) {
        unsafe {
            std::ptr::copy_nonoverlapping(
                buffer.arr.as_ptr(),
                self.p.add(self.offset),
                buffer.offset,
            );
        }

        self.offset += buffer.offset;
    }

    pub fn opcode_reg_reg(&mut self, opcode: u8, reg1: Register, reg2: Register) {
        let mut rex = 0x48;
        if is_extended(reg1) {
            rex |= 0x01;
        }
        if is_extended(reg2) {
            rex |= 0x04;
        }

        let modrm = 0xC0
            | ((get_register_code(reg2) as u8 & 0x07) << 3)
            | (get_register_code(reg1) as u8 & 0x07);
        self.emit_bytes(&[rex, opcode, modrm]);
    }

    pub fn opc_reg_imm(&mut self, mask: u8, reg: Register, imm32: u32) {
        let p = &mut [0u8; 7];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        let mut rex = 0x48;
        if self.is_extended(reg) {
            rex |= 0x01;
        }

        let opcode = 0x81;
        let modrm = 0xC0 | (mask << 3) | (self.get_register_code(reg) & 0x07);

        arr.push_u8(rex);
        arr.push_u8(opcode);
        arr.push_u8(modrm);
        arr.push_u32(imm32);

        self.emit_buffer(&arr);
    }

    pub fn shift_reg_cl(&mut self, shl: bool, reg: Register) {
        let mut rex = 0x48;
        if self.is_extended(reg) {
            rex |= 0x01;
        }

        let opcode = 0xD3;
        let m1 = if shl { 0x04 } else { 0x05 };
        let modrm = 0xC0 | (m1 << 3) | (self.get_register_code(reg) & 0x07);

        self.emit_bytes(&[rex, opcode, modrm]);
    }

    #[inline(always)]
    fn mov_reg_mem64_template(&mut self, dst_reg: Register, base_reg: Register, offset: i32) {
        let p = &mut [0u8; 8];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        let mut rex = 0x48;
        if is_extended(dst_reg) {
            rex |= 0x04;
        }
        if is_extended(base_reg) {
            rex |= 0x01;
        }

        let opcode = 0x8B;
        let modrm = 0x80
            | ((get_register_code(dst_reg) as u8 & 0x07) << 3)
            | (get_register_code(base_reg) as u8 & 0x07);

        arr.push_u8(rex);
        arr.push_u8(opcode);
        arr.push_u8(modrm);

        if base_reg == Register::RSP || base_reg == Register::R12 {
            let sib = 0x00 | (0x04 << 3) | (get_register_code(base_reg) as u8 & 0x07);
            arr.push_u8(sib);
        }

        arr.push_i32(offset);

        self.emit_buffer(&arr);
    }

    pub fn is_extended(&mut self, reg: Register) -> bool {
        return reg >= Register::R8 && reg <= Register::R15;
    }

    pub fn get_register_code(&mut self, reg: Register) -> u8 {
        return (reg as u8) - (Register::RAX as u8);
    }
}

impl IAmd64Assembler for FastAmd64Assembler {
    fn push_reg(&mut self, reg: Register) {
        if reg >= Register::RAX && reg <= Register::RDI {
            let opcode = (0x50 + get_register_code(reg)) as u8;
            self.emit_bytes(&[opcode]);
            return;
        }

        let rex = 0x41;
        let opcode = (0x50 + reg as u8 - Register::R8 as u8);
        self.emit_bytes(&[rex, opcode]);
    }

    fn push_mem64(&mut self, base_reg: Register, disp: i32) {
        let p = &mut [0u8; 8];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        if is_extended(base_reg) {
            let rex = 0x49;
            arr.push_u8(rex);
        }

        let opcode: u8 = 0xFF;
        let modrm = (0x80 | (0x06 << 3) | (get_register_code(base_reg) & 0x07)) as u8;
        arr.push_u8(opcode);
        arr.push_u8(modrm);

        if base_reg == Register::RSP || base_reg == Register::R12 {
            let sib: u8 = (0x00 | (0x04 << 3) | (get_register_code(base_reg) & 0x07)) as u8;
            arr.push_u8(sib);
        }

        arr.push_i32(disp);
        self.emit_buffer(&arr);
    }

    fn pop_reg(&mut self, reg: Register) {
        if reg >= Register::RAX && reg <= Register::RDI {
            let opcode = 0x58 + get_register_code(reg) as u8;
            self.emit_bytes(&[opcode]);
            return;
        }

        let rex = 0x41;
        let opcode = 0x58 + get_register_code(reg) as u8 - 8;
        self.emit_bytes(&[rex, opcode]);
        return;
    }

    fn mov_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.opcode_reg_reg(0x89, reg1, reg2);
    }

    fn mov_reg_mem64(&mut self, dst_reg: Register, base_reg: Register, offset: i32) {
        // This function is intentionally monomorphized for performance.
        // mov_reg_mem64 has a variable length encoding depending on the base register,
        // which prevents SROA from promoting our stack buffer to an SSA variable.
        if base_reg == Register::R12 {
            self.mov_reg_mem64_template(dst_reg, Register::R12, offset);
        } else if base_reg == Register::RSP {
            self.mov_reg_mem64_template(dst_reg, Register::RSP, offset);
        } else {
            self.mov_reg_mem64_template(dst_reg, base_reg, offset);
        }
    }

    fn mov_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register) {
        let p = &mut [0u8; 8];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        let mut rex = 0x48;
        if self.is_extended(src_reg) {
            rex |= 0x04;
        }
        if self.is_extended(base_reg) {
            rex |= 0x01;
        }

        let opcode = 0x89;
        let modrm = 0x80
            | ((self.get_register_code(src_reg) & 0x07) << 3)
            | (self.get_register_code(base_reg) & 0x07);

        arr.push_u8(rex);
        arr.push_u8(opcode);
        arr.push_u8(modrm);

        if base_reg == Register::RSP || base_reg == Register::R12 {
            let sib = 0x00 | (0x04 << 3) | (self.get_register_code(base_reg) & 0x07);
            arr.push_u8(sib);
        }

        arr.push_i32(offset);

        self.emit_buffer(&arr);
    }

    fn movabs_reg_imm64(&mut self, reg: Register, imm64: u64) {
        let p = &mut [0u8; 10];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        let mut rex = 0x48;
        if self.is_extended(reg) {
            rex |= 0x01;
        }

        let cond = reg >= Register::RAX && reg <= Register::RDI;
        let opcode = 0xB8
            + if cond {
                self.get_register_code(reg)
            } else {
                self.get_register_code(reg) - 8
            };

        arr.push_u8(rex);
        arr.push_u8(opcode);
        arr.push_u64(imm64);

        self.emit_buffer(&arr);
    }

    fn add_reg_reg(&mut self, dest: Register, src: Register) {
        self.opcode_reg_reg(0x01, dest, src);
    }

    fn add_reg_imm32(&mut self, reg: Register, imm32: u32) {
        self.opc_reg_imm(0x00, reg, imm32);
    }

    fn sub_reg_imm32(&mut self, reg: Register, imm32: u32) {
        self.opc_reg_imm(0x05, reg, imm32);
    }

    fn imul_reg_reg(&mut self, reg1: Register, reg2: Register) {
        let mut rex = 0x48;
        if self.is_extended(reg1) {
            rex |= 0x04;
        }
        if self.is_extended(reg2) {
            rex |= 0x01;
        }

        let opcode1 = 0x0F;
        let opcode2 = 0xAF;
        let modrm = 0xC0
            | ((self.get_register_code(reg1) & 0x07) << 3)
            | (self.get_register_code(reg2) & 0x07);

        self.emit_bytes(&[rex, opcode1, opcode2, modrm]);
    }

    fn and_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.opcode_reg_reg(0x21, reg1, reg2);
    }

    fn and_reg_imm32(&mut self, reg1: Register, imm32: u32) {
        self.opc_reg_imm(0x04, reg1, imm32);
    }

    fn and_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register) {
        let p = &mut [0u8; 8];
        let mut arr = StackBuffer { arr: p, offset: 0 };

        let mut rex = 0x48;
        if self.is_extended(src_reg) {
            rex |= 0x04;
        }
        if self.is_extended(base_reg) {
            rex |= 0x01;
        }

        let opcode = 0x21;
        let modrm = 0x80
            | ((self.get_register_code(src_reg) & 0x07) << 3)
            | (self.get_register_code(base_reg) & 0x07);

        arr.push_u8(rex);
        arr.push_u8(opcode);
        arr.push_u8(modrm);

        if base_reg == Register::RSP || base_reg == Register::R12 {
            let sib = 0x00 | (0x04 << 3) | (self.get_register_code(base_reg) & 0x07);
            arr.push_u8(sib);
        }

        arr.push_i32(offset);

        self.emit_buffer(&arr);
    }

    fn or_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.opcode_reg_reg(0x09, reg1, reg2);
    }

    fn xor_reg_reg(&mut self, reg1: Register, reg2: Register) {
        self.opcode_reg_reg(0x31, reg1, reg2);
    }

    fn not_reg(&mut self, reg: Register) {
        let mut rex = 0x48;
        if self.is_extended(reg) {
            rex |= 0x01;
        }

        let opcode = 0xF7;
        let modrm = 0xC0 | (0x02 << 3) | (self.get_register_code(reg) & 0x07);

        self.emit_bytes(&[rex, opcode, modrm]);
    }

    fn shl_reg_cl(&mut self, reg: Register) {
        self.shift_reg_cl(true, reg);
    }

    fn shr_reg_cl(&mut self, reg: Register) {
        self.shift_reg_cl(false, reg);
    }

    fn shr_reg_imm8(&mut self, reg: Register, imm8: u8) {
        let mut rex = 0x48;
        if self.is_extended(reg) {
            rex |= 0x01;
        }

        let opcode = 0xC1;
        let modrm = 0xC0 | (0x05 << 3) | (self.get_register_code(reg) & 0x07);

        self.emit_bytes(&[rex, opcode, modrm, imm8]);
    }

    fn call_reg(&mut self, reg: Register) {
        let mut rex = 0x00;
        if self.is_extended(reg) {
            rex = 0x41;
        }

        let opcode = 0xFF;
        let modrm = 0xC0 | (0x02 << 3) | (self.get_register_code(reg) & 0x07);

        if rex != 0 {
            self.emit_bytes(&[rex, opcode, modrm]);
        } else {
            self.emit_bytes(&[opcode, modrm]);
        }
    }

    fn ret(&mut self) {
        self.emit_bytes(&[0xC3]);
    }

    fn get_instructions(&mut self) -> Vec<Instruction> {
        let bytes = self.get_bytes();
        let mut decoder = iced_x86::Decoder::new(64, &bytes, iced_x86::DecoderOptions::NONE);
        decoder.set_ip(0);

        let mut instructions = Vec::new();
        while decoder.position() < bytes.len() {
            let instruction = decoder.decode();
            instructions.push(instruction);
        }

        instructions
    }

    fn get_bytes(&mut self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for i in 0..self.offset {
            unsafe {
                bytes.push(*self.p.add(i));
            }
        }
        return bytes;
    }

    fn reset(&mut self) {
        self.offset = 0;
    }
}

fn is_extended(reg: Register) -> bool {
    return reg >= Register::R8 && reg <= Register::R15;
}

fn get_register_code(reg: Register) -> u8 {
    return (reg as u8) - (Register::RAX as u8);
}
