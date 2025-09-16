use iced_x86::{Instruction, Register};

pub trait IAmd64Assembler {
    fn push_reg(&mut self, reg: Register);

    fn push_mem64(&mut self, base_reg: Register, offset: i32);

    fn pop_reg(&mut self, reg: Register);

    fn mov_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn mov_reg_mem64(&mut self, dst_reg: Register, base_reg: Register, offset: i32);

    fn mov_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register);

    fn movabs_reg_imm64(&mut self, reg: Register, imm: u64);

    fn add_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn add_reg_imm32(&mut self, reg: Register, imm32: u32);

    fn sub_reg_imm32(&mut self, reg: Register, imm32: u32);

    fn imul_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn and_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn and_reg_imm32(&mut self, reg: Register, imm: u32);

    fn and_mem64_reg(&mut self, base_reg: Register, offset: i32, src_reg: Register);

    fn or_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn xor_reg_reg(&mut self, reg1: Register, reg2: Register);

    fn not_reg(&mut self, reg: Register);

    fn shl_reg_cl(&mut self, reg: Register);

    fn shr_reg_cl(&mut self, reg: Register);

    fn shr_reg_imm8(&mut self, reg: Register, imm8: u8);

    fn call_reg(&mut self, reg: Register);

    fn ret(&mut self);

    fn get_instructions(&mut self) -> Vec<Instruction>;

    fn get_bytes(&mut self) -> Vec<u8>;

    fn reset(&mut self);
}
