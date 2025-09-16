use iced_x86::{IcedError, Register};
use rand::Rng;

use crate::assembler::{
    amd64_assembler::IAmd64Assembler, fast_amd64_assembler::FastAmd64Assembler,
    iced_amd64_assembler::IcedAmd64Assembler,
};

/// Differential tester that compares FastAmd64Assembler against IcedAmd64Assembler
pub struct Amd64AssemblerDifferentialTester {
    rand: rand::rngs::ThreadRng,
    registers: Vec<Register>,
    iced_assembler: IcedAmd64Assembler,
    fast_assembler: FastAmd64Assembler,
}

impl Amd64AssemblerDifferentialTester {
    /// Creates a new differential tester with the given buffer
    pub unsafe fn new(buffer: *mut u8) -> Result<Self, IcedError> {
        let registers = vec![
            Register::RAX,
            Register::RCX,
            Register::RDX,
            Register::RBX,
            Register::RSI,
            Register::RDI,
            Register::RSP,
            Register::RBP,
            Register::R8,
            Register::R9,
            Register::R10,
            Register::R11,
            Register::R12,
            Register::R13,
            Register::R14,
            Register::R15,
        ];

        Ok(Self {
            rand: rand::thread_rng(),
            registers,
            iced_assembler: IcedAmd64Assembler::new()?,
            fast_assembler: FastAmd64Assembler {
                p: buffer,
                offset: 0,
            },
        })
    }

    pub fn test() -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = vec![0u8; 64 * 4096];
        let ptr = buffer.as_mut_ptr();

        unsafe {
            let mut tester = Self::new(ptr)?;
            tester.run()?;
        }

        Ok(())
    }

    pub fn run(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        for i in 0..self.registers.len() {
            let reg1 = self.registers[i];
            self.diff_reg_insts(reg1)?;

            for j in (i + 1)..self.registers.len() {
                let reg2 = self.registers[j];
                self.diff_reg_reg_insts(reg1, reg2)?;
            }
        }

        println!("All differential tests passed!");
        Ok(())
    }

    fn diff_reg_insts(&mut self, reg: Register) -> Result<(), Box<dyn std::error::Error>> {
        self.diff("PushReg", |asm| asm.push_reg(reg))?;
        self.diff("PopReg", |asm| asm.pop_reg(reg))?;
        self.diff("NotReg", |asm| asm.not_reg(reg))?;
        self.diff("ShlRegCl", |asm| asm.shl_reg_cl(reg))?;
        self.diff("ShrRegCl", |asm| asm.shr_reg_cl(reg))?;
        self.diff("CallReg", |asm| asm.call_reg(reg))?;

        // Test reg, constant instructions
        for _ in 0..100 {
            let c = self.rand.gen::<i64>() as u64;

            self.diff("MovabsRegImm64", |asm| asm.movabs_reg_imm64(reg, c))?;
            self.diff("AddRegImm32", |asm| asm.add_reg_imm32(reg, c as u32))?;
            self.diff("SubRegImm32", |asm| asm.sub_reg_imm32(reg, c as u32))?;
            self.diff("AndRegImm32", |asm| asm.and_reg_imm32(reg, c as u32))?;
            self.diff("ShrRegImm8", |asm| asm.shr_reg_imm8(reg, c as u8))?;

            if reg != Register::RSP {
                self.diff("PushMem64", |asm| asm.push_mem64(reg, c as i32))?;
            }
        }

        Ok(())
    }

    fn diff_reg_reg_insts(
        &mut self,
        reg1: Register,
        reg2: Register,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // Test reg, reg instructions
        self.diff("MovRegReg", |asm| asm.mov_reg_reg(reg1, reg2))?;
        self.diff("MovRegReg", |asm| asm.mov_reg_reg(reg2, reg1))?;
        self.diff("AddRegReg", |asm| asm.add_reg_reg(reg1, reg2))?;
        self.diff("AddRegReg", |asm| asm.add_reg_reg(reg2, reg1))?;
        self.diff("AndRegReg", |asm| asm.and_reg_reg(reg1, reg2))?;
        self.diff("AndRegReg", |asm| asm.and_reg_reg(reg2, reg1))?;
        self.diff("OrRegReg", |asm| asm.or_reg_reg(reg1, reg2))?;
        self.diff("OrRegReg", |asm| asm.or_reg_reg(reg2, reg1))?;
        self.diff("XorRegReg", |asm| asm.xor_reg_reg(reg1, reg2))?;
        self.diff("XorRegReg", |asm| asm.xor_reg_reg(reg2, reg1))?;
        self.diff("ImulRegReg", |asm| asm.imul_reg_reg(reg1, reg2))?;
        self.diff("ImulRegReg", |asm| asm.imul_reg_reg(reg2, reg1))?;

        // Test reg, reg, constant instructions
        for _ in 0..100 {
            let c = self.rand.gen::<i32>();

            self.diff("MovMem64Reg", |asm| asm.mov_mem64_reg(reg1, c, reg2))?;
            self.diff("MovMem64Reg", |asm| asm.mov_mem64_reg(reg2, c, reg1))?;
            self.diff("MovRegMem64", |asm| asm.mov_reg_mem64(reg1, reg2, c))?;
            self.diff("MovRegMem64", |asm| asm.mov_reg_mem64(reg2, reg1, c))?;
            self.diff("AndMem64Reg", |asm| asm.and_mem64_reg(reg1, c, reg2))?;
            self.diff("AndMem64Reg", |asm| asm.and_mem64_reg(reg2, c, reg1))?;
        }

        Ok(())
    }

    /// Executes a test function on both assemblers and compares results
    fn diff<F>(&mut self, method_name: &str, func: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: Fn(&mut dyn IAmd64Assembler),
    {
        // Assemble the instruction using both assemblers
        func(&mut self.iced_assembler);
        func(&mut self.fast_assembler);

        // Compare the results
        self.compare(method_name)?;

        // Reset both assemblers
        self.iced_assembler.reset();
        self.fast_assembler.reset();

        Ok(())
    }

    /// Compares the output of both assemblers
    fn compare(&mut self, method_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let iced_insts = self.iced_assembler.get_instructions();
        let iced_bytes = self.iced_assembler.get_bytes();
        let our_insts = self.fast_assembler.get_instructions();
        let our_bytes = self.fast_assembler.get_bytes();

        if iced_insts.is_empty() || iced_bytes.is_empty() || iced_insts.len() != our_insts.len() {
            return Err(format!(
                "Method {} failed: instruction count mismatch (iced: {}, ours: {})",
                method_name,
                iced_insts.len(),
                our_insts.len()
            )
            .into());
        }

        // Check if instructions are equivalent
        if iced_insts.len() == 1 && our_insts.len() == 1 {
            let iced_str = format!("{}", iced_insts[0]);
            let our_str = format!("{}", our_insts[0]);

            if iced_str != our_str {
                return Err(format!(
                    "Method {} failed: Instruction '{}' and '{}' not equivalent!\nIced bytes: {:?}\nOur bytes: {:?}",
                    method_name,
                    iced_str,
                    our_str,
                    iced_bytes,
                    our_bytes
                ).into());
            }
        } else {
            // Compare all instructions
            for (i, (iced_inst, our_inst)) in iced_insts.iter().zip(our_insts.iter()).enumerate() {
                let iced_str = format!("{}", iced_inst);
                let our_str = format!("{}", our_inst);

                if iced_str != our_str {
                    return Err(format!(
                        "Method {} failed at instruction {}: '{}' != '{}'",
                        method_name, i, iced_str, our_str
                    )
                    .into());
                }
            }
        }

        Ok(())
    }
}
