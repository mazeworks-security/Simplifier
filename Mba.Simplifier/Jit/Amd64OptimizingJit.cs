using Iced.Intel;
using Mba.Common.Minimization;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Jit;
using Mba.Simplifier.Pipeline;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using static Iced.Intel.AssemblerRegisters;

namespace Mba.Simplifier.Interpreter
{
    enum LocKind
    {
        Register,
        Stack,
    }

    // Represents a storage location for a node's computed value.
    public struct Location
    {
        public Register Register;
        public bool IsStack;

        public static Location Reg(Register reg)
            => new Location() { Register = reg };

        public static Location Stack()
            => new Location() { IsStack = true };

        public bool IsRegister => Register != Register.None;
    }

    public struct NodeInfo
    {
        public uint numUses;

        // Allocate stack slot for the node if numUses > 1
        public uint slotIdx = uint.MaxValue;

        public NodeInfo(uint numInstances)
        {
            this.numUses = numInstances;
        }

        public override string ToString()
        {
            return $"numInstances:{numUses}, slotIdx: {slotIdx}";
        }
    }

    // This class implements a JIT compiler to x86 with register allocation and node reuse. 
    // The generated code is one order of magnitude faster than the previous JIT, and two to three orders of magnitude faster than our tree walking interpreter.
    public class Amd64OptimizingJit
    {
        private readonly AstCtx ctx;

        private IAmd64Assembler assembler;

        private readonly Stack<Register> freeRegisters = new(16);

        private readonly List<AstIdx> dfs = new(16);

        private readonly Dictionary<AstIdx, NodeInfo> seen = new();

        private uint slotCount = 0;

        Stack<Location> stack = new(16);

        private readonly Register argsRegister = Register.RCX;

        private readonly Register localsRegister = Register.RBP;

        private readonly Register scratch1 = Register.RSI;

        private readonly Register scratch2 = Register.RDI;

        private static readonly Register[] volatileRegs = { Register.RAX, Register.RCX, Register.RDX, Register.R8, Register.R9, Register.R10, Register.R11 };

        private static readonly Register[] nonvolatileRegs = { Register.RBP, Register.RBX, Register.RDI, Register.RSI, Register.R12, Register.R13, Register.R14, Register.R15};

        public Amd64OptimizingJit(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public unsafe void Compile(AstIdx idx, List<AstIdx> variables, nint pagePtr, bool useIcedBackend = false)
        {
            Assembler icedAssembler = useIcedBackend ? new Assembler(64) : null;
            assembler = useIcedBackend ? new IcedAmd64Assembler(icedAssembler) : new FastAmd64Assembler((byte*)pagePtr);

            // Collect information about the nodes necessary for JITing (dfs order, how many users a value has)
            CollectInfo(idx);

            // Compile the instructions to x86.
            LowerToX86(variables);

            // If using the fast assembler backend, we've already emitted x86.
            // However the stack pointer adjustment needs to fixed up, because it wasn't known during prologue emission.
            if (!useIcedBackend)
            {
                FixupFramePtr(pagePtr, slotCount);
                return;
            }

            // Otherwise adjust the RSP in ICED
            var instructions = icedAssembler.Instructions.ToList();
            FixupIcedFramePtr(instructions, slotCount);

            // Write the instructions to memory. 
            // ICED internally emits a list of assembled instructions rather than raw x86 bytes
            // so this must be done after the fact.
            WriteInstructions(pagePtr, instructions);
        }

        private void CollectInfo(AstIdx idx)
        {
            if (seen.TryGetValue(idx, out var existing))
            {
                seen[idx] = new NodeInfo(existing.numUses); 
                dfs.Add(idx);
                return;
            }

            var opcode = ctx.GetOpcode(idx);
            switch(opcode)
            {
                case AstOp.Add:
                case AstOp.Mul:
                case AstOp.Pow:
                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                case AstOp.Lshr:
                    var op0 = ctx.GetOp0(idx);
                    CollectInfo(op0);
                    var op1 = ctx.GetOp1(idx);
                    CollectInfo(op1);

                    seen[op0] = new NodeInfo(seen[op0].numUses + 1);
                    seen[op1] = new NodeInfo(seen[op1].numUses + 1);
                    break;
                case AstOp.Neg:
                case AstOp.Zext:
                case AstOp.Trunc:
                    var single = ctx.GetOp0(idx);
                    CollectInfo(single);
                    seen[single] = new NodeInfo(seen[single].numUses + 1);
                    break;
                default:
                    break;
            }

            dfs.Add(idx);
            seen[idx] = new NodeInfo(0);
        }

        // Compile the provided DAG to x86
        // TODO: Optionally disabled hashmap lookup/use tracking stuff for faster codegen. Pretend DAG is an AST if the duplicated cost is not too high
        private unsafe void LowerToX86(List<AstIdx> vars)
        {
            // rcx reserved for local variables ptr (or all vars in the case of a semi-linear result vector)
            // RSI, RDI reserved for temporary use
            freeRegisters.Push(Register.RAX);
            freeRegisters.Push(Register.RDX);
            freeRegisters.Push(Register.RBX);
            freeRegisters.Push(Register.R8);
            freeRegisters.Push(Register.R9);
            freeRegisters.Push(Register.R10);
            freeRegisters.Push(Register.R11);
            freeRegisters.Push(Register.R12);
            freeRegisters.Push(Register.R13);
            freeRegisters.Push(Register.R14);
            freeRegisters.Push(Register.R15);

            EmitPrologue(assembler, localsRegister, uint.MaxValue);
            for(int i = 0; i < dfs.Count; i++)
            {
                var idx = dfs[i];
                var nodeInfo = seen[idx];
                // If we've seen this value, load it's value from a local variable slot
                if (nodeInfo.numUses > 1 && nodeInfo.slotIdx != uint.MaxValue)
                {
                    LoadSlotValue(nodeInfo.slotIdx);
                    continue;
                }

                var opc = ctx.GetOpcode(idx);
                var width = ctx.GetWidth(idx);
                switch(opc)
                {
                    // Binary ops
                    case AstOp.Add:
                    case AstOp.Mul:
                    case AstOp.And:
                    case AstOp.Or:
                    case AstOp.Xor:
                    case AstOp.Pow:
                    case AstOp.Lshr:
                        LowerBinop(idx, opc, width, nodeInfo);
                        break;

                    case AstOp.Constant:
                        LowerConstant(idx);
                        break;

                    case AstOp.Symbol:
                        LowerVariable(idx, width, vars);
                        break;

                    case AstOp.Neg:
                    case AstOp.Trunc:
                        LowerUnaryOp(idx, opc, width, nodeInfo);
                        break;

                    case AstOp.Zext:
                        LowerZext(idx, nodeInfo);
                        break;

                    default:
                        throw new InvalidOperationException($"Cannot jit operation {opc}");
                }
            }

            if(stack.Count != 1)
                throw new InvalidOperationException($"Unbalanced stack!");

            // Move the result into RAX.
            var result = stack.Pop();
            if (result.IsRegister)
                assembler.MovRegReg(rax, result.Register);
            else
                assembler.PopReg(rax);

            // Reduce the result modulo 2**w
            assembler.MovabsRegImm64(scratch1, (ulong)ModuloReducer.GetMask(ctx.GetWidth(dfs[dfs.Count - 1])));
            assembler.AndRegReg(rax, scratch1);

            // Emit state restoring code
            EmitEpilogue(assembler, slotCount);
        }

        private void LoadSlotValue(uint slotIdx)
        {
            if (freeRegisters.Count != 0)
            {
                var t = freeRegisters.Pop();
                assembler.MovRegMem64(t, localsRegister, 8 * (int)slotIdx);
                stack.Push(Location.Reg(t));
                return;
            }

            assembler.PushMem64(localsRegister, 8 * (int)slotIdx);
            stack.Push(Location.Stack());
        }

        private unsafe void LowerBinop(AstIdx idx, AstOp opc, uint width, NodeInfo nodeInfo)
        {
            var rhsLoc = stack.Pop();

            // If the rhs is stored in a register, we use it.
            var rhsDest = scratch1;
            if (rhsLoc.IsRegister)
                rhsDest = rhsLoc.Register;
            // If stored on the stack, pop into scratch register.
            else
                assembler.PopReg(rhsDest);

            // Regardless we have the rhs in a register now.
            var lhsLoc = stack.Pop();
            var lhsDest = scratch2;
            if (lhsLoc.IsRegister)
                lhsDest = lhsLoc.Register;
            else
                assembler.PopReg(lhsDest);

            // Now we have both values in registers
            // Execute the instruction
            switch (opc)
            {
                case AstOp.Add:
                    assembler.AddRegReg(lhsDest, rhsDest); break;
                case AstOp.Mul:
                    assembler.ImulRegReg(lhsDest, rhsDest); break;
                case AstOp.And:
                    assembler.AndRegReg(lhsDest, rhsDest); break;
                case AstOp.Or:
                    assembler.OrRegReg(lhsDest, rhsDest); break;
                case AstOp.Xor:
                    assembler.XorRegReg(lhsDest, rhsDest); break;

                case AstOp.Lshr:
                    // TODO: For logical shifts, we need to reduce the other side modulo some constant!
                    // Actually maybe not, we should have already reduced modulo?
                    var w = (uint)ctx.GetWidth(idx);
                    if (w % 8 != 0)
                        throw new InvalidOperationException($"Cannot jit shr of non power of 2 width");
                    // Reduce shift count modulo bit width of operation
                    // TODO: Hand non power of two bit widths
                    assembler.AndRegImm32(rhsDest, w - 1);

                    // Execute lshr
                    assembler.PushReg(Register.RCX);
                    assembler.MovRegReg(Register.RCX, rhsDest);
                    assembler.ShrRegCl(lhsDest);
                    assembler.PopReg(Register.RCX);
                    break;

                case AstOp.Pow:
                    foreach (var r in volatileRegs)
                        assembler.PushReg(r);

                    assembler.MovRegReg(rcx, lhsDest);
                    assembler.MovRegReg(rdx, rhsDest);

                    // TODO: Inline `pow` function
                    assembler.MovabsRegImm64(r11, (ulong)AstCtx.Api.GetPowPtr());
                    assembler.SubRegImm32(rsp, 32);
                    assembler.CallReg(r11);
                    assembler.AddRegImm32(rsp, 32);
                    assembler.MovRegReg(scratch1, rax);

                    // Restore nonvolatile regs.
                    for (int regIdx = volatileRegs.Length - 1; regIdx >= 0; regIdx--)
                        assembler.PopReg(volatileRegs[regIdx]);

                    assembler.MovRegReg(lhsDest, scratch1);

                    break;
                default:
                    throw new InvalidOperationException($"{opc} is not a valid binop");
            }

            ReduceRegisterModulo(width, lhsDest, scratch1);

            if (rhsLoc.IsRegister)
                freeRegisters.Push(rhsLoc.Register);

            // If there are multiple users of this value, throw it in a stack slot.
            bool multipleUsers = nodeInfo.numUses > 1;
            if (multipleUsers)
            {
                // Otherwise there are multiple users. This needs to go on a stack slot
                assembler.MovMem64Reg(localsRegister, 8 * (int)slotCount, lhsDest);
                AssignValueSlot(idx, nodeInfo);
            }

            // If the lhs is already in a register, don't move it!
            if (lhsDest != scratch2)
            {
                stack.Push(Location.Reg(lhsDest));
                return;
            }

            // Try to allocate a reg for this value
            if (freeRegisters.Count > 0)
            {
                var dest = freeRegisters.Pop();
                assembler.MovRegReg(dest, lhsDest);
                stack.Push(Location.Reg(dest));
            }

            else
            {
                // Otherwise this goes on the stack
                assembler.PushReg(lhsDest);
                stack.Push(Location.Stack());
            }

            if (lhsLoc.IsRegister)
                freeRegisters.Push(lhsLoc.Register);
        }

        private void LowerConstant(AstIdx idx)
        {
            var c = ctx.GetConstantValue(idx);
            if (freeRegisters.Count != 0)
            {
                var dest = freeRegisters.Pop();
                assembler.MovabsRegImm64(dest, c);
                stack.Push(Location.Reg(dest));
                return;
            }

            // Otherwise no registers are free
            assembler.MovabsRegImm64(scratch1, c);
            assembler.PushReg(scratch1);
            stack.Push(Location.Stack());
        }

        private void LowerVariable(AstIdx idx, uint width, IReadOnlyList<AstIdx> vars)
        {
            uint offset = (uint)vars.IndexOf(idx);
            if (freeRegisters.Count != 0)
            {
                var dest = freeRegisters.Pop();
                assembler.MovRegMem64(dest, argsRegister, 8 * (int)offset);
                ReduceRegisterModulo(width, dest, scratch1);
                stack.Push(Location.Reg(dest));
                return;
            }

            assembler.PushMem64(argsRegister, 8 * (int)offset);
            stack.Push(Location.Stack());
            ReduceLocationModulo(stack.Peek(), width);
        }

        private void LowerUnaryOp(AstIdx idx, AstOp opc, uint width, NodeInfo nodeInfo)
        {
            var curr = stack.Pop();

            var destReg = scratch1;
            if (curr.IsRegister)
                destReg = curr.Register;
            else
                assembler.PopReg(destReg);

            if (opc == AstOp.Neg)
            {
                assembler.NotReg(destReg);
                ReduceRegisterModulo(width, destReg, scratch2);
            }

            else
            {
                assembler.MovabsRegImm64(scratch2, (ulong)ModuloReducer.GetMask(ctx.GetWidth(idx)));
                assembler.AndRegReg(destReg, scratch2);
            }

            bool mUsers = nodeInfo.numUses > 1;
            if (mUsers)
            {
                // Otherwise there are multiple users. This needs to go on a stack slot
                assembler.MovMem64Reg(localsRegister, 8 * (int)slotCount, destReg);
                AssignValueSlot(idx, nodeInfo);
            }

            if (destReg != scratch1)
            {
                stack.Push(Location.Reg(destReg));
                return;
            }

            if (freeRegisters.Count > 0)
            {
                var dest = freeRegisters.Pop();
                assembler.MovRegReg(dest, destReg);
                stack.Push(Location.Reg(dest));
                return;
            }

            // Otherwise this goes on the stack
            assembler.PushReg(destReg);
            stack.Push(Location.Stack());
        }

        private void LowerZext(AstIdx idx, NodeInfo nodeInfo)
        {
            // If we only have one user, this is a no-op. The result we care about is already on the location stack,
            // and the zero-extension is implicit. 
            var peek = stack.Peek();
            var width = ctx.GetWidth(ctx.GetOp0(idx));

            // Because we are zero extending, we need to reduce the value modulo 2**w
            // In other places we can get away with omitting this step.
            ReduceLocationModulo(peek, width);

            if (nodeInfo.numUses <= 1 )
                return;

            if (peek.IsRegister)
            {
                assembler.MovMem64Reg(localsRegister, 8 * (int)slotCount, peek.Register);
            }
            else
            {
                assembler.MovRegMem64(scratch1, Register.RSP, 0);
                assembler.MovMem64Reg(localsRegister, 8 * (int)slotCount, scratch1);
            }

            AssignValueSlot(idx, nodeInfo);
        }

        private void ReduceRegisterModulo(uint width, Register dstReg, Register freeReg)
        {
            Debug.Assert(dstReg != freeReg);
            if (width == 64)
                return;

            var mask = (ulong)ModuloReducer.GetMask(width);
            assembler.MovabsRegImm64(freeReg, mask);
            assembler.AndRegReg(dstReg, freeReg);
        }

        private void ReduceLocationModulo(Location loc, uint width)
        {
            if (width == 64)
                return;

            var mask = (ulong)ModuloReducer.GetMask(width);
            assembler.MovabsRegImm64(scratch1, mask);
            if (loc.IsRegister)
                assembler.AndRegReg(loc.Register, scratch1);
            else
                assembler.AndMem64Reg(Register.RSP, 0, scratch1);

        }

        private void AssignValueSlot(AstIdx idx, NodeInfo nodeInfo)
        {
            nodeInfo.slotIdx = slotCount;
            seen[idx] = nodeInfo;
            // Bump slot count up
            slotCount += 1;
        }

        private static void EmitPrologue(IAmd64Assembler assembler, Register localsRegister, uint numStackSlots)
        {
            // Push all nonvolatile registers
            foreach (var reg in nonvolatileRegs)
                assembler.PushReg(reg);
            // Allocate space for local variables
            assembler.SubRegImm32(rsp, 8 * numStackSlots);
            // Point rbp to the local var array
            assembler.MovRegReg(localsRegister, rsp);
            // mov rbp, rsp
            assembler.MovRegReg(rbp, rsp);
        }

        private static void EmitEpilogue(IAmd64Assembler assembler, uint numStackSlots)
        {
            // Reset rsp
            assembler.AddRegImm32(rsp, 8 * (uint)numStackSlots);
            // Restore nonvolatile registers (including rbp)
            for (int i = nonvolatileRegs.Length - 1; i >= 0; i--)
                assembler.PopReg(nonvolatileRegs[i]);

            assembler.Ret();
        }

        private static unsafe void FixupFramePtr(nint pagePtr, uint slotCount)
        {
            var subRspStart = pagePtr + 12;
            var encoding = *(ulong*)subRspStart & 0xFF00FFFFFFFFFFFF;
            if (encoding != 0x4800fffff8ec8148)
                throw new InvalidOperationException($"rsp fixup position changed!");

            var conv = slotCount * 8;
            *(uint*)(subRspStart + 3) = conv;
        }

        private static void FixupIcedFramePtr(List<Instruction> instructions, uint slotCount)
        {
            var subInst = instructions[8];
            if (subInst.Code != Code.Sub_rm64_imm8 && subInst.Code != Code.Sub_rm64_imm32)
                throw new InvalidOperationException($"rsp position changed!");
            instructions[8] = Instruction.Create(Code.Sub_rm64_imm32, Register.RSP, (int)slotCount * 8);
        }

        private unsafe void WriteInstructions(nint page, List<Instruction> instructions)
        {
            var bytes = JitUtils.EncodeInstructions(instructions, (ulong)page, out ulong _);
            for(int i = 0; i < bytes.Length; i++)
            {
                *(byte*)(page + i) = bytes[i];
            }
        }
    }
}
