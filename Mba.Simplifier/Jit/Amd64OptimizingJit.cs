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
using System.Net.Mail;
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

    [StructLayout(LayoutKind.Explicit)]
    public struct NodeInfo
    {
        [FieldOffset(0)]
        public ushort numUses;
        [FieldOffset(2)]
        public ushort varIdx;
        [FieldOffset(4)]
        public ushort slotIdx = ushort.MaxValue;
        [FieldOffset(6)]
        public ushort exists = 1;

        public NodeInfo(ushort numInstances)
        {
            this.numUses = numInstances;
        }

        public unsafe ulong ToUlong()
        {
            return Unsafe.As<NodeInfo, ulong>(ref this);
        }

        public unsafe static NodeInfo FromUlong(ulong x)
        {
            return *((NodeInfo*)&x);
        }

        public override string ToString()
        {
            return $"numInstances:{numUses}, slotIdx: {slotIdx}";
        }

        public bool Equivalent(NodeInfo other)
        {
            return this.ToUlong() == other.ToUlong();
        }
    }

    public interface IInfoStorage
    {
        public bool Contains(AstIdx idx);

        public NodeInfo Get(AstIdx idx);

        public void Set(AstIdx idx, NodeInfo info);

        public bool TryGet(AstIdx idx, out NodeInfo info);
    }

    public class MapInfoStorage : IInfoStorage
    {
        public readonly Dictionary<AstIdx, NodeInfo> map = new();

        public bool Contains(AstIdx idx)
        {
            return map.ContainsKey(idx);
        }

        public NodeInfo Get(AstIdx idx)
        {
            return map[idx];
        }

        public void Set(AstIdx idx, NodeInfo info)
        {
            map[idx] = info;
        }

        public bool TryGet(AstIdx idx, out NodeInfo info)
        {
            return map.TryGetValue(idx, out info);
        }
    }

    public class AuxInfoStorage : IInfoStorage
    {
        private readonly AstCtx ctx;

        public AuxInfoStorage(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public bool Contains(AstIdx idx)
        {
            return Get(idx).exists != 0;
        }

        public NodeInfo Get(AstIdx idx)
        {
            return NodeInfo.FromUlong(ctx.GetImutData(idx));
        }

        public void Set(AstIdx idx, NodeInfo info)
        {
            ctx.SetImutData(idx, info.ToUlong());
        }

        public bool TryGet(AstIdx idx, out NodeInfo info)
        {
            info = Get(idx);
            return info.exists != 0;
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

        IInfoStorage seen;

        private ushort slotCount = 0;

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
            seen = new MapInfoStorage();
        }

        public unsafe ulong Compile(AstIdx idx, List<AstIdx> variables, nint pagePtr, bool useIcedBackend = false)
        {
            Assembler icedAssembler = useIcedBackend ? new Assembler(64) : null;
            assembler = useIcedBackend ? new IcedAmd64Assembler(icedAssembler) : new FastAmd64Assembler((byte*)pagePtr);

            
            // Collect information about the nodes necessary for JITing (dfs order, how many users a value has)
            CollectInfo(ctx, idx, dfs, seen);

            var dfs2 = new List<AstIdx>();
            CollectInfoFast(ctx, idx, dfs2, new MapInfoStorage());
            dfs2.Reverse();

            var dfs1 = dfs;
            if (!dfs.SequenceEqual(dfs2))
            {
                Console.WriteLine("Not equal");
                Debugger.Break();
            }

            Debugger.Break();

            // Store each variables argument index
            for (int i = 0; i < variables.Count; i++)
            {
                var vIdx = variables[i];
                var data = seen.Get(vIdx);
                data.varIdx = (byte)i;
                seen.Set(vIdx, data);
            }

            // Compile the instructions to x86.
            LowerToX86();

            // Clear each node's mutable data
            foreach (var id in dfs)
            {
                seen.Set(id, NodeInfo.FromUlong(0));
            }

            // If using the fast assembler backend, we've already emitted x86.
            // However the stack pointer adjustment needs to fixed up, because it wasn't known during prologue emission.
            if (!useIcedBackend)
            {
                FixupFramePtr(pagePtr, slotCount);
                var asm = (assembler as FastAmd64Assembler);
                return (ulong)((ulong)asm.ptr - (ulong)asm.start);
            }

            // Otherwise adjust the RSP in ICED
            var instructions = icedAssembler.Instructions.ToList();
            FixupIcedFramePtr(instructions, slotCount);

            // Write the instructions to memory. 
            // ICED internally emits a list of assembled instructions rather than raw x86 bytes
            // so this must be done after the fact.
            return WriteInstructions(pagePtr, instructions);
        }

        private static void CollectInfoFast(AstCtx ctx, AstIdx idx, List<AstIdx> dfs, IInfoStorage seen)
        {
            var s1 = new Stack<AstIdx>();
            var s2 = new Stack<AstIdx>(0);
            s1.Push(idx);

            while(s1.Any())
            {
                var current = s1.Peek();
                s1.Pop();
                dfs.Add(current);

                if (seen.Contains(current))
                    continue;
                seen.Set(current, new(1));

                var left = GetLeft(ctx, current);
                if (left != null)
                {
                    s1.Push(left.Value.value);
                }

                var right = GetRight(ctx, current);
                if (right != null)
                {
                    s1.Push(right.Value.value);
                }
            }
        }


        private static (AstIdx owner, AstIdx value)? GetLeft(AstCtx ctx, AstIdx idx)
        {
            return ctx.GetOpcode(idx) switch
            {
                AstOp.Add or AstOp.Mul or AstOp.Pow or AstOp.And or AstOp.Or or AstOp.Xor or AstOp.Lshr or AstOp.Neg or AstOp.Zext or AstOp.Trunc => (idx, ctx.GetOp0(idx)),
                _ => null,
            };
        }

        private static (AstIdx owner, AstIdx value)? GetRight(AstCtx ctx, AstIdx idx)
        {
            return ctx.GetOpcode(idx) switch
            {
                AstOp.Add or AstOp.Mul or AstOp.Pow or AstOp.And or AstOp.Or or AstOp.Xor or AstOp.Lshr => (idx, ctx.GetOp1(idx)),
                _ => null,
            };
        }

        static ushort Inc(ushort cl)
        {
            cl += 1;
            return cl == 0 ? ushort.MaxValue : cl;
        }


        private static void CollectInfo(AstCtx ctx, AstIdx idx, List<AstIdx> dfs, IInfoStorage seen)
        {
            if (seen.TryGet(idx, out var existing))
            {
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
                    CollectInfo(ctx,op0, dfs, seen);
                    var op1 = ctx.GetOp1(idx);
                    CollectInfo(ctx, op1, dfs, seen);

                    seen.Set(op0, new NodeInfo(Inc(seen.Get(op0).numUses)));
                    seen.Set(op1, new NodeInfo(Inc(seen.Get(op1).numUses)));
                    break;
                case AstOp.Neg:
                case AstOp.Zext:
                case AstOp.Trunc:
                    var single = ctx.GetOp0(idx);
                    CollectInfo(ctx, single, dfs, seen);
                    seen.Set(single, new NodeInfo(Inc(seen.Get(single).numUses)));
                    break;
                case AstOp.Constant:
                default:
                    break;
            }

            dfs.Add(idx);
            seen.Set(idx, new NodeInfo(0));
        }

        // Compile the provided DAG to x86
        // TODO: Optionally disabled hashmap lookup/use tracking stuff for faster codegen. Pretend DAG is an AST if the duplicated cost is not too high
        private unsafe void LowerToX86()
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
                var nodeInfo = seen.Get(idx);
                // If we've seen this value, load it's value from a local variable slot
                if (nodeInfo.numUses > 1 && nodeInfo.slotIdx != ushort.MaxValue)
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
                        LowerVariable(nodeInfo.varIdx, width);
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
                    if (width % 8 != 0)
                        throw new InvalidOperationException($"Cannot jit shr of non power of 2 width");
                    // Reduce shift count modulo bit width of operation
                    // TODO: Hand non power of two bit widths
                    // TODO: Shift beyond bounds should yield zero
                    assembler.AndRegImm32(rhsDest, width - 1);

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
                    throw new InvalidOperationException($"{opc} is not a valid binop ");
            }

            ReduceRegisterModulo(width, lhsDest, scratch1);

            if (rhsLoc.IsRegister)
                freeRegisters.Push(rhsLoc.Register);

            // If there are multiple users of this value, throw it in a stack slot.
            bool multipleUsers = nodeInfo.numUses > 1;
            if (multipleUsers)
            {
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

        private void LowerVariable(int varArrIdx, uint width)
        {
            if (freeRegisters.Count != 0)
            {
                var dest = freeRegisters.Pop();
                assembler.MovRegMem64(dest, argsRegister, 8 * varArrIdx);
                ReduceRegisterModulo(width, dest, scratch1);
                stack.Push(Location.Reg(dest));
                return;
            }

            assembler.PushMem64(argsRegister, 8 * varArrIdx);
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
                assembler.MovabsRegImm64(scratch2, (ulong)ModuloReducer.GetMask(width));
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
            seen.Set(idx, nodeInfo);
            // Bump slot count up. Throw if we hit the max slot limit
            checked
            {
                slotCount += 1;
            }
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

        private unsafe ulong WriteInstructions(nint page, List<Instruction> instructions)
        {
            var bytes = JitUtils.EncodeInstructions(instructions, (ulong)page, out ulong _);
            for(int i = 0; i < bytes.Length; i++)
            {
                *(byte*)(page + i) = bytes[i];
            }
            return (ulong)bytes.Length;
        }
    }
}
