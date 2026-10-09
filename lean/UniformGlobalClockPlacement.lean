import UniformGlobalClockConductor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockPlacement
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op BlockAt)
open UniformGlobalClockConductor
noncomputable section
lemma instruction_at (head tail:Program) (ins:Instruction) (base:ℕ) (h:head.length=base):
 (head++[ins]++tail)[base]?=some ins:=by
 rw[←h,List.append_assoc,List.getElem?_append_right (le_refl _)]
 simp only[Nat.sub_self,List.singleton_append,List.getElem?_cons_zero]
lemma boot_code (prepare child:Program) (W:ℕ):
 BlockAt boot (programFor prepare child W) (0):=by
 have link:=UniformRankCrossPreparationMachine.block_of_segment boot
  ([]) ([Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code++
  [Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code++
  [Instruction.jump 5]++
  [Instruction.halt]) (0) (by
   simp only[List.length_nil])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma axis_code (prepare child:Program) (W:ℕ):
 BlockAt axisBoot (programFor prepare child W) (6):=by
 have link:=UniformRankCrossPreparationMachine.block_of_segment axisBoot
  (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]) ([Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code++
  [Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code++
  [Instruction.jump 5]++
  [Instruction.halt]) (6) (by
   simp only[List.length_append,List.length_map,boot_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma advance_code (prepare child:Program) (W:ℕ):
 BlockAt advance (programFor prepare child W) (advanceBase prepare):=by
 have link:=UniformRankCrossPreparationMachine.block_of_segment advance
  (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))) ([Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code++
  [Instruction.jump 5]++
  [Instruction.halt]) (advanceBase prepare) (by
   simp only[List.length_append,List.length_map,boot_length,axisBoot_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma tick_code (prepare child:Program) (W:ℕ):
 BlockAt tickAdvance (programFor prepare child W) (tickBase prepare child W):=by
 have link:=UniformRankCrossPreparationMachine.block_of_segment tickAdvance
  (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code++
  [Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))) ([Instruction.jump 5]++
  [Instruction.halt]) (tickBase prepare child W) (by
   simp only[List.length_append,List.length_map,boot_length,axisBoot_length,advance_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma clock_branch (prepare child:Program) (W:ℕ):
 (programFor prepare child W)[5]?=some (.branchLT 5920 5921 6 (finalPC prepare child W)):=rfl
lemma axis_branch (prepare child:Program) (W:ℕ):
 (programFor prepare child W)[10]?=some (.branchLT 5922 5938 11 (kernelBase prepare)):=rfl
lemma axis_backedge (prepare child:Program) (W:ℕ):
 (programFor prepare child W)[advanceBase prepare+5]?=some (.jump 10):=by
 have link:=instruction_at (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code) ((UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code++
  [Instruction.jump 5]++
  [Instruction.halt]) (.jump 10) (advanceBase prepare+5) (by
  simp only[List.length_append,List.length_map,boot_length,axisBoot_length,advance_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma clock_backedge (prepare child:Program) (W:ℕ):
 (programFor prepare child W)[tickBase prepare child W+1]?=some (.jump 5):=by
 have link:=instruction_at (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code++
  [Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code) ([Instruction.halt]) (.jump 5) (tickBase prepare child W+1) (by
  simp only[List.length_append,List.length_map,boot_length,axisBoot_length,advance_length,tickAdvance_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
lemma halt_at (prepare child:Program) (W:ℕ):
 (programFor prepare child W)[finalPC prepare child W]?=some (.halt):=by
 have link:=instruction_at (boot.map Op.code++
  [Instruction.branchLT 5920 5921 6 (finalPC prepare child W)]++
  axisBoot.map Op.code++
  [Instruction.branchLT 5922 5938 11 (kernelBase prepare)]++
  prepare.map (relocate 11 (dispatchBase prepare))++
  UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
  UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
  advance.map Op.code++
  [Instruction.jump 10]++
  (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
  tickAdvance.map Op.code++
  [Instruction.jump 5]) ([]) (.halt) (finalPC prepare child W) (by
  simp only[List.length_append,List.length_map,boot_length,axisBoot_length,advance_length,tickAdvance_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil,dispatchBase,adapterBase,advanceBase,kernelBase,tickBase,finalPC])
 simpa only[programFor,List.append_assoc,List.nil_append,List.singleton_append,List.append_nil,List.cons_append] using link
end
end ExactFourierCircuits.UniformGlobalClockPlacement
