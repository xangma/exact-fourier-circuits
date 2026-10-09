import UniformGlobalKernelDiagonalAssembly
import UniformGlobalAxisUnionAdapter
import UniformGlobalCalendarDispatchWhole

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockConductor
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- The completed cache allocator's measured ends are copied before any
per-axis replay. The horizon5921 was accumulated by charged timing loads. -/
def boot:List Op:=[.literal 5939 1,.literal 5920 0,.mul 5936 6819 5939,
 .mul 5937 6821 5939,.add 5938 102 5939]
def axisBoot:List Op:=[.literal 5922 0,.mul 5924 5936 5939,.mul 5925 5937 5939,.mul 5923 6020 5939]
def advance:List Op:=[.mul 5924 5934 5939,.mul 5925 5935 5939,
 .add 5922 5922 5939,.literal 5933 2,.add 5923 5923 5933]
def tickAdvance:List Op:=[.add 5920 5920 5939]
lemma boot_length:boot.length=5:=rfl
lemma axisBoot_length:axisBoot.length=4:=rfl
lemma advance_length:advance.length=5:=rfl
lemma tickAdvance_length:tickAdvance.length=1:=rfl

def dispatchBase (prepare:Program):ℕ:=11+prepare.length
def adapterBase (prepare:Program):ℕ:=dispatchBase prepare+281
def advanceBase (prepare:Program):ℕ:=adapterBase prepare+69
def kernelBase (prepare:Program):ℕ:=advanceBase prepare+6
def tickBase (prepare child:Program) (W:ℕ):ℕ:=
 kernelBase prepare+(UniformGlobalKernelDiagonalAssembly.programFor child W).length
def finalPC (prepare child:Program) (W:ℕ):ℕ:=tickBase prepare child W+2

/-- Literal clock/all-axis control. The preparation site is reserved for the
actual epoch/cache-range producer, whose numerical proof is separate. Actual
281 dispatch, actual69 matching-axis publication, and actual kernel+diagonal
are already fixed here, once each, and are revisited by charged backedges. -/
def programFor (prepare child:Program) (W:ℕ):Program:=
 boot.map Op.code++[.branchLT 5920 5921 6 (finalPC prepare child W)]++axisBoot.map Op.code++
 [.branchLT 5922 5938 11 (kernelBase prepare)]++
 prepare.map (relocate 11 (dispatchBase prepare))++
 UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
 UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
 advance.map Op.code++[.jump 10]++
 (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
 tickAdvance.map Op.code++[.jump 5,.halt]

lemma program_length (prepare child:Program) (W:ℕ):
 (programFor prepare child W).length=prepare.length+child.length+1183:=by
 simp only[programFor,List.length_append,List.length_map,boot_length,axisBoot_length,advance_length,
  tickAdvance_length,UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,
  UniformGlobalKernelDiagonalAssembly.program_length,List.length_cons,List.length_nil]
 omega
lemma prepare_code (prepare child:Program) (W:ℕ):
 CodeAt prepare (programFor prepare child W) 11 (dispatchBase prepare):=by
 have link:= UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 5920 5921 6 (finalPC prepare child W)]++axisBoot.map Op.code++
   [.branchLT 5922 5938 11 (kernelBase prepare)])
  (UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
   UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
   advance.map Op.code++[.jump 10]++
   (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
   tickAdvance.map Op.code++[.jump 5,.halt]) prepare 11 (dispatchBase prepare) rfl
 simpa only[programFor,List.append_assoc] using link
lemma dispatch_code (prepare child:Program) (W:ℕ):
 CodeAt UniformGlobalCalendarDispatch.program (programFor prepare child W) (dispatchBase prepare) (adapterBase prepare):=by
 have link:= UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 5920 5921 6 (finalPC prepare child W)]++axisBoot.map Op.code++
   [.branchLT 5922 5938 11 (kernelBase prepare)]++prepare.map (relocate 11 (dispatchBase prepare)))
  (UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
   advance.map Op.code++[.jump 10]++
   (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
   tickAdvance.map Op.code++[.jump 5,.halt]) UniformGlobalCalendarDispatch.program (dispatchBase prepare) (adapterBase prepare) (by
    simp only[List.length_append,List.length_map,boot_length,axisBoot_length,List.length_cons,List.length_nil,dispatchBase])
 simpa only[programFor,List.append_assoc] using link
lemma adapter_code (prepare child:Program) (W:ℕ):
 CodeAt UniformGlobalAxisUnionAdapter.program (programFor prepare child W) (adapterBase prepare) (advanceBase prepare):=by
 have link:= UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 5920 5921 6 (finalPC prepare child W)]++axisBoot.map Op.code++
   [.branchLT 5922 5938 11 (kernelBase prepare)]++prepare.map (relocate 11 (dispatchBase prepare))++
   UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare)))
  (advance.map Op.code++[.jump 10]++
   (UniformGlobalKernelDiagonalAssembly.programFor child W).map (relocate (kernelBase prepare) (tickBase prepare child W))++
   tickAdvance.map Op.code++[.jump 5,.halt]) UniformGlobalAxisUnionAdapter.program (adapterBase prepare) (advanceBase prepare) (by
    simp only[List.length_append,List.length_map,boot_length,axisBoot_length,List.length_cons,List.length_nil,
     UniformGlobalCalendarDispatch.program_length,adapterBase,dispatchBase])
 simpa only[programFor,List.append_assoc] using link
lemma kernel_code (prepare child:Program) (W:ℕ):
 CodeAt (UniformGlobalKernelDiagonalAssembly.programFor child W) (programFor prepare child W)
  (kernelBase prepare) (tickBase prepare child W):=by
 have link:= UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 5920 5921 6 (finalPC prepare child W)]++axisBoot.map Op.code++
   [.branchLT 5922 5938 11 (kernelBase prepare)]++prepare.map (relocate 11 (dispatchBase prepare))++
   UniformGlobalCalendarDispatch.program.map (relocate (dispatchBase prepare) (adapterBase prepare))++
   UniformGlobalAxisUnionAdapter.program.map (relocate (adapterBase prepare) (advanceBase prepare))++
   advance.map Op.code++[.jump 10]) (tickAdvance.map Op.code++[.jump 5,.halt]) (UniformGlobalKernelDiagonalAssembly.programFor child W)
  (kernelBase prepare) (tickBase prepare child W) (by
    simp only[List.length_append,List.length_map,boot_length,axisBoot_length,List.length_cons,List.length_nil,
     UniformGlobalCalendarDispatch.program_length,UniformGlobalAxisUnionAdapter.program_length,advance_length,
     kernelBase,advanceBase,adapterBase,dispatchBase])
 simpa only[programFor,List.append_assoc] using link
end
end ExactFourierCircuits.UniformGlobalClockConductor
