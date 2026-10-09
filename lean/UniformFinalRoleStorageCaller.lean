import UniformFinalRoleStorageAlpha

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleStorageCaller
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformFinalRoleExecution UniformFinalPhysicalTablePrefix UniformSequentialExecution UniformFinalRoleCaller
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
/-- The kernel caller consumes the actual fast53 tables and constructs the
complete prepared all-W input of the first clock. -/
theorem kernel {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (s:State)
 (entry:Result n x s) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (H.roleArgs W true),UniformRoleInputMachine.program] s
  (18+(5*(W*V n)+16*V n+24)) u∧u.pc=41∧
 UniformActualClockEntry.Source n (values x true (UniformSelectedPhysicalCRT.physicalAlpha n)) u∧
 UniformActualClockEntry.Prepared (values x true (UniformSelectedPhysicalCRT.physicalAlpha n))∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (UniformSelectedPhysicalCRT.physicalAlpha n j)) u∧
 UniformFinalRoleExecution.Frame n s u∧u.natReg 7300=UniformKernelSpectrumStorage.base c n:=by
 obtain ⟨u,run,up,cells,args,frame⟩:=UniformFinalRoleExecution.execution hn x true
  (UniformSelectedPhysicalCRT.physicalAlpha n) s entry.core entry.data (source_address entry)
  entry.tableArgs.alpha entry.alpha wb
 have source:=UniformFinalRoleClockValues.source _ u cells
 exact ⟨u,run,up,source,UniformFinalRoleClockValues.prepared x _,
  UniformFinalRoleClockValues.kernel_numeric x true _ u source,frame,args.storage⟩

/-- The data caller physically gathers standard padded input through the real
AP table after the fixed loader; its complete all-W source is produced. -/
theorem data {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (s:State)
 (entry:Result n x s) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (H.roleArgs W false),UniformRoleInputMachine.program,
   UniformPhysicalCRTConsumerMachine.alphaProgram] s
  (19+(5*(W*V n)+16*V n+24)+(9*V n+10)) u∧u.pc=17∧
 UniformActualClockEntry.Source n (UniformFinalRoleAlpha.physical x (UniformSelectedPhysicalCRT.physicalAlpha n)) u∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (UniformSelectedPhysicalCRT.physicalAlpha n j)) u∧
 UniformFinalRoleExecution.Frame n s u∧u.natReg 7300=UniformKernelSpectrumStorage.base c n:=by
 obtain ⟨a,run,_ap,cells,args,frame⟩:=UniformFinalRoleExecution.execution hn x false
  (UniformSelectedPhysicalCRT.physicalAlpha n) s entry.core entry.data (source_address entry)
  entry.tableArgs.alpha entry.alpha wb
 let a0:=setPC a 0
 have core:UniformAxisCachePreparationRetention.Core n x a0:=(frame.core hn entry.core).withPC
 have source:a0.natReg 6026=2*UniformJointAllocation.slab c n:=
  (frame.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans (source_address entry)
 have tableAddress:a0.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n:=
  (frame.natReg _ (by unfold R.Protected;omega) (by unfold H.Changed;omega)).trans entry.tableArgs.alpha
 have table:UniformGlobalNatPreparation.PermutationBank (V n) (UniformKernelSpectrumStorage.alphaBase c n) a0.natHeap
  (UniformSelectedPhysicalCRT.physicalAlpha n):=fun j=>(congrFun frame.natHeap _).trans (entry.alpha j)
 obtain ⟨u,alpha,up,physical,aframe,storage⟩:=UniformFinalRoleStorageAlpha.execution_with_storage hn x _ a0 core (args_pc args)
  source tableAddress table cells rfl (changePC_bound _ a 0 (LocalStages.bound run) (by omega))
 have stages:=run.append (UniformSequentialExecution.LocalStages.cons alpha (.nil u alpha.final_bound))
 have output:=UniformFinalRoleClockValues.source _ u physical
 refine ⟨u,?_,up,output,UniformFinalRoleClockValues.data_numeric x _ u output,
  frame_trans frame (frame_before_pc aframe),storage⟩
 simpa only[List.cons_append,List.nil_append,Nat.add_zero,Bool.false_eq_true,ite_false] using stages
end
end ExactFourierCircuits.UniformFinalRoleStorageCaller
