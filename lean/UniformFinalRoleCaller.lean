import UniformFinalRoleClockValues
import UniformFinalPhysicalTablePrefix
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleCaller
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformFinalRoleExecution UniformFinalPhysicalTablePrefix UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
lemma LocalStages.bound {n B t:ℕ} {x:Fin n→ℂ} {ps:List Program} {s u:State}
 (h:UniformSequentialExecution.LocalStages n B x ps s t u):WordBound B u:=by
 induction h with
 | nil _ bound=>exact bound
 | cons _ _ ih=>exact ih
lemma frame_pc {n pc:ℕ} {s u:State} (h:UniformFinalRoleExecution.Frame n s u):
 UniformFinalRoleExecution.Frame n s (setPC u pc):=
 ⟨h.natHeap,h.scalar,h.natReg,h.scalarReg,h.outputs,h.roots⟩
lemma frame_before_pc {n pc:ℕ} {s u:State} (h:UniformFinalRoleExecution.Frame n (setPC s pc) u):
 UniformFinalRoleExecution.Frame n s u:=
 ⟨h.natHeap,h.scalar,h.natReg,h.scalarReg,h.outputs,h.roots⟩
lemma frame_trans {n:ℕ} {s a u:State} (h:UniformFinalRoleExecution.Frame n s a)
 (f:UniformFinalRoleExecution.Frame n a u):UniformFinalRoleExecution.Frame n s u:=
 ⟨f.natHeap.trans h.natHeap,fun q hq=>(f.scalar q hq).trans (h.scalar q hq),
  fun q hq hc=>(f.natReg q hq hc).trans (h.natReg q hq hc),
  fun q h20 h32 h94=>(f.scalarReg q h20 h32 h94).trans (h.scalarReg q h20 h32 h94),
  f.outputs.trans h.outputs,f.roots.trans h.roots⟩
lemma source_address {n:ℕ} {x:Fin n→ℂ} {s:State} (h:Result n x s):
 s.natReg 6026=2*UniformJointAllocation.slab c n:=by
 have a:=h.headers 6 (by decide)
 simpa only[Nat.reduceAdd,UniformJointAllocationMachine.factors,List.getElem_cons_succ,List.getElem_cons_zero] using a
lemma volume_positive {n:ℕ} (hn:0<n):0<V n:=by
 have h:=UniformWorkingLength.workingLength_lower n
 change 2*n≤V n at h
 omega

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
 UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨u,run,up,cells,_args,frame⟩:=UniformFinalRoleExecution.execution hn x true
  (UniformSelectedPhysicalCRT.physicalAlpha n) s entry.core entry.data (source_address entry)
  entry.tableArgs.alpha entry.alpha wb
 have source:=UniformFinalRoleClockValues.source _ u cells
 exact ⟨u,run,up,source,UniformFinalRoleClockValues.prepared x _,
  UniformFinalRoleClockValues.kernel_numeric x true _ u source,frame⟩

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
 UniformFinalRoleExecution.Frame n s u:=by
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
 obtain ⟨u,alpha,up,physical,aframe⟩:=UniformFinalRoleAlpha.execution hn x _ a0 core (args_pc args)
  source tableAddress table cells rfl (changePC_bound _ a 0 (LocalStages.bound run) (by omega))
 have stages:=run.append (UniformSequentialExecution.LocalStages.cons alpha (.nil u alpha.final_bound))
 have output:=UniformFinalRoleClockValues.source _ u physical
 refine ⟨u,?_,up,output,UniformFinalRoleClockValues.data_numeric x _ u output,
  frame_trans frame (frame_before_pc aframe)⟩
 simpa only[List.cons_append,List.nil_append,Nat.add_zero,Bool.false_eq_true,ite_false] using stages
end
end ExactFourierCircuits.UniformFinalRoleCaller
