import UniformActualCompleteClockExecution
import UniformFinalRoleTableEntries
import UniformFinalClockOuterTable
import UniformConcreteFinalOutputTail
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalThirdClockOutput
open UniformMachine UniformTensorMonomialMachine UniformFinalNumericJoin UniformSequentialExecution
noncomputable section
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program
local notation "c"=>UniformActualGlobalConstants.constants
abbrev V (n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev B (n:ℕ):ℕ:=UniformJointAllocation.envelope c n
abbrev S (n:ℕ):ℕ:=UniformFinalMovementGeometry.S n
abbrev K (n:ℕ):ℕ:=S n+V n
abbrev Q (n:ℕ):ℕ:=UniformKernelSpectrumStorage.base c n
abbrev AP (n:ℕ):Fin (V n)≃Fin (V n):=UniformSelectedPhysicalCRT.physicalAlpha n
abbrev BP (n:ℕ):Fin (V n)≃Fin (V n):=UniformSelectedPhysicalCRT.physicalBeta n

lemma zero_heap {L A:ℕ} (alpha beta:Fin L≃Fin L) (s u:State)
 (h:HeapTransform alpha beta (A+0*L) (A+0*L) s u):HeapTransform alpha beta A A s u:=by
 simpa only[Nat.zero_mul,Nat.add_zero] using h
lemma zero_numeric {L A:ℕ} (f:Fin L→ℂ) (s:State)
 (h:NumericValues (A+0*L) f s):NumericValues A f s:=by
 simpa only[Nat.zero_mul,Nat.add_zero] using h

/-- Join the same actual third clock endpoint to actual CRT and output stages.
The only transform inputs are the earlier genuine clock heap postconditions;
the third action is derived from this clock's own numeric output. -/
theorem execution {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ)
 (v:ℕ→Fin (V n)→Scalar) (s thirdOut:State) (ticks:ℕ)
 (clockRun:BoundedExecution UniformActualGlobalClockProgram.program n x (B n) (setPC s 0) ticks thirdOut)
 (clock:UniformActualCompleteClockExecution.Output hn x v (setPC s 0) thirdOut)
 (entry:UniformFinalClockEntries.Entry hn x v (setPC s 0))
 (table:UniformFinalPhysicalTablePrefix.Result n x (setPC s 0))
 (kernelIn kernelOut dataIn dataOut productOut:State)
 (kernelInput:NumericValues (K n) (fun i=>kernel (n:=n) (AP n i)) kernelIn)
 (kernelRun:HeapTransform (AP n) (BP n) (K n) (K n) kernelIn kernelOut)
 (kernelTags:∀i,(scalars (V n) (K n) kernelOut i).dependent=false)
 (kernelSaved:∀i:Fin (V n),dataOut.scalarHeap (Q n+i.val)=kernelOut.scalarHeap (K n+i.val))
 (dataInput:NumericValues (S n) (fun i=>data x (AP n i)) dataIn)
 (dataRun:HeapTransform (AP n) (BP n) (S n) (S n) dataIn dataOut)
 (pointwise:NumericValues (S n) (fun i=>(scalars (V n) (S n) dataOut i).value*
  (scalars (V n) (Q n) dataOut i).value) productOut)
 (thirdReindex:∀i:Fin (V n),s.scalarHeap (S n+i.val)=
  productOut.scalarHeap (S n+((BP n).symm (AP n i)).val)):
 ∃u,LocalStages n (B n) x
  [UniformActualGlobalClockProgram.program,UniformPhysicalCRTConsumerMachine.program,
   UniformSequentialAssembly.natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]
  s (ticks+(18*V n+18)+(13*n+18)) u∧ComputesDFT n x u∧u.rootOrders=s.rootOrders∧
  u.rootOrders=[UniformMasterRootMachine.order n]∧u.pc=17:=by
 have roles:0<UniformActualClockEntry.roles:=UniformRecursiveSelfCallMachine.W_positive
 have thirdRun:HeapTransform (AP n) (BP n) (S n) (S n) (setPC s 0) thirdOut:=by
  change HeapTransform (AP n) (BP n) (UniformActualClockEntry.sourceBase n)
   (UniformActualClockEntry.sourceBase n) (setPC s 0) thirdOut
  exact zero_heap (A:=UniformActualClockEntry.sourceBase n) (AP n) (BP n) (setPC s 0) thirdOut
   (UniformFinalClockHeapTransform.heap_transform v (setPC s 0) thirdOut entry.input.source clock.numeric 0 roles)
 let f:Fin (V n)→ℂ:=fun j=>(UniformPhysicalSynchronizedSchedule.fourier n).mulVec (fun k=>(v 0 k).value) j
 have numeric:NumericValues (S n) f thirdOut:=by
  change NumericValues (UniformActualClockEntry.sourceBase n) f thirdOut
  exact zero_numeric (A:=UniformActualClockEntry.sourceBase n) f thirdOut (clock.numeric 0 roles)
 have thirdTable:=clock.retained.table hn table
 let third0:=setPC thirdOut 0
 have table0:UniformFinalPhysicalTablePrefix.Result n x third0:=thirdTable.withPC
 obtain ⟨finalOut,crtRun,_sourceReindex,finalReindex,_sourceNumeric,_targetNumeric,frame,_outside,_consumer,_pc⟩:=
  UniformFinalMovementCaller.final_crt hn x f third0
   (UniformFinalMovementCaller.Header.of_table table0) (UniformFinalMovementCaller.Tables.of_table table0)
   numeric rfl (changePC_bound _ thirdOut 0 clockRun.final_bound (by omega))
 have finalTable:=(UniformFinalClockOuterRetention.Frame.movement hn frame).table hn table0
 obtain ⟨_saved,u,tail,dft,roots,pc⟩:=UniformConcreteFinalOutputTail.of_three_transform_heaps hn
  (AP n) (BP n) x (K n) (S n) (K n) (Q n)
  kernelIn kernelOut dataIn dataOut productOut (setPC s 0) thirdOut finalOut
  kernelInput kernelRun kernelTags kernelSaved dataInput dataRun pointwise thirdReindex thirdRun finalReindex
  finalTable.core.metadata finalTable.core.operands (UniformFinalMovementCaller.Header.of_table finalTable).target
  crtRun.final_bound
 have first:LocalStages n (B n) x
  [UniformActualGlobalClockProgram.program,UniformPhysicalCRTConsumerMachine.program]
  s (ticks+(18*V n+18)) finalOut:=by
  simpa only[Nat.add_zero] using LocalStages.cons clockRun (LocalStages.cons crtRun (.nil finalOut crtRun.final_bound))
 refine ⟨u,?_,dft,roots.trans (frame.roots.trans clock.retained.roots),roots.trans finalTable.data.roots,pc⟩
 simpa only[List.cons_append,List.nil_append] using first.append tail
end
end ExactFourierCircuits.UniformFinalThirdClockOutput
