import UniformActualCompleteClockResult
import UniformFinalClockOuterRuntime
import UniformFinalClockHeapTransform

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalKernelClockSave
open UniformMachine UniformFinalNumericJoin UniformSelectedPhysicalCRT UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
attribute [local irreducible] UniformActualGlobalClockProgram.program
abbrev volume(n:ℕ):ℕ:=UniformInitialPreparation.len n
def kernelBase(n:ℕ):ℕ:=UniformActualClockEntry.sourceBase n+volume n
abbrev savedBase(n:ℕ):ℕ:=UniformFinalMovementFrame.Q n
abbrev budget(n:ℕ):ℕ:=UniformJointAllocation.envelope c n

structure Result {n:ℕ}[NeZero (volume n)](hn:0<n)(x:Fin n→ℂ)(s kernelOut u:State):Prop where
 transform:HeapTransform (physicalAlpha n) (physicalBeta n) (kernelBase n) (kernelBase n) s kernelOut
 numeric:NumericValues (kernelBase n) (fun i=>kernelSpectrum (n:=n) (physicalBeta n i)) kernelOut
 kernelCells:∀i:Fin (volume n),kernelOut.scalarHeap (kernelBase n+i.val)=
  some (UniformPairMachine.prepared (kernelSpectrum (n:=n) (physicalBeta n i)))
 saved:∀i:Fin (volume n),u.scalarHeap (savedBase n+i.val)=
  some (UniformPairMachine.prepared (kernelSpectrum (n:=n) (physicalBeta n i)))
 copied:∀i:Fin (volume n),u.scalarHeap (savedBase n+i.val)=kernelOut.scalarHeap (kernelBase n+i.val)
 table:UniformFinalPhysicalTablePrefix.Result n x u
 cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) u
 runtime:UniformFinalClockRuntime.Runtime n u
 frame:UniformFinalClockOuterRetention.Frame n s u
 movement:UniformFinalMovementFrame.Frame n kernelOut u
 copyFrame:UniformKernelSpectrumCopy.Frame (savedBase n) (volume n) kernelOut u
 pc:u.pc=14

/-- Join the same actual complete-clock run to the real copy15. Spectrum
values, prepared tags and every retained input are derived from that run. -/
theorem execution {n ticks:ℕ}[NeZero (volume n)](hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (volume n)→Scalar)(s kernelOut:State)
 (pc:s.pc=0)
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x (budget n) s ticks kernelOut)
 (output:UniformActualCompleteClockExecution.Output hn x v s kernelOut)
 (table:UniformFinalPhysicalTablePrefix.Result n x s)
 (cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)(prepared:UniformActualClockEntry.Prepared v)
 (kernelInput:NumericValues (kernelBase n) (fun i=>kernel (n:=n) (physicalAlpha n i)) s):
 ∃u,LocalStages n (budget n) x [UniformActualGlobalClockProgram.program,UniformKernelSpectrumCopy.program]
 s (ticks+7*volume n+9) u ∧ Result hn x s kernelOut u:=by
 have role:1<UniformActualClockEntry.roles:=UniformFinalRoleGeometry.roles_two
 have transform:HeapTransform (physicalAlpha n) (physicalBeta n) (kernelBase n) (kernelBase n) s kernelOut:=by
  simpa only[kernelBase,Nat.one_mul] using
   UniformFinalClockHeapTransform.heap_transform v s kernelOut source output.numeric 1 role
 have numeric:=UniformFinalClockHeapTransform.kernel_spectrum (physicalAlpha n) (physicalBeta n)
  s kernelOut kernelInput transform
 have tags:∀i:Fin (volume n),(scalars (volume n) (kernelBase n) kernelOut i).dependent=false:=by
  simpa only[kernelBase,Nat.one_mul] using
   UniformFinalClockHeapTransform.prepared_tags kernelOut (output.prepared prepared) 1 role
 have cells:∀i:Fin (volume n),kernelOut.scalarHeap (kernelBase n+i.val)=
  some (UniformPairMachine.prepared (kernelSpectrum (n:=n) (physicalBeta n i))):=
  prepared_copy _ kernelOut kernelOut numeric tags (fun _=>rfl)
 let k0:State:={kernelOut with pc:=0}
 have tableK:=output.retained.table hn table
 obtain ⟨u,copy,saved,frame,copyFrame,up⟩:=UniformFinalMovementCaller.save hn x
  (fun i=>kernelSpectrum (n:=n) (physicalBeta n i)) k0
  (UniformFinalMovementCaller.Header.of_table tableK.withPC) numeric tags rfl
  (changePC_bound _ kernelOut 0 run.final_bound (Nat.zero_le _))
 have movement:UniformFinalMovementFrame.Frame n kernelOut u:=by
  exact frame.beforePC kernelOut.pc
 have copiedFrame:UniformKernelSpectrumCopy.Frame (savedBase n) (volume n) kernelOut u:=by
  rcases copyFrame with ⟨hN,hS,hO,hR,hG⟩
  exact ⟨hN,hS,hO,hR,hG⟩
 have outer:=output.retained.trans (UniformFinalClockOuterRetention.Frame.movement hn movement)
 have reset:{s with pc:=0}=s:=by rw[←pc]
 have stages:LocalStages n (budget n) x [UniformActualGlobalClockProgram.program,UniformKernelSpectrumCopy.program]
  s (ticks+((7*volume n+9)+0)) u:=
  .cons (by rw[reset];exact run) (.cons copy (.nil u copy.final_bound))
 refine ⟨u,by simpa only[Nat.add_zero,Nat.add_assoc] using stages,?_⟩
 exact ⟨transform,numeric,cells,saved,fun i=>(saved i).trans (cells i).symm,
  outer.table hn table,outer.cache_all hn cache,
  UniformFinalClockOuterRetention.Frame.movement_runtime hn movement output.runtime,
  outer,movement,copiedFrame,up⟩

lemma Result.beforePC {n p:ℕ}[NeZero (volume n)]{hn:0<n}{x:Fin n→ℂ}{s kernelOut u:State}
 (h:Result hn x s kernelOut u):Result hn x {s with pc:=p} kernelOut u:=
 ⟨h.transform,h.numeric,h.kernelCells,h.saved,h.copied,h.table,h.cache,h.runtime,
  h.frame.beforePC p,h.movement,h.copyFrame,h.pc⟩

lemma stages_beforePC {n B ticks p:ℕ}{x:Fin n→ℂ}{q:Program}{qs:List Program}{s u:State}
 (h:LocalStages n B x (q::qs) s ticks u):LocalStages n B x (q::qs) {s with pc:=p} ticks u:=by
 cases h with
 | cons first rest=>exact .cons first rest

/-- The same executed subroutine joins from the preceding stage's actual
state; the existing LocalStages relocation charges its real continuation. -/
theorem execution_local {n ticks:ℕ}[NeZero (volume n)](hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (volume n)→Scalar)(s kernelOut:State)
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x (budget n) {s with pc:=0} ticks kernelOut)
 (output:UniformActualCompleteClockExecution.Output hn x v {s with pc:=0} kernelOut)
 (table:UniformFinalPhysicalTablePrefix.Result n x s)
 (cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)(prepared:UniformActualClockEntry.Prepared v)
 (kernelInput:NumericValues (kernelBase n) (fun i=>kernel (n:=n) (physicalAlpha n i)) s):
 ∃u,LocalStages n (budget n) x [UniformActualGlobalClockProgram.program,UniformKernelSpectrumCopy.program]
 s (ticks+7*volume n+9) u ∧ Result hn x s kernelOut u:=by
 have cache0:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) {s with pc:=0}:=by
  intro j hj
  exact UniformAxisCacheContents.transport (cache j hj) ⟨by intros;rfl,by intros;rfl⟩
 obtain ⟨u,stages,result⟩:=execution hn x v {s with pc:=0} kernelOut rfl run output
  table.withPC cache0 source prepared kernelInput
 refine ⟨u,?_,result.beforePC (p:=s.pc)⟩
 exact stages_beforePC (s:={s with pc:=0}) (p:=s.pc) stages

end
end ExactFourierCircuits.UniformFinalKernelClockSave
