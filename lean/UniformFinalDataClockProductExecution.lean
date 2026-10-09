import UniformFinalDataClockProductResult
import UniformActualCompleteClockExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDataClockProduct
open UniformMachine UniformFinalNumericJoin UniformSelectedPhysicalCRT UniformSequentialExecution
open UniformFinalClockOuterRetention
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
attribute [local irreducible] Nat.add Nat.mul UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program

lemma stages_bound {n B ticks:ℕ}{x:Fin n→ℂ}{ps:List Program}{s u:State}
 (h:LocalStages n B x ps s ticks u):WordBound B u:=by
 induction h with
 | nil s bound=>exact bound
 | cons _ _ ih=>exact ih

lemma stages_beforePC {n B ticks p:ℕ}{x:Fin n→ℂ}{q:Program}{qs:List Program}{s u:State}
 (h:LocalStages n B x (q::qs) s ticks u):LocalStages n B x (q::qs) {s with pc:=p} ticks u:=by
 cases h with
 | cons first rest=>exact .cons first rest

/-- Same actual data-clock run, real pointwise multiplication and both CRT
moves; its third entry is derived from generated physical banks and frames. -/
theorem execution {n ticks:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (volume n)→Scalar)(y:Fin (volume n)→ℂ)(s dataOut:State)
 (pc:s.pc=0)
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x (budget n) s ticks dataOut)
 (output:UniformActualCompleteClockExecution.Output hn x v s dataOut)
 (table:UniformFinalPhysicalTablePrefix.Result n x s)
 (cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
 (saved:∀j:Fin (volume n),s.scalarHeap (savedBase n+j.val)=some (UniformPairMachine.prepared (y j))):
 ∃productOut thirdIn,LocalStages n (budget n) x
  [UniformActualGlobalClockProgram.program,UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]
  s (ticks+27*volume n+27) thirdIn ∧ Result hn x y s dataOut productOut thirdIn:=by
 have role:0<UniformActualClockEntry.roles:=lt_of_lt_of_le (by decide:0<2) UniformFinalRoleGeometry.roles_two
 have transform:HeapTransform (physicalAlpha n) (physicalBeta n) (sourceBase n) (sourceBase n) s dataOut:=by
  exact zero_role_transform (physicalAlpha n) (physicalBeta n) s dataOut
   (UniformFinalClockHeapTransform.heap_transform v s dataOut source output.numeric 0 role)
 have tableK:=output.retained.table hn table
 have savedK:∀j:Fin (volume n),dataOut.scalarHeap (savedBase n+j.val)=some (UniformPairMachine.prepared (y j)):=
  fun j=>(output.spectrum j).trans (saved j)
 have dataSource:=UniformFinalClockHeapTransform.numeric_source v dataOut output.numeric
 let d0:=UniformTensorMonomialMachine.setPC dataOut 0
 obtain ⟨p,u,tail,numeric,reindex,standard,uSource,uSaved,frame,up⟩:=
  UniformFinalMovementCaller.pointwise_crt hn x (UniformFinalClockHeapTransform.actualValues n dataOut) y d0
  (UniformFinalMovementCaller.Header.of_table tableK.withPC)
  (UniformFinalMovementCaller.Tables.of_table tableK.withPC) dataSource savedK rfl
  (changePC_bound _ dataOut 0 run.final_bound (Nat.zero_le _))
 have movement:UniformFinalMovementFrame.Frame n dataOut u:=frame.beforePC dataOut.pc
 have outer:=output.retained.trans (Frame.movement hn movement)
 have tableU:=outer.table hn table
 have cacheU:=outer.cache_all hn cache
 have runtime:=Frame.movement_runtime hn movement output.runtime
 have actualSource:UniformActualClockEntry.Source n (thirdValues (n:=n) dataOut y) u:=uSource
 have productNumeric:NumericValues (sourceBase n) (product (n:=n) dataOut) p:=by
  exact Eq.mp (congrArg (fun f=>NumericValues (sourceBase n) f p) (product_eq dataOut y savedK)) numeric
 have reindexed:NumericValues (sourceBase n)
  (fun j=>product (n:=n) dataOut ((physicalBeta n).symm (physicalAlpha n j))) u:=by
  intro j
  exact (congrArg (Option.map Scalar.value) (reindex j)).trans (productNumeric _)
 have wb:=stages_bound tail
 have input:=UniformFinalClockRuntime.input hn x (thirdValues (n:=n) dataOut y)
  (UniformTensorMonomialMachine.setPC u 0) runtime.pc tableU.withPC.core.metadata tableU.withPC.core.operands
  actualSource rfl (changePC_bound _ u 0 wb (Nat.zero_le _))
 have cache0:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n)
  (UniformTensorMonomialMachine.setPC u 0):=by
  intro j hj
  exact UniformAxisCacheContents.transport (cacheU j hj) ⟨by intros;rfl,by intros;rfl⟩
 have reset:{s with pc:=0}=s:=by rw[←pc]
 have tailOriginal:LocalStages n (budget n) x
  [UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]
  dataOut ((9*volume n+9)+(18*volume n+18)) u:=
  stages_beforePC (s:=d0) (p:=dataOut.pc) tail
 have joined:LocalStages n (budget n) x
  [UniformActualGlobalClockProgram.program,UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]
  s (ticks+((9*volume n+9)+(18*volume n+18))) u:=
  .cons (by rw[reset];exact run) tailOriginal
 refine ⟨p,u,?_,transform,output.spectrum,productNumeric,reindex,standard,reindexed,actualSource,
  ⟨input,UniformAxisCacheInputs.of_core tableU.withPC.core,cache0⟩,tableU.withPC,
  cacheU,runtime,uSaved,fun j=>(uSaved j).trans (savedK j).symm,outer,movement,up⟩
 convert joined using 1;omega

end
end ExactFourierCircuits.UniformFinalDataClockProduct
