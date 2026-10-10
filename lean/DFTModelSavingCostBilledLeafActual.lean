import DFTModelSavingCostBilledLeaves
import DFTModelSavingCostFactor
import DFTModelSavingNativeLeafTyped

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
open UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch nativeWorkFactor

/-- Every genuine nonrecursive typed instruction is charged against the exact
native same-program duration, including the stream's 22-instruction overhead.
This is independent of either source run's actual flag pattern. -/
theorem leaf_actual_billed (q rest : ℕ) (cost : ℕ→ℕ) (i : UniformNativeScheduleSemantics.Instruction)
    (leaf : DFTModelSavingNativeLeafTyped.Leaf i) (I : ℂ)
    (h : Handler DFTModelSavingRecords.Port)
    (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar) (qp : 1≤q) :
    (Code.run (DFTModelSavingRecords.dispatch W) h
      (rest,(DFTModelCacheRecords.dataTape (Instruction.record q i).data,
        ((q*m+rest,I),paired f f0)))).work+22≤
      nativeWorkFactor*UniformRecursiveTypedBody.ticks q rest cost i := by
  have source:=DFTModelSavingDirection.dataTape_source (Instruction.record q i)
  have header:=raw_headers (Instruction.record q i) _ source
  cases i with
  | initial=>
    have cap:=marker_native_billed W rest
      (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q .initial))
      (UniformRecursiveRecordControl.dispatchCost (Instruction.record q .initial).opcode)
      _ ((q*m+rest,I),paired f f0) h (Or.inr (header.1.trans rfl))
    exact cap.trans (Nat.mul_le_mul_right _ factor_marker)
  | boundary a=>
    have cap:=marker_native_billed W rest
      (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q (.boundary a)))
      (UniformRecursiveRecordControl.dispatchCost (Instruction.record q (.boundary a)).opcode)
      _ ((q*m+rest,I),paired f f0) h (Or.inl (header.1.trans rfl))
    exact cap.trans (Nat.mul_le_mul_right _ factor_marker)
  | «macro» a v=>
    cases v with
    | edge old new role edge=>exact False.elim leaf
    | shear d src ne c hc=>
      have cap:=scalar_native_billed W rest (q*m+rest) c.val I _ (paired f f0) h
        (header.1.trans rfl) rfl
      exact cap.trans (Nat.mul_le_mul_right _ factor_scalar_exchange)
  | translation=>
    have eqr:=UniformNativeHandlerSemantics.translation_record q
    change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=
      Instruction.record q .translation at eqr
    have bank : DFTModelSavingY.RecordSource q UniformNativeHandlerSemantics.actualDirections
        (DFTModelCacheRecords.dataTape (Instruction.record q .translation).data) := by
      rw [←eqr]
      exact DFTModelSavingNativeY.record_source q _
    have cap:=translation_native_billed q rest (q*m+rest) I _
      UniformNativeHandlerSemantics.actualDirections bank f f0
      (Nat.two_pow_pos ExplicitSeedBudget.roleBits) rfl qp (header.1.trans rfl) h
    exact cap.trans (Nat.mul_le_mul_right _ factor_translation)
  | exchange=>
    have cap:=exchange_native_billed W rest (q*m+rest) I _ (paired f f0) h
      (header.1.trans rfl) rfl
    have eqr:=UniformNativeHandlerSemantics.exchange_record q
    change UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs=
      Instruction.record q .exchange at eqr
    have count : (DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data).look 6 0=
        UniformNativeHandlerSemantics.actualPairs.length := by
      rw [header.2.2.2.2.2.2.1,←eqr]
      rfl
    rw [count] at cap
    exact cap.trans (Nat.mul_le_mul_right _ factor_scalar_exchange)
  | padding=>exact False.elim leaf

end
end ExactFourierCircuits.DFTModelSavingCost
