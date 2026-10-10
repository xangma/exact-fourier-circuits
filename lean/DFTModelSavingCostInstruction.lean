import DFTModelSavingCostFixedRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.residual
  DFTModelSavingRecords.padding DFTModelSavingScalar.program DFTModelSavingY.program
  DFTModelRecursiveExchange.program DFTModelResidualTable.program
  unitAllowance ExplicitSeedBudget.m

/-- Every genuine typed record has this actual selected-branch bound. No
matrix action, child result or flag pattern is assumed; children are billed
once at the same smaller q and complete-W bank length. -/
theorem instruction_work (q r k C : ℕ) (I : ℂ) (i : Instruction)
    (raw : Tape ℕ) (source : RawSource (Instruction.record q i) raw)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1≤q) (hr : r < m) (fits : UniformBatching.roleBits≤q*(m-1)+r)
    (len : bank.len=UniformBatching.width*2^(q*m+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤
      recordUnit m UniformBatching.width*recordWeight (Instruction.record q i)*2^(q*m+r)+
        UniformRecursiveRuntimeInventory.recursiveDirections (Instruction.record q i)*
          2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  cases i with
  | initial=>exact marker_record_work q r k C I _ raw source bank h (Or.inr (by change 6≤6;omega))
  | boundary a=>exact marker_record_work q r k C I _ raw source bank h (Or.inl rfl)
  | «macro» a v=>
    cases v with
    | edge old new role edge=>
      have eq : seedWidth=m := dimension_eq
      have cap:=edge_dispatch_work q r k C (fixedBlock a).embedding role edge raw source I bank h
        qp (by norm_num [seedWidth,ExplicitSeedBudget.h]) (by rwa [eq])
        (by rwa [eq]) (by rwa [eq]) children
      simpa only [recordCharge,Instruction.record,UniformRecursiveRuntimeInventory.macro_directions,
        UniformFixedCoefficientCodec.decodeMacro,Macro.residuals,eq] using cap
    | shear d src ne c hc=>exact scalar_record_work q r k C I _ raw source bank h rfl len
  | translation=>
    exact translation_record_work q r k C I _ raw source bank h rfl rfl
      (show seedWidth=m from dimension_eq) hr len
  | exchange=>exact exchange_record_work q r k C I _ raw source bank h rfl len
  | padding=>
    exact padding_record_work q r k C I _ raw source bank h
      (UniformPaddingRecordProjections.opcode q) (UniformPaddingRecordProjections.columns q)
      qp hr fits len children

end
end ExactFourierCircuits.DFTModelSavingCost
