import DFTModelSavingPeakArithmetic

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.padding
  paddingLocal paddingCoeff directionLocal directionCoeff UniformBatching.width
  DFTModelCacheRecords.unitPeak ExplicitSeedBudget.m

/-- Keep the fixed role cardinality outside the proof's reduction boundary. -/
theorem padding_dispatch_bound (q r k C dest count : ℕ) (I : ℂ)
    (raw : Tape ℕ) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (op : raw.look 0 0=5) (columns : raw.look 1 0=q)
    (destination : raw.look 3 0=dest) (copies : raw.look 4 0=count)
    (qp : 1 ≤ q) (rp : r < m) (len : bank.len=UniformBatching.width*2^(q*m+r))
    (before : Boolean bank) (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤
        max C ((paddingCoeff m dest count+5)*(2^(q*m+r)*2^(q*m+r))) := by
  have mp : 1 ≤ m := by norm_num [m,ExplicitSeedBudget.m]
  have pred : m-1+1=m := Nat.sub_add_cancel mp
  have cap:=padding_peak q (m-1) r k C I raw bank h columns pred qp (by rwa [pred])
    before preserve children
  have boundEq : paddingLocal q (m-1+1) r (raw.look 3 0) (raw.look 4 0) bank.len=
      paddingLocal q m r dest count (UniformBatching.width*2^(q*m+r)) := by
    rw [pred,destination,copies,len]
  have localCap:=paddingLocal_bound q m r dest count (Nat.lt_of_lt_of_le (by decide : 0<1) mp)
  have full:=(cap.trans_eq (congrArg (max C) boundEq)).trans (max_le_max le_rfl localCap)
  apply (padding_dispatch_peak UniformBatching.width r raw ((k,I),bank) h op).le.trans
  refine max_le (full.trans (max_le_max le_rfl (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))) ?_
  exact (padding_const_bound (paddingCoeff m dest count) _ (volume_bounds q m r (by omega)).1).trans
    (le_max_right _ _)

end
end ExactFourierCircuits.DFTModelSavingPeak
