import DFTModelSavingPeakDirection
import DFTModelSavingCostPaddingSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingPadding
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelCacheRecords.unit DFTModelCacheRecords.unitPeak ExplicitSeedBudget.m

def paddingLocal (q m r dest count L : ℕ) : ℕ :=
  directionLocal q m r (dest+count) L m+DFTModelCacheRecords.unitPeak+count+10

lemma padding_role_peak (q w r i k C : ℕ) (I : ℂ) (raw : Tape ℕ)
    (initial : Node.T) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (columns : raw.look 1 0=q) (widthEq : w+1=ExplicitSeedBudget.m)
    (qp : 1 ≤ q) (rp : r < w+1) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) (hi : i ≤ raw.look 4 0) :
    (roleBill h r i raw initial ((k,I),bank)).peak ≤ max C (paddingLocal q (w+1) r (raw.look 3 0) (raw.look 4 0) bank.len) := by
  let a:=raw.look 3 0+i
  let unitTape:=(run DFTModelCacheRecords.unit (q,a)).val
  have source : DFTModelSavingDirection.RawSource
      (macroRecord q (DFTModelSavingCost.singletonEmbedding a)
        (.edge _ _ (0:Fin 1) (UniformRecursivePaddingUnitEdge.unitEdge (w+1)))) unitTape := by
    rw [widthEq]
    exact DFTModelSavingCost.unit_source q a
  have peak:=direction_peak q r (DFTModelSavingCost.singletonEmbedding a) (0:Fin 1)
    (UniformRecursivePaddingUnitEdge.unitEdge (w+1)) unitTape source k C I bank h qp rp before preserve children
  change _ ≤ max C (directionLocal q (w+1) r a bank.len (w+1)) at peak
  have unitPeak:=DFTModelCacheRecords.unit_peak q a
  change max (Code.run DFTModelSavingRecords.residual h
    (r,((run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val,((k,I),bank)))).peak
    (run (argumentsWith DFTModelCacheRecords.unit) ((r,(raw,initial)),(i,((k,I),bank)))).peak ≤ _
  rw [columns,argumentsWith_run,columns]
  dsimp only [Bill.peak]
  change max (Code.run DFTModelSavingRecords.residual h (r,(unitTape,((k,I),bank)))).peak
    (max (max 3 a) (run DFTModelCacheRecords.unit (q,a)).peak) ≤ _
  refine max_le (peak.trans (max_le_max le_rfl ?_)) ?_
  · dsimp [paddingLocal,directionLocal,a]
    have mult:=Nat.mul_le_mul_right (2^(q*(w+1)+r)) (show raw.look 3 0+i+3 ≤ raw.look 3 0+raw.look 4 0+3 by omega)
    omega
  · apply max_le (max_le ?_ ?_) (unitPeak.trans ?_)
    · apply le_trans _ (le_max_right _ _)
      unfold paddingLocal
      omega
    · apply le_trans _ (le_max_right _ _)
      dsimp [paddingLocal,directionLocal,a]
      have power : 1 ≤ 2^(q*(w+1)+r):=Nat.two_pow_pos _
      have mult:=Nat.le_mul_of_pos_right (raw.look 3 0+raw.look 4 0+3) power
      omega
    · apply le_trans _ (le_max_right _ _)
      unfold paddingLocal
      omega

/-- Padding freshly prints every unit record and keeps the same Boolean
invariant through its actual residual calls. -/
theorem padding_peak (q w r k C : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (columns : raw.look 1 0=q) (widthEq : w+1=ExplicitSeedBudget.m)
    (qp : 1 ≤ q) (rp : r < w+1) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run DFTModelSavingRecords.padding h (r,(raw,((k,I),bank)))).peak ≤ max C (paddingLocal q (w+1) r (raw.look 3 0) (raw.look 4 0) bank.len) := by
  let B:=max C (paddingLocal q (w+1) r (raw.look 3 0) (raw.look 4 0) bank.len)
  have flags : ∀n,Boolean (steps h r raw ((k,I),bank) n).val.2 := by
    intro n
    apply DFTModelSavingShapeBoolean.steps_boolean _ _ before
    intro i z hz
    rw [←body_run]
    rw [DFTModelSavingRecords.paddingBody,DFTModelClockBatch.code_comp_value]
    exact DFTModelSavingShapeBoolean.residual_loop_boolean h _ hz preserve
  have peaks : ∀n,n ≤ raw.look 4 0→(steps h r raw ((k,I),bank) n).peak ≤ B := by
    intro n
    induction n with
    | zero=>intro _;exact Nat.zero_le _
    | succ n ih=>
      intro cap
      have shape:=steps_preserved h r n k I raw bank
      have same : (steps h r raw ((k,I),bank) n).val=
        ((k,I),(steps h r raw ((k,I),bank) n).val.2):=Prod.ext shape.1 rfl
      have peak:=padding_role_peak q w r n k C I raw ((k,I),bank)
        (steps h r raw ((k,I),bank) n).val.2 h columns widthEq qp rp (flags n) preserve children (by omega)
      rw [shape.2] at peak
      change max (max (steps h r raw ((k,I),bank) n).peak
        (roleBill h r n raw ((k,I),bank) (steps h r raw ((k,I),bank) n).val).peak) (n+1) ≤ B
      rw [same]
      refine max_le (max_le (ih (by omega)) peak) ?_
      apply le_trans cap
      apply le_trans _ (le_max_right _ _)
      unfold paddingLocal
      omega
  rw [padding_run]
  change max (steps h r raw ((k,I),bank) (raw.look 4 0)).peak 4 ≤ B
  refine max_le (peaks _ le_rfl) ?_
  dsimp [B,paddingLocal]
  omega
end
end ExactFourierCircuits.DFTModelSavingPeak
