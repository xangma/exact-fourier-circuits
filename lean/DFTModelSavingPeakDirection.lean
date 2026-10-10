import DFTModelSavingPeakResidual
import DFTModelSavingDirectionSource
import DFTModelSavingShapeBoolean

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program DFTModelSavingRecords.residual

def directionLocal (q m r a L dim : ℕ) : ℕ :=
  40*(2^(q*m+r)*2^(q*m+r))+(a+3)*2^(q*m+r)+L+m+
    UniformBatching.width*2^q+10+8+m*(dim+1)+dim+10

lemma direction_row_peak {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (i : Fin edge.dimension) (k C : ℕ) (I : ℂ) (bank : Tape Tagged.T) (initial : Node.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1 ≤ q) (rp : r < w+1)
    (before : Boolean bank)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (rowBill h r i.val raw initial ((k,I),bank)).peak ≤ max C (directionLocal q (w+1) r (emb role).val bank.len edge.dimension) := by
  have headers:=macro_headers q emb role edge raw source
  have bits:=row_source q emb role edge raw source i
  have nz : edgeVectors edge i≠0 := by
    intro eq
    have norm:=UniformResidualFibers.edgeVector_norm edge i
    rw [eq] at norm
    simp [BinaryFrames.dot] at norm
  have small : raw.look 5 0<2 := by
    rw [headers.2.2.2.1]
    split <;> decide
  have peak:=residual_source_peak h q w r (edgeVectors edge i) (row (w+1) i.val raw)
    (emb role).val (raw.look 5 0) k C I bank qp rp bits nz small before children
  have arg:=arguments_peak r i.val raw initial ((k,I),bank)
  rw [headers.2.1] at arg
  simp only [rowBill,decoded,Bill.pay]
  rw [headers.1,headers.2.1,headers.2.2.1]
  refine max_le (peak.trans (max_le_max le_rfl ?_)) ?_
  · unfold directionLocal
    omega
  · apply arg.trans
    apply le_trans _ (le_max_right _ _)
    unfold directionLocal
    have mult:=Nat.mul_le_mul_left (w+1) (Nat.le_of_lt i.isLt)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

/-- The chronological direction loop retains Boolean flags and bank length;
only actual complete smaller batches use the recursive peak hypothesis. -/
theorem direction_peak {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (k C : ℕ) (I : ℂ) (bank : Tape Tagged.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1 ≤ q) (rp : r < w+1)
    (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run DFTModelSavingRecords.residual h (r,(raw,((k,I),bank)))).peak ≤ max C (directionLocal q (w+1) r (emb role).val bank.len edge.dimension) := by
  let B:=max C (directionLocal q (w+1) r (emb role).val bank.len edge.dimension)
  have flags : ∀n,Boolean (steps h r raw ((k,I),bank) n).val.2 := by
    intro n
    apply DFTModelSavingShapeBoolean.steps_boolean _ _ before
    intro i z hz
    rw [←direction_run]
    exact DFTModelSavingShapeBoolean.direction_boolean h _ hz preserve
  have costs : ∀n,n ≤ edge.dimension→(steps h r raw ((k,I),bank) n).peak ≤ B := by
    intro n
    induction n with
    | zero=>intro _;exact Nat.zero_le _
    | succ n ih=>
      intro cap
      have shape:=steps_preserved h r n k I raw bank
      have same : (steps h r raw ((k,I),bank) n).val=
        ((k,I),(steps h r raw ((k,I),bank) n).val.2) := Prod.ext shape.1 rfl
      have rowPeak:=direction_row_peak q r emb role edge raw source ⟨n,by omega⟩ k C I
        (steps h r raw ((k,I),bank) n).val.2 ((k,I),bank) h qp rp (flags n) children
      rw [shape.2] at rowPeak
      change max (max (steps h r raw ((k,I),bank) n).peak
        (rowBill h r n raw ((k,I),bank) (steps h r raw ((k,I),bank) n).val).peak) (n+1) ≤ B
      rw [same]
      refine max_le (max_le (ih (by omega)) rowPeak) ?_
      apply le_trans cap
      apply le_trans _ (le_max_right _ _)
      unfold directionLocal
      omega
  rw [residual_run,(macro_headers q emb role edge raw source).2.2.2.2]
  exact max_le (costs edge.dimension le_rfl) (by dsimp [B,directionLocal];omega)

end
end ExactFourierCircuits.DFTModelSavingPeak
