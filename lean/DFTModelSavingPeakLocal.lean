import DFTModelSavingPeakPadding
import DFTModelSavingPeakLeaves
import DFTModelSavingCostFixed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unitPeak UniformBatching.width
  DFTModelSavingRecords.dispatch

def directionCoeff (m a dim : ℕ) : ℕ :=
  40+(a+3)+2*UniformBatching.width+m+28+m*(dim+1)+dim

def paddingCoeff (m dest count : ℕ) : ℕ :=
  directionCoeff m (dest+count) m+DFTModelCacheRecords.unitPeak+count+10

lemma volume_bounds (q m r : ℕ) (mp : 0 < m) :
    1 ≤ 2^(q*m+r)*2^(q*m+r) ∧ 2^(q*m+r) ≤ 2^(q*m+r)*2^(q*m+r) ∧
      2^q ≤ 2^(q*m+r)*2^(q*m+r) := by
  have positive : 1 ≤ 2^(q*m+r):=Nat.two_pow_pos _
  have square : 2^(q*m+r) ≤ 2^(q*m+r)*2^(q*m+r):=Nat.le_mul_of_pos_right _ positive
  refine ⟨positive.trans square,square,?_⟩
  apply le_trans _ square
  apply Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ))
  exact (Nat.le_mul_of_pos_right q mp).trans (Nat.le_add_right _ _)

lemma directionLocal_bound (q m r a dim : ℕ) (mp : 0 < m) :
    directionLocal q m r a (UniformBatching.width*2^(q*m+r)) dim ≤ directionCoeff m a dim*(2^(q*m+r)*2^(q*m+r)) := by
  obtain ⟨one,volume,small⟩:=volume_bounds q m r mp
  calc
    _=40*(2^(q*m+r)*2^(q*m+r))+(a+3)*2^(q*m+r)+
      UniformBatching.width*2^(q*m+r)+m+UniformBatching.width*2^q+28+m*(dim+1)+dim := by
      unfold directionLocal
      ring
    _ ≤ 40*(2^(q*m+r)*2^(q*m+r))+(a+3)*(2^(q*m+r)*2^(q*m+r))+
      UniformBatching.width*(2^(q*m+r)*2^(q*m+r))+m*(2^(q*m+r)*2^(q*m+r))+
      UniformBatching.width*(2^(q*m+r)*2^(q*m+r))+28*(2^(q*m+r)*2^(q*m+r))+
      (m*(dim+1))*(2^(q*m+r)*2^(q*m+r))+dim*(2^(q*m+r)*2^(q*m+r)) := by
      have av:=Nat.mul_le_mul_left (a+3) volume
      have wv:=Nat.mul_le_mul_left UniformBatching.width volume
      have mv:=Nat.mul_le_mul_left m one
      have ws:=Nat.mul_le_mul_left UniformBatching.width small
      have c28:=Nat.mul_le_mul_left 28 one
      have md:=Nat.mul_le_mul_left (m*(dim+1)) one
      have dd:=Nat.mul_le_mul_left dim one
      simp only [Nat.mul_one] at mv c28 md dd
      omega
    _= _ := by unfold directionCoeff;ring

lemma paddingLocal_bound (q m r dest count : ℕ) (mp : 0 < m) :
    paddingLocal q m r dest count (UniformBatching.width*2^(q*m+r)) ≤ paddingCoeff m dest count*(2^(q*m+r)*2^(q*m+r)) := by
  have dir:=directionLocal_bound q m r (dest+count) m mp
  have one:=(volume_bounds q m r mp).1
  unfold paddingLocal paddingCoeff
  calc
    _ ≤ directionCoeff m (dest+count) m*(2^(q*m+r)*2^(q*m+r))+
      DFTModelCacheRecords.unitPeak*(2^(q*m+r)*2^(q*m+r))+
      count*(2^(q*m+r)*2^(q*m+r))+10*(2^(q*m+r)*2^(q*m+r)) := by
      have up:=Nat.mul_le_mul_left DFTModelCacheRecords.unitPeak one
      have cc:=Nat.mul_le_mul_left count one
      have ten:=Nat.mul_le_mul_left 10 one
      simp only [Nat.mul_one] at up cc ten
      omega
    _=_ := by ring

/-- Raw edge record bound from its genuine direction source. -/
theorem edge_peak {R S w : ℕ} (q r k C : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (I : ℂ) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1 ≤ q) (rp : r < w+1) (len : bank.len=UniformBatching.width*2^(q*(w+1)+r))
    (before : Boolean bank) (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (directionCoeff (w+1) (emb role).val edge.dimension*
        (2^(q*(w+1)+r)*2^(q*(w+1)+r))) := by
  have peak:=direction_peak q r emb role edge raw source k C I bank h qp rp before preserve children
  have op : raw.look 0 0=0 := (DFTModelSavingCost.raw_headers _ raw source).1
  rw [dispatch_peak,op,ite_eq_left rfl]
  rw [len] at peak
  exact peak.trans (max_le_max le_rfl (directionLocal_bound q (w+1) r (emb role).val edge.dimension (by omega)))

lemma edge_peak_pos {R S dim : ℕ} (q r k C : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label dim} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (I : ℂ) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (positive : 0 < dim) (qp : 1 ≤ q) (rp : r < dim)
    (len : bank.len=UniformBatching.width*2^(q*dim+r))
    (before : Boolean bank) (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).peak ≤ max C (directionCoeff dim (emb role).val edge.dimension*(2^(q*dim+r)*2^(q*dim+r))) := by
  cases dim with
  | zero=>omega
  | succ w=>exact edge_peak q r k C emb role edge raw source I bank h qp rp len before preserve children

end
end ExactFourierCircuits.DFTModelSavingPeak
