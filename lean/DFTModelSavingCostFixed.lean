import DFTModelSavingCostDispatch
import DFTModelSavingCostScalar
import DFTModelSavingCostExchange
import DFTModelSavingCostY
import DFTModelSavingCostPadding
import UniformRecursiveRuntimeInventory
import UniformPaddingRecordProjections

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

/-- Fixed local work only. The recursive child coefficient is kept separately. -/
def recordUnit (m R : ℕ) : ℕ := 1000*(m+1)*(R+1)+unitAllowance+1000

def recordWeight (r : Record) : ℕ :=
  UniformRecursiveRuntimeInventory.recursiveDirections r+r.dimension+r.source+r.data.length+1

lemma raw_headers (r : Record) (raw : Tape ℕ) (source : RawSource r raw) :
    raw.look 0 0=r.opcode ∧ raw.look 1 0=r.columns ∧ raw.look 2 0=r.width ∧
    raw.look 3 0=r.dest ∧ raw.look 4 0=r.source ∧ raw.look 5 0=r.inverse ∧
    raw.look 6 0=r.dimension ∧ raw.look 7 0=r.scalar :=
  ⟨source.header ⟨0,by decide⟩,source.header ⟨1,by decide⟩,
    source.header ⟨2,by decide⟩,source.header ⟨3,by decide⟩,
    source.header ⟨4,by decide⟩,source.header ⟨5,by decide⟩,
    source.header ⟨6,by decide⟩,source.header ⟨7,by decide⟩⟩

lemma directionAllowance_bound (q m r R C : ℕ) (hr : r < m) :
    directionAllowance q m r (R*2^(q*m+r)) C≤
      recordUnit m R*2^(q*m+r)+2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have coeff : 322*m+240*r+1284+104*R+41*m+63≤ recordUnit m R := by
    unfold recordUnit
    nlinarith
  have scaled:=Nat.mul_le_mul_right (2^(q*m+r)) coeff
  unfold directionAllowance
  nlinarith

lemma edge_dispatch_work {R S m : ℕ} (q r k C : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label m} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (I : ℂ) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1≤q) (wide : 3 ≤ m) (hr : r < m)
    (fits : UniformBatching.roleBits≤q*(m-1)+r)
    (len : bank.len=UniformBatching.width*2^(q*m+r))
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤
      recordUnit m UniformBatching.width*recordWeight (macroRecord q emb (.edge old new role edge))*
        2^(q*m+r)+edge.dimension*2^(q*(m-1)+r-UniformBatching.roleBits)*C := by
  cases m with
  | zero=>omega
  | succ w=>
    have cost:=direction_work q r emb role edge raw source k C I bank h qp (by omega) fits children
    have op:= (raw_headers _ raw source).1
    change raw.look 0 0=0 at op
    rw [dispatch_work,op,ite_eq_left rfl]
    rw [len] at cost
    have cap:=directionAllowance_bound q (w+1) r UniformBatching.width C hr
    have expanded:=Nat.mul_le_mul_right edge.dimension cap
    have vp : 1≤2^(q*(w+1)+r) := Nat.two_pow_pos _
    have unit : 23≤ recordUnit (w+1) UniformBatching.width := by unfold recordUnit;omega
    have reserve:=Nat.mul_le_mul_right (2^(q*(w+1)+r)) unit
    have weight : recordWeight (macroRecord q emb (.edge old new role edge))≥ edge.dimension+1 := by
      simp only [recordWeight,UniformRecursiveRuntimeInventory.recursiveDirections,macroRecord]
      norm_num only [ite_true,Nat.zero_add,Nat.zero_mul]
      omega
    have weightCap:=Nat.mul_le_mul_right (2^(q*(w+1)+r))
      (Nat.mul_le_mul_left (recordUnit (w+1) UniformBatching.width) weight)
    simp only [Nat.add_sub_cancel] at *
    nlinarith

lemma scalar_dispatch_work (R rest k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port) (op : raw.look 0 0=1) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,((k,I),bank)))).work≤127+179*bank.len := by
  rw [dispatch_work,op]
  norm_num only [Nat.one_ne_zero,Nat.sub_self,ite_false,ite_true]
  have cap:=scalar_work R k I raw bank
  omega

lemma exchange_dispatch_work (R rest k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port) (op : raw.look 0 0=4) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,((k,I),bank)))).work≤
      90+(74+131*bank.len)*(raw.look 6 0) := by
  rw [dispatch_work,op]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  have cap:=exchange_work R raw ((k,I),bank)
  dsimp only at cap
  omega

lemma yAllowance_bound (q m r R : ℕ) (raw : Tape ℕ)
    (columns : raw.look 1 0=q) (width : raw.look 2 0=m) (wide : 3 ≤ m) (hr : r < m) :
    yAllowance r raw (R*2^(q*m+r))≤ recordUnit m R*2^(q*m+r) := by
  have xor:=xor_work_volume q (m-1) r (by omega)
  have pred : m-1+1=m := Nat.sub_add_cancel (by omega)
  rw [pred] at xor
  have qv : q≤2^(q*m+r) :=
    (show q≤q*m+r by nlinarith).trans Nat.lt_two_pow_self.le
  have mv : q*m≤2^(q*m+r) := (Nat.le_add_right _ _).trans Nat.lt_two_pow_self.le
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  unfold yAllowance
  rw [columns,width,DFTModelResidualTable.program_work]
  have coeff : 122+16+73+(120*(m+r)+154)*R+204≤ recordUnit m R := by
    unfold recordUnit
    nlinarith
  have scaled:=Nat.mul_le_mul_right (2^(q*m+r)) coeff
  nlinarith

lemma translation_dispatch_work (q m r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (op : raw.look 0 0=3) (columns : raw.look 1 0=q) (width : raw.look 2 0=m)
    (wide : 3 ≤ m) (hr : r < m) (len : bank.len=UniformBatching.width*2^(q*m+r)) :
    (Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
      (r,(raw,((k,I),bank)))).work≤
      recordUnit m UniformBatching.width*(raw.look 6 0+1)*2^(q*m+r) := by
  rw [dispatch_work,op]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  have cap:=y_work UniformBatching.width r k I raw bank
  change (run (DFTModelSavingY.program UniformBatching.width) (r,(raw,((k,I),bank)))).work≤_ at cap
  have row:=yAllowance_bound q m r UniformBatching.width raw columns width wide hr
  rw [len] at cap
  have rows:=Nat.mul_le_mul_right (raw.look 6 0) row
  have vp : 1≤2^(q*m+r) := Nat.two_pow_pos _
  have unit : 61≤ recordUnit m UniformBatching.width := by unfold recordUnit;omega
  have control:=Nat.mul_le_mul_right (2^(q*m+r)) unit
  nlinarith

end
end ExactFourierCircuits.DFTModelSavingCost
