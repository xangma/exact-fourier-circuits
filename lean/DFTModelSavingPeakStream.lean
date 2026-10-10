import DFTModelSavingPeakInstruction
import DFTModelSavingCostRecords
import DFTModelSavingNativeControl

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
open UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.stream
  UniformBatching.width

def listCap : List ℕ→ℕ | []=>0 | a::as=>max a (listCap as)
lemma mem_le_listCap {a : ℕ} {as : List ℕ} (h:a∈as) : a ≤ listCap as := by
  induction as with
  | nil=>simp at h
  | cons b bs ih=>
    rcases List.mem_cons.mp h with rfl|h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

def streamCoeff : ℕ := listCap (instructions.map instructionCoeff)+instructions.length+1
attribute [local irreducible] streamCoeff instructions

lemma instructionCoeff_le (i : Instruction) (hi : i∈instructions) : instructionCoeff i ≤ streamCoeff := by
  have cap : instructionCoeff i ≤ listCap (instructions.map instructionCoeff):=mem_le_listCap (List.mem_map.mpr ⟨i,hi,rfl⟩)
  unfold streamCoeff
  exact cap.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1))

/-- The real finite printed seed is traversed chronologically. The peak of
all records is a maximum; the original loop count is also charged. -/
theorem stream_peak (q r k C : ℕ) (I : ℂ) (bank : Tape Tagged.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1 ≤ q) (rp : r < m) (shape : k=q*m+r)
    (len : bank.len=UniformBatching.width*2^k) (before : Boolean bank)
    (preserve : ∀z : Node.T,Boolean z.2→Boolean (h z).val)
    (children : ∀J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→Boolean v→
      (h ((q,J),v)).peak ≤ C) :
    (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
      (r,(DFTModelCacheRecords.recordTape (scheduleRecords q),((k,I),bank)))).peak ≤ max C (streamCoeff*(2^k*2^k)) := by
  let rs:=DFTModelCacheRecords.recordTape (scheduleRecords q)
  let f:=fun i z=>Code.run (DFTModelSavingRecords.dispatch UniformBatching.width) h
    (r,(rs.look i (Tape.empty ℕ),z))
  let steps:=fun i=>Bill.steps ((k,I),bank) f i
  let B:=max C (streamCoeff*(2^k*2^k))
  have flags : ∀n,Boolean (steps n).val.2 := by
    intro n
    apply DFTModelSavingShapeBoolean.steps_boolean _ _ before
    intro i z hz
    exact DFTModelSavingShapeBoolean.dispatch_boolean UniformBatching.width h _ hz preserve
  have lengths : ∀n,(steps n).val.1=(k,I) ∧ (steps n).val.2.len=bank.len := by
    intro n
    apply DFTModelSavingShape.steps_preserves
    intro i z
    exact DFTModelSavingShape.dispatch_preserves UniformBatching.width h _
  have rsLen : rs.len=instructions.length:=by
    change (scheduleRecords q).length=instructions.length
    rw [←records_actual,List.length_map]
  have peaks : ∀n,n ≤ rs.len→(steps n).peak ≤ B := by
    intro n
    induction n with
    | zero=>intro _;exact Nat.zero_le _
    | succ n ih=>
      intro cap
      have nn : n < instructions.length := (Nat.lt_of_succ_le cap).trans_eq rsLen
      let i:=instructions[n]'nn
      have mem : i∈instructions:=List.getElem_mem nn
      have live : n < (scheduleRecords q).length := by
        rw [←records_actual,List.length_map]
        exact nn
      have entry := congrArg (fun records : List Record => records[n]?) (records_actual q)
      rw [List.getElem?_map,List.getElem?_eq_getElem nn,Option.map_some,
        List.getElem?_eq_getElem live] at entry
      have rawEq : rs.look n (Tape.empty ℕ)=DFTModelCacheRecords.dataTape (Instruction.record q i).data := by
        rw [DFTModelSavingNativeControl.recordTape_lookup _ n live]
        exact congrArg (fun record : Record => DFTModelCacheRecords.dataTape record.data) (Option.some.inj entry).symm
      have same : (steps n).val=((k,I),(steps n).val.2):=Prod.ext (lengths n).1 rfl
      have nodeLen : (steps n).val.2.len=UniformBatching.width*2^k:=(lengths n).2.trans len
      have pk:=instruction_peak q r k C I i (DFTModelCacheRecords.dataTape (Instruction.record q i).data) (DFTModelSavingDirection.dataTape_source _) (steps n).val.2 h qp rp shape nodeLen (flags n) preserve children
      rw [←shape] at pk
      have scaled:=Nat.mul_le_mul_right (2^k*2^k) (instructionCoeff_le i mem)
      change max (max (steps n).peak (f n (steps n).val).peak) (n+1) ≤ B
      dsimp only [f]
      rw [rawEq,same]
      refine max_le (max_le (ih (by omega)) (pk.trans (max_le_max le_rfl scaled))) ?_
      have one : 1 ≤ (2:ℕ)^k*2^k := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      have count : instructions.length ≤ streamCoeff := by
        unfold streamCoeff
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ 1)
      exact cap.trans (rsLen.le.trans ((count.trans (Nat.le_mul_of_pos_right _ one)).trans (le_max_right _ _)))
  rw [DFTModelSavingCost.stream_run]
  change max (steps rs.len).peak rs.len ≤ B
  refine max_le (peaks _ le_rfl) ?_
  have one : 1 ≤ (2:ℕ)^k*2^k := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have count : instructions.length ≤ streamCoeff := by
    unfold streamCoeff
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ 1)
  exact (rsLen.le.trans (count.trans (Nat.le_mul_of_pos_right _ one))).trans (le_max_right _ _)
end
end ExactFourierCircuits.DFTModelSavingPeak
