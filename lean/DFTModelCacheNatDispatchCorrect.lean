import DFTModelCacheNatDispatchProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

attribute [local irreducible] instruction

theorem selectFrom_value (code : List Instruction) (base : ℕ) (v : LocalValue)
    (lower : base≤v.1) :
    (run (selectFrom base code) v).val=
      match code[v.1-base]? with | none=>v | some i=>result i v := by
  induction code generalizing base with
  | nil => rw [selectFrom_nil]; rfl
  | cons i is ih =>
    rw [selectFrom_cons]
    by_cases h:v.1=base
    · subst base
      simp only [Nat.sub_self,ite_true,Bill.pay,List.getElem?_cons_zero]
      exact instruction_value i v
    · have positive:0<v.1-base := by omega
      have eqn:v.1-base=(v.1-(base+1))+1 := by omega
      simp only [ne_of_gt positive,ite_false,Bill.pay]
      rw [ih (base+1) (by omega),eqn,List.getElem?_cons_succ]

theorem selectFrom_valid (code : List Instruction) (base : ℕ) (v : LocalValue)
    (lower : base≤v.1) :
    (run (selectFrom base code) v).valid ↔
      ∃ i,code[v.1-base]?=some i ∧ Domain i v := by
  induction code generalizing base with
  | nil => rw [selectFrom_nil]; simp
  | cons i is ih =>
    rw [selectFrom_cons]
    by_cases h:v.1=base
    · subst base
      simp only [Nat.sub_self,ite_true,Bill.pay,List.getElem?_cons_zero,Option.some.injEq]
      constructor
      · intro hv; exact ⟨i,rfl,(instruction_valid i v).mp hv⟩
      · rintro ⟨j,hj,hv⟩; subst j; exact (instruction_valid i v).mpr hv
    · have positive:0<v.1-base := by omega
      have eqn:v.1-base=(v.1-(base+1))+1 := by omega
      simp only [ne_of_gt positive,ite_false,Bill.pay]
      rw [ih (base+1) (by omega),eqn,List.getElem?_cons_succ]

theorem program_value (code : List Instruction) (v : LocalValue) :
    (run (program code) v).val=next code v := by
  change (run (selectFrom 0 code) v).val=_
  rw [selectFrom_value code 0 v (Nat.zero_le _)]
  simp only [Nat.sub_zero,next]
  cases code[v.1]? <;> rfl

theorem program_valid (code : List Instruction) (v : LocalValue) :
    (run (program code) v).valid ↔ Accepted code v := by
  simpa only [program,Accepted,Nat.sub_zero] using selectFrom_valid code 0 v (Nat.zero_le _)

theorem program_selected (code : List Instruction) (v : LocalValue) (i : Instruction)
    (h : code[v.1]?=some i) :
    (run (program code) v).val=result i v ∧
      ((run (program code) v).valid↔Domain i v) := by
  constructor
  · rw [program_value]; simp only [next,h]
  · rw [program_valid]
    simp only [Accepted,h,Option.some.injEq]
    constructor
    · rintro ⟨j,hj,hv⟩; subst j; exact hv
    · intro hv; exact ⟨i,rfl,hv⟩

theorem program_rejects (code : List Instruction) (v : LocalValue)
    (h : code.length≤v.1) :
    (run (program code) v).val=v ∧ ¬(run (program code) v).valid := by
  have missing:code[v.1]?=none := List.getElem?_eq_none h
  rw [program_value,program_valid]
  simp [next,Accepted,missing]

theorem program_halt (code : List Instruction) (v : LocalValue)
    (h : code[v.1]?=some .halt) :
    (run (program code) v).val=v ∧ (run (program code) v).valid := by
  obtain ⟨value,valid⟩:=program_selected code v .halt h
  exact ⟨value,valid.mpr trivial⟩

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
