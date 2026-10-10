import DFTModelCacheNatDispatchCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

attribute [local irreducible] instruction

theorem selectFrom_work (code : List Instruction) (base : ℕ) (v : LocalValue) :
    (run (selectFrom base code) v).work≤
      35*(v.2.1.len+v.2.2.len)+100+6*code.length := by
  induction code generalizing base with
  | nil => rw [selectFrom_nil]; simp only [List.length_nil,Nat.mul_zero,Nat.add_zero];omega
  | cons i is ih =>
    rw [selectFrom_cons]
    by_cases h:v.1-base=0
    · simp only [h,ite_true,Bill.pay,List.length_cons]
      have bound:=instruction_work i v
      omega
    · simp only [h,ite_false,Bill.pay,List.length_cons]
      have bound:=ih (base+1)
      omega

theorem selectFrom_peak (code : List Instruction) (base : ℕ) (v : LocalValue) (B : ℕ)
    (lower : base≤v.1) (pcBound : v.1≤B)
    (selected : ∀i,code[v.1-base]?=some i→PeakBound i v B) :
    (run (selectFrom base code) v).peak≤B := by
  induction code generalizing base with
  | nil => rw [selectFrom_nil]; exact Nat.zero_le B
  | cons i is ih =>
    rw [selectFrom_cons]
    by_cases h:v.1=base
    · subst base
      simp only [Nat.sub_self,ite_true,Bill.pay]
      have bound:=instruction_peak i v B (selected i (by simp))
      omega
    · have positive:0<v.1-base := by omega
      have eqn:v.1-base=(v.1-(base+1))+1 := by omega
      simp only [ne_of_gt positive,ite_false,Bill.pay]
      have bound:=ih (base+1) (by omega) (by
        intro j hj
        apply selected j
        simpa only [eqn,List.getElem?_cons_succ] using hj)
      omega

theorem program_work (code : List Instruction) (v : LocalValue) :
    (run (program code) v).work≤35*(v.2.1.len+v.2.2.len)+100+6*code.length :=
  selectFrom_work code 0 v

theorem program_peak (code : List Instruction) (v : LocalValue) (B : ℕ)
    (pcBound : v.1≤B) (selected : ∀i,code[v.1]?=some i→PeakBound i v B) :
    (run (program code) v).peak≤B := by
  exact selectFrom_peak code 0 v B (Nat.zero_le _) pcBound (by simpa using selected)

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
