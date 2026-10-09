import DFTModelCRTProgram
import UniformCRTMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTMetadata
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev SearchInput := p w w
abbrev SearchCell := p SearchInput (p w w)

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

def coefficient : Prog false SearchCell w := .comp (.atom .fst) (.atom .fst)
def modulus : Prog false SearchCell w := .comp (.atom .fst) (.atom .snd)
def candidate : Prog false SearchCell w := .comp (.atom .snd) (.atom .fst)
def previous : Prog false SearchCell w := .comp (.atom .snd) (.atom .snd)
def residue : Prog false SearchCell w := nat .mod (nat .mul coefficient candidate) modulus
def equalityTest : Prog false SearchCell w :=
  nat .add (nat .sub residue (.atom (.lit 1)))
    (nat .sub (.atom (.lit 1)) residue)
def searchCell : Prog false SearchCell w := .ifz equalityTest candidate previous

/-- Exhaustive modular inverse search, with no inverse primitive or supplied answer. -/
def inverse : Prog false SearchInput w :=
  .loop (.atom .snd) (.atom (.lit 0)) searchCell

def choose (a q j old : ℕ) : ℕ := if a*j%q=1 then j else old

theorem searchCell_value (a q j old : ℕ) :
    (Code.run searchCell () ((a,q),(j,old))).val=choose a q j old := by
  have eq : (a*j%q-1)+(1-a*j%q)=0 ↔ a*j%q=1 := by omega
  simp only [searchCell,equalityTest,nat,residue,coefficient,candidate,modulus,previous,
    Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  simp only [eq,choose]
  split_ifs <;> rfl

theorem searchCell_work (a q j old : ℕ) :
    (Code.run searchCell () ((a,q),(j,old))).work=45 := by
  by_cases h : (a*j%q-1)+(1-a*j%q)=0 <;>
    simp only [searchCell,equalityTest,nat,residue,coefficient,candidate,modulus,previous,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h,ite_true,ite_false]

theorem searchCell_peak (a q j old : ℕ) :
    (Code.run searchCell () ((a,q),(j,old))).peak≤a*j+1 := by
  have bound := Nat.mod_le (a*j) q
  by_cases h : (a*j%q-1)+(1-a*j%q)=0 <;>
    simp only [searchCell,equalityTest,nat,residue,coefficient,candidate,modulus,previous,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h,ite_true,ite_false,
      max_le_iff] <;> omega

theorem searchCell_valid (a q j old : ℕ) :
    (Code.run searchCell () ((a,q),(j,old))).valid := by
  by_cases h : (a*j%q-1)+(1-a*j%q)=0 <;>
    simp only [searchCell,equalityTest,nat,residue,coefficient,candidate,modulus,previous,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h,ite_true,ite_false] <;> trivial

def searchSteps (a q C : ℕ) : Bill ℕ :=
  Bill.steps 0 (fun j old => Code.run searchCell () ((a,q),(j,old))) C

theorem searchSteps_work (a q C : ℕ) : (searchSteps a q C).work=46*C+1 := by
  induction C with
  | zero => rfl
  | succ C ih =>
      change (searchSteps a q C).work+(Code.run searchCell () ((a,q),(C,_))).work+1=_
      rw [searchCell_work,ih]
      omega

theorem searchSteps_valid (a q C : ℕ) : (searchSteps a q C).valid := by
  induction C with
  | zero => trivial
  | succ C ih => exact ⟨ih,searchCell_valid _ _ _ _⟩

theorem searchSteps_peak (a q C : ℕ) : (searchSteps a q C).peak≤ max C (a*C+1) := by
  induction C with
  | zero => exact Nat.zero_le _
  | succ C ih =>
      change max (max (searchSteps a q C).peak
        (Code.run searchCell () ((a,q),(C,_))).peak) (C+1)≤_
      apply max_le
      · apply max_le
        · apply ih.trans
          apply max_le_max (by omega)
          exact Nat.add_le_add_right (Nat.mul_le_mul_left a (by omega)) 1
        · exact (searchCell_peak _ _ _ _).trans
            ((Nat.add_le_add_right (Nat.mul_le_mul_left a (by omega)) 1).trans (le_max_right _ _))
      · exact le_max_left _ _

theorem searchSteps_inverse (a q : ℕ) (hq : 1<q) (coprime : Nat.Coprime a q)
    (C : ℕ) (cap : C≤q) :
    (searchSteps a q C).val=
      if ((a : ZMod q)⁻¹).val<C then ((a : ZMod q)⁻¹).val else 0 := by
  induction C with
  | zero => rfl
  | succ C ih =>
      change (Code.run searchCell () ((a,q),(C,(searchSteps a q C).val))).val=_
      rw [searchCell_value,ih (by omega)]
      have unique : a*C%q=1 ↔ C=((a : ZMod q)⁻¹).val := by
        constructor
        · exact UniformCRTMachine.inverse_unique a q C hq coprime (by omega)
        · intro eq
          rw [eq]
          exact UniformCRTMachine.inverse_value_spec a q hq coprime
      simp only [choose,unique]
      by_cases he : C=((a : ZMod q)⁻¹).val
      · simp [he]
      · simp only [he,ite_false]
        by_cases hl : ((a : ZMod q)⁻¹).val<C
        · simp [hl,show ((a : ZMod q)⁻¹).val<C+1 from by omega]
        · simp [hl,show ¬((a : ZMod q)⁻¹).val<C+1 from by omega]

theorem inverse_value (a q : ℕ) (hq : 1<q) (coprime : Nat.Coprime a q) :
    (Code.run inverse () (a,q)).val=((a : ZMod q)⁻¹).val := by
  change (searchSteps a q q).val=_
  rw [searchSteps_inverse _ _ hq coprime _ (le_refl _)]
  let : NeZero q := ⟨by omega⟩
  simp only [ZMod.val_lt,ite_true]

theorem inverse_work (a q : ℕ) : (Code.run inverse () (a,q)).work=46*q+4 := by
  change 1+(1+(searchSteps a q q).work)+1=_
  rw [searchSteps_work]
  omega

theorem inverse_peak (a q : ℕ) : (Code.run inverse () (a,q)).peak≤ max q (a*q+1) := by
  change max (max 0 (max 0 (searchSteps a q q).peak)) 0≤_
  simpa only [max_zero,zero_max] using searchSteps_peak a q q

theorem inverse_valid (a q : ℕ) : (Code.run inverse () (a,q)).valid := by
  change True ∧ (True ∧ (searchSteps a q q).valid)
  exact ⟨trivial,trivial,searchSteps_valid _ _ _⟩

theorem searchSteps_le (a q C : ℕ) : (searchSteps a q C).val≤C := by
  induction C with
  | zero => exact le_rfl
  | succ C ih =>
      change (Code.run searchCell () ((a,q),(C,(searchSteps a q C).val))).val≤C+1
      rw [searchCell_value]
      by_cases h : a*C%q=1
      · simp only [choose,h,ite_true]
        exact Nat.le_succ C
      · simp only [choose,h,ite_false]
        exact ih.trans (Nat.le_succ C)

theorem inverse_le (a q : ℕ) : (Code.run inverse () (a,q)).val≤q := searchSteps_le a q q

end
end ExactFourierCircuits.DFTModelCRTMetadata
