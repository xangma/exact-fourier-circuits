import DFTModelResidualCore
import ModelEquivalenceInterpreter

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapBits
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

def flag (z : ℕ) : ℕ := if 0 < z then 1 else 0
def high (z : ℕ) : ℕ := if z = 0 then 0 else Nat.log2 z + 1

theorem flag_le (z : ℕ) : flag z ≤ 1 := by simp [flag]; split <;> omega
theorem high_zero : high 0 = 0 := by simp [high]
theorem high_div (z : ℕ) : high z = flag z + high (z / 2) := by
  by_cases hz : z = 0
  · simp [hz, high, flag]
  by_cases h2 : 2 ≤ z
  · have hd : z / 2 ≠ 0 := by omega
    have hp : 0 < z := by omega
    simp only [high, hz, hd, ↓reduceIte, flag, hp]
    rw [Nat.log2_def z]
    simp only [h2, ↓reduceIte]
    omega
  · have he : z = 1 := by omega
    simp [he, high, flag, Nat.log2_def]

abbrev HighState := p w w
abbrev HighInput := p w w
abbrev HighBodyInput := p HighInput (p w HighState)

def highQ : Prog false HighBodyInput w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def highCount : Prog false HighBodyInput w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def highBody : Prog false HighBodyInput HighState :=
  .fork (binary .div highQ (.atom (.lit 2)))
    (binary .add highCount (binary .lt (.atom (.lit 0)) highQ))
def highInit : Prog false HighInput HighState := .fork (.atom .snd) (.atom (.lit 0))
def highLoop : Prog false HighInput HighState := .loop (.atom .fst) highInit highBody
def highCell : Prog false HighInput w := .comp highLoop (.atom .snd)
def highTable : Prog false w (Ty.a w) := .tab power highCell

theorem highBody_run (b z i q h : ℕ) :
    run highBody ((b,z),(i,(q,h))) =
      ⟨(q/2,h+flag q),27,max 2 (max (q/2) (h+flag q)),True⟩ := by
  simp [highBody, highQ, highCount, binary, flag, run, Code.run, Atom.run,
    NOp.run, Bill.pass, Bill.pay, Bill.word, Bill.one, max_left_comm, max_comm]

def highSteps (b z n : ℕ) : Bill (ℕ × ℕ) :=
  Bill.steps (z,0) (fun i s => run highBody ((b,z),(i,s))) n

theorem highSteps_q (b z n : ℕ) : (highSteps b z n).val.1 = z / 2^n := by
  induction n with
  | zero => simp [highSteps, Bill.steps, Bill.one]
  | succ n ih =>
    change (run highBody ((b,z),(n,(highSteps b z n).val))).val.1 = _
    rw [highBody_run, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem highSteps_invariant (b z n : ℕ) :
    (highSteps b z n).val.2 + high (highSteps b z n).val.1 = high z := by
  induction n with
  | zero => simp [highSteps, Bill.steps, Bill.one]
  | succ n ih =>
    change (run highBody ((b,z),(n,(highSteps b z n).val))).val.2 +
      high (run highBody ((b,z),(n,(highSteps b z n).val))).val.1 = _
    rw [highBody_run]
    dsimp only [Bill.val]
    rw [Nat.add_assoc, ← high_div]
    exact ih

theorem highSteps_count (b z n : ℕ) : (highSteps b z n).val.2 ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (run highBody ((b,z),(n,(highSteps b z n).val))).val.2 ≤ _
    rw [highBody_run]
    have hf := flag_le (highSteps b z n).val.1
    change (highSteps b z n).val.2 + flag (highSteps b z n).val.1 ≤ n+1
    omega

theorem highSteps_work (b z n : ℕ) : (highSteps b z n).work = 28*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (highSteps b z n).work + (run highBody ((b,z),(n,(highSteps b z n).val))).work + 1 = _
    rw [highBody_run, ih]
    dsimp only [Bill.work]
    omega

theorem highSteps_valid (b z n : ℕ) : (highSteps b z n).valid := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change (highSteps b z n).valid ∧ (run highBody ((b,z),(n,(highSteps b z n).val))).valid
    rw [highBody_run]
    exact ⟨ih,trivial⟩

theorem highSteps_peak (b z n : ℕ) : (highSteps b z n).peak ≤ max 2 (max n z) := by
  induction n with
  | zero => simp [highSteps, Bill.steps, Bill.one]
  | succ n ih =>
    change max (max (highSteps b z n).peak
      (run highBody ((b,z),(n,(highSteps b z n).val))).peak) (n+1) ≤ _
    rw [highBody_run]
    have hq := highSteps_q b z n
    have hqd : (highSteps b z n).val.1 / 2 ≤ z :=
      le_trans (Nat.div_le_self _ _) (by rw [hq]; exact Nat.div_le_self _ _)
    have hc := highSteps_count b z n
    have hf := flag_le (highSteps b z n).val.1
    change max (max (highSteps b z n).peak
      (max 2 (max ((highSteps b z n).val.1/2) ((highSteps b z n).val.2+flag (highSteps b z n).val.1)))) (n+1) ≤ max 2 (max (n+1) z)
    omega

theorem highCell_value (b z : ℕ) (hz : z < 2^b) : (run highCell (b,z)).val = high z := by
  change (highSteps b z b).val.2 = _
  have h := highSteps_invariant b z b
  have hq : (highSteps b z b).val.1 = 0 := by rw [highSteps_q, Nat.div_eq_of_lt hz]
  simpa [hq, high_zero] using h

theorem highCell_work (b z : ℕ) : (run highCell (b,z)).work = 28*b+8 := by
  change 1+(3+(highSteps b z b).work)+1+1+1 = _
  rw [highSteps_work]
  omega

theorem highCell_valid (b z : ℕ) : (run highCell (b,z)).valid := by
  change (True ∧ (True ∧ True ∧ True) ∧ (highSteps b z b).valid) ∧ True
  exact ⟨⟨trivial,⟨trivial,trivial,trivial⟩,highSteps_valid b z b⟩,trivial⟩

theorem highCell_peak (b z : ℕ) : (run highCell (b,z)).peak ≤ max 2 (max b z) := by
  simpa only [highCell, highLoop, highInit, run, Code.run, Atom.run,
    Bill.pass, Bill.pay, Bill.one, Bill.word, max_zero, zero_max, highSteps] using highSteps_peak b z b

theorem highTable_value (b : ℕ) :
    (run highTable b).val = Tape.tab (2^b) high := by
  change (Bill.tab (run power b).val 0 (fun z => run highCell (b,z))).val = _
  rw [power_value, ModelEquivalenceInterpreter.tab_value]
  change Tape.mk (2^b) (fun z => (run highCell (b,z.val)).val) = Tape.mk (2^b) (fun z => high z.val)
  congr 1
  funext z
  exact highCell_value b z.val z.isLt

theorem highTable_length (b : ℕ) : (run highTable b).val.len = 2^b := by
  change (Bill.tab (run power b).val 0 (fun z => run highCell (b,z))).val.len = _
  rw [power_value, ModelEquivalenceInterpreter.tab_value]
  rfl

theorem highTable_work (b : ℕ) :
    (run highTable b).work = 8*b+7+(28*b+12)*2^b := by
  change (run power b).work + (Bill.tab (run power b).val 0 (fun z => run highCell (b,z))).work + 1 = _
  rw [power_value, power_work, ModelEquivalenceInterpreter.tab_work]
  have hs : (∑ j ∈ Finset.range (2^b), (run highCell (b,j)).work) = (2^b)*(28*b+8) := by
    calc
      _ = ∑ _j ∈ Finset.range (2^b), (28*b+8) := Finset.sum_congr rfl (fun j _ => highCell_work b j)
      _ = _ := by simp
  rw [hs]
  ring

theorem highTable_valid (b : ℕ) : (run highTable b).valid := by
  change (run power b).valid ∧ (Bill.tab (run power b).val 0 (fun z => run highCell (b,z))).valid
  exact ⟨power_valid b, (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun z _ => highCell_valid b z)⟩

theorem highTable_peak (b : ℕ) : (run highTable b).peak ≤ max 2 (2^b) := by
  change max (max (run power b).peak
    (Bill.tab (run power b).val 0 (fun z => run highCell (b,z))).peak) 0 ≤ _
  rw [power_value, ModelEquivalenceInterpreter.tab_peak]
  have hp := power_peak b
  have hb : b ≤ 2^b := Nat.le_of_lt b.lt_two_pow_self
  have hs : (Finset.range (2^b)).sup (fun z => (run highCell (b,z)).peak) ≤ max 2 (2^b) := by
    apply Finset.sup_le
    intro z hz
    have hc := highCell_peak b z
    have hz' := Finset.mem_range.mp hz
    omega
  omega

end
end ExactFourierCircuits.DFTModelSectorMapBits
