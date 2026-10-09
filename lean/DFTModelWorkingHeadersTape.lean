import DFTModelRootProgram
import ModelEquivalenceInterpreter

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev PrimeResult := p w (a w)
abbrev Input := p w (p w (p w (a w)))

def nat {r : Port} {s : Ty} (op : NOp) (f g : Code false r s w) : Code false r s w :=
  .comp (.fork f g) (.atom (.int op))

def prependLength : Prog false PrimeResult w :=
  nat .add (.comp (.atom .snd) (.atom .len)) (.atom (.lit 1))
def prependCell : Prog false (p PrimeResult w) w :=
  .ifz (.atom .snd) (.comp (.atom .fst) (.atom .fst))
    (.comp (.fork (.comp (.atom .fst) (.atom .snd))
      (nat .sub (.atom .snd) (.atom (.lit 1)))) (.atom .look))
def prepend : Prog false PrimeResult (a w) := .tab prependLength prependCell

def cons (p : ℕ) (v : Tape ℕ) : Tape ℕ :=
  Tape.tab (v.len+1) (fun i => if i=0 then p else v.look (i-1) 0)

theorem prependLength_run (p : ℕ) (v : Tape ℕ) :
    run prependLength (p,v) = ⟨v.len+1,7,v.len+1,True⟩ := by
  simp [prependLength,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem prependCell_run (p : ℕ) (v : Tape ℕ) (i : ℕ) :
    run prependCell ((p,v),i) =
      ⟨if i=0 then p else v.look (i-1) 0,if i=0 then 5 else 13,
        if i=0 then 0 else max 1 (i-1),True⟩ := by
  by_cases hi : i=0 <;>
    simp [prependCell,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
      Bill.word,hi,Ty.blank]

theorem prepend_value (p : ℕ) (v : Tape ℕ) : (run prepend (p,v)).val = cons p v := by
  change (Bill.tab (run prependLength (p,v)).val w.blank
    (fun i => run prependCell ((p,v),i))).val = _
  rw [prependLength_run,ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab (v.len+1))
  funext i
  exact congrArg Bill.val (prependCell_run p v i)

theorem prepend_work (p : ℕ) (v : Tape ℕ) : (run prepend (p,v)).work ≤ 17*v.len+27 := by
  change (run prependLength (p,v)).work+
    (Bill.tab (run prependLength (p,v)).val w.blank
      (fun i => run prependCell ((p,v),i))).work+1 ≤ _
  rw [prependLength_run,ModelEquivalenceInterpreter.tab_work]
  dsimp only [Bill.work,Bill.val]
  have h : (∑ i ∈ Finset.range (v.len+1), (run prependCell ((p,v),i)).work) ≤ 13*(v.len+1) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (v.len+1), 13 := by
        apply Finset.sum_le_sum
        intro i _
        rw [prependCell_run]
        dsimp only [Bill.work]
        split <;> omega
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem prepend_peak (p : ℕ) (v : Tape ℕ) : (run prepend (p,v)).peak ≤ v.len+1 := by
  change max (max (run prependLength (p,v)).peak
    (Bill.tab (run prependLength (p,v)).val w.blank
      (fun i => run prependCell ((p,v),i))).peak) 0 ≤ _
  rw [prependLength_run,ModelEquivalenceInterpreter.tab_peak]
  dsimp only [Bill.peak,Bill.val]
  refine max_le (max_le le_rfl (max_le le_rfl ?_)) (by omega)
  apply Finset.sup_le
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [prependCell_run]
  dsimp only
  split <;> omega

theorem prepend_valid (p : ℕ) (v : Tape ℕ) : (run prepend (p,v)).valid := by
  change (run prependLength (p,v)).valid ∧
    (Bill.tab (run prependLength (p,v)).val w.blank
      (fun i => run prependCell ((p,v),i))).valid
  rw [prependLength_run]
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro i _
  rw [prependCell_run]
  trivial

end
end ExactFourierCircuits.DFTModelWorkingHeaders
