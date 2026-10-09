import ModelEquivalenceInterpreter

set_option autoImplicit false

/-!
A closed upstream `Code false` prepared-power table.  The recursive call builds
only a table of ceil(N/2) powers, and the parent publishes its N cells with one
`tab`.  There is no mutable dense-tape update or supplied table/handler in the
public program.  All complex multiplication is between prepared scalars.
-/
namespace ExactFourierCircuits.DFTModelPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w sc
abbrev Output := a sc
abbrev RecPort : Port := some (Input, Output)
abbrev Expansion := p Input Output
abbrev Cell := p Expansion w

def half (n : ℕ) : ℕ := (n+1)/2

def small {r : Port} : Code false r Input Output :=
  .tab (.atom .fst) (.atom .cone)

def halfInput {r : Port} : Code false r Input Input :=
  .fork
    (.comp (.fork
      (.comp (.fork (.atom .fst) (.atom (.lit 1))) (.atom (.int .add)))
      (.atom (.lit 2))) (.atom (.int .div)))
    (.atom .snd)

def oldPower {r : Port} : Code false r Cell sc :=
  .comp (.fork
    (.comp (.atom .fst) (.atom .snd))
    (.comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .div))))
    (.atom .look)

def square {r : Port} : Code false r Cell sc :=
  .comp (.fork oldPower oldPower) (.atom (.scale .scalar))

def parityFactor {r : Port} : Code false r Cell sc :=
  .ifz (.comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .mod)))
    (.atom .cone)
    (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))

def cell {r : Port} : Code false r Cell sc :=
  .comp (.fork square parityFactor) (.atom (.scale .scalar))

def expand {r : Port} : Code false r Expansion Output :=
  .tab (.comp (.atom .fst) (.atom .fst)) cell

def large : Code false RecPort Input Output :=
  .comp (.fork (.atom .id) (.comp halfInput .call)) expand

def test {r : Port} : Code false r Input w :=
  .comp (.fork (.atom .fst) (.atom (.lit 2))) (.atom (.int .lt))

def step : Code false RecPort Input Output := .ifz test large small

/-- Fixed code; the length itself is the fuel bound, with early halving exits. -/
def program : Prog false Input Output :=
  .comp (.fork (.atom .fst) (.atom .id)) (.descend small step)

theorem halfInput_run {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    halfInput.run h (n,z) = ⟨(half n,z),11,max 2 (n+1),True⟩ := by
  simp only [halfInput, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word, half]
  congr 1 <;> first | omega | simp

theorem cell_run {r : Port} (h : Handler r) (n i : ℕ) (z : ℂ) (v : Tape ℂ) :
    cell.run h (((n,z),v),i) =
      ⟨(v.look (i/2) 0)^2 * (if i%2=0 then 1 else z),
        if i%2=0 then 35 else 39, max 2 (i/2),True⟩ := by
  by_cases he : i%2=0
  · simp [cell, square, oldPower, parityFactor, Code.run, Atom.run,
      NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word, he, pow_two, Ty.blank]
  · simp [cell, square, oldPower, parityFactor, Code.run, Atom.run,
      NOp.run, Bill.pass, Bill.pay, Bill.one, Bill.word, he, pow_two, Ty.blank]
    omega

theorem small_value {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    (small.run h (n,z)).val = Tape.tab n (fun _ => 1) := by
  change (Bill.tab n sc.blank (fun _ => Bill.one (1 : ℂ))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem small_work {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    (small.run h (n,z)).work = 5*n+4 := by
  change 1+(Bill.tab n sc.blank (fun _ => Bill.one (1 : ℂ))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  simp [Bill.one]
  omega

theorem small_peak {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    (small.run h (n,z)).peak = n := by
  change max (max 0 (Bill.tab n sc.blank (fun _ => Bill.one (1 : ℂ))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp [Bill.one]

theorem small_valid {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) :
    (small.run h (n,z)).valid := by
  change True ∧ (Bill.tab n sc.blank (fun _ => Bill.one (1 : ℂ))).valid
  exact ⟨trivial, (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (by simp [Bill.one])⟩

theorem expand_value {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (expand.run h ((n,z),v)).val = Tape.tab n (fun i =>
      (v.look (i/2) 0)^2 * (if i%2=0 then 1 else z)) := by
  change (Bill.tab n sc.blank (fun i => cell.run h (((n,z),v),i))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 1
  funext i
  exact congrArg Bill.val (cell_run h n i z v)

theorem expand_work {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (expand.run h ((n,z),v)).work ≤ 49*n+6 := by
  change 3+(Bill.tab n sc.blank (fun i => cell.run h (((n,z),v),i))).work+1 ≤ _
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑ i ∈ Finset.range n, (cell.run h (((n,z),v),i)).work) ≤ 45*n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, 45 := Finset.sum_le_sum (fun i _ => by
        rw [cell_run]
        dsimp only [Bill.work]
        split <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem expand_peak {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (expand.run h ((n,z),v)).peak ≤ n+2 := by
  change max (max 0 (Bill.tab n sc.blank (fun i => cell.run h (((n,z),v),i))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs : (Finset.range n).sup (fun i => (cell.run h (((n,z),v),i)).peak) ≤ n+2 := by
    apply Finset.sup_le
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [cell_run]
    dsimp only [Bill.peak]
    omega
  omega

theorem expand_valid {r : Port} (h : Handler r) (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    (expand.run h ((n,z),v)).valid := by
  change (True ∧ True) ∧ (Bill.tab n sc.blank (fun i => cell.run h (((n,z),v),i))).valid
  refine ⟨⟨trivial,trivial⟩, (ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro i _
  rw [cell_run]
  trivial

end
end ExactFourierCircuits.DFTModelPreparation
