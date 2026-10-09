import UniformMachine
import OAI.Computability.FourierTransform.RAM

set_option autoImplicit false

/-! Exact natural-operation bridge. The upstream integer primitives are total;
the guarded code below records our partial division/modulo domain in `valid`.
Its invalid branch uses only a prepared inverse of zero and never tests a scalar.
This is a primitive-level bridge, not a whole-machine compiler. -/
namespace ExactFourierCircuits.ModelEquivalenceNat
open UniformMachine
open OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty
noncomputable section

def toUpstream : NatOp → NOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod

def fromUpstream : NOp → Option NatOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .lt => none

theorem from_to (op : NatOp) : fromUpstream (toUpstream op) = some op := by
  cases op <;> rfl

theorem to_injective : Function.Injective toUpstream := by
  intro op op' h
  have := congrArg fromUpstream h
  simpa only [from_to, Option.some.injEq] using this

def ValidOperands : NatOp → ℕ → ℕ → Prop
  | .div, _, b => b ≠ 0
  | .mod, _, b => b ≠ 0
  | _, _, _ => True

theorem raw_work (op : NatOp) (a b : ℕ) :
    ((toUpstream op).run (a,b)).work = 1 := by
  cases op <;> rfl

theorem raw_peak (op : NatOp) (a b : ℕ) :
    ((toUpstream op).run (a,b)).peak = ((toUpstream op).run (a,b)).val := by
  cases op <;> rfl

theorem raw_valid (op : NatOp) (a b : ℕ) :
    ((toUpstream op).run (a,b)).valid := by
  cases op <;> trivial

theorem evalNat_some_iff (op : NatOp) (a b v : ℕ) :
    evalNat op a b = some v ↔
      ValidOperands op a b ∧ ((toUpstream op).run (a,b)).val = v := by
  cases op <;> by_cases hb : b = 0 <;>
    simp [evalNat, ValidOperands, toUpstream, NOp.run, Bill.word, hb]

theorem evalNat_none_iff (op : NatOp) (a b : ℕ) :
    evalNat op a b = none ↔ ¬ValidOperands op a b := by
  cases op <;> by_cases hb : b = 0 <;>
    simp [evalNat, ValidOperands, hb]

theorem accepted_exact (op : NatOp) (a b : ℕ) (h : ValidOperands op a b) :
    evalNat op a b = some ((toUpstream op).run (a,b)).val :=
  (evalNat_some_iff op a b _).2 ⟨h,rfl⟩

theorem div_zero_boundary (a : ℕ) :
    evalNat .div a 0 = none ∧ (NOp.div.run (a,0)).val = 0 ∧
      (NOp.div.run (a,0)).valid := by
  simp [evalNat, NOp.run, Bill.word]

theorem mod_zero_boundary (a : ℕ) :
    evalNat .mod a 0 = none ∧ (NOp.mod.run (a,0)).val = a ∧
      (NOp.mod.run (a,0)).valid := by
  simp [evalNat, NOp.run, Bill.word]

/-- Return the total natural result while making the executed path invalid. -/
def invalidNat (op : NatOp) : Prog false (p w w) w :=
  .comp (.fork (.atom (.int (toUpstream op)))
    (.comp (.atom (.cz .scalar)) (.atom .inv))) (.atom .fst)

/-- Only the two partial natural operations require a denominator guard. -/
def natCode (op : NatOp) : Prog false (p w w) w :=
  match op with
  | .div => .ifz (.atom .snd) (invalidNat .div) (.atom (.int .div))
  | .mod => .ifz (.atom .snd) (invalidNat .mod) (.atom (.int .mod))
  | _ => .atom (.int (toUpstream op))

def work : NatOp → ℕ → ℕ
  | .div, b => if b = 0 then 9 else 3
  | .mod, b => if b = 0 then 9 else 3
  | _, _ => 1

theorem invalidNat_run (op : NatOp) (a b : ℕ) :
    run (invalidNat op) (a,b) =
      ⟨((toUpstream op).run (a,b)).val, 7,
        ((toUpstream op).run (a,b)).val, False⟩ := by
  cases op <;>
    simp [invalidNat, run, Code.run, Atom.run, toUpstream, NOp.run,
      Bill.pass, Bill.pay, Bill.one, Bill.word]

theorem natCode_run (op : NatOp) (a b : ℕ) :
    run (natCode op) (a,b) =
      ⟨((toUpstream op).run (a,b)).val, work op b,
        ((toUpstream op).run (a,b)).val, ValidOperands op a b⟩ := by
  cases op <;> by_cases hb : b = 0 <;>
    simp [natCode, invalidNat, run, Code.run, Atom.run, toUpstream, NOp.run,
      work, ValidOperands, Bill.pass, Bill.pay, Bill.one, Bill.word, hb]

theorem natCode_value (op : NatOp) (a b : ℕ) :
    (run (natCode op) (a,b)).val = ((toUpstream op).run (a,b)).val := by
  rw [natCode_run]

theorem natCode_valid_iff (op : NatOp) (a b : ℕ) :
    (run (natCode op) (a,b)).valid ↔ ValidOperands op a b := by
  rw [natCode_run]

theorem natCode_work (op : NatOp) (a b : ℕ) :
    (run (natCode op) (a,b)).work = work op b := by
  rw [natCode_run]

theorem natCode_peak (op : NatOp) (a b : ℕ) :
    (run (natCode op) (a,b)).peak = (run (natCode op) (a,b)).val := by
  rw [natCode_run]

theorem natCode_work_le (op : NatOp) (a b : ℕ) :
    (run (natCode op) (a,b)).work ≤ 9 := by
  rw [natCode_work]
  cases op <;> by_cases hb : b = 0 <;> simp [work, hb]

theorem accepted_work_le (op : NatOp) (a b : ℕ) (h : ValidOperands op a b) :
    (run (natCode op) (a,b)).work ≤ 3 := by
  rw [natCode_work]
  cases op <;> simp_all [ValidOperands, work]

/-- Upstream validity, rather than its total fallback value, reflects failure. -/
theorem natCode_reflects (op : NatOp) (a b v : ℕ) :
    evalNat op a b = some v ↔
      (run (natCode op) (a,b)).valid ∧ (run (natCode op) (a,b)).val = v := by
  rw [evalNat_some_iff, natCode_valid_iff, natCode_value]

theorem natCode_reflects_failure (op : NatOp) (a b : ℕ) :
    evalNat op a b = none ↔ ¬(run (natCode op) (a,b)).valid := by
  rw [evalNat_none_iff, natCode_valid_iff]

theorem lt_true_iff (a b : ℕ) : (NOp.lt.run (a,b)).val = 1 ↔ a < b := by
  simp [NOp.run, Bill.word]

theorem lt_false_iff (a b : ℕ) : (NOp.lt.run (a,b)).val = 0 ↔ b ≤ a := by
  simp [NOp.run, Bill.word]

/-- Integer branching preserves our strict comparison and its two targets. -/
def branchCode (yes no : ℕ) : Prog false (p w w) w :=
  .ifz (.atom (.int .lt)) (.atom (.lit no)) (.atom (.lit yes))

theorem branchCode_run (a b yes no : ℕ) :
    run (branchCode yes no) (a,b) =
      ⟨if a < b then yes else no, 3,
        max (if a < b then 1 else 0) (if a < b then yes else no), True⟩ := by
  by_cases h : a < b <;>
    simp [branchCode, run, Code.run, Atom.run, NOp.run,
      Bill.pass, Bill.pay, Bill.word, h]

theorem branchCode_value (a b yes no : ℕ) :
    (run (branchCode yes no) (a,b)).val = if a < b then yes else no := by
  rw [branchCode_run]

theorem branchCode_peak_le (a b yes no B : ℕ)
    (hB : 1 ≤ B) (hy : yes ≤ B) (hn : no ≤ B) :
    (run (branchCode yes no) (a,b)).peak ≤ B := by
  rw [branchCode_run]
  by_cases h : a < b <;> simp [h, hB, hy, hn]

end
end ExactFourierCircuits.ModelEquivalenceNat
