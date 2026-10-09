import UniformPairMachine
import ModelEquivalenceInterpreter

set_option autoImplicit false

/-!
# The actual prepared-coefficient pair block in upstream `Code false`

The published input pair is read before either result is constructed. Complex
data have paint `left`; coefficients have paint `scalar`. The conservative
dependency tag is ordinary natural data, and is combined by a charged test.
There is no data-by-data multiplication and no tape update in this block.
-/
namespace ExactFourierCircuits.DFTModelBinaryPair
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Datum := p w (c .left)
abbrev Pair := p Datum Datum
abbrev Coefficients := p sc sc
abbrev Input := p Coefficients Pair

def encode (z : Scalar) : Datum.T :=
  (if z.dependent then 1 else 0,z.value)

def coefficient (second : Bool) : Prog false Input sc :=
  .comp (.atom .fst) (if second then .atom .snd else .atom .fst)

def datum (second : Bool) : Prog false Input Datum :=
  .comp (.atom .snd) (if second then .atom .snd else .atom .fst)

def tag (second : Bool) : Prog false Input w :=
  .comp (datum second) (.atom .fst)

def value (second : Bool) : Prog false Input (c .left) :=
  .comp (datum second) (.atom .snd)

def tagSum : Prog false Input w :=
  .comp (.fork (tag false) (tag true)) (.atom (.int .add))

def combinedTag : Prog false Input w :=
  .ifz tagSum (.atom (.lit 0)) (.atom (.lit 1))

def term (secondCoefficient secondDatum : Bool) : Prog false Input (c .left) :=
  .comp (.fork (coefficient secondCoefficient) (value secondDatum))
    (.atom (.scale .left))

def combination (swapped : Bool) : Prog false Input Datum :=
  .fork combinedTag
    (.comp (.fork (term swapped false) (term (!swapped) true)) (.atom (.add .left)))

/-- The same two linear combinations as the actual eleven instructions. -/
def program : Prog false Input Pair :=
  .fork (combination false) (combination true)

def flags (u v : Datum.T) : ℕ := if u.1+v.1 = 0 then 0 else 1

def result (a b : ℂ) (u v : Datum.T) : Pair.T :=
  ((flags u v,a*u.2+b*v.2),(flags u v,b*u.2+a*v.2))

theorem combination_run (swapped : Bool) (a b : ℂ) (u v : Datum.T) :
    run (combination swapped) ((a,b),(u,v)) =
      ⟨(flags u v,if swapped then b*u.2+a*v.2 else a*u.2+b*v.2),
        41,u.1+v.1,True⟩ := by
  cases swapped <;> by_cases h : u.1 = 0 ∧ v.1 = 0 <;>
    simp [combination,combinedTag,tagSum,term,coefficient,value,tag,datum,flags,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h]
  all_goals exact Nat.one_le_iff_ne_zero.mpr (fun hz => h (Nat.add_eq_zero_iff.mp hz))

theorem program_run (a b : ℂ) (u v : Datum.T) :
    run program ((a,b),(u,v)) = ⟨result a b u v,83,u.1+v.1,True⟩ := by
  change ((run (combination false) ((a,b),(u,v))).pass (fun y =>
    (run (combination true) ((a,b),(u,v))).pass (fun z => Bill.one (y,z)))) = _
  rw [combination_run,combination_run]
  simp [result,Bill.pass,Bill.one]

theorem flags_encode (u v : Scalar) :
    flags (encode u) (encode v) = if u.dependent || v.dependent then 1 else 0 := by
  cases hu : u.dependent <;> cases hv : v.dependent <;> simp [flags,encode,hu,hv]

theorem result_encode (a b : ℂ) (u v : Scalar) :
    result a b (encode u) (encode v) =
      (encode (UniformPairMachine.combine a b u v),
        encode (UniformPairMachine.combine b a u v)) := by
  unfold result
  rw [flags_encode]
  rfl

theorem encoded_peak (u v : Scalar) :
    (encode u).1+(encode v).1 ≤ 2 := by
  cases hu : u.dependent <;> cases hv : v.dependent <;> simp [encode,hu,hv]

/-- Source correspondence for the genuine pair-register program, including tags. -/
theorem actual_execution {n B : ℕ} (x : Fin n → ℂ) (s : State)
    (a b : ℂ) (u v : Scalar) (ready : UniformPairMachine.Ready a b u v s)
    (distinct : s.natReg 0 ≠ s.natReg 1) (code : 11 ≤ B) (wb : WordBound B s) :
    ∃ t, BoundedExecution UniformPairMachine.program n x B s 11 t ∧
      t.natReg = s.natReg ∧ t.natHeap = s.natHeap ∧
      t.outputs = s.outputs ∧ t.rootOrders = s.rootOrders ∧
      t.scalarHeap (s.natReg 0) = some (UniformPairMachine.combine a b u v) ∧
      t.scalarHeap (s.natReg 1) = some (UniformPairMachine.combine b a u v) ∧
      (run program ((a,b),(encode u,encode v))).val =
        (encode (UniformPairMachine.combine a b u v),
          encode (UniformPairMachine.combine b a u v)) ∧
      (run program ((a,b),(encode u,encode v))).valid ∧
      (run program ((a,b),(encode u,encode v))).work ≤ 8*11 ∧
      (run program ((a,b),(encode u,encode v))).peak ≤ B := by
  have execution := UniformPairMachine.bounded_execution n x B s a b u v ready code wb
  have values := UniformPairMachine.final_values s a b u v distinct
  have frame := UniformPairMachine.final_frame s a b u v
  refine ⟨UniformPairMachine.finalState s a b u v,execution,
    frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,values.1,values.2,?_,?_,?_,?_⟩
  · rw [program_run,result_encode]
  · rw [program_run]
    trivial
  · rw [program_run]
    change 83 ≤ 8*11
    omega
  · rw [program_run]
    have h := encoded_peak u v
    change (encode u).1+(encode v).1 ≤ B
    exact Nat.le_trans h (Nat.le_trans (by decide : 2 ≤ 11) code)

end
end ExactFourierCircuits.DFTModelBinaryPair
