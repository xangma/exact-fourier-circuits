import DFTModelRecursiveScalarCore
import DFTModelClockControl
import UniformFixedNetworkLiteralDecoderMachine

set_option autoImplicit false

/-! Charged literal Nat metadata for the fixed saving seed. The list is a
compile-time finite payload of integer literals. No array/table atom is added;
this program constructs a fresh tape using the original upstream tab syntax.
Its quadratic payload cost is a fixed seed constant, independent of runtime k. -/
namespace ExactFourierCircuits.DFTModelRecursiveMetadata
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelClockControl
open UniformFixedNetworkScheduleMachine (Record)
noncomputable section

def predecessor : Prog false w w :=
  .comp (.fork (.atom .id) (.atom (.lit 1))) (.atom (.int .sub))
def literalCell : List ℕ → Prog false w w
  | [] => .atom (.lit 0)
  | v::vs => .ifz (.atom .id) (.atom (.lit v)) (.comp predecessor (literalCell vs))

def literalTape {s : Ty} (vs : List ℕ) : Prog false s (Ty.a w) :=
  .tab (.atom (.lit vs.length)) (.comp (.atom .snd) (literalCell vs))

theorem predecessor_run (j : ℕ) : run predecessor j=⟨j-1,5,max 1 (j-1),True⟩ := by
  simp [predecessor,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem literalCell_zero (v : ℕ) (vs : List ℕ) :
    run (literalCell (v::vs)) 0=⟨v,3,v,True⟩ := by
  rw [literalCell,ifz_run]
  simp [atom_run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem literalCell_succ (v : ℕ) (vs : List ℕ) (j : ℕ) :
    run (literalCell (v::vs)) (j+1)=
      ⟨(run (literalCell vs) j).val,(run (literalCell vs) j).work+8,
        max (max 1 j) (run (literalCell vs) j).peak,(run (literalCell vs) j).valid⟩ := by
  rw [literalCell,ifz_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,Nat.add_one_ne_zero,ite_false]
  rw [comp_run,predecessor_run]
  simp only [Bill.pass,Bill.pay,Nat.add_sub_cancel,max_zero,true_and]
  congr 1; ac_rfl

theorem literalCell_value (vs : List ℕ) (j : ℕ) :
    (run (literalCell vs) j).val=(vs[j]?).getD 0 := by
  induction vs generalizing j with
  | nil => rfl
  | cons v vs ih =>
    cases j with
    | zero => rw [literalCell_zero]; rfl
    | succ j => rw [literalCell_succ]; exact ih j

theorem literalCell_valid (vs : List ℕ) (j : ℕ) : (run (literalCell vs) j).valid := by
  induction vs generalizing j with
  | nil => trivial
  | cons v vs ih =>
    cases j with
    | zero => rw [literalCell_zero]; trivial
    | succ j => rw [literalCell_succ]; exact ih j

theorem literalCell_work (vs : List ℕ) (j : ℕ) :
    (run (literalCell vs) j).work≤8*vs.length+3 := by
  induction vs generalizing j with
  | nil => simp [literalCell,atom_run,Atom.run,Bill.word]
  | cons v vs ih =>
    cases j with
    | zero => rw [literalCell_zero]; simp
    | succ j =>
      rw [literalCell_succ]
      have h:=ih j
      simp only [List.length_cons]
      omega

theorem literalCell_peak (vs : List ℕ) (j B : ℕ) (index : j≤B) (one : 1≤B)
    (literals : ∀v∈vs,v≤B) : (run (literalCell vs) j).peak≤B := by
  induction vs generalizing j with
  | nil => simp [literalCell,atom_run,Atom.run,Bill.word]
  | cons v vs ih =>
    have hv:=literals v (by simp)
    have rest:∀a∈vs,a≤B:=by intro a ha;exact literals a (by simp [ha])
    cases j with
    | zero => rw [literalCell_zero];exact hv
    | succ j =>
      rw [literalCell_succ]
      exact max_le (max_le one (by omega)) (ih j (by omega) rest)

theorem literalTape_value {s : Ty} (vs : List ℕ) (x : s.T) :
    (run (literalTape vs) x).val=Tape.tab vs.length (fun j => (vs[j]?).getD 0) := by
  change (Bill.tab vs.length w.blank (fun j => run
    (.comp (.atom .snd) (literalCell vs)) (x,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab vs.length)
  funext j
  change (run (literalCell vs) j).val=_
  exact literalCell_value vs j

theorem literalTape_valid {s : Ty} (vs : List ℕ) (x : s.T) :
    (run (literalTape vs) x).valid := by
  change True ∧ (Bill.tab vs.length w.blank (fun j => run
    (.comp (.atom .snd) (literalCell vs)) (x,j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  change True ∧ (run (literalCell vs) j).valid
  exact ⟨trivial,literalCell_valid vs j⟩

theorem literalTape_work {s : Ty} (vs : List ℕ) (x : s.T) :
    (run (literalTape vs) x).work≤4+vs.length*(8*vs.length+9) := by
  change 1+(Bill.tab vs.length w.blank (fun j => run
    (.comp (.atom .snd) (literalCell vs)) (x,j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j ∈ Finset.range vs.length,(run
    (.comp (.atom .snd) (literalCell vs)) (x,j)).work)≤vs.length*(8*vs.length+5) := by
    calc
      _ ≤ ∑_j ∈ Finset.range vs.length,(8*vs.length+5) := by
        apply Finset.sum_le_sum
        intro j _
        change 1+(run (literalCell vs) j).work+1≤_
        have h:=literalCell_work vs j
        omega
      _ = _ := by simp
  nlinarith

theorem literalTape_peak {s : Ty} (vs : List ℕ) (x : s.T) (B : ℕ)
    (len : vs.length≤B) (one : 1≤B) (literals : ∀v∈vs,v≤B) :
    (run (literalTape vs) x).peak≤B := by
  change max (max vs.length (Bill.tab vs.length w.blank (fun j => run
    (.comp (.atom .snd) (literalCell vs)) (x,j))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le len (max_le len ?_)
  apply Finset.sup_le
  intro j hj
  change max (max 0 (run (literalCell vs) j).peak) 0≤B
  simpa only [zero_max,max_zero] using literalCell_peak vs j B
    (by have h:=Finset.mem_range.mp hj;omega) one literals

end
end ExactFourierCircuits.DFTModelRecursiveMetadata
