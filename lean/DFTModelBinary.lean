import UniformBinaryCStageMachine
import DFTModelBinaryPair

set_option autoImplicit false

/-!
# Fresh-tape translation of the complete actual binary C stage

Each source iteration reads one disjoint pair and writes its two results. One
upstream `Code.tab` therefore builds all output pairs from the same readonly
input bank, with linear work. This is a stage translation with an explicit
pair-major bank representation; it is not a whole-machine compiler theorem.
The prepared C coefficients are inputs and their actual low-heap provenance
is required by the source-stage contract.
-/
namespace ExactFourierCircuits.DFTModelBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine OAI.ExactFourier
noncomputable section

abbrev Input := p w (p DFTModelBinaryPair.Coefficients (Ty.a DFTModelBinaryPair.Pair))
abbrev CellInput := p Input w

def coefficients : Prog false CellInput DFTModelBinaryPair.Coefficients :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))

def oldTape : Prog false CellInput (Ty.a DFTModelBinaryPair.Pair) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))

def oldPair : Prog false CellInput DFTModelBinaryPair.Pair :=
  .comp (.fork oldTape (.atom .snd)) (.atom .look)

def cell : Prog false CellInput DFTModelBinaryPair.Pair :=
  .comp (.fork coefficients oldPair) DFTModelBinaryPair.program

/-- A single fresh allocation for all disjoint source pairs. -/
def program : Prog false Input (Ty.a DFTModelBinaryPair.Pair) := .tab (.atom .fst) cell

def data {M : ℕ} (v : Fin M → Fin 2 → Scalar) : Tape DFTModelBinaryPair.Pair.T :=
  ⟨M,fun j => (DFTModelBinaryPair.encode (v j 0),DFTModelBinaryPair.encode (v j 1))⟩

def input {M : ℕ} (v : Fin M → Fin 2 → Scalar) : Input.T :=
  (M,((a,b),data v))

theorem cell_run (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryPair.Pair.T) (j : ℕ) :
    run cell ((M,((c,d),v)),j) =
      ⟨DFTModelBinaryPair.result c d (v.look j ((0,0),(0,0))).1
        (v.look j ((0,0),(0,0))).2,99,
        (v.look j ((0,0),(0,0))).1.1+(v.look j ((0,0),(0,0))).2.1,True⟩ := by
  change ((run (.fork coefficients oldPair) ((M,((c,d),v)),j)).pass
    (fun z => run DFTModelBinaryPair.program z)).pay 1 0 = _
  have h : run (.fork coefficients oldPair) ((M,((c,d),v)),j) =
      Bill.mk ((c,d),v.look j ((0,0),(0,0))) 15 0 True := by
    simp [coefficients,oldPair,oldTape,run,Code.run,Atom.run,
      Bill.pass,Bill.pay,Bill.one,Ty.blank]
  rw [h]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelBinaryPair.program_run]
  simp

theorem program_value (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryPair.Pair.T) :
    (run program (M,((c,d),v))).val = Tape.tab M (fun j =>
      DFTModelBinaryPair.result c d (v.look j ((0,0),(0,0))).1 (v.look j ((0,0),(0,0))).2) := by
  change (Bill.tab M DFTModelBinaryPair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab M) (funext (fun j => congrArg Bill.val (cell_run M c d v j)))

theorem program_work (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryPair.Pair.T) :
    (run program (M,((c,d),v))).work = 103*M+4 := by
  change 1+(Bill.tab M DFTModelBinaryPair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((M,((c,d),v)),j)).work) = (fun _ => 99) := by
    funext j
    exact congrArg Bill.work (cell_run M c d v j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryPair.Pair.T) :
    (run program (M,((c,d),v))).valid := by
  change True ∧ (Bill.tab M DFTModelBinaryPair.Pair.blank
    (fun j => run cell ((M,((c,d),v)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem input_value {P Q : ℕ} (v : Fin (P*Q) → Fin 2 → Scalar) :
    (run program (input v)).val = data (UniformBinaryCStageMachine.transformed v) := by
  rw [input,program_value]
  unfold data
  dsimp only [Tape.tab,Tape.len]
  congr 1
  funext j
  simp only [Tape.look,j.isLt,↓reduceDIte]
  rw [DFTModelBinaryPair.result_encode]
  rfl

theorem input_peak {M : ℕ} (v : Fin M → Fin 2 → Scalar) :
    (run program (input v)).peak ≤ max M 2 := by
  change max (max 0 (Bill.tab M DFTModelBinaryPair.Pair.blank
    (fun j => run cell ((M,((a,b),data v)),j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,zero_max]
  apply max_le (le_max_left _ _)
  apply Finset.sup_le
  intro j hj
  have lt : j < M := Finset.mem_range.mp hj
  rw [cell_run]
  change ((data v).look j ((0,0),(0,0))).1.1+
    ((data v).look j ((0,0),(0,0))).2.1 ≤ max M 2
  simp only [data,Tape.look,lt,↓reduceDIte]
  exact Nat.le_trans (DFTModelBinaryPair.encoded_peak (v ⟨j,lt⟩ 0) (v ⟨j,lt⟩ 1)) (le_max_right _ _)

theorem work_preserved {M : ℕ} (v : Fin M → Fin 2 → Scalar) :
    (run program (input v)).work ≤ 5*(25*M+6) := by
  rw [input,program_work]
  omega

/-- This relation uses the actual source address permutation, not an assumed
functional update or an independently specified Fourier transform. -/
def Represents (P A Q : ℕ) (v : Tape DFTModelBinaryPair.Pair.T) (s : State) : Prop :=
  v.len = P*Q ∧ ∀ j : Fin (P*Q), ∀ t : Fin 2, ∃ z,
    s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t) = some z ∧
      (if t=0 then (v.look j.val ((0,0),(0,0))).1
        else (v.look j.val ((0,0),(0,0))).2) = DFTModelBinaryPair.encode z

/-- Complete actual 30-instruction stage versus genuine upstream `Code false`.
No output-bank, transformed-coefficient, or stage execution premise is used. -/
theorem actual_execution {n B P A Q : ℕ} (x : Fin n → ℂ)
    (v : Fin (P*Q) → Fin 2 → Scalar) (s : State)
    (pc : s.pc=0) (stride : s.natReg 2800=P) (base : s.natReg 2801=A)
    (count : s.natReg 2802=Q) (positive : 0<P) (separate : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (source : ∀ j t, s.scalarHeap (UniformBinaryCStageMachine.coordinate P A Q j t)=some (v j t))
    (wb : WordBound B s) (code : 30≤B) (extent : A+P*2*Q≤B) :
    ∃ u, BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(P*Q)+6) u ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s u ∧ UniformBinaryCStageMachine.Constants u ∧
      Represents P A Q (run program (input v)).val u ∧
      (run program (input v)).valid ∧
      (run program (input v)).work ≤ 5*(25*(P*Q)+6) ∧
      (run program (input v)).peak ≤ B := by
  obtain ⟨u,execution,values,frame⟩ := UniformBinaryCStageMachine.execution n B x P A Q v s
    pc stride base count positive separate constants source wb code extent
  refine ⟨u,execution,frame,frame.constants separate constants,?_,
    program_valid _ _ _ _,work_preserved v,?_⟩
  · rw [input_value]
    refine ⟨rfl,?_⟩
    intro j t
    refine ⟨UniformBinaryCStageMachine.transformed v j t,values j t,?_⟩
    fin_cases t <;> simp [data,Tape.look,j.isLt]
  · have h : P*Q ≤ B := by
      have eq : P*2*Q=2*(P*Q) := by ring
      rw [eq] at extent
      omega
    exact (input_peak v).trans (max_le h (by omega))

end
end ExactFourierCircuits.DFTModelBinary
