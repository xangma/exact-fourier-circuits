import UniformRolePointwiseMachine
import ModelEquivalenceInterpreter

set_option autoImplicit false

/-!
# Functional translation of the actual final DFT pointwise stage

The source block reads each data cell once, multiplies by a disjoint prepared
kernel cell, and overwrites only that data cell. No later iteration needs the
old contents of a different overwritten cell. Thus one fresh `Code.tab` is
sufficient for the whole block; no tape is rebuilt per source instruction.

The integer tag is retained as data. The scalar multiplication has statically
prepared left input and statically data right input, and uses `Prog false`.
This module translates this actual stage, not the recursive global clocks or
the complete twenty-stage program. Bank materialization is an explicit entry
representation; its earlier production is not claimed free.

This value-only representation is a local stage lemma: arbitrary prepared
offsets are not injected into the left-data channel by a closed compiler.
`DFTModelMemoryAffinePointwise` supplies the offset/homogeneous representation
needed to compose with an actual translated state.
-/
namespace ExactFourierCircuits.DFTModelMemoryPointwise
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Datum := p w (c .left)
abbrev Input := p w (p (Ty.a Datum) (Ty.a sc))
abbrev CellInput := p Input w

def dataTape : Prog false CellInput (Ty.a Datum) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))

def kernelTape : Prog false CellInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))

def dataRead : Prog false CellInput Datum :=
  .comp (.fork dataTape (.atom .snd)) (.atom .look)

def kernelRead : Prog false CellInput sc :=
  .comp (.fork kernelTape (.atom .snd)) (.atom .look)

def multiply : Prog false (p Datum sc) Datum :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.comp (.fork (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
      (.atom (.scale .left)))

def cell : Prog false CellInput Datum := .comp (.fork dataRead kernelRead) multiply

/-- The compiled source pointwise block constructs its output exactly once. -/
def program : Prog false Input (Ty.a Datum) := .tab (.atom .fst) cell

def encode (x : Scalar) : ℕ × ℂ := (if x.dependent then 1 else 0, x.value)

def data {L : ℕ} (v : Fin L → Scalar) : Tape (ℕ × ℂ) :=
  ⟨L,fun j => encode (v j)⟩

def kernel {L : ℕ} (y : Fin L → ℂ) : Tape ℂ := ⟨L,y⟩

def input {L : ℕ} (v : Fin L → Scalar) (y : Fin L → ℂ) : Input.T :=
  (L,(data v,kernel y))

theorem multiply_run (v : ℕ × ℂ) (y : ℂ) :
    run multiply (v,y) = ⟨(v.1,y*v.2),11,0,True⟩ := by
  simp [multiply,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem cell_run (L : ℕ) (v : Tape (ℕ × ℂ)) (y : Tape ℂ) (j : ℕ) :
    run cell ((L,(v,y)),j) =
      ⟨((v.look j (0,0)).1,(y.look j 0)*(v.look j (0,0)).2),31,0,True⟩ := by
  simp [cell,dataRead,kernelRead,dataTape,kernelTape,multiply,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem program_value (L : ℕ) (v : Tape (ℕ × ℂ)) (y : Tape ℂ) :
    (run program (L,(v,y))).val = Tape.tab L
      (fun j => ((v.look j (0,0)).1,(y.look j 0)*(v.look j (0,0)).2)) := by
  change (Bill.tab L Datum.blank (fun j => run cell ((L,(v,y)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab L) (funext (fun j => congrArg Bill.val (cell_run L v y j)))

theorem program_work (L : ℕ) (v : Tape (ℕ × ℂ)) (y : Tape ℂ) :
    (run program (L,(v,y))).work = 35*L+4 := by
  change 1+(Bill.tab L Datum.blank (fun j => run cell ((L,(v,y)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((L,(v,y)),j)).work) = (fun _ => 31) := by
    funext j
    exact congrArg Bill.work (cell_run L v y j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_peak (L : ℕ) (v : Tape (ℕ × ℂ)) (y : Tape ℂ) :
    (run program (L,(v,y))).peak = L := by
  change max (max 0 (Bill.tab L Datum.blank
    (fun j => run cell ((L,(v,y)),j))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (fun j => (run cell ((L,(v,y)),j)).peak) = (fun _ => 0) := by
    funext j
    exact congrArg Bill.peak (cell_run L v y j)
  rw [h]
  simp

theorem program_valid (L : ℕ) (v : Tape (ℕ × ℂ)) (y : Tape ℂ) :
    (run program (L,(v,y))).valid := by
  change True ∧ (Bill.tab L Datum.blank (fun j => run cell ((L,(v,y)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem input_value {L : ℕ} (v : Fin L → Scalar) (y : Fin L → ℂ) :
    (run program (input v y)).val =
      data (fun j => UniformChirpPointwiseMachine.productScalar (v j) (y j)) := by
  rw [input,program_value]
  unfold data
  dsimp only [Tape.tab,Tape.len]
  congr 1
  funext j
  simp [Tape.look,kernel,j.isLt,encode,
    UniformChirpPointwiseMachine.productScalar,mul_comm]
  rfl

/-- Constant-factor work comparison against the actual source block's charged cost. -/
theorem work_preserved {L : ℕ} (v : Fin L → Scalar) (y : Fin L → ℂ) :
    (run program (input v y)).work ≤ 4*(9*L+9) := by
  rw [input,program_work]
  omega

/-- Agreement concerns the actual bank cells, including their conservative tags. -/
def Represents (L S : ℕ) (v : Tape (ℕ × ℂ)) (s : State) : Prop :=
  v.len = L ∧ ∀ j : Fin L, ∃ z,
    s.scalarHeap (S+j.val) = some z ∧ v.look j.val (0,0) = encode z

/-- The existing seventeen-instruction stage and this typed program agree on
the produced bank. All untouched roles, heaps and outputs retain the source frame. -/
theorem actual_execution {n W L S Q B : ℕ} (x : Fin n → ℂ)
    (v : ℕ → Fin L → Scalar) (y : Fin L → ℂ) (s : State)
    (roles : 0 < W) (source : UniformRolePointwiseMachine.Source W L S v s)
    (prepared : ∀j : Fin L, s.scalarHeap (Q+j.val) =
      some (UniformPairMachine.prepared (y j)))
    (width : s.natReg 103 = L) (base : s.natReg 6026 = S)
    (kernelBase : s.natReg 7300 = Q) (separate : S+L ≤ Q ∨ Q+L ≤ S)
    (kernelFit : Q+L ≤ B) (extent : S+W*L ≤ B) (code : 64 ≤ B)
    (pc : s.pc = 0) (wb : WordBound B s) :
    ∃ u, BoundedExecution UniformRolePointwiseMachine.program n x B s (9*L+9) u ∧
      UniformRolePointwiseMachine.Source W L S (UniformRolePointwiseMachine.multiplied v y) u ∧
      UniformRolePointwiseMachine.Frame S L s u ∧ u.pc = 16 ∧
      Represents L S (run program (input (v 0) y)).val u ∧
      (run program (input (v 0) y)).valid ∧
      (run program (input (v 0) y)).work ≤ 4*(9*L+9) ∧
      (run program (input (v 0) y)).peak ≤ B := by
  obtain ⟨u,hu,values,frame,upc⟩ := UniformRolePointwiseMachine.execution
    x v y s roles source prepared width base kernelBase separate kernelFit extent code pc wb
  refine ⟨u,hu,values,frame,upc,?_,program_valid _ _ _,work_preserved _ _,?_⟩
  · rw [input_value]
    refine ⟨rfl,?_⟩
    intro j
    refine ⟨UniformChirpPointwiseMachine.productScalar (v 0 j) (y j),?_,?_⟩
    · simpa [UniformRolePointwiseMachine.multiplied] using values 0 roles j
    · simp [data,Tape.look,j.isLt]
  · rw [input,program_peak]
    have one : L ≤ W*L := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right L
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt roles))
    omega

end
end ExactFourierCircuits.DFTModelMemoryPointwise
