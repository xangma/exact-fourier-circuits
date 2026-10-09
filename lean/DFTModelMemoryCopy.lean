import DFTModelMemoryPointwise
import UniformKernelSpectrumCopy

set_option autoImplicit false

/-! Functional translation of the actual fifteen-instruction prepared kernel save.
The original bank remains available as the input tape; the saved bank is one fresh tape.
No field arithmetic, roots, flag normalization or mutable-tape atom is introduced. -/
namespace ExactFourierCircuits.DFTModelMemoryCopy
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Input (t : Ty) := p w (Ty.a t)

def cell (t : Ty) : Prog false (p (Input t) w) t :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)

def program (t : Ty) : Prog false (Input t) (Ty.a t) := .tab (.atom .fst) (cell t)

theorem cell_run (t : Ty) (L : ℕ) (v : Tape t.T) (j : ℕ) :
    run (cell t) ((L,v),j) = ⟨v.look j t.blank,7,0,True⟩ := by
  simp [cell,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem program_value (t : Ty) (L : ℕ) (v : Tape t.T) :
    (run (program t) (L,v)).val = Tape.tab L (fun j => v.look j t.blank) := by
  change (Bill.tab L t.blank (fun j => run (cell t) ((L,v),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab L) (funext (fun j => congrArg Bill.val (cell_run t L v j)))

theorem program_work (t : Ty) (L : ℕ) (v : Tape t.T) :
    (run (program t) (L,v)).work = 11*L+4 := by
  change 1+(Bill.tab L t.blank (fun j => run (cell t) ((L,v),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run (cell t) ((L,v),j)).work) = (fun _ => 7) := by
    funext j
    exact congrArg Bill.work (cell_run t L v j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_peak (t : Ty) (L : ℕ) (v : Tape t.T) :
    (run (program t) (L,v)).peak = L := by
  change max (max 0 (Bill.tab L t.blank (fun j => run (cell t) ((L,v),j))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (fun j => (run (cell t) ((L,v),j)).peak) = (fun _ => 0) := by
    funext j
    exact congrArg Bill.peak (cell_run t L v j)
  rw [h]
  simp

theorem program_valid (t : Ty) (L : ℕ) (v : Tape t.T) :
    (run (program t) (L,v)).valid := by
  change True ∧ (Bill.tab L t.blank (fun j => run (cell t) ((L,v),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem full_copy (t : Ty) (v : Tape t.T) : (run (program t) (v.len,v)).val = v := by
  rw [program_value]
  cases v with
  | mk len pos =>
    dsimp only [Tape.tab,Tape.len]
    congr 1
    funext j
    simp [Tape.look,j.isLt]

/-- Preserve the actual source block's work up to a uniform factor of two. -/
theorem work_preserved (t : Ty) (L : ℕ) (v : Tape t.T) :
    (run (program t) (L,v)).work ≤ 2*(7*L+9) := by
  rw [program_work]
  omega

def input {L : ℕ} (v : Fin L → Scalar) : (Input DFTModelMemoryPointwise.Datum).T :=
  (L,DFTModelMemoryPointwise.data v)

theorem input_value {L : ℕ} (v : Fin L → Scalar) :
    (run (program DFTModelMemoryPointwise.Datum) (input v)).val = DFTModelMemoryPointwise.data v := by
  exact full_copy DFTModelMemoryPointwise.Datum (DFTModelMemoryPointwise.data v)

/-- Direct operational correspondence to the actual save-role1 stage. -/
theorem actual_execution {n L S Q B : ℕ} (x : Fin n → ℂ) (v : Fin L → Scalar) (s : State)
    (source : ∀j : Fin L, s.scalarHeap (S+L+j.val) = some (v j))
    (width : s.natReg 103 = L) (base : s.natReg 6026 = S) (storage : s.natReg 7300 = Q)
    (separate : Q+L ≤ S+L) (sourceFit : S+L+L ≤ B) (storageFit : Q+L ≤ B)
    (code : 15 ≤ B) (pc : s.pc = 0) (wb : WordBound B s) :
    ∃ u, BoundedExecution UniformKernelSpectrumCopy.program n x B s (7*L+9) u ∧
      (∀j : Fin L, u.scalarHeap (Q+j.val) = some (v j)) ∧
      UniformKernelSpectrumCopy.Frame Q L s u ∧ u.pc = 14 ∧
      DFTModelMemoryPointwise.Represents L Q
        (run (program DFTModelMemoryPointwise.Datum) (input v)).val u ∧
      (run (program DFTModelMemoryPointwise.Datum) (input v)).valid ∧
      (run (program DFTModelMemoryPointwise.Datum) (input v)).work ≤ 2*(7*L+9) ∧
      (run (program DFTModelMemoryPointwise.Datum) (input v)).peak ≤ B := by
  obtain ⟨u,hu,values,frame,upc⟩ := UniformKernelSpectrumCopy.execution
    x v s source width base storage separate sourceFit storageFit code pc wb
  refine ⟨u,hu,values,frame,upc,?_,program_valid _ _ _,work_preserved _ _ _,?_⟩
  · rw [input_value]
    refine ⟨rfl,?_⟩
    intro j
    refine ⟨v j,values j,?_⟩
    simp [DFTModelMemoryPointwise.data,Tape.look,j.isLt]
  · rw [input,program_peak]
    omega

/-- The actual DFT kernel save has a statically prepared representation, so
its result can feed `Atom.scale` without converting a data-typed value. -/
def preparedInput {L : ℕ} (y : Fin L → ℂ) : (Input sc).T :=
  (L,DFTModelMemoryPointwise.kernel y)

theorem prepared_value {L : ℕ} (y : Fin L → ℂ) :
    (run (program sc) (preparedInput y)).val = DFTModelMemoryPointwise.kernel y := by
  exact full_copy sc (DFTModelMemoryPointwise.kernel y)

theorem actual_prepared_execution {n L S Q B : ℕ} (x : Fin n → ℂ)
    (y : Fin L → ℂ) (s : State)
    (source : ∀j : Fin L, s.scalarHeap (S+L+j.val) =
      some (UniformPairMachine.prepared (y j)))
    (width : s.natReg 103 = L) (base : s.natReg 6026 = S) (storage : s.natReg 7300 = Q)
    (separate : Q+L ≤ S+L) (sourceFit : S+L+L ≤ B) (storageFit : Q+L ≤ B)
    (code : 15 ≤ B) (pc : s.pc = 0) (wb : WordBound B s) :
    ∃ u, BoundedExecution UniformKernelSpectrumCopy.program n x B s (7*L+9) u ∧
      UniformKernelSpectrumCopy.Frame Q L s u ∧ u.pc = 14 ∧
      (∀j : Fin L, u.scalarHeap (Q+j.val) = some (UniformPairMachine.prepared
        ((run (program sc) (preparedInput y)).val.look j.val 0))) ∧
      (run (program sc) (preparedInput y)).valid ∧
      (run (program sc) (preparedInput y)).work ≤ 2*(7*L+9) ∧
      (run (program sc) (preparedInput y)).peak ≤ B := by
  obtain ⟨u,hu,values,frame,upc⟩ := UniformKernelSpectrumCopy.execution
    x (fun j => UniformPairMachine.prepared (y j)) s source width base storage
    separate sourceFit storageFit code pc wb
  refine ⟨u,hu,frame,upc,?_,program_valid _ _ _,work_preserved _ _ _,?_⟩
  · intro j
    rw [prepared_value]
    simpa [DFTModelMemoryPointwise.kernel,Tape.look,j.isLt] using values j
  · rw [preparedInput,program_peak]
    omega

end
end ExactFourierCircuits.DFTModelMemoryCopy
