import DFTModelMemoryCopy
import DFTModelAffineCore

set_option autoImplicit false

/-!
# Affine translation of the actual pointwise bank

The input bank carries a prepared offset separately from its homogeneous data
component. This program scales both components by a prepared kernel, without
injecting a prepared value into the left-data type. The physical source bank
and its affine representation remain explicit entry contracts; their production
belongs to the preceding translated stages.
-/
namespace ExactFourierCircuits.DFTModelMemoryAffinePointwise
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
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
      DFTModelAffine.scale)
def cell : Prog false CellInput Datum := .comp (.fork dataRead kernelRead) multiply
def program : Prog false Input (Ty.a Datum) := .tab (.atom .fst) cell

def scaled (z : Datum.T) (y : ℂ) : Datum.T := (z.1,(y*z.2.1,y*z.2.2))
def data {L : ℕ} (z : Fin L → Datum.T) : Tape Datum.T := ⟨L,z⟩
def input {L : ℕ} (z : Fin L → Datum.T) (y : Fin L → ℂ) : Input.T :=
  (L,(data z,DFTModelMemoryPointwise.kernel y))

theorem multiply_run (z : Datum.T) (y : ℂ) :
    run multiply (z,y) = ⟨scaled z y,25,0,True⟩ := by
  simp [multiply,DFTModelAffine.scale,scaled,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]

theorem cell_run (L : ℕ) (z : Tape Datum.T) (y : Tape ℂ) (j : ℕ) :
    run cell ((L,(z,y)),j) =
      ⟨scaled (z.look j (0,(0,0))) (y.look j 0),45,0,True⟩ := by
  simp [cell,dataRead,kernelRead,dataTape,kernelTape,multiply,
    DFTModelAffine.scale,scaled,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem program_value (L : ℕ) (z : Tape Datum.T) (y : Tape ℂ) :
    (run program (L,(z,y))).val = Tape.tab L
      (fun j => scaled (z.look j (0,(0,0))) (y.look j 0)) := by
  change (Bill.tab L Datum.blank (fun j => run cell ((L,(z,y)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab L) (funext (fun j => congrArg Bill.val (cell_run L z y j)))

theorem program_work (L : ℕ) (z : Tape Datum.T) (y : Tape ℂ) :
    (run program (L,(z,y))).work = 49*L+4 := by
  change 1+(Bill.tab L Datum.blank (fun j => run cell ((L,(z,y)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell ((L,(z,y)),j)).work) = (fun _ => 45) := by
    funext j
    exact congrArg Bill.work (cell_run L z y j)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_peak (L : ℕ) (z : Tape Datum.T) (y : Tape ℂ) :
    (run program (L,(z,y))).peak = L := by
  change max (max 0 (Bill.tab L Datum.blank
    (fun j => run cell ((L,(z,y)),j))).peak) 0 = _
  rw [ModelEquivalenceInterpreter.tab_peak]
  have h : (fun j => (run cell ((L,(z,y)),j)).peak) = (fun _ => 0) := by
    funext j
    exact congrArg Bill.peak (cell_run L z y j)
  rw [h]
  simp

theorem program_valid (L : ℕ) (z : Tape Datum.T) (y : Tape ℂ) :
    (run program (L,(z,y))).valid := by
  change True ∧ (Bill.tab L Datum.blank (fun j => run cell ((L,(z,y)),j))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem input_value {L : ℕ} (z : Fin L → Datum.T) (y : Fin L → ℂ) :
    (run program (input z y)).val = data (fun j => scaled (z j) (y j)) := by
  rw [input,program_value]
  unfold data
  dsimp only [Tape.tab,Tape.len]
  congr 1
  funext j
  simp [Tape.look,DFTModelMemoryPointwise.kernel,j.isLt]

theorem work_preserved {L : ℕ} (z : Fin L → Datum.T) (y : Fin L → ℂ) :
    (run program (input z y)).work ≤ 6*(9*L+9) := by
  rw [input,program_work]
  omega

theorem scaled_represents (z : Datum.T) (v : Scalar) (y : ℂ)
    (h : DFTModelAffine.Represents z v) :
    DFTModelAffine.Represents (scaled z y)
      (UniformChirpPointwiseMachine.productScalar v y) := by
  rcases h with ⟨tag,value,prepared⟩
  refine ⟨tag,?_,?_⟩
  · change v.value*y = y*z.2.1+y*z.2.2
    rw [value]
    ring
  · intro hv
    change y*z.2.2 = 0
    rw [prepared hv,mul_zero]

/-- The offset relation is exactly the zero-input baseline relation, before
and after this pointwise stage; homogeneous values need not vanish. -/
theorem scaled_baseline (z : Datum.T) (v₀ : Scalar) (y : ℂ)
    (baseline : v₀.value = z.2.1) :
    (UniformChirpPointwiseMachine.productScalar v₀ y).value = (scaled z y).2.1 := by
  change v₀.value*y = y*z.2.1
  rw [baseline,mul_comm]

def Represents (L S : ℕ) (z : Tape Datum.T) (s : State) : Prop :=
  z.len = L ∧ ∀j : Fin L, ∃v, s.scalarHeap (S+j.val) = some v ∧
    DFTModelAffine.Represents (z.look j.val (0,(0,0))) v

/-- Actual seventeen-instruction execution and actual typed `tab` agree.
The entry relation is over supplied typed bank values, not a host injection
of arbitrary field values into the left-data type. -/
theorem actual_execution {n W L S Q B : ℕ} (x : Fin n → ℂ)
    (v : ℕ → Fin L → Scalar) (z : Fin L → Datum.T) (y : Fin L → ℂ) (s : State)
    (roles : 0 < W) (source : UniformRolePointwiseMachine.Source W L S v s)
    (represented : ∀j, DFTModelAffine.Represents (z j) (v 0 j))
    (prepared : ∀j : Fin L, s.scalarHeap (Q+j.val) =
      some (UniformPairMachine.prepared (y j)))
    (width : s.natReg 103 = L) (base : s.natReg 6026 = S)
    (kernelBase : s.natReg 7300 = Q) (separate : S+L ≤ Q ∨ Q+L ≤ S)
    (kernelFit : Q+L ≤ B) (extent : S+W*L ≤ B) (code : 64 ≤ B)
    (pc : s.pc = 0) (wb : WordBound B s) :
    ∃u, BoundedExecution UniformRolePointwiseMachine.program n x B s (9*L+9) u ∧
      UniformRolePointwiseMachine.Source W L S (UniformRolePointwiseMachine.multiplied v y) u ∧
      UniformRolePointwiseMachine.Frame S L s u ∧ u.pc = 16 ∧
      Represents L S (run program (input z y)).val u ∧
      (run program (input z y)).valid ∧
      (run program (input z y)).work ≤ 6*(9*L+9) ∧
      (run program (input z y)).peak ≤ B := by
  obtain ⟨u,hu,values,frame,upc⟩ := UniformRolePointwiseMachine.execution
    x v y s roles source prepared width base kernelBase separate kernelFit extent code pc wb
  refine ⟨u,hu,values,frame,upc,?_,program_valid _ _ _,work_preserved _ _,?_⟩
  · rw [input_value]
    refine ⟨rfl,?_⟩
    intro j
    refine ⟨UniformChirpPointwiseMachine.productScalar (v 0 j) (y j),?_,?_⟩
    · simpa [UniformRolePointwiseMachine.multiplied] using values 0 roles j
    · simpa [data,Tape.look,j.isLt] using scaled_represents (z j) (v 0 j) (y j) (represented j)
  · rw [input,program_peak]
    have one : L ≤ W*L := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right L
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt roles))
    omega

/-- The same typed result's offset agrees with an actual zero-input bank
execution when the entry offsets agree. No homogeneous component is injected
into the prepared kernel tape. -/
theorem actual_baseline_execution {n W L S Q B : ℕ}
    (v₀ : ℕ → Fin L → Scalar) (z : Fin L → Datum.T) (y : Fin L → ℂ) (s₀ : State)
    (roles : 0 < W) (source : UniformRolePointwiseMachine.Source W L S v₀ s₀)
    (baseline : ∀j, (v₀ 0 j).value = (z j).2.1)
    (prepared : ∀j : Fin L, s₀.scalarHeap (Q+j.val) =
      some (UniformPairMachine.prepared (y j)))
    (width : s₀.natReg 103 = L) (base : s₀.natReg 6026 = S)
    (kernelBase : s₀.natReg 7300 = Q) (separate : S+L ≤ Q ∨ Q+L ≤ S)
    (kernelFit : Q+L ≤ B) (extent : S+W*L ≤ B) (code : 64 ≤ B)
    (pc : s₀.pc = 0) (wb : WordBound B s₀) :
    ∃u₀, BoundedExecution UniformRolePointwiseMachine.program n (fun _ => 0) B
        s₀ (9*L+9) u₀ ∧
      UniformRolePointwiseMachine.Source W L S
        (UniformRolePointwiseMachine.multiplied v₀ y) u₀ ∧
      UniformRolePointwiseMachine.Frame S L s₀ u₀ ∧ u₀.pc = 16 ∧
      ∀j : Fin L, ∃a₀, u₀.scalarHeap (S+j.val) = some a₀ ∧
        a₀.value = ((run program (input z y)).val.look j.val (0,(0,0))).2.1 := by
  obtain ⟨u₀,hu,values,frame,upc⟩ := UniformRolePointwiseMachine.execution
    (fun _ => 0) v₀ y s₀ roles source prepared width base kernelBase separate
    kernelFit extent code pc wb
  refine ⟨u₀,hu,values,frame,upc,?_⟩
  intro j
  refine ⟨UniformChirpPointwiseMachine.productScalar (v₀ 0 j) (y j),?_,?_⟩
  · simpa [UniformRolePointwiseMachine.multiplied] using values 0 roles j
  · rw [input_value]
    simpa [data,Tape.look,j.isLt] using scaled_baseline (z j) (v₀ 0 j) (y j) (baseline j)

/-- An arbitrary tagged affine bank can be saved by the actual copy block.
This is useful beyond the statically prepared kernel-save specialization. -/
theorem actual_copy_execution {n L S Q B : ℕ} (x : Fin n → ℂ)
    (v : Fin L → Scalar) (z : Fin L → Datum.T) (s : State)
    (source : ∀j : Fin L, s.scalarHeap (S+L+j.val) = some (v j))
    (represented : ∀j, DFTModelAffine.Represents (z j) (v j))
    (width : s.natReg 103 = L) (base : s.natReg 6026 = S) (storage : s.natReg 7300 = Q)
    (separate : Q+L ≤ S+L) (sourceFit : S+L+L ≤ B) (storageFit : Q+L ≤ B)
    (code : 15 ≤ B) (pc : s.pc = 0) (wb : WordBound B s) :
    ∃u, BoundedExecution UniformKernelSpectrumCopy.program n x B s (7*L+9) u ∧
      (∀j : Fin L, u.scalarHeap (Q+j.val) = some (v j)) ∧
      UniformKernelSpectrumCopy.Frame Q L s u ∧ u.pc = 14 ∧
      Represents L Q (run (DFTModelMemoryCopy.program Datum) (L,data z)).val u ∧
      (run (DFTModelMemoryCopy.program Datum) (L,data z)).valid ∧
      (run (DFTModelMemoryCopy.program Datum) (L,data z)).work ≤ 2*(7*L+9) ∧
      (run (DFTModelMemoryCopy.program Datum) (L,data z)).peak ≤ B := by
  obtain ⟨u,hu,values,frame,upc⟩ := UniformKernelSpectrumCopy.execution
    x v s source width base storage separate sourceFit storageFit code pc wb
  refine ⟨u,hu,values,frame,upc,?_,DFTModelMemoryCopy.program_valid _ _ _,
    DFTModelMemoryCopy.work_preserved _ _ _,?_⟩
  · change Represents L Q (run (DFTModelMemoryCopy.program Datum) ((data z).len,data z)).val u
    rw [DFTModelMemoryCopy.full_copy]
    refine ⟨rfl,?_⟩
    intro j
    refine ⟨v j,values j,?_⟩
    simpa [data,Tape.look,j.isLt] using represented j
  · rw [DFTModelMemoryCopy.program_peak]
    omega

/-- A typed copy also preserves an existing affine bank representation. -/
theorem copy_represents {L S : ℕ} (z : Tape Datum.T) (s : State)
    (h : Represents L S z s) :
    Represents L S (run (DFTModelMemoryCopy.program Datum) (z.len,z)).val s := by
  rw [DFTModelMemoryCopy.full_copy]
  exact h

end
end ExactFourierCircuits.DFTModelMemoryAffinePointwise
