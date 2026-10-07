import UniformRadixTwoDAG
import UniformLinearMachine
import UniformAssembly

set_option autoImplicit false

/-! The actual printed radix-two records execute in the fixed linear RAM
interpreter. Prepared power outputs occupy a disjoint heap region, using the
raw shared-preparation register references (no free compact-bank copy). Input,
root, power, table producers and output emission are separate charged phases.
The entry certificate contains only these localized initialization facts; it
contains no FFT action, final-state or schedule-validity premise. -/
namespace ExactFourierCircuits.UniformRadixTwoMachine
open UniformMachine UniformPreparationMachine UniformRadixTwoDAG
open OAI.ExactFourier

/-- First address beyond all input and fresh FFT data registers. -/
def prepBase (k : ℕ) : ℕ := width k + count k

/-- Translate a printed coefficient slot to its actual shared-DAG register. -/
def coefficientAddress (k c : ℕ) : ℕ :=
  if h : c < width k then prepBase k + ((powers k).output ⟨c,h⟩).val
  else prepBase k

def rowOf (k : ℕ) : Op ℕ → Row
  | .add a b => ⟨.add,a,b⟩
  | .sub a b => ⟨.sub,a,b⟩
  | .scale c a => ⟨.mul,coefficientAddress k c,a⟩

def row (k : ℕ) (j : Fin (count k)) : Row := rowOf k (instruction k j)

def rows (k : ℕ) : List Row := (List.finRange (count k)).map (row k)

/-- A concrete producer of the three natural fields for each printed row. -/
def encodedTable (k a : ℕ) : Option ℕ :=
  if h : a/3 < count k then
    let r := row k ⟨a/3,h⟩
    if a%3 = 0 then some (opcode r.op)
    else if a%3 = 1 then some r.left else some r.right
  else none

@[simp] theorem rows_length (k : ℕ) : (rows k).length = count k := by simp [rows]

theorem rows_from_records (k : ℕ) : rows k = (records k).map (rowOf k) := by
  simp [rows,records,row,List.map_map,Function.comp_def]

theorem coefficientAddress_ge (k c : ℕ) : prepBase k ≤ coefficientAddress k c := by
  unfold coefficientAddress
  split <;> omega

theorem coefficientAddress_lt (k c : ℕ) :
    coefficientAddress k c < prepBase k + (powers k).length := by
  have hp : 0 < (powers k).length := by rw [powers_length]; omega
  unfold coefficientAddress
  split
  · rename_i hc
    have := ((powers k).output ⟨c,hc⟩).isLt; omega
  · omega

theorem encodedTable_fields (k : ℕ) (j : Fin (count k)) :
    encodedTable k (3*j.val) = some (opcode (row k j).op) ∧
    encodedTable k (3*j.val+1) = some (row k j).left ∧
    encodedTable k (3*j.val+2) = some (row k j).right := by
  have h0 : (3*j.val)/3 = j.val := by omega
  have h1 : (3*j.val+1)/3 = j.val := by omega
  have h2 : (3*j.val+2)/3 = j.val := by omega
  have hm0 : (3*j.val)%3 = 0 := by omega
  have hm1 : (3*j.val+1)%3 = 1 := by omega
  have hm2 : (3*j.val+2)%3 = 2 := by omega
  simp [encodedTable,h0,h1,h2,hm0,hm1,hm2,j.isLt]

theorem row_addresses (k : ℕ) (j : Fin (count k)) :
    (row k j).left < prepBase k+(powers k).length ∧
    (row k j).right < prepBase k+(powers k).length := by
  have hb (r : ℕ) (hr : r ∈ (instruction k j).refs) : r < prepBase k := by
    have h := printed_refs_before k j r hr
    have hj := j.isLt
    unfold prepBase
    omega
  have hp : 0 < (powers k).length := by rw [powers_length]; omega
  cases hg : instruction k j with
  | add a b =>
    have ha := hb a (by simp [hg,Op.refs])
    have hb' := hb b (by simp [hg,Op.refs])
    simpa [row,rowOf,hg] using And.intro (by omega : a < prepBase k+(powers k).length)
      (by omega : b < prepBase k+(powers k).length)
  | sub a b =>
    have ha := hb a (by simp [hg,Op.refs])
    have hb' := hb b (by simp [hg,Op.refs])
    simpa [row,rowOf,hg] using And.intro (by omega : a < prepBase k+(powers k).length)
      (by omega : b < prepBase k+(powers k).length)
  | scale c a =>
    have ha := hb a (by simp [hg,Op.refs])
    simpa [row,rowOf,hg] using And.intro (coefficientAddress_lt k c)
      (by omega : a < prepBase k+(powers k).length)

theorem encodedTable_bound (k a v : ℕ) (h : encodedTable k a = some v) :
    a < 3*count k ∧ v < prepBase k+(powers k).length := by
  unfold encodedTable at h
  split at h
  · rename_i hj
    have ha : a < 3*count k := by omega
    have hr := row_addresses k ⟨a/3,hj⟩
    split at h
    · have he := Option.some.inj h
      subst v
      have hop : opcode (row k ⟨a/3,hj⟩).op ≤ 3 := by
        cases (row k ⟨a/3,hj⟩).op <;> decide
      have hp := powers_length k
      have hw := width_pos k
      exact ⟨ha,by unfold prepBase; omega⟩
    · split at h
      · have he := Option.some.inj h; subst v; exact ⟨ha,hr.1⟩
      · have he := Option.some.inj h; subst v; exact ⟨ha,hr.2⟩
  · contradiction

/-- A concrete integer envelope for all printed data and preparation addresses. -/
def memoryBound (k : ℕ) : ℕ := 4*count k+6*width k+44

theorem memoryBound_phase (k : ℕ) : 4*count k+width k+44 ≤ memoryBound k := by
  unfold memoryBound
  omega

theorem memoryBound_storage (k : ℕ) :
    3*count k ≤ memoryBound k ∧ prepBase k+(powers k).length ≤ memoryBound k := by
  rw [powers_length]
  unfold memoryBound prepBase
  omega

/-- The relocated machine envelope fits in 2k+8 bits, i.e. O(log width). Entry
producers still have to establish this bound for their own complete states. -/
theorem memoryBound_power (k : ℕ) : memoryBound k+31 ≤ 2^(2*k+8) := by
  have hr := register_bound k
  have hw := width_pos k
  have hb : memoryBound k+31 ≤ 256*(width k)^2 := by
    unfold memoryBound
    nlinarith
  have he : 256*(width k)^2 = 2^(2*k+8) := by
    rw [width_eq,pow_add,show 2*k=k*2 by omega,pow_mul]
    norm_num
    ring
  exact hb.trans_eq he

noncomputable section

def dataScalar (v : ℂ) : Scalar := ⟨v,true⟩
def preparedScalar (v : ℂ) : Scalar := ⟨v,false⟩

def leftScalar (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) : Op ℕ → Scalar
  | .add a _ => dataScalar (natValues k omega x a)
  | .sub a _ => dataScalar (natValues k omega x a)
  | .scale c _ => preparedScalar (preparedBank k omega c)

def rightScalar (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) : Op ℕ → Scalar
  | .add _ b => dataScalar (natValues k omega x b)
  | .sub _ b => dataScalar (natValues k omega x b)
  | .scale _ a => dataScalar (natValues k omega x a)

theorem eval_row (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (g : Op ℕ) :
    evalField (rowOf k g).op (leftScalar k omega x g) (rightScalar k omega x g) =
      some (dataScalar (g.evalBank (preparedBank k omega) (natValues k omega x))) := by
  cases g <;> rfl

/-- Localized initialized input/preparation/table facts. These are producer
postconditions, not an assumed circuit action. Other heap entries may be dirty. -/
def Entry (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State) : Prop :=
  s.pc = 0 ∧ s.natReg 0 = count k ∧ s.natReg 9 = width k ∧
  (∀ j : Fin (count k),
    s.natHeap (3*j.val) = some (opcode (row k j).op) ∧
    s.natHeap (3*j.val+1) = some (row k j).left ∧
    s.natHeap (3*j.val+2) = some (row k j).right) ∧
  (∀ i : Fin (width k), s.scalarHeap i.val = some (dataScalar (x i))) ∧
  (∀ c : Fin (width k), s.scalarHeap (coefficientAddress k c.val) =
    some (preparedScalar ((powers k).run (UniformNewton.Preparation.roots omega)
      (powers_admissible k omega) c)))

def Frontier (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (t : ℕ) (s : State) : Prop :=
  s.pc = 3 ∧ s.natReg 0 = count k ∧ s.natReg 1 = t ∧
  s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧ s.natReg 9 = width k+t ∧
  (∀ j : Fin (count k),
    s.natHeap (3*j.val) = some (opcode (row k j).op) ∧
    s.natHeap (3*j.val+1) = some (row k j).left ∧
    s.natHeap (3*j.val+2) = some (row k j).right) ∧
  (∀ a, a < width k+t → s.scalarHeap a = some (dataScalar (natValues k omega x a))) ∧
  (∀ c : Fin (width k), s.scalarHeap (coefficientAddress k c.val) =
    some (preparedScalar (preparedBank k omega c.val)))

theorem initialized_frontier (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State)
    (h : Entry k omega x s) : Frontier k omega x 0 (initialized s) := by
  rcases h with ⟨hp,h0,h9,ht,hi,hc⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [initialized,writeNat,next,hp]
  · simpa [initialized,writeNat,next] using h0
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simp [initialized,writeNat,next]
  · simpa [initialized,writeNat,next] using h9
  · simpa [initialized,writeNat,next] using ht
  · intro a ha
    have hi' := hi ⟨a,by omega⟩
    change s.scalarHeap a = some (dataScalar (natValues k omega x a))
    rw [show natValues k omega x a = x ⟨a,by omega⟩ from natValues_input k omega x ⟨a,by omega⟩]
    exact hi'
  · intro c
    have hc' := hc c
    rw [powers_run] at hc'
    simpa [initialized,writeNat,next,preparedBank_eq k omega c.val c.isLt] using hc'

theorem row_ready (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (j : Fin (count k)) (s : State) (h : Frontier k omega x j.val s) :
    UniformLinearMachine.Ready (row k j) s (leftScalar k omega x (instruction k j))
      (rightScalar k omega x (instruction k j))
      (dataScalar (natValues k omega x (width k+j.val))) := by
  rcases h with ⟨hp,h0,hj,h2,h3,h9,ht,hd,hc⟩
  refine ⟨hp,by simp [hj,h0,j.isLt],h2,h3,?_,?_,?_,?_,?_,?_⟩
  · simpa [hj] using (ht j).1
  · simpa [hj] using (ht j).2.1
  · simpa [hj] using (ht j).2.2
  · have hbefore (r : ℕ) (hr : r ∈ (instruction k j).refs) : r < width k+j.val :=
      printed_refs_before k j r hr
    have hscalar := instruction_scalar_bound k j
    cases hg : instruction k j with
    | add a b =>
      simpa [row,rowOf,hg,leftScalar] using hd a (hbefore a (by simp [hg,Op.refs]))
    | sub a b =>
      simpa [row,rowOf,hg,leftScalar] using hd a (hbefore a (by simp [hg,Op.refs]))
    | scale c a =>
      have hcb : c < width k := hscalar c (by simp [hg,Op.scalars])
      simpa [row,rowOf,hg,leftScalar] using hc ⟨c,hcb⟩
  · have hbefore (r : ℕ) (hr : r ∈ (instruction k j).refs) : r < width k+j.val :=
      printed_refs_before k j r hr
    cases hg : instruction k j with
    | add a b => simpa [row,rowOf,hg,rightScalar] using hd b (hbefore b (by simp [hg,Op.refs]))
    | sub a b => simpa [row,rowOf,hg,rightScalar] using hd b (hbefore b (by simp [hg,Op.refs]))
    | scale c a => simpa [row,rowOf,hg,rightScalar] using hd a (hbefore a (by simp [hg,Op.refs]))
  · rw [printed_gate]
    exact eval_row k omega x _


def advance (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (j : Fin (count k)) (s : State) : State :=
  rowEnd (row k j) s (leftScalar k omega x (instruction k j))
    (rightScalar k omega x (instruction k j))
    (dataScalar (natValues k omega x (width k+j.val)))

theorem advance_frontier (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (j : Fin (count k)) (s : State) (h : Frontier k omega x j.val s) :
    Frontier k omega x (j.val+1) (advance k omega x j s) := by
  rcases h with ⟨hp,h0,hj,h2,h3,h9,ht,hd,hc⟩
  obtain ⟨hp',h0',hj',h2',h3',h9',ht',hd',_,_⟩ :=
    row_frame (row k j) s (leftScalar k omega x (instruction k j))
      (rightScalar k omega x (instruction k j))
      (dataScalar (natValues k omega x (width k+j.val)))
  change Frontier k omega x (j.val+1) (rowEnd _ s _ _ _)
  refine ⟨hp',h0'.trans h0,by omega,h2'.trans h2,h3'.trans h3,by omega,?_,?_,?_⟩
  · simpa [ht'] using ht
  · intro a ha
    rw [hd',h9]
    by_cases he : a = width k+j.val
    · subst a; simp
    · simpa [he] using hd a (by omega)
  · intro c
    rw [hd',h9]
    have hb := coefficientAddress_ge k c.val
    have hjb := j.isLt
    have he : coefficientAddress k c.val ≠ width k+j.val := by unfold prepBase at hb; omega
    simpa [he] using hc c

/-- A printed suffix, retaining the actual global gate numbers. -/
def rowsFrom (k t l : ℕ) (h : t+l ≤ count k) : List Row :=
  List.ofFn (fun j : Fin l => row k ⟨t+j.val,by omega⟩)

theorem rowsFrom_zero (k t : ℕ) (h : t+0 ≤ count k) : rowsFrom k t 0 h = [] := rfl

theorem rowsFrom_succ (k t l : ℕ) (h : t+(l+1) ≤ count k) :
    rowsFrom k t (l+1) h = row k ⟨t,by omega⟩ :: rowsFrom k (t+1) l (by omega) := by
  unfold rowsFrom
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext j
  apply congrArg (row k)
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

def finish (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    (l t : ℕ) → t+l ≤ count k → State → State
  | 0, _, _, s => s
  | l+1, t, h, s => finish k omega x l (t+1) (by omega)
      (advance k omega x ⟨t,by omega⟩ s)

theorem finish_valid (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (l t : ℕ) (hlt : t+l ≤ count k) (s : State) (h : Frontier k omega x t s) :
    UniformLinearMachine.ValidSchedule (rowsFrom k t l hlt) s
        (finish k omega x l t hlt s) ∧
      Frontier k omega x (t+l) (finish k omega x l t hlt s) := by
  induction l generalizing t s with
  | zero => exact ⟨.nil s,h⟩
  | succ l ih =>
    let j : Fin (count k) := ⟨t,by omega⟩
    have hr := row_ready k omega x j s h
    have hf := advance_frontier k omega x j s h
    have hi := ih (t+1) (by omega) (advance k omega x j s) hf
    rw [rowsFrom_succ]
    exact ⟨.cons hr hi.1,by simpa [finish,j,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi.2⟩

def finalState (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State) : State :=
  finish k omega x (count k) 0 (by omega) (initialized s)

theorem compiled_schedule (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State)
    (h : Entry k omega x s) :
    UniformLinearMachine.ValidSchedule (rows k) (initialized s) (finalState k omega x s) ∧
      Frontier k omega x (count k) (finalState k omega x s) := by
  have hv := finish_valid k omega x (count k) 0 (by omega) (initialized s)
    (initialized_frontier k omega x s h)
  have he : rowsFrom k 0 (count k) (by omega) = rows k := by
    simp [rowsFrom,rows,List.ofFn_eq_map]
  simpa only [he,Nat.zero_add,finalState] using hv

/-- The full fixed-interpreter phase, with every dispatched instruction charged.
Preparation and emission costs are intentionally not included in this phase. -/
theorem bounded_interpretation (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ)
    (s : State) (B : ℕ) (h : Entry k omega x s)
    (hB : 4*count k+width k+40 ≤ B) (hb : WordBound B s) :
    BoundedExecution UniformPreparationMachine.program (width k) x B s
      (totalCost (rows k)+5) {finalState k omega x s with pc := 30} ∧
    totalCost (rows k)+5 ≤ 21*count k+5 ∧
    (finalState k omega x s).outputs = s.outputs ∧
    (finalState k omega x s).rootOrders = s.rootOrders := by
  have hi := UniformLinearMachine.interpreted_schedule (width k) x (rows k) (width k) B s
    (finalState k omega x s) (by simpa using hB) h.1
    (by simpa using h.2.1) h.2.2.1 hb (compiled_schedule k omega x s h).1
  exact ⟨hi.1,by simpa using hi.2.1,hi.2.2.1,hi.2.2.2.1⟩


theorem output_address (k : ℕ) (i : Fin (width k)) :
    refNat (output k i) = count k+i.val := by
  cases k with
  | zero => simp only [output,refNat,count,Nat.zero_add]
  | succ k =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [output,Fin.addCases_left]
      change width (k+1)+(nodeFin (k+1) (.add i)).val = count (k+1)+i.val
      rw [nodeFin_add]
      simp only [count,width]
      omega
    · simp only [output,Fin.addCases_right]
      change width (k+1)+(nodeFin (k+1) (.sub i)).val = count (k+1)+(width k+i.val)
      rw [nodeFin_sub]
      simp only [count,width]
      omega

/-- The actual finished heap contains every input and computed node value. -/
def Values (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State) : Prop :=
  ∀ r : Ref k, s.scalarHeap (refNat r) = some (dataScalar (values k omega x r))

/-- Ordered output ports are a contiguous heap segment, including k=0. -/
def Outputs (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State) : Prop :=
  ∀ i : Fin (width k), s.scalarHeap (count k+i.val) = some (dataScalar (run k omega x i))

theorem final_values (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State)
    (h : Entry k omega x s) : Values k omega x (finalState k omega x s) := by
  intro r
  have hv := (compiled_schedule k omega x s h).2.2.2.2.2.2.2.2.1
    (refNat r) (refNat_bound r)
  simpa [natValues_ref] using hv

theorem final_outputs (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (s : State)
    (h : Entry k omega x s) : Outputs k omega x (finalState k omega x s) := by
  intro i
  have hv := final_values k omega x s h (output k i)
  have hr : run k omega x i = values k omega x (output k i) :=
    (runPrefix_correct k omega x (count k) (le_refl _) _
      (refNat_bound (output k i))).trans (natValues_ref k omega x (output k i))
  simpa [output_address,hr] using hv

theorem final_specified_outputs (k : ℕ) (x : Fin (width k) → ℂ) (s : State)
    (h : Entry k (zeta (width k)) x s) :
    ∀ i : Fin (width k), (finalState k (zeta (width k)) x s).scalarHeap (count k+i.val) =
      some (dataScalar ((fourierMatrix (width k)).mulVec x i)) := by
  have ho := final_outputs k (zeta (width k)) x s h
  simpa [Outputs,run_specified] using ho

/-- A fixed literal loop emits the contiguous result segment. Register1 on entry
holds its base; this is exactly the final gate counter of the FFT interpreter. -/
def emissionProgram : Program := [
  .natLiteral 2 0, .natBinary .add 4 1 2, .length 0,
  .natLiteral 2 1, .natLiteral 1 0,
  .branchLT 1 0 6 11, .natBinary .add 3 4 1, .loadScalar 0 3,
  .output 1 0, .natBinary .add 1 1 2, .jump 5, .halt]

/-- This initializer uses the actual .length instruction, not the entry reg0. -/
def emissionInitialized (n : ℕ) (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (writeNat s 2 0) 4 (s.natReg 1)) 0 n) 2 1) 1 0

def emissionEntered (s : State) : State := {s with pc := 6}
def emissionPointer (s : State) : State := writeNat (emissionEntered s) 3 (s.natReg 4+s.natReg 1)
def emissionLoaded (s : State) (v : Scalar) : State := writeScalar (emissionPointer s) 0 v

def emissionWritten (s : State) (v : Scalar) : State :=
  {next (emissionLoaded s v) with outputs := Function.update s.outputs (s.natReg 1) (some v.value)}

def emissionAdvanced (s : State) (v : Scalar) : State :=
  {writeNat (emissionWritten s v) 1 (s.natReg 1+1) with pc := 5}

/-- Each iteration charges its branch, address addition, load, output, increment
and backward jump. Prepared scalars are never used as data operands here. -/
theorem emission_row (n base B : ℕ) (x : Fin n → ℂ) (s : State) (v : Scalar)
    (hp : s.pc = 5) (h0 : s.natReg 0 = n) (h1 : s.natReg 1 < n)
    (h2 : s.natReg 2 = 1) (h4 : s.natReg 4 = base)
    (hs : s.scalarHeap (base+s.natReg 1) = some v)
    (hB : base+n+12 ≤ B) (hb : WordBound B s) :
    BoundedRuns emissionProgram n x B s 6 (emissionAdvanced s v) := by
  have hb1 : WordBound B (emissionEntered s) := changePC_bound B s 6 hb (by omega)
  have hb2 : WordBound B (emissionPointer s) := writeNat_bound B (emissionEntered s) 3
    (s.natReg 4+s.natReg 1) hb1 (by simp [emissionEntered]; omega) (by omega)
  have hb3 : WordBound B (emissionLoaded s v) := writeScalar_bound B (emissionPointer s) 0 v
    hb2 (by simp [emissionPointer,emissionEntered,writeNat,next]; omega)
  have hb4 : WordBound B (emissionWritten s v) :=
    emit_bound B (emissionLoaded s v) (s.natReg 1) v.value 9 hb3 (by omega) (by omega)
  have hb5 : WordBound B (writeNat (emissionWritten s v) 1 (s.natReg 1+1)) :=
    writeNat_bound B (emissionWritten s v) 1 (s.natReg 1+1) hb4
      (by simp [emissionWritten,emissionLoaded,emissionPointer,emissionEntered,writeNat,writeScalar,next]; omega)
      (by omega)
  have hb6 : WordBound B (emissionAdvanced s v) := changePC_bound B _ 5 hb5 (by omega)
  refine .next hb ?_ (.next hb1 ?_ (.next hb2 ?_ (.next hb3 ?_ (.next hb4 ?_ (.next hb5 ?_ (.refl hb6))))))
  all_goals simp [step,emissionProgram,emissionEntered,emissionPointer,emissionLoaded,
    emissionWritten,emissionAdvanced,writeNat,writeScalar,next,hp,h0,h1,h2,h4,hs,evalNat]


def EmissionFrontier (n base : ℕ) (v : Fin n → Scalar) (t : ℕ) (s : State) : Prop :=
  s.pc = 5 ∧ s.natReg 0 = n ∧ s.natReg 1 = t ∧ s.natReg 2 = 1 ∧ s.natReg 4 = base ∧
  (∀ i : Fin n, s.scalarHeap (base+i.val) = some (v i)) ∧
  (∀ i : Fin n, i.val < t → s.outputs i.val = some (v i).value)

theorem emission_advance_frontier (n base : ℕ) (v : Fin n → Scalar) (t : ℕ)
    (ht : t < n) (s : State) (h : EmissionFrontier n base v t s) :
    EmissionFrontier n base v (t+1) (emissionAdvanced s (v ⟨t,ht⟩)) := by
  rcases h with ⟨hp,h0,h1,h2,h4,hs,ho⟩
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · simpa [emissionAdvanced,emissionWritten,emissionLoaded,emissionPointer,
      emissionEntered,writeNat,writeScalar,next] using h0
  · simp [emissionAdvanced,writeNat,next,h1]
  · simpa [emissionAdvanced,emissionWritten,emissionLoaded,emissionPointer,
      emissionEntered,writeNat,writeScalar,next] using h2
  · simpa [emissionAdvanced,emissionWritten,emissionLoaded,emissionPointer,
      emissionEntered,writeNat,writeScalar,next] using h4
  · simpa [emissionAdvanced,emissionWritten,emissionLoaded,emissionPointer,
      emissionEntered,writeNat,writeScalar,next] using hs
  · intro i hi
    change Function.update s.outputs (s.natReg 1) (some (v ⟨t,ht⟩).value) i.val = _
    rw [h1]
    by_cases he : i.val = t
    · have hie : i = ⟨t,ht⟩ := Fin.ext he
      subst i; simp
    · simpa [he] using ho i (by omega)

def emissionFinish (n base : ℕ) (v : Fin n → Scalar) :
    (l t : ℕ) → t+l ≤ n → State → State
  | 0, _, _, s => s
  | l+1,t,h,s => emissionFinish n base v l (t+1) (by omega)
      (emissionAdvanced s (v ⟨t,by omega⟩))

theorem emission_finish_runs (n base B : ℕ) (x : Fin n → ℂ) (v : Fin n → Scalar)
    (l t : ℕ) (hlt : t+l ≤ n) (s : State)
    (h : EmissionFrontier n base v t s) (hB : base+n+12 ≤ B) (hb : WordBound B s) :
    BoundedRuns emissionProgram n x B s (6*l) (emissionFinish n base v l t hlt s) ∧
    EmissionFrontier n base v (t+l) (emissionFinish n base v l t hlt s) := by
  induction l generalizing t s with
  | zero => exact ⟨.refl hb,h⟩
  | succ l ih =>
    let i : Fin n := ⟨t,by omega⟩
    have hr := emission_row n base B x s (v i) h.1 h.2.1 (by rw [h.2.2.1]; omega)
      h.2.2.2.1 h.2.2.2.2.1 (by simpa [h.2.2.1] using h.2.2.2.2.2.1 i) hB hb
    have hf := emission_advance_frontier n base v t i.isLt s h
    have hi := ih (t+1) (by omega) (emissionAdvanced s (v i)) hf hr.final_bound
    refine ⟨?_,?_⟩
    · simpa [emissionFinish,i,Nat.mul_add,Nat.add_comm] using hr.trans hi.1
    · simpa [emissionFinish,i,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi.2

/-- Five charged setup instructions establish the loop counters and result base. -/
theorem emission_startup (n base B : ℕ) (x : Fin n → ℂ) (v : Fin n → Scalar)
    (s : State) (hp : s.pc = 0) (h1 : s.natReg 1 = base)
    (hs : ∀ i : Fin n, s.scalarHeap (base+i.val) = some (v i))
    (hB : base+n+12 ≤ B) (hb : WordBound B s) :
    BoundedRuns emissionProgram n x B s 5 (emissionInitialized n s) ∧
    EmissionFrontier n base v 0 (emissionInitialized n s) := by
  let s1 := writeNat s 2 0
  let s2 := writeNat s1 4 base
  let s3 := writeNat s2 0 n
  let s4 := writeNat s3 2 1
  let s5 := writeNat s4 1 0
  have hb1 := writeNat_bound B s 2 0 hb (by omega) (by omega)
  have hb2 := writeNat_bound B s1 4 base hb1 (by simp [s1,writeNat,next,hp]; omega) (by omega)
  have hb3 := writeNat_bound B s2 0 n hb2 (by simp [s2,s1,writeNat,next,hp]; omega) (by omega)
  have hb4 := writeNat_bound B s3 2 1 hb3 (by simp [s3,s2,s1,writeNat,next,hp]; omega) (by omega)
  have hb5 := writeNat_bound B s4 1 0 hb4 (by simp [s4,s3,s2,s1,writeNat,next,hp]; omega) (by omega)
  refine ⟨?_,?_⟩
  · have he : s5 = emissionInitialized n s := by simp only [s5,s4,s3,s2,s1,emissionInitialized,h1]
    rw [← he]
    refine .next hb ?_ (.next hb1 ?_ (.next hb2 ?_ (.next hb3 ?_ (.next hb4 ?_ (.refl hb5)))))
    all_goals simp [step,emissionProgram,s1,s2,s3,s4,s5,writeNat,next,hp,h1,evalNat]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simp [emissionInitialized,writeNat,next,hp]
    · simp [emissionInitialized,writeNat,next]
    · simp [emissionInitialized,writeNat,next]
    · simp [emissionInitialized,writeNat,next]
    · simp [emissionInitialized,writeNat,next,h1]
    · simpa [emissionInitialized,writeNat,next,h1] using hs
    · intro i hi; omega

theorem emission_finish_frames (n base : ℕ) (v : Fin n → Scalar)
    (l t : ℕ) (h : t+l ≤ n) (s : State) :
    (emissionFinish n base v l t h s).natHeap = s.natHeap ∧
    (emissionFinish n base v l t h s).scalarHeap = s.scalarHeap ∧
    (emissionFinish n base v l t h s).rootOrders = s.rootOrders := by
  induction l generalizing t s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ l ih =>
    have hi := ih (t+1) (by omega) (emissionAdvanced s (v ⟨t,by omega⟩))
    simpa [emissionFinish,emissionAdvanced,emissionWritten,emissionLoaded,
      emissionPointer,emissionEntered,writeNat,writeScalar,next] using hi

/-- A complete fixed emission phase, including startup and halt. -/
theorem emission_execution (n base B : ℕ) (x : Fin n → ℂ) (v : Fin n → Scalar)
    (s : State) (hp : s.pc = 0) (h1 : s.natReg 1 = base)
    (hs : ∀ i : Fin n, s.scalarHeap (base+i.val) = some (v i))
    (hB : base+n+12 ≤ B) (hb : WordBound B s) :
    ∃ u, BoundedExecution emissionProgram n x B s (6*n+7) u ∧
      (∀ i : Fin n, u.outputs i.val = some (v i).value) ∧
      u.rootOrders = s.rootOrders ∧ u.scalarHeap = s.scalarHeap := by
  have hstart := emission_startup n base B x v s hp h1 hs hB hb
  let u := emissionFinish n base v n 0 (by omega) (emissionInitialized n s)
  have hrows := emission_finish_runs n base B x v n 0 (by omega) (emissionInitialized n s)
    hstart.2 hB hstart.1.final_bound
  have hu : EmissionFrontier n base v n u := by simpa [u] using hrows.2
  have hbfinal : WordBound B u := hrows.1.final_bound
  have hexit : BoundedExecution emissionProgram n x B u 2 {u with pc := 11} := by
    refine .next hbfinal ?_ (.halt (changePC_bound B u 11 hbfinal (by omega)) ?_)
    · simp [step,emissionProgram,hu.1,hu.2.1,hu.2.2.1]
    · simp [step,emissionProgram]
  refine ⟨{u with pc := 11},?_,?_,?_,?_⟩
  · convert hstart.1.executes (hrows.1.executes hexit) using 1; omega
  · intro i
    exact hu.2.2.2.2.2.2 i (by have := i.isLt; omega)
  · have hf := (emission_finish_frames n base v n 0 (by omega) (emissionInitialized n s)).2.2
    simpa [u,emissionInitialized,writeNat,next] using hf
  · have hf := (emission_finish_frames n base v n 0 (by omega) (emissionInitialized n s)).2.1
    simpa [u,emissionInitialized,writeNat,next] using hf


/-- Two actual charged execution stages, with a PC-reset marking the handoff.
The assembled theorem below charges that handoff as a literal jump. -/
theorem staged_specified (k : ℕ) (x : Fin (width k) → ℂ) (s : State) (B : ℕ)
    (h : Entry k (zeta (width k)) x s) (hB : 4*count k+width k+44 ≤ B)
    (hb : WordBound B s) :
    ∃ v,
      BoundedExecution UniformPreparationMachine.program (width k) x B s
        (totalCost (rows k)+5) {finalState k (zeta (width k)) x s with pc := 30} ∧
      BoundedExecution emissionProgram (width k) x B
        {finalState k (zeta (width k)) x s with pc := 0} (6*width k+7) v ∧
      ComputesDFT (width k) x v ∧ v.rootOrders = s.rootOrders ∧
      totalCost (rows k)+6*width k+12 ≤ 21*count k+6*width k+12 := by
  have hi := bounded_interpretation k (zeta (width k)) x s B h (by omega) hb
  have hf := (compiled_schedule k (zeta (width k)) x s h).2
  have hcounter : (finalState k (zeta (width k)) x s).natReg 1 = count k := hf.2.2.1
  have hheap := final_specified_outputs k x s h
  have hentrybound := changePC_bound B {finalState k (zeta (width k)) x s with pc := 30} 0
    hi.1.final_bound (by omega)
  obtain ⟨v,hv,ho,hr,_⟩ := emission_execution (width k) (count k) B x
    (fun i => dataScalar ((fourierMatrix (width k)).mulVec x i))
    {finalState k (zeta (width k)) x s with pc := 0} rfl hcounter hheap (by omega) hentrybound
  refine ⟨v,hi.1,hv,ho,hr.trans hi.2.2.2,?_⟩
  have hc := totalCost_bound (rows k)
  rw [rows_length] at hc
  omega

/-- Interpreter halt and emitter halt become charged continuation jumps;
a final literal halt terminates the combined program. -/
def executionProgram : Program :=
  UniformAssembly.embed
    (UniformPreparationMachine.program.map (UniformAssembly.relocate 0 31))
    emissionProgram [.halt] 43

theorem executionProgram_length : executionProgram.length = 44 := by
  simp [executionProgram,UniformAssembly.embed,UniformPreparationMachine.program,emissionProgram]

theorem interpretation_code : UniformAssembly.CodeAt UniformPreparationMachine.program executionProgram 0 31 := by
  intro i hi
  change ((UniformPreparationMachine.program.map (UniformAssembly.relocate 0 31) ++
      emissionProgram.map (UniformAssembly.relocate 31 43)) ++ [.halt])[0+i]? = _
  rw [Nat.zero_add,List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi)]
  simp only [List.getElem?_map]

theorem emission_code : UniformAssembly.CodeAt emissionProgram executionProgram 31 43 := by
  have hc := UniformAssembly.embed_code
    (UniformPreparationMachine.program.map (UniformAssembly.relocate 0 31)) emissionProgram [.halt] 43
  have hp : (UniformPreparationMachine.program.map (UniformAssembly.relocate 0 31)).length = 31 := by rfl
  rw [hp] at hc
  exact hc

/-- A single fixed literal program executes and emits this FFT topology. Entry
facts are still the charged producer postconditions: no initialization/root/
power/table producer cost is silently included in the displayed phase bound. -/
theorem execution_specified (k : ℕ) (x : Fin (width k) → ℂ) (s : State) (B : ℕ)
    (h : Entry k (zeta (width k)) x s) (hB : 4*count k+width k+44 ≤ B)
    (hb : WordBound B s) :
    ∃ v,
      BoundedExecution executionProgram (width k) x (B+31) s
        (totalCost (rows k)+6*width k+13) v ∧
      ComputesDFT (width k) x v ∧ v.rootOrders = s.rootOrders ∧
      totalCost (rows k)+6*width k+13 ≤ 21*count k+6*width k+13 := by
  obtain ⟨v,hi,he,ho,hr,hcost⟩ := staged_specified k x s B h hB hb
  have hip := UniformAssembly.BoundedExecution.placed interpretation_code
    (by omega : 0+B ≤ B+31) (by omega : 31 ≤ B+31) hi
  have hep := UniformAssembly.BoundedExecution.placed emission_code
    (by omega : 31+B ≤ B+31) (by omega : 43 ≤ B+31) he
  have hip' : BoundedRuns executionProgram (width k) x (B+31) s
      (totalCost (rows k)+5) {finalState k (zeta (width k)) x s with pc := 31} := by
    simpa [UniformAssembly.placed] using hip
  have hep' : BoundedRuns executionProgram (width k) x (B+31)
      {finalState k (zeta (width k)) x s with pc := 31} (6*width k+7) {v with pc := 43} := by
    simpa [UniformAssembly.placed] using hep
  have hhalt : BoundedExecution executionProgram (width k) x (B+31) {v with pc := 43} 1
      {v with pc := 43} := .halt hep'.final_bound (by
        simp [step,executionProgram,UniformAssembly.embed,
          UniformPreparationMachine.program,emissionProgram])
  refine ⟨{v with pc := 43},?_,ho,hr,by omega⟩
  convert hip'.executes (hep'.executes hhalt) using 1; omega


/-- Semantic post-state of the charged producers. Its preparation region stores
all registers of the shared power DAG, not merely hypothetical scalar outputs.
This definition is not an execution from UniformMachine.initial. -/
def loadedHeap (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (a : ℕ) : Option Scalar :=
  if h : a < width k then some (dataScalar (x ⟨a,h⟩))
  else if prepBase k ≤ a then
    if h : a-prepBase k < (powers k).length then
      some (preparedScalar ((powers k).program.run (UniformNewton.Preparation.roots omega)
        (powers_admissible k omega) ⟨a-prepBase k,h⟩))
    else none
  else none

def entryState (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) : State :=
  ⟨0,(fun r => if r = 0 then count k else if r = 9 then width k else 0),
    (fun _ => Scalar.zero),encodedTable k,loadedHeap k omega x,(fun _ => none),[width k]⟩

theorem entryState_ready (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    Entry k omega x (entryState k omega x) := by
  refine ⟨rfl,by simp [entryState],by simp [entryState],encodedTable_fields k,?_,?_⟩
  · intro i
    simp [entryState,loadedHeap,i.isLt]
  · intro c
    have hcn : ¬coefficientAddress k c.val < width k := by
      have hbase := coefficientAddress_ge k c.val
      unfold prepBase at hbase
      omega
    change loadedHeap k omega x (coefficientAddress k c.val) = _
    rw [loadedHeap,dite_eq_right hcn,ite_eq_left (coefficientAddress_ge k c.val)]
    rw [coefficientAddress,dite_eq_left c.isLt,Nat.add_sub_cancel_left]
    simp only [dite_eq_left ((powers k).output c).isLt]
    rfl

theorem loadedHeap_bound (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) (a : ℕ)
    (v : Scalar) (h : loadedHeap k omega x a = some v) :
    a < prepBase k+(powers k).length := by
  have hp : 0 < (powers k).length := by rw [powers_length]; omega
  unfold loadedHeap at h
  split at h
  · rename_i ha
    unfold prepBase
    omega
  · split at h
    · split at h
      · omega
      · contradiction
    · contradiction

theorem entryState_wordBound (k : ℕ) (omega : ℂ) (x : Fin (width k) → ℂ) :
    WordBound (memoryBound k) (entryState k omega x) := by
  refine ⟨by simp [entryState,memoryBound],?_,?_,?_,?_,?_⟩
  · intro r
    simp only [entryState]
    split_ifs <;> unfold memoryBound <;> omega
  · intro a v h
    have he := encodedTable_bound k a v h
    have hm := memoryBound_storage k
    exact ⟨by omega,by omega⟩
  · intro a v h
    have he := loadedHeap_bound k omega x a v h
    have hm := memoryBound_storage k
    omega
  · intro a v h
    simp [entryState] at h
  · intro d h
    simp only [entryState,List.mem_singleton] at h
    subst d
    unfold memoryBound
    omega

/-- Closed execution-phase theorem from the explicit producer post-state.
Only the producer executions/costs remain outside this theorem. -/
theorem prepared_state_execution (k : ℕ) (x : Fin (width k) → ℂ) :
    ∃ v,
      BoundedExecution executionProgram (width k) x (memoryBound k+31)
        (entryState k (zeta (width k)) x) (totalCost (rows k)+6*width k+13) v ∧
      ComputesDFT (width k) x v ∧ v.rootOrders = [width k] ∧
      totalCost (rows k)+6*width k+13 ≤ 21*count k+6*width k+13 := by
  exact execution_specified k x (entryState k (zeta (width k)) x) (memoryBound k)
    (entryState_ready k _ x) (memoryBound_phase k) (entryState_wordBound k _ x)

end
end ExactFourierCircuits.UniformRadixTwoMachine
