import UniformRadixTwoMachine

set_option autoImplicit false

/-! Heap-only helpers run inside the original input context. The local array
width is supplied through registers and tables, rather than changing the global
length seen by input/output instructions. -/
namespace ExactFourierCircuits.UniformContext
open UniformMachine

/-- Precisely the instructions whose semantics do not inspect the ambient input. -/
def instructionFree : Instruction → Bool
  | .length .. | .input .. | .output .. => false
  | _ => true

def ContextFree (p : Program) : Prop := ∀ i ∈ p, instructionFree i = true

noncomputable section

theorem step_same (p : Program) (hp : ContextFree p)
    (n : ℕ) (x : Fin n → ℂ) (m : ℕ) (y : Fin m → ℂ) (s : State) :
    step p n x s = step p m y s := by
  cases hf : p[s.pc]? with
  | none => simp [step,hf]
  | some i =>
    have hi := hp i (List.mem_of_getElem? hf)
    cases i <;> simp only [instructionFree,Bool.false_eq_true] at hi
    all_goals simp only [step,hf]

theorem execution {p : Program} (hp : ContextFree p) {n m t : ℕ}
    {x : Fin n → ℂ} (y : Fin m → ℂ) {s u : State}
    (h : Executes p n x s t u) : Executes p m y s t u := by
  induction h with
  | halt hs => exact .halt ((step_same p hp m y n x _).trans hs)
  | next hs _ ih => exact .next ((step_same p hp m y n x _).trans hs) ih

theorem bounded_execution {p : Program} (hp : ContextFree p) {n m B t : ℕ}
    {x : Fin n → ℂ} (y : Fin m → ℂ) {s u : State}
    (h : BoundedExecution p n x B s t u) : BoundedExecution p m y B s t u := by
  induction h with
  | halt hb hs => exact .halt hb ((step_same p hp m y n x _).trans hs)
  | next hb hs _ ih => exact .next hb ((step_same p hp m y n x _).trans hs) ih

theorem runs {p : Program} (hp : ContextFree p) {n m t : ℕ}
    {x : Fin n → ℂ} (y : Fin m → ℂ) {s u : State}
    (h : Runs p n x s t u) : Runs p m y s t u := by
  induction h with
  | refl s => exact .refl s
  | next hs _ ih => exact .next ((step_same p hp m y n x _).trans hs) ih

theorem bounded_runs {p : Program} (hp : ContextFree p) {n m B t : ℕ}
    {x : Fin n → ℂ} (y : Fin m → ℂ) {s u : State}
    (h : BoundedRuns p n x B s t u) : BoundedRuns p m y B s t u := by
  induction h with
  | refl hb => exact .refl hb
  | next hb hs _ ih => exact .next hb ((step_same p hp m y n x _).trans hs) ih

end

theorem preparation_contextFree : ContextFree UniformPreparationMachine.program := by
  simp [ContextFree,UniformPreparationMachine.program,instructionFree]

noncomputable section

/-- Actual printed FFT interpretation inside an arbitrary enclosing input
context. Initialized local heap facts and all producer costs remain explicit. -/
theorem fft_in_context (k : ℕ) (omega : ℂ)
    (x : Fin (UniformRadixTwoDAG.width k) → ℂ) (n : ℕ) (y : Fin n → ℂ)
    (s : State) (B : ℕ) (h : UniformRadixTwoMachine.Entry k omega x s)
    (hB : 4*UniformRadixTwoDAG.count k+UniformRadixTwoDAG.width k+40 ≤ B)
    (hb : WordBound B s) :
    BoundedExecution UniformPreparationMachine.program n y B s
      (UniformPreparationMachine.totalCost (UniformRadixTwoMachine.rows k)+5)
      {UniformRadixTwoMachine.finalState k omega x s with pc := 30} :=
  bounded_execution preparation_contextFree y
    (UniformRadixTwoMachine.bounded_interpretation k omega x s B h hB hb).1

/-- Its specified local Fourier result still inhabits the heap; the ambient
input vector cannot alter it through this context-free interpreter. -/
theorem fft_heap_in_context (k : ℕ)
    (x : Fin (UniformRadixTwoDAG.width k) → ℂ) (n : ℕ) (y : Fin n → ℂ)
    (s : State) (B : ℕ) (h : UniformRadixTwoMachine.Entry k (OAI.ExactFourier.zeta
      (UniformRadixTwoDAG.width k)) x s)
    (hB : 4*UniformRadixTwoDAG.count k+UniformRadixTwoDAG.width k+40 ≤ B)
    (hb : WordBound B s) :
    BoundedExecution UniformPreparationMachine.program n y B s
      (UniformPreparationMachine.totalCost (UniformRadixTwoMachine.rows k)+5)
      {UniformRadixTwoMachine.finalState k (OAI.ExactFourier.zeta
        (UniformRadixTwoDAG.width k)) x s with pc := 30} ∧
    ∀ i : Fin (UniformRadixTwoDAG.width k),
      (UniformRadixTwoMachine.finalState k (OAI.ExactFourier.zeta
        (UniformRadixTwoDAG.width k)) x s).scalarHeap (UniformRadixTwoDAG.count k+i.val) =
        some (UniformRadixTwoMachine.dataScalar
          ((OAI.ExactFourier.fourierMatrix (UniformRadixTwoDAG.width k)).mulVec x i)) :=
  ⟨fft_in_context k _ x n y s B h hB hb,UniformRadixTwoMachine.final_specified_outputs k x s h⟩

end
end ExactFourierCircuits.UniformContext
