import UniformPairMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformPairDiagonalMachine
open UniformMachine
open UniformPairMachine (Ready prepared product loadedLeft loadedBoth prepared_mul)
noncomputable section

def program : Program :=
  [.loadScalar 2 0,.loadScalar 3 1,.fieldBinary .mul 2 0 2,
   .fieldBinary .mul 3 1 3,.storeScalar 0 2,.storeScalar 1 3,.halt]

theorem program_length : program.length=7 := rfl

theorem contextFree : UniformContext.ContextFree program := by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program]

def scaledLeft (s : State) (c : ℂ) (u v : Scalar) : State :=
  writeScalar (loadedBoth s u v) 2 (product c u)
def scaledBoth (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (scaledLeft s c u v) 3 (product d v)
def storedLeft (s : State) (c d : ℂ) (u v : Scalar) : State :=
  {next (scaledBoth s c d u v) with
    scalarHeap:=Function.update s.scalarHeap (s.natReg 0) (some (product c u))}
def finalState (s : State) (c d : ℂ) (u v : Scalar) : State :=
  { next (storedLeft s c d u v) with
    scalarHeap := Function.update (storedLeft s c d u v).scalarHeap
      (s.natReg 1) (some (product d v)) }

theorem bounded_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (c d : ℂ) (u v : Scalar) (hr : Ready c d u v s)
    (hB : 7≤B) (hs : WordBound B s) :
    BoundedExecution program n x B s 7 (finalState s c d u v) := by
  obtain ⟨hp,hu,hv,hc,hd⟩ := hr
  have h1 := writeScalar_bound B s 2 u hs (by omega)
  have h2 := writeScalar_bound B (loadedLeft s u) 3 v h1
    (by simp [loadedLeft,writeScalar,next,hp];omega)
  have h3 := writeScalar_bound B (loadedBoth s u v) 2 (product c u) h2
    (by simp [loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h4 := writeScalar_bound B (scaledLeft s c u v) 3 (product d v) h3
    (by simp [scaledLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h5 := UniformInPlaceMachine.storeScalar_bound B (scaledBoth s c d u v)
    (s.natReg 0) (product c u) h4
    (by simp [scaledBoth,scaledLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega) (hs.2.1 0)
  have h6 := UniformInPlaceMachine.storeScalar_bound B (storedLeft s c d u v)
    (s.natReg 1) (product d v) h5
    (by simp [storedLeft,scaledBoth,scaledLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega) (hs.2.1 1)
  refine .next hs (u:=loadedLeft s u) ?_ (.next h1 (u:=loadedBoth s u v) ?_
    (.next h2 (u:=scaledLeft s c u v) ?_ (.next h3 (u:=scaledBoth s c d u v) ?_
      (.next h4 (u:=storedLeft s c d u v) ?_ (.next h5 (u:=finalState s c d u v) ?_
        (.halt h6 ?_))))))
  all_goals simp [step,program,finalState,storedLeft,scaledBoth,scaledLeft,loadedBoth,
    loadedLeft,writeScalar,next,hp,hu,hv,hc,hd,prepared_mul]

theorem final_frame (s : State) (c d : ℂ) (u v : Scalar) :
    (finalState s c d u v).natReg=s.natReg ∧ (finalState s c d u v).natHeap=s.natHeap ∧
      (finalState s c d u v).outputs=s.outputs ∧ (finalState s c d u v).rootOrders=s.rootOrders ∧
      ∀ r,r<2 ∨ 4≤r → (finalState s c d u v).scalarReg r=s.scalarReg r := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  have h2 : r≠2 := by omega
  have h3 : r≠3 := by omega
  simp [finalState,storedLeft,scaledBoth,scaledLeft,loadedBoth,loadedLeft,
    writeScalar,next,h2,h3]

theorem final_heap (s : State) (c d : ℂ) (u v : Scalar) :
    (finalState s c d u v).scalarHeap=Function.update
      (Function.update s.scalarHeap (s.natReg 0) (some (product c u)))
        (s.natReg 1) (some (product d v)) := rfl

theorem final_values (s : State) (c d : ℂ) (u v : Scalar) (h : s.natReg 0≠s.natReg 1) :
    (finalState s c d u v).scalarHeap (s.natReg 0)=some (product c u) ∧
      (finalState s c d u v).scalarHeap (s.natReg 1)=some (product d v) := by
  simp [final_heap,h]

theorem untouched (s : State) (c d : ℂ) (u v : Scalar) (i : ℕ)
    (h0 : i≠s.natReg 0) (h1 : i≠s.natReg 1) :
    (finalState s c d u v).scalarHeap i=s.scalarHeap i := by simp [final_heap,h0,h1]

/-- Actual prepared-bank entries survive every pair operation on data heaps≥6. -/
theorem preserves_bank (s : State) (c d : ℂ) (u v : Scalar)
    (h0 : 6 ≤ s.natReg 0) (h1 : 6 ≤ s.natReg 1) (j : Fin 6) :
    (finalState s c d u v).scalarHeap j.val=s.scalarHeap j.val :=
  untouched _ _ _ _ _ _ (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem diagonal_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (c d : ℂ) (u v : Scalar) (hr : Ready c d u v s) (hB : 7≤B) (hs : WordBound B s)
    (h : s.natReg 0≠s.natReg 1) :
    BoundedExecution program n x B s 7 (finalState s c d u v) ∧
      (finalState s c d u v).scalarHeap (s.natReg 0)=
        some ⟨(diagonal c d).mulVec ![u.value,v.value] 0,u.dependent⟩ ∧
      (finalState s c d u v).scalarHeap (s.natReg 1)=
        some ⟨(diagonal c d).mulVec ![u.value,v.value] 1,v.dependent⟩ := by
  have hf := final_values s c d u v h
  refine ⟨bounded_execution n x B s c d u v hr hB hs,?_,?_⟩
  · simpa [diagonal,Matrix.mulVec,dotProduct,Fin.sum_univ_two,product] using hf.1
  · simpa [diagonal,Matrix.mulVec,dotProduct,Fin.sum_univ_two,product] using hf.2

end
end ExactFourierCircuits.UniformPairDiagonalMachine
