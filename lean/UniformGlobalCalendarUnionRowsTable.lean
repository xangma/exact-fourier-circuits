import UniformGlobalCalendarUnionRowsLoop

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarUnionRows
open UniformMachine
noncomputable section

lemma writeRows_low (O used : ℕ) (records : ℕ → ℕ × ℕ) (j fuel : ℕ)
 (heap : ℕ → Option ℕ) (a : ℕ) (ha : a < O+3*(used+j)) :
 writeRows O used records j fuel heap a = heap a := by
 induction fuel generalizing j heap with
 | zero => rfl
 | succ fuel ih =>
   rw [writeRows,ih _ _ (by omega)]
   simp (disch := omega) [storeRow]

/-- Every printed row retains both actual endpoints and an explicit coefficient1. -/
theorem writeRows_get (O used : ℕ) (records : ℕ → ℕ × ℕ) (j fuel : ℕ)
 (heap : ℕ → Option ℕ) (i : ℕ) (lo : j ≤ i) (hi : i < j+fuel) :
 writeRows O used records j fuel heap (O+3*(used+i)) = some (records i).1 ∧
 writeRows O used records j fuel heap (O+3*(used+i)+1) = some (records i).2 ∧
 writeRows O used records j fuel heap (O+3*(used+i)+2) = some 1 := by
 induction fuel generalizing j heap with
 | zero => omega
 | succ fuel ih =>
   by_cases same : i=j
   · subst i
     simp only [writeRows]
     rw [writeRows_low _ _ _ _ _ _ _ (by omega),writeRows_low _ _ _ _ _ _ _ (by omega),
      writeRows_low _ _ _ _ _ _ _ (by omega)]
     simp (disch := omega) [storeRow]
   · exact ih (j+1) (storeRow O (used+j) (records j).1 (records j).2 heap) (by omega) (by omega)

lemma program_natOnly : ∀ ins ∈ program, UniformLocalRectangleDescriptors.NatOnly ins := by
 have all : program.all (fun ins => decide (UniformLocalRectangleDescriptors.NatOnly ins)) = true := by decide
 exact fun ins hi => of_decide_eq_true ((List.all_eq_true.mp all) ins hi)

theorem execution_scalarFrame {n B ticks : ℕ} {x : Fin n → ℂ} {s u : State}
 (run : BoundedExecution program n x B s ticks u) : UniformLocalRectangleDescriptors.ScalarFrame s u :=
 UniformLocalRectangleDescriptors.natOnly_execution program_natOnly run.executes

/-- The complete actual printer outputs a three-word matching table suitable
for the real55 constructor, with all endpoint reads and writes charged. -/
theorem execution_table {n P N O used B : ℕ} (x : Fin n → ℂ) (records : ℕ → ℕ × ℕ)
 (s : State) (args : Args P N O used s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 23 ≤ B) (source : Rows P N records s.natHeap)
 (sourceFit : P+2*N ≤ B) (fresh : P+2*N ≤ O)
 (values : ∀ k, k<N → (records k).1 ≤ B ∧ (records k).2 ≤ B)
 (outputFit : O+3*(used+N) ≤ B) :
 ∃ u, BoundedExecution program n x B s (16*N+8) u ∧
 Header P N O (used+N) N u ∧ UniformLocalRectangleDescriptors.ScalarFrame s u ∧
 (∀ i, i<N → u.natHeap (O+3*(used+i)) = some (records i).1 ∧
   u.natHeap (O+3*(used+i)+1) = some (records i).2 ∧
   u.natHeap (O+3*(used+i)+2) = some 1) := by
 obtain ⟨u,run,header,heap⟩ := execution x records s args pc wb code source sourceFit fresh values outputFit
 refine ⟨u,run,header,execution_scalarFrame run,?_⟩
 intro i hi
 rw [heap]
 exact writeRows_get O used records 0 N s.natHeap i (by omega) (by omega)

end
end ExactFourierCircuits.UniformGlobalCalendarUnionRows
