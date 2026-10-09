import UniformGlobalCalendarFactorMergeLoop
import UniformGlobalDiagonalRowsMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarFactorMerge
open UniformMachine
open UniformPairMachine (prepared)
noncomputable section

lemma mergeHeap_frame (O : ℕ) (f g : ℕ → ℂ) (j fuel : ℕ) (heap : ℕ → Option Scalar)
 (a : ℕ) (outside : a<O+j ∨ O+j+fuel ≤ a) : mergeHeap O f g j fuel heap a=heap a := by
 induction fuel generalizing j heap with
 | zero => rfl
 | succ fuel ih =>
   rw [mergeHeap,ih _ _ (by omega)]
   simp (disch := omega) [storeProduct]

lemma mergeHeap_get (O : ℕ) (f g : ℕ → ℂ) (j fuel : ℕ) (heap : ℕ → Option Scalar)
 (i : ℕ) (lo : j ≤ i) (hi : i<j+fuel) :
 mergeHeap O f g j fuel heap (O+i)=some (prepared (f i*g i)) := by
 induction fuel generalizing j heap with
 | zero => omega
 | succ fuel ih =>
   by_cases same : i=j
   · subst i
     rw [mergeHeap,mergeHeap_frame _ _ _ _ _ _ _ (by omega)]
     simp [storeProduct]
   · exact ih (j+1) (storeProduct O j f g heap) (by omega) (by omega)

/-- A genuine produced nine-lane entry supplies the charged merger's scalar reads. -/
def entryValues (entry : UniformGlobalDiagonalRowsMachine.Entry) (lane : Fin 9) (j : ℕ) : ℂ :=
 if h : j<entry.radix then entry.value lane ⟨j,h⟩ else 1

lemma produced_factors (entry : UniformGlobalDiagonalRowsMachine.Entry) (lane : Fin 9) (s : State)
 (pool : UniformGlobalDiagonalRowsMachine.Pools [entry] s) :
 Factors (entry.pool+lane.val*entry.radix) entry.radix (entryValues entry lane) s.scalarHeap := by
 intro j hj
 simpa only [entryValues,dite_eq_left hj] using pool entry (by simp) lane ⟨j,hj⟩

/-- The full literal merger consumes actual produced factor cells and preserves
the other eight lanes of the fresh9r pool, plus every cache/source cell. -/
theorem produced_execution {n O B : ℕ} (x : Fin n → ℂ)
 (entry : UniformGlobalDiagonalRowsMachine.Entry) (lane : Fin 9) (g : ℕ → ℂ) (s : State)
 (args : Args entry.pool entry.radix lane.val O s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 15 ≤ B) (pool : UniformGlobalDiagonalRowsMachine.Pools [entry] s)
 (target : Factors O entry.radix g s.scalarHeap)
 (sourceFit : entry.pool+9*entry.radix ≤ B) (fresh : entry.pool+9*entry.radix ≤ O)
 (outputFit : O+entry.radix ≤ B) :
 ∃ u, BoundedExecution program n x B s (9*entry.radix+7) u ∧
 Header entry.pool entry.radix lane.val O entry.radix u ∧
 Factors O entry.radix (fun j => entryValues entry lane j*g j) u.scalarHeap ∧
 (∀ a, a<O ∨ O+entry.radix ≤ a → u.scalarHeap a=s.scalarHeap a) ∧
 u.natHeap=s.natHeap ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs := by
 obtain ⟨u,run,header,heap,nh,roots,outputs⟩ := execution x (entryValues entry lane) g s args pc wb code
  (produced_factors entry lane s pool) target sourceFit fresh lane.isLt outputFit
 refine ⟨u,run,header,?_,?_,nh,roots,outputs⟩
 · intro j hj
   rw [heap]
   exact mergeHeap_get O (entryValues entry lane) g 0 entry.radix s.scalarHeap j (by omega) (by omega)
 · intro a outside
   rw [heap]
   exact mergeHeap_frame O (entryValues entry lane) g 0 entry.radix s.scalarHeap a (by omega)

end
end ExactFourierCircuits.UniformGlobalCalendarFactorMerge
