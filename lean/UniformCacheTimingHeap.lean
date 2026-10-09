import UniformCacheTimingNode
import UniformCacheTimingBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingHeap
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformCacheTimingReference UniformCacheTimingBounds
open UniformCacheTimingRows UniformCacheTimingPrefix

lemma value_eq (q : Visit) (child : ℕ) :
 UniformCacheTimingNodeBody.value q child=
 if q.task.width<2 ∨ UniformWorkspacePlanner.selected q.task.width=0
 then UniformLocalCacheTiming.directDuration q.task.width else child+correction q := by
 simp only [UniformCacheTimingNodeBody.value,amounts_eq,correction]

/-- Project one actual reverse-node output onto its duration bank. -/
lemma output_duration (U V T R k N : ℕ) (q : Visit) (heap : ℕ→Option ℕ) (d : ℕ→ℕ)
 (bank:∀j,j<N→heap (U+j)=some (d j)) (index:k<N)
 (parent:k=0 ∨ q.task.parent<k) (separate:U+N ≤ V) (separateStarts:V+N ≤ T)
 (j : ℕ) (hj:j<N) :
 UniformCacheTimingNode.outputHeap U V T R k (d k) (d q.task.parent) q heap (U+j)=
 some (bottomStep k q d j) := by
 have hpref:writePrefixes T ((q.rectangleBase-R)/7) 0 (currentRows q.task) heap (U+j)=some (d j) := by
  rw [writePrefixes_outside _ _ _ _ _ _ (Or.inl (by omega))]
  exact bank j hj
 have par : k=0 ∨ q.task.parent<N:=by omega
 have cross : U+j≠V+k:=by omega
 simp (disch:=omega) only [UniformCacheTimingNode.outputHeap,UniformCacheTimingNodeStore.outputHeap,
  value_eq,bottomStep,Function.update_apply]
 split_ifs <;> simp_all [Function.update_apply]
 all_goals split_ifs <;> rfl

lemma output_correction (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (separate:U+N ≤ V) (_separateStarts:V+N ≤ T) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap (V+k)=some (correction q) := by
 unfold UniformCacheTimingNode.outputHeap UniformCacheTimingNodeStore.outputHeap
 split_ifs <;> simp (disch:=omega) [amounts_eq,correction]

lemma output_correction_other (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (separate:U+N ≤ V) (separateStarts:V+N ≤ T)
 (j : ℕ) (hj:j<N) (ne:j≠k) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap (V+j)=heap (V+j) := by
 unfold UniformCacheTimingNode.outputHeap UniformCacheTimingNodeStore.outputHeap
 split_ifs <;> simp (disch:=omega) only [Function.update_apply,ite_eq_right] <;> rw [writePrefixes_outside _ _ _ _ _ _ (Or.inl (by omega))]

lemma output_prefix (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (separate:U+N ≤ V) (separateStarts:V+N ≤ T)
 (z : ℕ) (hz:z<(currentRows q.task).length) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap
  (T+(q.rectangleBase-R)/7+z)=some (requestPrefix q z) := by
 unfold UniformCacheTimingNode.outputHeap UniformCacheTimingNodeStore.outputHeap
 split_ifs <;> simp (disch:=omega) only [Function.update_apply,ite_eq_right] <;> rw [writePrefixes_inside _ _ _ _ _ z hz] <;>
  simp only [Nat.zero_add,amounts_eq,requestPrefix]

lemma output_prefix_other (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (separate:U+N ≤ V) (separateStarts:V+N ≤ T)
 (a : ℕ) (outside:a<(q.rectangleBase-R)/7 ∨ (q.rectangleBase-R)/7+(currentRows q.task).length ≤ a) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap (T+a)=heap (T+a) := by
 unfold UniformCacheTimingNode.outputHeap UniformCacheTimingNodeStore.outputHeap
 split_ifs <;> simp (disch:=omega) only [Function.update_apply,ite_eq_right] <;> rw [writePrefixes_outside _ _ _ _ _ _ (by omega)]

lemma output_outside (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (a : ℕ)
 (outsideU:a<U ∨ U+N ≤ a) (outsideV:a<V ∨ V+N ≤ a)
 (outsideT:a<T+(q.rectangleBase-R)/7 ∨ T+(q.rectangleBase-R)/7+(currentRows q.task).length ≤ a) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap a=heap a := by
 unfold UniformCacheTimingNode.outputHeap UniformCacheTimingNodeStore.outputHeap
 split_ifs <;> simp (disch:=omega) only [Function.update_apply,ite_eq_right] <;> rw [writePrefixes_outside _ _ _ _ _ _ outsideT]

lemma output_belowU (U V T R k N child old : ℕ) (q : Visit) (heap : ℕ→Option ℕ)
 (index:k<N) (parent:q.task.parent ≤ k) (separate:U+N ≤ V) (separateStarts:V+N ≤ T)
 (a : ℕ) (low:a<U) :
 UniformCacheTimingNode.outputHeap U V T R k child old q heap a=heap a := by
 exact output_outside U V T R k N child old q heap index parent a
  (Or.inl low) (Or.inl (by omega)) (Or.inl (by omega))

end ExactFourierCircuits.UniformCacheTimingHeap
