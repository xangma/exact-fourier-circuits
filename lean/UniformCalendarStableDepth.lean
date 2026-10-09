import UniformLocalCacheChronology
import UniformCrossDepthReplayPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarStableDepth
noncomputable section

/-- Stable insertion never changes the occurrence order inside one key. -/
lemma filter_insert {α : Type} (key : α→ℕ) (d : ℕ) (a : α) (L : List α) :
 (L.orderedInsert (fun a b=>key a≤key b) a).filter (fun b=>decide (key b=d))=
 if key a=d then a::L.filter (fun b=>decide (key b=d)) else L.filter (fun b=>decide (key b=d)):=by
 induction L with
 | nil=>by_cases h:key a=d <;>simp[h]
 | cons b L ih=>
  rw[List.orderedInsert_cons]
  by_cases before:key a≤key b
  · rw[ite_eq_left before]
    by_cases h:key a=d <;>simp[h]
  · rw[ite_eq_right before]
    by_cases h:key a=d
    · have ne:key b≠d:=by omega
      simp only[List.filter_cons,show decide (key b=d)=false from decide_eq_false ne,
       Bool.false_eq_true,ite_false,ih,h,ite_true]
    · simp only[List.filter_cons,ih,h,ite_false]

lemma filter_sort {α : Type} (key : α→ℕ) (d : ℕ) (L : List α) :
 (L.insertionSort (fun a b=>key a≤key b)).filter (fun b=>decide (key b=d))=
 L.filter (fun b=>decide (key b=d)):=by
 induction L with
 | nil=>rfl
 | cons a L ih=>
  rw[List.insertionSort_cons,filter_insert,ih]
  by_cases h:key a=d <;>simp[h]

/-- The real unsorted physical depth bucket is exactly the standard rendered
stable depth bucket, not merely a permutation with the same whole action. -/
theorem activeBuckets_eq {r n t : ℕ} (p : UniformReplayPrint.Program r n t)
 (enabled : Bool) (H : ℕ) :
 UniformCrossDepthReplayPreparation.activeBuckets p enabled H=
 UniformDAGLayers.depthBuckets (UniformDAGLayers.natSweep p enabled) (UniformDAGLayers.natLevel p) H:=by
 rw[UniformCrossDepthReplayPreparation.depthBuckets_ofFn]
 apply congrArg List.ofFn
 funext d
 exact (filter_sort (fun s:UniformReplayPrint.ShearCode ℕ r=>UniformDAGLayers.natLevel p s.dst)
  d.val (UniformDAGLayers.natSweep p enabled)).symm

theorem bucket_at {r n t : ℕ} (p : UniformReplayPrint.Program r n t)
 (enabled : Bool) (H d : ℕ) (bound : d≤H) :
 ((UniformDAGLayers.depthBuckets (UniformDAGLayers.natSweep p enabled)
  (UniformDAGLayers.natLevel p) H)[d]?).getD []=
 UniformCrossDepthReplayPreparation.bucket p enabled d:=by
 rw[←activeBuckets_eq p enabled H]
 simp only[UniformCrossDepthReplayPreparation.activeBuckets]
 rw[List.getElem?_eq_getElem (by simp only[List.length_ofFn];omega)]
 simp only[Option.getD_some,List.getElem_ofFn]

end
end ExactFourierCircuits.UniformCalendarStableDepth
