import UniformActualCalendarPhysicalRefinement
import UniformActualCalendarScan

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBundleRefinement
noncomputable section
open UniformActualCalendarRegistry UniformActualCalendarPhysicalRefinement
open UniformDirectLeafForestData UniformDirectLeafForestState UniformLocalCacheTreeMachine
open UniformAxisCacheRequestSource UniformGlobalCalendarUnion

lemma flatten_records (L:List Scan):
 (Scan.flatten L).records=(L.map Scan.records).flatten:=by
 induction L with
 | nil=>rfl
 | cons a L ih=>simp only[Scan.flatten,Scan.append,List.map_cons,List.flatten_cons,ih]

lemma scan_records {r O T B D:ℕ}{L:List (ℕ×ℕ)}
 {nodes:List UniformCacheRangeSelector.Range}{s:UniformMachine.State}
 (b:Bundle r O T B D L nodes s):
 b.scan.records=L++(List.ofFn (fun i:Fin nodes.length=>
  List.ofFn (fun j:Fin (nodes.get i).count=>(nodes.get i).records j.val))).flatten:=by
 unfold Bundle.scan
 rw[show ∀a b:Scan,(a.append b).records=a.records++b.records from fun _ _=>rfl]
 rw[flatten_records]
 simp only[List.map_ofFn,Function.comp_def,Family.scan]

/-- Record provenance is independent of cached values: the actual Bundle scan
uses precisely the corrected physical bank formula. -/
theorem actual_records (n:ℕ)(p:Parameters)(visits:List Visit)(A:ℕ)
 {r O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle r O T B D (UniformActualCacheRectangleSource.entries n (requests visits))
  (UniformDirectLeafForestRangeSource.nodeRanges p visits A) s):
 b.scan.records=physicalRecords n p visits A:=by
 rw[scan_records]
 apply congrArg (List.append _)
 apply congrArg List.flatten
 apply List.ext_getElem
 · simp only[List.length_ofFn,UniformDirectLeafForestRangeSource.nodeRanges]
 · intro i hi hj
   simp only[List.getElem_ofFn,UniformDirectLeafForestRangeSource.nodeRanges,
    List.get_eq_getElem,UniformActualCalendarForestRegistry.block]
   apply List.ext_getElem
   · simp
   · intro j hj hk
     simp only[List.getElem_ofFn]
     rfl

/-- The registry built from actual caches selects exactly the real original
tree's active occurrences; the bijection is derived, not supplied. -/
def rootEnumeration (n v o R:ℕ)(p:Parameters)(A t:ℕ)
 {r O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle r O T B D
  (UniformActualCacheRectangleSource.entries n (requests (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1))
  (UniformDirectLeafForestRangeSource.nodeRanges p (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 A) s):
 Fin (b.events t).length≃ActiveIndex
  (UniformLocalCacheTiming.treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)) t:=
 (finCongr (congrArg List.length (b.events_scan t))).trans
  ((finCongr (congrArg (fun L=>(scan L t b.scan.make).length) (actual_records n p _ A b))).trans
   (UniformActualCalendarPhysicalRefinement.rootEnumeration n v o R p A t b.scan.make))

end
end ExactFourierCircuits.UniformActualCalendarBundleRefinement
