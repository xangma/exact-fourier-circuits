import UniformActualCalendarAtomRecords
import UniformCalendarScanActive

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarPhysicalRefinement
noncomputable section
open UniformLocalCacheTreeMachine UniformDirectLeafForestData UniformAxisCacheRequestSource
open UniformActualCalendarMacroOrder UniformCalendarActualAtoms UniformActualCalendarAtomRecords
open UniformGlobalCalendarDispatch UniformGlobalCalendarUnion UniformActualCalendarRegistry

def physicalRecords (n:ℕ)(p:Parameters)(visits:List Visit)(A:ℕ):List (ℕ×ℕ):=
 UniformActualCacheRectangleSource.entries n (requests visits)++
 (List.ofFn (fun i:Fin visits.length=>UniformActualCalendarForestRegistry.block p visits A i)).flatten

/-- Exact stored timestamp/kind records, in the literal selector's bank order,
are the native1/28 refinement of the real preparation macro events. -/
theorem physical_records (n:ℕ)(p:Parameters)(visits:List Visit)(A:ℕ):
 physicalRecords n p visits A=(preparationEvents visits).flatMap (records n):=by
 unfold physicalRecords preparationEvents
 rw[List.flatMap_append,List.flatMap_map,List.flatMap_assoc]
 apply congrArg₂ List.append
 · unfold UniformActualCacheRectangleSource.entries
   apply congrArg (List.flatMap · (requests visits))
   funext q
   exact (rectangle_records n q).symm
 · have eq:List.ofFn (fun i:Fin visits.length=>UniformActualCalendarForestRegistry.block p visits A i)=
    visits.map (fun q=>(directEvents q).flatMap (records n)):=by
    calc
     _=List.ofFn (fun i:Fin visits.length=>(directEvents (visits.get i)).flatMap (records n)):=by
       apply congrArg List.ofFn
       funext i
       exact forest_block n p visits A i
     _=_:=by
       apply List.ext_getElem
       · simp
       · intro i hi hj
         simp only [List.getElem_ofFn, List.getElem_map, List.get_eq_getElem]
   rw[eq]
   rfl

def scan (L:List (ℕ×ℕ))(tick:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event):List UniformGlobalCalendarDispatch.Event:=
 events 0 0 tick (UniformCalendarScanActive.recordAt L) make 0 L.length

/-- The actual physical record formula determines the original tree's active
occurrences. Address and event factories are retained in the literal scan. -/
def rootEnumeration (n v o R:ℕ)(p:Parameters)(A t:ℕ)
 (make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event):
 Fin (scan (physicalRecords n p (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 A) t make).length≃
 ActiveIndex (UniformLocalCacheTiming.treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)) t:=
 (finCongr (congrArg (fun L=>(scan L t make).length) (physical_records n p _ A))).trans
  (UniformCalendarScanActive.rootEnumeration n v o R t make)

end
end ExactFourierCircuits.UniformActualCalendarPhysicalRefinement
