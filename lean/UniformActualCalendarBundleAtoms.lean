import UniformCalendarScanAtoms
import UniformActualCalendarBundleRefinement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBundleAtoms
noncomputable section
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformCalendarScanActive
open UniformCalendarScanAtoms UniformCalendarAtomCollapse UniformCalendarRefinementActive
open UniformCalendarActualAtoms UniformCalendarIntervalPartition UniformLocalCacheTreeMachine
open UniformAxisCacheRequestSource UniformGlobalCalendarDispatch UniformGlobalCalendarUnion

variable (n:ℕ)(p:UniformDirectLeafForestData.Parameters)(visits:List Visit)(A t:ℕ)
 {r O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle r O T B D (UniformActualCacheRectangleSource.entries n (requests visits))
  (UniformDirectLeafForestRangeSource.nodeRanges p visits A) s)

lemma events_eq:
 b.events t=events 0 0 t (recordAt (fineRecords n (preparationEvents visits))) b.scan.make 0
  (fineRecords n (preparationEvents visits)).length:=by
 rw[b.events_scan]
 change events 0 0 t (recordAt b.scan.records) b.scan.make 0 b.scan.records.length=_
 exact congrArg (fun L=>events 0 0 t (recordAt L) b.scan.make 0 L.length)
  ((UniformActualCalendarBundleRefinement.actual_records n p visits A b).trans
   (UniformActualCalendarPhysicalRefinement.physical_records n p visits A))

def enumeration:Fin (b.events t).length≃ActiveAtom (preparationEvents visits)
 (pieces n (preparationEvents visits)) t:=
 (finCongr (congrArg List.length (events_eq n p visits A t b))).trans
  (atomEnumeration n (preparationEvents visits) t b.scan.make)

lemma event (i:Fin (b.events t).length):
 (b.events t).get i=b.scan.make
  (UniformCalendarRefinementActive.order n (preparationEvents visits)
   (enumeration n p visits A t b i).val).val
  (t-(((preparationEvents visits).get (enumeration n p visits A t b i).val.1).start+
   prefixDuration (pieces n (preparationEvents visits) (enumeration n p visits A t b i).val.1)
    (enumeration n p visits A t b i).val.2.val)):=by
 have get_cast {α:Type}{xs ys:List α}(eq:xs=ys)(i:Fin xs.length):
  xs.get i=ys.get (finCongr (congrArg List.length eq) i):=by cases eq;rfl
 exact (get_cast (events_eq n p visits A t b) i).trans
  (atom_event n (preparationEvents visits) t b.scan.make
   (finCongr (congrArg List.length (events_eq n p visits A t b)) i))

end
end ExactFourierCircuits.UniformActualCalendarBundleAtoms
