import UniformActualCalendarBundleAtoms

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRootAtoms
noncomputable section
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformLocalCacheTreeMachine
open UniformCalendarActualAtoms UniformCalendarRefinementActive UniformCalendarAtomCollapse
open UniformGlobalCalendarUnion UniformLocalCacheTiming

variable (n v o R:ℕ)(p:UniformDirectLeafForestData.Parameters)(A t:ℕ)
 {r O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle r O T B D
  (UniformActualCacheRectangleSource.entries n
   (UniformAxisCacheRequestSource.requests (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1))
  (UniformDirectLeafForestRangeSource.nodeRanges p (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 A) s)

def enumeration:Fin (b.events t).length≃ActiveIndex
 (treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)) t:=
 (UniformActualCalendarBundleAtoms.enumeration n p _ A t b).trans
  ((UniformCalendarAtomCollapse.collapse _ (pieces n _) (fun i=>durations_sum n ((preparationEvents (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).get i).event) t).trans
   (UniformCalendarPermutationActive.activeEquiv (root_preparation_perm v o R) t))

lemma descriptor (i:Fin (b.events t).length):
 (treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)).get (enumeration n v o R p A t b i).val=
 (preparationEvents (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).get
  (UniformActualCalendarBundleAtoms.enumeration n p _ A t b i).val.1:=by
 have eq:=UniformCalendarPermutationActive.activeEquiv_get (root_preparation_perm v o R) t
  (UniformCalendarAtomCollapse.collapse _ (pieces n _) (fun j=>durations_sum n ((preparationEvents (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).get j).event) t
   (UniformActualCalendarBundleAtoms.enumeration n p _ A t b i))
 exact eq

end
end ExactFourierCircuits.UniformActualCalendarRootAtoms
