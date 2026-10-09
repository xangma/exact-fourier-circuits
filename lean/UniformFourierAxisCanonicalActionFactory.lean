import UniformFourierAxisCanonicalAction
import UniformActualCalendarRetainedTreeAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCanonicalActionFactory
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformFourierAxisCommonResult UniformFourierAxisOperationalCases
noncomputable section

/-- One heap-independent ordered Action family, fixed by the original genuine
cache producer, for every axis and clock including inactive epochs. -/
def action (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))
 {s:State}(cache:UniformAxisCacheContents.Contents c n hn j s)(g:ℕ):
 UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events)
  (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix:=by
 classical
 by_cases tree:TreeAt (depth n j) g
 · rw[events,UniformFourierAxisCanonicalEvents.eventsAt_tree _ tree]
   exact UniformActualCalendarRetainedTreeAction.action c n hn j cache g tree
 · by_cases boundary:UniformFourierAxisPrepareBoundary.BoundaryAt (depth n j) g
   · exact UniformFourierAxisCanonicalAction.boundary hn j _ boundary
   · have inactive:2*depth n j+5≤g:=by
      unfold TreeAt at tree
      unfold UniformFourierAxisPrepareBoundary.BoundaryAt at boundary
      omega
     exact UniformFourierAxisCanonicalAction.inactive hn j _ inactive

end
end ExactFourierCircuits.UniformFourierAxisCanonicalActionFactory
