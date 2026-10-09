import UniformActualCalendarAtomsResult
import UniformFinalAxisCacheBundle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRetainedLocalAction
noncomputable section
open OAI.ExactFourier UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformAllAxisSeedPreparation UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests
open UniformCalendarNativeRootAction UniformFinalAxisCacheBundle

/-- Every local Toeplitz tick is assembled from the genuine retained rectangle
and corrected direct-leaf factories. No action or family premise is required. -/
def action (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))
 {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)(t:ℕ):
 UniformCalendarAxisAction.Action (radix n j) ((reference c n hn j h).events t)
  (UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan (radix n j))
   (NewtonFourier.invH (zeta (radix n j))) (by simp) t).matrix:=by
 have ends:=ends_bound c n hn
 have fits:=axis_fit c n j
 have pool: (parameters c n j).start.pool+9*(parameters c n j).radix*
  UniformDirectLeafForestModel.demand (visits c n j)≤3*slab c n:=
  (forest_bounds c n hn j).1.trans (fits.2.trans (by omega))
 have nat: (parameters c n j).start.permutation+(3*(parameters c n j).radix+11)*
  UniformDirectLeafForestModel.demand (visits c n j)≤3*slab c n:=
  (forest_bounds c n hn j).2.trans (fits.1.trans (by omega))
 let b:=reference c n hn j h
 have produce:=UniformActualCalendarAtomsResult.result (geometry c n hn j)
  h.rectangles h.leaves (facts c n j) hn (O:=3*slab c n) (T:=3*slab c n)
  le_rfl le_rfl (radix_fit c n hn j) rfl rfl pool nat t
 exact UniformCalendarNativeRootAction.action n (radix n j) 0 (axis c n j).requests
  (parameters c n j) (axisBase n j.val) t (radix n j) b (by omega)
  (NewtonFourier.invH (zeta (radix n j))) (by simp) (fun a fit L actual=>produce a fit L actual)

end
end ExactFourierCircuits.UniformActualCalendarRetainedLocalAction
