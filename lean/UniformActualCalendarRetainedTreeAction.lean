import UniformActualCalendarRetainedLocalAction
import UniformAxisBoundarySelectedClock
import UniformFourierAxisOperationalCases

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRetainedTreeAction
noncomputable section
open OAI.ExactFourier UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformAllAxisSeedPreparation UniformFinalAxisCacheBundle
open UniformFourierAxisPrepareTree UniformFourierAxisOperationalCases
open UniformAxisBoundarySelectedClock UniformReflectedFourierCalendar
open NewtonFourier CoefficientTime

/-- Reflection changes the query clock only. The forward cache's genuine local
phase is exactly the phase of the original specified transposed epoch. -/
lemma selected_tree {r:ℕ}(positive:0<r){omega:ℂ}(root:IsPrimitiveRoot omega r)
 (g:ℕ)(tree:TreeAt (depth r) g):
 selected positive root g=
 UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan r)
  (invH omega) (by simp) (localTick (depth r) g):=by
 unfold selected
 have len:=toeplitz_length r omega
 rcases tree with early|late
 · have h:=UniformReflectedCalendarSource.upper_source
    (fun j:Fin r=>NewtonFourier.H omega j.val) (fun j:Fin r=>scale omega j.val)
    (fun j:Fin r=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (UniformNewton.Hvalue_ne_zero root) (UniformNewton.scaleValue_ne_zero positive root)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero positive root j))
    (invH omega) (by simp) g (by omega) (by simpa only[len] using early.2)
   simpa only[len,localTick,ite_eq_left early.2] using h
 · have queryEq:localTick (depth r) g=g-depth r-4:=ite_eq_right (by omega)
   have bound:g-depth r-4<(UniformLocalFourierLayers.toeplitz r (invH omega) (by simp)).length:=by
    rw[len];omega
   have clock:(UniformLocalFourierLayers.toeplitz r (invH omega) (by simp)).length+4+(g-depth r-4)=g:=by
    rw[len];omega
   rw[queryEq]
   simpa only[clock] using UniformReflectedCalendarSource.forward_source
    (fun j:Fin r=>NewtonFourier.H omega j.val) (fun j:Fin r=>scale omega j.val)
    (fun j:Fin r=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (UniformNewton.Hvalue_ne_zero root) (UniformNewton.scaleValue_ne_zero positive root)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero positive root j))
    (invH omega) (by simp) (g-depth r-4) bound

lemma specified_tree {r:ℕ}(positive:0<r)(g:ℕ)(tree:TreeAt (depth r) g):
 specified r g=
 UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan r)
  (invH (zeta r)) (by simp) (localTick (depth r) g):=by
 simp only[specified,dite_eq_left positive]
 exact selected_tree positive (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt positive)) g tree

/-- Pure canonical TREE action from the initial retained cache. This fixes one
preparation-order family for all later axes and clocks. -/
def action (c:Constants)(n:ℕ)(hn:0<n)(j:Fin (ell n))
 {s:State}(h:UniformAxisCacheContents.Contents c n hn j s)(g:ℕ)
 (tree:TreeAt (depth (radix n j)) g):
 UniformCalendarAxisAction.Action (radix n j)
  ((reference c n hn j h).events (localTick (depth (radix n j)) g))
  (specified (radix n j) g).matrix:=by
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2)
  (UniformFourierAxisGeometry.geometry c hn j).radix
 exact UniformCalendarAxisAction.congr
  (UniformActualCalendarRetainedLocalAction.action c n hn j h (localTick (depth (radix n j)) g))
  (congrArg UniformLayerSnapshot.Snapshot.matrix (specified_tree positive g tree)).symm

end
end ExactFourierCircuits.UniformActualCalendarRetainedTreeAction
