import UniformLocalCacheTiming
import UniformSelectedCRT

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarClockBounds
open UniformLocalCacheTreeMachine UniformLocalCacheTiming UniformBalancedToeplitz
open scoped BigOperators
noncomputable section

/-- The genuine literal tree clock has the already proved fourth-logarithm bound. -/
lemma plan_duration {r:ℕ}(P:Plan r):
 planDuration P≤depthUnit*(Nat.clog 2 r+1)^4:=by
 have hf:PowerSeries.constantCoeff (1:PowerSeries ℂ)≠0:=by simp
 have h:=UniformLocalFourierLayers.render_length P (1:PowerSeries ℂ) hf
 rw [UniformLocalCacheTiming.render_duration P (1:PowerSeries ℂ) hf] at h
 exact h
lemma tree_duration {r:ℕ}(P:Plan r)(o:ℕ):
 treeDuration (ofPlan P o)≤depthUnit*(Nat.clog 2 r+1)^4:=by
 rw [ofPlan_duration]
 exact plan_duration P

lemma tree_events (T:Tree)(start:ℕ):
 (treeTimed start T).length≤T.nodeCount+T.rectangles.length:=by
 induction T generalizing start with
 | direct v o=>simp [treeTimed,Tree.nodeCount,Tree.rectangles]
 | split v o b L R ihL ihR=>
  simp only [treeTimed,List.length_append,sequenceRows_length,Tree.nodeCount,Tree.rectangles]
  have l:=ihL start
  have r:=ihR start
  omega
lemma plan_events {r:ℕ}(P:Plan r)(o start:ℕ)(hr:0<r):
 (treeTimed start (ofPlan P o)).length≤r^2+2*r-1:=by
 have events:=tree_events (ofPlan P o) start
 have nodes:=ofPlan_nodeCount_tight P o hr
 have rows:=ofPlan_rectangles_length P o
 omega

/-- Every selected radix has this actual quadratic bound, including the binary axis. -/
def radixCap(n:ℕ):ℕ:=128*(UniformWorkingLength.axisCount n+2)^2
/-- Parallel axis schedules use the maximum clock, rather than serializing their depths. -/
def synchronizedDepth(n:ℕ):ℕ:=Finset.univ.sup (fun j=>
 treeDuration (ofPlan (plan (UniformSelectedCRT.radices n j)) 0))
def clockCap(n:ℕ):ℕ:=depthUnit*(Nat.clog 2 (radixCap n)+1)^4
lemma selected_radix {n:ℕ}(hn:0<n)(j:Fin (UniformWorkingLength.axisCount n+1)):
 UniformSelectedCRT.radices n j≤radixCap n:=UniformSelectedCRT.radix_quadratic hn j
lemma selected_clock {n:ℕ}(hn:0<n)(j:Fin (UniformWorkingLength.axisCount n+1)):
 treeDuration (ofPlan (plan (UniformSelectedCRT.radices n j)) 0)≤clockCap n:=by
 have h:=tree_duration (plan (UniformSelectedCRT.radices n j)) 0
 have c:=Nat.clog_mono_right 2 (selected_radix hn j)
 exact h.trans (Nat.mul_le_mul_left depthUnit (Nat.pow_le_pow_left (by omega) 4))
lemma synchronized_bound {n:ℕ}(hn:0<n):synchronizedDepth n≤clockCap n:=by
 unfold synchronizedDepth
 exact Finset.sup_le (fun j _=>selected_clock hn j)
end
end ExactFourierCircuits.UniformCalendarClockBounds
