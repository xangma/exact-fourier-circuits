import UniformAxisCacheTimingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRootDuration
open UniformMachine UniformJointCacheAllocation UniformLocalCacheTreeMachine
open UniformLocalCacheTimingMetadata UniformCacheTimingReference

lemma root_positive (r R:ℕ):0<nodeCount r 0 R:=by
 unfold nodeCount rootVisits
 rw [walk]
 simp only [List.length_cons]
 omega

/-- Register6175 points to the actual charged root-duration cell. Its value is
the maximum-child balanced Toeplitz duration, not a supplied timing constant. -/
theorem root_duration {r N S:ℕ}{s:State}(ready:UniformAxisCacheTimingExecution.Ready r N S s):
 s.natHeap (s.natReg 6175)=some (UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)):=by
 rw [ready.timing.durations]
 have h:=ready.printed.durations 0 (root_positive r (axisBank r N S).requests)
 change s.natHeap (axisBank r N S).durations=some (taskDuration ⟨r,0,0,0⟩) at h
 simpa only [taskDuration,UniformLocalCacheTiming.ofPlan_duration] using h

end ExactFourierCircuits.UniformAxisCacheRootDuration
