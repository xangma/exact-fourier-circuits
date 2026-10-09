import UniformAxisCachePrepareExecution
import UniformJointCacheTime
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTimingGeometry
open UniformJointCacheAllocation UniformJointCacheExtent
open UniformLocalCacheTimingMetadata UniformLocalCacheTreeMachine
open UniformAxisCacheAllocationMachine (wordBudget)

lemma walk_length (fuel k c:ℕ)(tasks:List Task):(walk fuel k c tasks).1.length≤fuel:=by
 induction fuel generalizing k c tasks with
 | zero=>simp [walk]
 | succ fuel ih=>
  cases tasks with
  | nil=>simp [walk]
  | cons t ts=>simpa only[walk,List.length_cons,Nat.succ_le_succ_iff] using
    (ih (k+1) (c+7*UniformLocalRectangleDescriptors.emittedCount t.width) (children t k++ts))
lemma nodes_bound (r R:ℕ):nodeCount r 0 R≤2*r+1:=walk_length _ _ _ _
lemma requests_bound (r R:ℕ):requestCount r 0 R≤r^2:=
 UniformLocalCacheTreeCoverage.root_walk_visitSum_bound _ _ _

lemma cap_lower(r:ℕ):334*r^2≤capacity r:=by
 have h:=Nat.mul_le_mul_left (r^2) (show 334≤352*Nat.clog 2 (4*r)+330+4 by omega)
 simpa only[capacity,slotCount_formula,Nat.mul_comm] using h

lemma search_fits (r N S:ℕ)(radix:2≤r):UniformWorkspaceSearchMachine.budget r≤wordBudget r N S:=by
 have cap:=cap_lower r
 have formula:=UniformAxisCacheAllocationMachine.endNat_formula r N S
 unfold UniformWorkspaceSearchMachine.budget wordBudget
 change 1024*(r+1)^2+256≤20000*(2*r+1)+(axisBank r N S).endNat+(axisBank r N S).endScalar+100
 nlinarith only[cap,formula,radix,Nat.zero_le ((3*r)*capacity r),Nat.zero_le ((axisBank r N S).endScalar),Nat.zero_le (7*(2*r+2)*r^2)]

lemma duration_cap(r:ℕ):UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)≤28*capacity r:=by
 have duration:=UniformJointCacheTime.plan_duration_bound (UniformBalancedToeplitz.plan r) (le_refl r)
 have slots:=actual_request_slots r (UniformBalancedToeplitz.plan r)
 omega
lemma duration_fits(r N S:ℕ)(radix:2≤r):
 UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)≤wordBudget r N S:=by
 apply (duration_cap r).trans
 have formula:=UniformAxisCacheAllocationMachine.endNat_formula r N S
 by_cases large:6≤r
 · unfold wordBudget
   change 28*capacity r≤20000*(2*r+1)+(axisBank r N S).endNat+(axisBank r N S).endScalar+100
   nlinarith only[formula,large,Nat.zero_le ((axisBank r N S).endScalar),Nat.zero_le (r^2),Nat.zero_le (7*(2*r+2)*r^2),Nat.zero_le (capacity r)]
 · have upper:r≤5:=by omega
   interval_cases r <;>
    norm_num [wordBudget,axisBank,capacity,slotCount_formula,Nat.clog] <;>omega

lemma producer_layout (r N S B:ℕ)(radix:2≤r)(budget:wordBudget r N S≤B):
 UniformLocalCacheTreeExecution.Layout r 0 (axisBank r N S).tasks (axisBank r N S).nodes
  (axisBank r N S).requests B:=by
 have num:=(UniformAxisCacheAllocationMachine.numeric_bounds r N S).mono budget
 constructor
 · have row:=num.rowBudget;change 20000*(2*r+1)≤B at row;omega
 · exact (search_fits r N S radix).trans budget
 · dsimp[axisBank];omega
 · dsimp[axisBank];omega
 · have ending:=num.endpoints (axisBank r N S).endNat (by simp)
   dsimp[axisBank] at ending ⊢;omega
 · have h:=num.twice;omega
 · have row:=num.rowBudget;change 20000*(2*r+1)≤B at row;omega

lemma timing_layout (r N S B:ℕ)(budget:wordBudget r N S≤B):
 UniformCacheTimingReverseData.Layout (axisBank r N S).nodes (axisBank r N S).durations
  (axisBank r N S).nodeStarts (axisBank r N S).requestStarts
  (nodeCount r 0 (axisBank r N S).requests) (requestCount r 0 (axisBank r N S).requests) B:=by
 have nodes:=nodes_bound r (axisBank r N S).requests
 have requests:=requests_bound r (axisBank r N S).requests
 have num:=(UniformAxisCacheAllocationMachine.numeric_bounds r N S).mono budget
 have ending:=num.endpoints (axisBank r N S).endNat (by simp)
 constructor
 · have row:=num.rowBudget;change 20000*(2*r+1)≤B at row;omega
 · dsimp[axisBank] at nodes ⊢;omega
 · dsimp[axisBank] at nodes ⊢;omega
 · dsimp[axisBank] at nodes ⊢;omega
 · dsimp[axisBank] at ending requests ⊢;omega

lemma source_gap (r N S:ℕ)(radix:2≤r):
 (axisBank r N S).requests+7*requestCount r 0 (axisBank r N S).requests+4≤(axisBank r N S).durations:=by
 have requests:=requests_bound r (axisBank r N S).requests
 have square:4≤r^2:=by nlinarith
 dsimp[axisBank] at requests ⊢
 nlinarith only[requests,square,Nat.zero_le ((3*r+11)*capacity r),Nat.zero_le (2*r*r^2)]

lemma row_fits (r N S B:ℕ)(budget:wordBudget r N S≤B):20000*(r+1)≤B:=by
 have row:=((UniformAxisCacheAllocationMachine.numeric_bounds r N S).mono budget).rowBudget
 change 20000*(2*r+1)≤B at row
 omega
end ExactFourierCircuits.UniformAxisCacheTimingGeometry
