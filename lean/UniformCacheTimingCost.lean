import UniformCacheTimingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingCost
open UniformCacheTimingRows UniformCacheTimingReverseData
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeExecution (visitSum)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformLocalRectangleDescriptors (Row emittedCount)

lemma rows_ticks_bound (L:List Row)(ell:ℕ)
 (bound:∀q∈L,Nat.clog 2 (2*(q.a+q.e))≤ell):UniformCacheTimingRows.ticks L≤(4*ell+28)*L.length+1:=by
 induction L with
 | nil=>simp [UniformCacheTimingRows.ticks]
 | cons q qs ih=>
  have head:=bound q (by simp)
  have tail:=ih (fun a ha=>bound a (by simp [ha]))
  simp only [UniformCacheTimingRows.ticks,List.map_cons,List.sum_cons,List.length_cons] at tail ⊢
  simp only [Nat.mul_add,Nat.mul_one] at head tail ⊢
  omega

lemma reverse_ticks_bound (L:List Visit)(ell:ℕ)
 (bound:∀q∈L,∀a∈currentRows q.task,Nat.clog 2 (2*(a.a+a.e))≤ell):
 UniformCacheTimingReverseData.ticks L L.length≤35*L.length+(4*ell+28)*visitSum L+1:=by
 have sums:(L.map UniformCacheTimingNode.budget).sum≤35*L.length+(4*ell+28)*visitSum L:=by
  induction L with
  | nil=>simp [visitSum]
  | cons q qs ih=>
   have head:=rows_ticks_bound (currentRows q.task) ell (bound q (by simp))
   have tail:=ih (fun a ha=>bound a (by simp [ha]))
   rw [UniformLocalCacheTreeCoverage.currentRows_length] at head
   simp only [List.map_cons,List.sum_cons,List.length_cons,visitSum] at tail ⊢
   have headBudget:UniformCacheTimingNode.budget q≤(4*ell+28)*emittedCount q.task.width+35:=by
    unfold UniformCacheTimingNode.budget
    omega
   simp only [Nat.mul_add,Nat.mul_one]
   omega
 simpa only [UniformCacheTimingReverseData.ticks,List.take_length] using Nat.add_le_add_right sums 1

/-- Every instruction in all three timing passes is charged. Startup is a
polynomial in the local width; parallel schedule duration still uses max. -/
lemma whole_ticks_bound (L:List Visit)(ell:ℕ)
 (bound:∀q∈L,∀a∈currentRows q.task,Nat.clog 2 (2*(a.a+a.e))≤ell):
 5*L.length+15+UniformCacheTimingReverseData.ticks L L.length+
 UniformCacheTimingForwardLoop.ticks (UniformCacheTimingForwardCanonical.data L) 0 L.length+2≤
 66*L.length+(4*ell+36)*visitSum L+19:=by
 have reverse:=reverse_ticks_bound L ell bound
 have forward:=UniformCacheTimingForwardCanonical.execution_ticks_bound L
 simp only [Nat.add_mul] at reverse ⊢
 omega
lemma polynomial_bound (v N K:ℕ)(nodes:N≤2*v+1)(requests:K≤v^2):
 66*N+(8*v+36)*K+19≤1000*(v+1)^3:=by
 have product:=Nat.mul_le_mul_left (8*v+36) requests
 nlinarith
end ExactFourierCircuits.UniformCacheTimingCost
