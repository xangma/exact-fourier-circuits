import UniformFinalCacheAsymptotics
import UniformGlobalEnvelope
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterCost
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation Filter Asymptotics
open UniformFinalCacheAsymptotics
noncomputable section

/-- Majorants for the twenty actual stages, in physical execution order.
The table and complete-clock terms are separate so the obsolete O(V*ell)
reference printer cannot silently be absorbed into the target bound. Header
program costs include their charged halt/continuation instructions. -/
def stageCosts (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)(n:ℕ):List ℕ:=
 let V:=UniformInitialPreparation.len n
 [UniformAllAxisConjugatePreparation.fullBudget n,62,67,cacheBudget c n,
 tableHeader n,table n,18,5*(W*V)+16*V+24,clock n,7*V+9,19,
 5*(W*V)+16*V+24,9*V+10,clock n,9*V+9,18*V+18,
 clock n,18*V+18,12,13*n+6]
def totalBudget (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)(n:ℕ):ℕ:=
 (stageCosts c W tableHeader table clock n).sum+1
lemma stages_length (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)(n:ℕ):
 (stageCosts c W tableHeader table clock n).length=20:=rfl
lemma totalBudget_eq (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)(n:ℕ):
 totalBudget c W tableHeader table clock n=
 UniformAllAxisConjugatePreparation.fullBudget n+cacheBudget c n+
 3*clock n+table n+(10*W+93)*UniformInitialPreparation.len n+13*n+297+tableHeader n:=by
 simp only[totalBudget,stageCosts,List.sum_cons,List.sum_nil]
 ring

/-- Every finalized stage except the table and three complete clock traversals. -/
def overhead (c:Constants)(W:ℕ)(n:ℕ):ℕ:=
 UniformAllAxisConjugatePreparation.fullBudget n+cacheBudget c n+
 (10*W+93)*UniformInitialPreparation.len n+13*n+297
lemma totalBudget_split (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)(n:ℕ):
 totalBudget c W tableHeader table clock n=overhead c W n+3*clock n+table n+tableHeader n:=by
 rw[totalBudget_eq];unfold overhead;ring

lemma overhead_isBigO_input (c:Constants)(W:ℕ):
 (fun n:ℕ=>(overhead c W n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=by
 have scaled: (fun n:ℕ=>((10*W+93:ℕ):ℝ)*(UniformInitialPreparation.len n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=
  UniformAllAxisSeedCost.workingLength_isBigO_input.const_mul_left _
 have linear:(fun n:ℕ=>(13:ℝ)*(n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=
  (isBigO_refl (fun n:ℕ=>(n:ℝ)) atTop).const_mul_left 13
 have constant:(fun _n:ℕ=>(297:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)):=
  ((isLittleO_const_id_atTop (297:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
 simpa only[overhead,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
  (((UniformGlobalEnvelope.fullPreparationBudget_isBigO_input.add
   (cacheBudget_isLittleO_input c).isBigO).add scaled).add linear).add constant

lemma input_isBigO_paper : (fun n:ℕ=>(n:ℝ)) =O[atTop] asymptoticCost UniformExponent.theta:=
 UniformNetworkCost.input_isBigO_workingCost.trans UniformAsymptotics.workingCost_isBigO_paper

/-- Final arithmetic join. The clock is the actual complete-clock majorant;
the table premise must be discharged by the actual amortized replacement,
not by the reference33 routine. No execution theorem is asserted here. -/
theorem totalBudget_isBigO_paper (c:Constants)(W:ℕ)(tableHeader table clock:ℕ→ℕ)
 (header:(fun n:ℕ=>(tableHeader n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)))
 (tables:(fun n:ℕ=>(table n:ℝ)) =O[atTop] (fun n:ℕ=>(n:ℝ)))
 (clocks:(fun n:ℕ=>(clock n:ℝ)) =O[atTop] asymptoticCost UniformExponent.theta):
 (fun n:ℕ=>(totalBudget c W tableHeader table clock n:ℝ)) =O[atTop] asymptoticCost UniformExponent.theta:=by
 have h:=(overhead_isBigO_input c W).trans input_isBigO_paper
 have clock:=(clocks.const_mul_left (3:ℝ))
 simpa only[totalBudget_split,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
  ((h.add clock).add (tables.trans input_isBigO_paper)).add (header.trans input_isBigO_paper)

end
end ExactFourierCircuits.UniformFinalOuterCost
