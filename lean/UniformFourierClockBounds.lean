import UniformCalendarPreparationBounds

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierClockBounds
open UniformCalendarClockBounds UniformLocalCacheTiming UniformBalancedToeplitz
open UniformJointAllocation UniformJointCacheAllocation UniformJointCacheTime
noncomputable section

def localDepth(n:ℕ)(j:Fin (UniformWorkingLength.axisCount n+1)):ℕ:=
 planDuration (plan (UniformSelectedCRT.radices n j))
/-- Both Toeplitz epochs and all five boundary diagonal layers. -/
def localHorizon(n:ℕ)(j:Fin (UniformWorkingLength.axisCount n+1)):ℕ:=2*localDepth n j+5
/-- The actual global horizon is a maximum over the full Fourier schedules. -/
def horizon(n:ℕ):ℕ:=Finset.univ.sup (localHorizon n)
def horizonCap(n:ℕ):ℕ:=2*clockCap n+5
lemma selected_depth{n:ℕ}(hn:0<n)(j:Fin (UniformWorkingLength.axisCount n+1)):
 localDepth n j ≤ clockCap n:=by
 simpa only [localDepth,ofPlan_duration] using selected_clock hn j
lemma selected_bound{n:ℕ}(hn:0<n)(j:Fin (UniformWorkingLength.axisCount n+1)):
 localHorizon n j ≤ horizonCap n:=by
 have h:=selected_depth hn j
 unfold localHorizon horizonCap
 omega
lemma bound{n:ℕ}(hn:0<n):horizon n ≤ horizonCap n:=
 Finset.sup_le (fun j _=>selected_bound hn j)
lemma selected_le(n:ℕ)(j:Fin (UniformWorkingLength.axisCount n+1)):
 localHorizon n j ≤ horizon n:=Finset.le_sup (f:=localHorizon n) (Finset.mem_univ j)
lemma local_positive(n:ℕ)(j:Fin (UniformWorkingLength.axisCount n+1)):5 ≤ localHorizon n j:=by
 unfold localHorizon
 omega
lemma positive(n:ℕ):5 ≤ horizon n:=
 (local_positive n ⟨0,by omega⟩).trans (selected_le n ⟨0,by omega⟩)

/-- Every clockPrefix maximum is updated by the same max equation as the real7 block. -/
def clockPrefix(n k:ℕ):ℕ:=(Finset.range k).sup (fun i=>
 if h:i<UniformWorkingLength.axisCount n+1 then localHorizon n ⟨i,h⟩ else 0)
lemma prefix_zero(n:ℕ):clockPrefix n 0=0:=by simp [clockPrefix]
lemma prefix_step(n k:ℕ)(hk:k<UniformWorkingLength.axisCount n+1):
 clockPrefix n (k+1)=max (clockPrefix n k) (localHorizon n ⟨k,hk⟩):=by
 simp only [clockPrefix,Finset.range_add_one,Finset.sup_insert,dite_eq_left hk]
 exact max_comm _ _
lemma prefix_bound{n:ℕ}(hn:0<n)(k:ℕ):clockPrefix n k ≤ horizonCap n:=by
 unfold clockPrefix
 apply Finset.sup_le
 intro i _
 split_ifs with h
 · exact selected_bound hn ⟨i,h⟩
 · omega

lemma prefix_eq_horizon(n:ℕ):clockPrefix n (UniformWorkingLength.axisCount n+1)=horizon n:=by
 apply Nat.le_antisymm
 · unfold clockPrefix
   apply Finset.sup_le
   intro i hi
   have h:i<UniformWorkingLength.axisCount n+1:=Finset.mem_range.mp hi
   simp only [dite_eq_left h]
   exact selected_le n ⟨i,h⟩
 · unfold horizon
   apply Finset.sup_le
   intro j _
   have h:=Finset.le_sup
    (f:=fun i=>if h:i<UniformWorkingLength.axisCount n+1 then localHorizon n ⟨i,h⟩ else 0)
    (Finset.mem_range.mpr j.isLt)
   simpa only [clockPrefix,dite_eq_left j.isLt] using h

/-- Ordinary selected-radix bounds make the real horizon arithmetic fit the
same machine word envelope at every positive input length. -/
lemma selected_word(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 localHorizon n j ≤ envelope c n:=by
 have r:UniformSelectedCRT.radices n j ≤ 4*n:=
  (UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1
 have d:=duration_word_bound c n _ (plan (UniformSelectedCRT.radices n j)) r
 have large:=fixed_large c
 unfold localHorizon localDepth envelope
 omega
lemma horizon_word(c:Constants){n:ℕ}(hn:0<n):horizon n ≤ envelope c n:=
 Finset.sup_le (fun j _=>selected_word c hn j)
lemma full_preparation{n:ℕ}(hn:0<n):
 horizon n*UniformCalendarPreparationBounds.allAxesBudget n ≤
 horizonCap n*((UniformWorkingLength.axisCount n+1)*
 UniformCalendarPreparationBounds.preparationBudget (radixCap n) (UniformJointCacheExtent.capacity (radixCap n))):=
 Nat.mul_le_mul (bound hn) (UniformCalendarPreparationBounds.all_axes_bound hn)
end
end ExactFourierCircuits.UniformFourierClockBounds
