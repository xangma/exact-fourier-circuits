import UniformJointDiagonalHeaderInstallation
import UniformJointCacheAllocation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarArena
open UniformJointAllocation UniformJointCacheAllocation UniformJointCacheExtent
open scoped BigOperators

/-- The old allocation proof's explicit polynomial bound, before its generous slab absorption. -/
lemma cache_total_polynomial(n:ℕ)(hn:0<n):total n ≤ 12000000*(n+2)^5:=by
 have first:total n ≤ ell n*(6000000*(n+2)^4):=by
  rw [total_formula]
  calc
   offsetSum (fun i=>jointSize (UniformAllAxisSeedPreparation.radixAt n i)) (ell n) ≤
    ∑_i∈Finset.range (ell n),6000000*(n+2)^4:=by
     apply Finset.sum_le_sum
     intro i hi
     have lt:i<ell n:=Finset.mem_range.mp hi
     rw [UniformAllAxisSeedPreparation.radixAt_eq n ⟨i,lt⟩]
     exact selected_joint_bound n hn ⟨i,lt⟩
   _=ell n*(6000000*(n+2)^4):=by simp
 have axes:ell n ≤ 2*(n+2):=by
  have h:=(actual_sizes n hn).1
  change ell n ≤ 2*n+1 at h
  omega
 have scaled:=Nat.mul_le_mul_right (6000000*(n+2)^4) axes
 apply first.trans
 convert scaled using 1;ring

/-- Plenty of genuinely unused space remains before2U; no cache-end guess is required. -/
lemma reserve(c:Constants){n:ℕ}(hn:0<n):16*total n+4096 ≤ slab c n:=by
 have cache:=cache_total_polynomial n hn
 have one:1 ≤ (n+2)^5:=by
  exact Nat.one_le_pow _ _ (by omega)
 have small:16*total n+4096 ≤ 192004096*(n+2)^5:=by
  nlinarith only [cache,one]
 have large:192004096 ≤ 100000*(fixed c+1):=by
  have fixedLarge:=fixed_large c
  omega
 have power:(n+2)^5 ≤ (n+2)^19:=Nat.pow_le_pow_right (by omega) (by decide)
 exact small.trans ((Nat.mul_le_mul_right _ large).trans (Nat.mul_le_mul_left _ power))

/-- Fresh arenas follow all measured persistent caches in their respective heaps. -/
def natBase(c:Constants)(n:ℕ):ℕ:=natEnd c n
def scalarBase(c:Constants)(n:ℕ):ℕ:=scalarEnd c n
def size(n:ℕ):ℕ:=4*total n+2048
lemma arena_fit(U total headAmount caches:ℕ)(need:headAmount+caches ≤ total)
 (room:16*total+4096 ≤ U):U+headAmount+caches+(4*total+2048) ≤ 2*U:=by nlinarith only [need,room]
lemma nat_fits(c:Constants){n:ℕ}(hn:0<n):natBase c n+size n ≤ 2*slab c n:=by
 have need:2*ell n+natTotal n ≤ total n:=by unfold total;omega
 have fit:=arena_fit (slab c n) (total n) (2*ell n) (natTotal n) need (reserve c hn)
 simpa only [natBase,natEnd,natStart,size] using fit
lemma scalar_fits(c:Constants){n:ℕ}(hn:0<n):scalarBase c n+size n ≤ 2*slab c n:=by
 have need:9*UniformAllAxisSeedPreparation.prefixSum n (ell n)+scalarTotal n ≤ total n:=by
  unfold total;omega
 have fit:=arena_fit (slab c n) (total n) (9*UniformAllAxisSeedPreparation.prefixSum n (ell n)) (scalarTotal n) need (reserve c hn)
 simpa only [scalarBase,scalarEnd,scalarStart,size] using fit
lemma prior_nat(c:Constants)(n:ℕ)(j:Fin (ell n)):(axis c n j).endNat ≤ natBase c n:=
 (axis_fit c n j).1
lemma prior_scalar(c:Constants)(n:ℕ)(j:Fin (ell n)):(axis c n j).endScalar ≤ scalarBase c n:=
 (axis_fit c n j).2
lemma axis_budgets(n:ℕ):
 natTotal n ≤ size n ∧ scalarTotal n ≤ size n ∧
 9*UniformAllAxisSeedPreparation.prefixSum n (ell n) ≤ size n:=by
 unfold size total
 omega
lemma before_diagonal(c:Constants){n:ℕ}(hn:0<n):
 scalarBase c n+size n ≤ (UniformJointDiagonalHeaderInstallation.rows c n hn).coefficient:=
 UniformJointDiagonalHeaderInstallation.pools_before c hn _ (scalar_fits c hn)
end ExactFourierCircuits.UniformGlobalCalendarArena
