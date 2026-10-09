import UniformFourierAxisWorkspace

set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelSpectrumStorage
open UniformJointAllocation UniformJointCacheAllocation
namespace A
export UniformGlobalCalendarArena (scalarBase size)
end A
noncomputable section

/-- A durable prepared spectrum lies beyond every mutable per-axis pool and
strictly below the common numerical source at2U. -/
def base(c:Constants)(n:ℕ):ℕ:=2*slab c n-UniformInitialPreparation.len n

lemma reserve(c:Constants){n:ℕ}(hn:0<n):
 16*total n+4096+2*UniformInitialPreparation.len n≤ slab c n:=by
 have cache:=UniformGlobalCalendarArena.cache_total_polynomial n hn
 have length:UniformInitialPreparation.len n≤4*n:=
  (UniformWorkingLength.workingLength_upper hn).le
 have one:1≤(n+2)^5:=Nat.one_le_pow _ _ (by omega)
 have linear:n+2≤(n+2)^5:=by
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1≤n+2) (by decide:1≤5)
 have small:16*total n+4096+2*UniformInitialPreparation.len n≤192004104*(n+2)^5:=by
  nlinarith only [cache,length,one,linear]
 have large:192004104≤100000*(fixed c+1):=by
  have h:=fixed_large c;omega
 have power:(n+2)^5≤(n+2)^19:=Nat.pow_le_pow_right (by omega) (by decide)
 exact small.trans ((Nat.mul_le_mul_right _ large).trans (Nat.mul_le_mul_left _ power))

/-- The two physical CRT tables occupy separate Nat cells in the same reserved
high gap. The Nat and Scalar heaps have distinct address spaces. -/
def alphaBase(c:Constants)(n:ℕ):ℕ:=2*slab c n-2*UniformInitialPreparation.len n
def betaInverseBase(c:Constants)(n:ℕ):ℕ:=base c n
lemma nat_arena_fit(c:Constants){n:ℕ}(hn:0<n):
 UniformGlobalCalendarArena.natBase c n+A.size n+2*UniformInitialPreparation.len n≤2*slab c n:=by
 have room:=reserve c hn
 have need:2*ell n+natTotal n≤total n:=by unfold total;omega
 dsimp only [UniformGlobalCalendarArena.natBase,natEnd,natStart,A.size,UniformGlobalCalendarArena.size]
 nlinarith only [room,need]
lemma tables_adjacent(c:Constants){n:ℕ}(hn:0<n):
 alphaBase c n+UniformInitialPreparation.len n=betaInverseBase c n∧
 betaInverseBase c n+UniformInitialPreparation.len n=2*slab c n:=by
 have fit:=nat_arena_fit c hn
 unfold alphaBase betaInverseBase base
 omega
lemma nat_arena_before(c:Constants){n:ℕ}(hn:0<n):
 UniformGlobalCalendarArena.natBase c n+A.size n≤alphaBase c n:=by
 have fit:=nat_arena_fit c hn
 unfold alphaBase
 omega
lemma nat_caches_before(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (axis c n j).endNat≤alphaBase c n:=by
 have old:=UniformGlobalCalendarArena.prior_nat c n j
 exact old.trans ((Nat.le_add_right _ _).trans (nat_arena_before c hn))
lemma nat_merged_before(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (UniformFourierAxisWorkspace.axis c n j).endNat≤alphaBase c n:=by
 have next:=UniformFourierAxisWorkspace.prefix_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformFourierAxisWorkspace.prefix_step,UniformAllAxisSeedPreparation.radixAt_eq n j] at next
 have demand:UniformFourierAxisWorkspace.natDemand n≤A.size n:=
  (UniformFourierAxisWorkspace.demand_bound hn).trans (UniformGlobalCalendarArena.axis_budgets n).1
 dsimp only [UniformFourierAxisWorkspace.axis]
 rw [(UniformFourierAxisWorkspace.axis_ends _ _ _).1]
 have sum:UniformFourierAxisWorkspace.natPrefix n j.val+
  UniformFourierAxisWorkspace.natAmount (UniformAllAxisSeedPreparation.radix n j)≤A.size n:=next.trans demand
 have middle:UniformGlobalCalendarArena.natBase c n+
  UniformFourierAxisWorkspace.natPrefix n j.val+
  UniformFourierAxisWorkspace.natAmount (UniformAllAxisSeedPreparation.radix n j)≤
  UniformGlobalCalendarArena.natBase c n+A.size n:=by omega
 exact middle.trans (nat_arena_before c hn)

lemma arena_fit(c:Constants){n:ℕ}(hn:0<n):
 A.scalarBase c n+A.size n+UniformInitialPreparation.len n≤2*slab c n:=by
 have room:=reserve c hn
 have need:9*UniformAllAxisSeedPreparation.prefixSum n (ell n)+scalarTotal n≤total n:=by
  unfold total;omega
 dsimp only [A.scalarBase,UniformGlobalCalendarArena.scalarBase,scalarEnd,scalarStart,
  A.size,UniformGlobalCalendarArena.size]
 nlinarith only [room,need]

lemma end_eq(c:Constants){n:ℕ}(hn:0<n):base c n+UniformInitialPreparation.len n=2*slab c n:=by
 have fit:=arena_fit c hn
 unfold base
 omega
lemma arena_before(c:Constants){n:ℕ}(hn:0<n):A.scalarBase c n+A.size n≤base c n:=by
 have fit:=arena_fit c hn
 unfold base
 omega
lemma caches_before(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (axis c n j).endScalar≤base c n:=by
 have old:=UniformGlobalCalendarArena.prior_scalar c n j
 exact old.trans ((Nat.le_add_right _ _).trans (arena_before c hn))
lemma merged_before(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 (UniformFourierAxisWorkspace.axis c n j).endScalar≤base c n:=by
 have cumulative:=UniformAllAxisSeedPreparation.prefix_mono n (Nat.succ_le_of_lt j.isLt)
 rw [UniformAllAxisSeedPreparation.prefix_succ,UniformAllAxisSeedPreparation.radixAt_eq n j] at cumulative
 have budget:9*UniformAllAxisSeedPreparation.prefixSum n (ell n)≤A.size n:=
  (UniformGlobalCalendarArena.axis_budgets n).2.2
 have scaled:=Nat.mul_le_mul_left 9 cumulative
 change A.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val+
  9*UniformAllAxisSeedPreparation.radix n j≤base c n
 have sum:9*UniformAllAxisSeedPreparation.prefixSum n j.val+
  9*UniformAllAxisSeedPreparation.radix n j≤A.size n:=by omega
 exact (by omega :A.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val+
  9*UniformAllAxisSeedPreparation.radix n j≤A.scalarBase c n+A.size n).trans (arena_before c hn)
lemma boundary_before(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n)):
 slab c n+9*UniformAllAxisSeedPreparation.radix n j≤base c n:=by
 have before:=UniformFourierAxisWorkspace.boundary_before_merged c n j
 have endPool:(UniformFourierAxisWorkspace.axis c n j).pool≤
  (UniformFourierAxisWorkspace.axis c n j).endScalar:=by
  dsimp [UniformFourierAxisWorkspace.axis,UniformFourierAxisWorkspace.axisBank]
  omega
 exact before.trans (endPool.trans (merged_before c hn j))
lemma cell_below_source(c:Constants){n:ℕ}(hn:0<n)(j:Fin (UniformInitialPreparation.len n)):
 base c n+j.val<2*slab c n:=by
 have h:=end_eq c hn
 have hj:=j.isLt
 omega
end
end ExactFourierCircuits.UniformKernelSpectrumStorage
