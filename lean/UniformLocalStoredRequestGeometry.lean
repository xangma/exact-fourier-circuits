import UniformCanonicalCacheSlotComplete
import UniformLocalCacheRetainedPrefixes
import UniformLocalRectangleCacheBindings
import UniformCanonicalCachePhaseEnds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestGeometry
open UniformMachine UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformJointAllocation UniformCanonicalCacheSlotGeometry
open UniformLocalRectangleCacheBindings
namespace W
abbrev original:=UniformJointCacheWorkspace.original
abbrev stride:=UniformJointCacheWorkspace.stride
end W
noncomputable section
lemma phase_layout (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n))(q:Row)
 (g:UniformJointCacheWorkspace.Geometry n j q):
 UniformSeedHeightPreparation.Layout n j
  (UniformLocalRectanglePhaseBanks.actual q (W.original n q)) (envelope constants n):=by
 rw [UniformJointCacheWorkspace.actual_original]
 exact UniformJointCacheWorkspace.ambient_layout constants hn j q g

lemma true_before {n:ℕ}(hn:0<n)(j:Fin (axisCount n))(q:Row)
 (g:UniformJointCacheWorkspace.Geometry n j q):
 UniformCrossHeightPreparationMachine.recordBase
  (UniformLocalRectanglePhaseBanks.actual q (W.original n q)).height
  (8*(UniformLocalRectanglePhaseBanks.actual q (W.original n q)).exponent+7) ≤ 18*W.stride n:=by
 rw [UniformJointCacheWorkspace.actual_original]
 exact (UniformJointCacheWorkspace.slots_before hn j q g).2.1

lemma slots_before {n:ℕ}(hn:0<n)(j:Fin (axisCount n))(q:Row)
 (g:UniformJointCacheWorkspace.Geometry n j q):
 17*W.stride n+55*UniformLocalReplayAssembly.phasePrefix
  (8*(UniformLocalRectanglePhaseBanks.actual q (W.original n q)).exponent+6) 6 ≤ 18*W.stride n:=by
 rw [UniformJointCacheWorkspace.actual_original]
 exact (UniformJointCacheWorkspace.slots_before hn j q g).2.2.1

lemma phase_ends (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n))(q:Row)
 (g:UniformJointCacheWorkspace.Geometry n j q):
 UniformCacheRetentionRegions.PhaseEnds (UniformLocalRectanglePhaseBanks.actual q (W.original n q))
  (UniformLocalRectanglePhaseBanks.nextParameters n j q (W.original n q) (UniformJointCacheWorkspace.work n))
  (11*W.stride n) (17*W.stride n)
  (UniformLocalDisabledHeightMachine.disabled
   (UniformLocalRectanglePhaseBanks.actual q (W.original n q)).height
   (18*W.stride n) (19*W.stride n) (20*W.stride n) (21*W.stride n)) (slab constants n):=by
 rw [UniformJointCacheWorkspace.actual_original]
 exact UniformCanonicalCachePhaseEnds.slab_ends constants hn j q g

lemma binding (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(q:Row)(k time:ℕ):
 Bindings (context constants n j q k time) q (W.original n q) (W.stride n)
  (17*W.stride n) (11*W.stride n) (18*W.stride n) (19*W.stride n)
  (20*W.stride n) (21*W.stride n):=by
 have h:=UniformJointCacheWorkspace.actual_original n q
 refine ⟨?_,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl⟩
 · simpa only [context] using congrArg UniformSeedHeightPreparation.Config.height h.symm
 · simpa only [context] using congrArg UniformSeedHeightPreparation.Config.gates h.symm

lemma prefixes (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n))(q:Row)(k time:ℕ)
 (hk:k ≤ UniformJointCacheExtent.capacity (radix n j)):
 UniformLocalCacheContextConductor.Prefixes n (context constants n j q k time):=by
 obtain ⟨_,seed,_,nat⟩:=UniformJointCacheWorkspace.retained hn
 have persistent:=persistent_bounds constants hn j k hk
 have before:=UniformJointCacheWorkspace.below_cache constants n
 change 2000*W.stride n ≤ slab constants n at before
 change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ W.stride n at nat
 constructor
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 23*W.stride n
   omega
 · change UniformConjugateRankSpectrumPreparation.seedEnd n ≤
    (UniformJointCacheAllocation.slot (UniformJointCacheAllocation.axis constants n j) k).factor
   change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ W.stride n at seed
   exact seed.trans (by omega)
 · change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ 22*W.stride n
   change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ W.stride n at seed
   omega
 · change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ 22*W.stride n+1
   change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ W.stride n at seed
   omega
end
end ExactFourierCircuits.UniformLocalStoredRequestGeometry
