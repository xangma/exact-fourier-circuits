import UniformFinalPhysicalTableGeometry
import UniformFinalStartupSource

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT permutations after (5.5), PDF p.22
(`eq:crt-fourier`), and §5.4 integer/address bounds, PDF p.24.

The produced physical CRT table and its protected-bank geometry refine the
paper's costed index permutations. Allocation addresses, headers and frames are
implementation bookkeeping rather than a separate paper argument.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPhysicalTableInputs
open UniformMachine UniformNatBlockMachine UniformJointAllocation UniformInitialPreparation
open UniformAxisCachePreparationRetention UniformFinalPhysicalTableGeometry
noncomputable section

lemma args(c:UniformJointAllocation.Constants)(n:ℕ)(s:State)
 (h:UniformPhysicalCRTTableHeaders.Args c n s)
 (directory:s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n):
 UniformFastPhysicalCRTMachine.Args (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n) s:=
 ⟨h.axes,h.volume,h.seed.trans directory,h.sourceAlpha,h.sourceBeta,h.destAlpha,h.destInverse,h.work⟩

lemma safe(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s:State)
 (core:Core n x s)(source:s.natReg 6026=2*slab c n)
 (directory:s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n):
 readable UniformPhysicalCRTTableHeaders.operations s∧
 peak UniformPhysicalCRTTableHeaders.operations s≤envelope c n:=by
 have original:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤ slab c n:=
  (UniformAllAxisSeedPreparation.word_setup hn).2.2.trans (canonical_below c n)
 have copy:copyBase n≤UniformAllAxisSeedPreparation.directoryBase n:=by
  unfold UniformAllAxisSeedPreparation.directoryBase UniformPermutationInversePreparation.inverseBase
  omega
 have arithmetic:=actual_arithmetic c n hn
 dsimp only at arithmetic
 apply UniformPhysicalCRTTableHeaders.safe
 · rw[source];unfold envelope;omega
 · rw[core.metadata.saved.copyAddress,core.metadata.saved.count,core.metadata.saved.workingLength,directory]
   change copyBase n+12*ell n+4*len n+UniformAllAxisSeedPreparation.directoryBase n+100≤envelope c n
   have count:ell n≤ slab c n:=by
    change UniformAllAxisSeedPreparation.directoryBase n+2*(ell n+1)≤ slab c n at original
    omega
   unfold envelope
   omega

lemma header_core(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s:State)
 (core:Core n x s):Core n x (applyBlock UniformPhysicalCRTTableHeaders.operations s):=by
 have f:=UniformPhysicalCRTTableHeaders.frame s
 apply UniformAxisCachePreparationRetention.transport c n 0 hn x s _ core
 · exact ⟨f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1⟩
 · intro q _;exact congrFun f.1 q
 · intro q hq
   exact f.2.2.2.2.2 q (by unfold UniformPhysicalCRTTableHeaders.Changed;omega)

lemma header_data{n:ℕ}{x:Fin n→ℂ}(s:State)(h:UniformFinalStartupData.Data n x s):
 UniformFinalStartupData.Data n x (applyBlock UniformPhysicalCRTTableHeaders.operations s):=by
 have f:=UniformPhysicalCRTTableHeaders.frame s
 exact h.transport f.1 f.2.1 f.2.2.2.2.1 f.2.2.2.1

lemma installed(c:UniformJointAllocation.Constants){n:ℕ}(_hn:0<n)(x:Fin n→ℂ)(s:State)
 (core:Core n x s)(source:s.natReg 6026=2*slab c n)
 (directory:s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n):
 UniformFastPhysicalCRTMachine.Args (UniformAllAxisSeedPreparation.axisCount n) (len n) (addresses c n)
  (applyBlock UniformPhysicalCRTTableHeaders.operations s):=by
 apply args c n _ (UniformPhysicalCRTTableHeaders.values c n s core.metadata source)
 exact ((UniformPhysicalCRTTableHeaders.frame s).2.2.2.2.2 6904
  (by unfold UniformPhysicalCRTTableHeaders.Changed;omega)).trans directory
end
end ExactFourierCircuits.UniformFinalPhysicalTableInputs
