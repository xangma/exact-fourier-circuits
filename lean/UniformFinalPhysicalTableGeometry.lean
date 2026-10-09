import UniformPhysicalCRTTableHeaders
import UniformFastSelectedPhysicalCRT
import UniformFastPhysicalCRTMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT permutations after (5.5), PDF p.22
(`eq:crt-fourier`), and §5.4 integer/address bounds, PDF p.24.

The produced physical CRT table and its protected-bank geometry refine the
paper's costed index permutations. Allocation addresses, headers and frames are
implementation bookkeeping rather than a separate paper argument.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalPhysicalTableGeometry
open UniformJointAllocation UniformInitialPreparation UniformFastPhysicalCRTMachine
open scoped BigOperators
noncomputable section

def addresses(c:UniformJointAllocation.Constants)(n:ℕ):UniformFastPhysicalCRTMachine.Addresses where
 directory:=UniformAllAxisSeedPreparation.directoryBase n
 alpha:=copyBase n+alphaBase n
 beta:=copyBase n+betaBase n
 physicalAlpha:=UniformKernelSpectrumStorage.alphaBase c n
 inverseBeta:=UniformKernelSpectrumStorage.betaInverseBase c n
 work:=2*slab c n

lemma sources_before_directory(n:ℕ):
 copyBase n+alphaBase n+len n≤UniformAllAxisSeedPreparation.directoryBase n∧
 copyBase n+betaBase n+len n≤UniformAllAxisSeedPreparation.directoryBase n:=by
 unfold UniformAllAxisSeedPreparation.directoryBase UniformPermutationInversePreparation.inverseBase
 unfold copyBase alphaBase betaBase UniformGlobalNatPreparation.amount
 unfold UniformCRTTraversalMachine.betaBase
 unfold UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase
 omega

structure Fits(c:UniformJointAllocation.Constants)(n:ℕ):Prop where
 directory:(addresses c n).directory+2*UniformAllAxisSeedPreparation.axisCount n≤(addresses c n).physicalAlpha
 alpha:(addresses c n).alpha+len n≤(addresses c n).physicalAlpha
 beta:(addresses c n).beta+len n≤(addresses c n).physicalAlpha
 alphaEnd:(addresses c n).physicalAlpha+len n=(addresses c n).inverseBeta
 inverseEnd:(addresses c n).inverseBeta+len n=(addresses c n).work
 work:(addresses c n).work+2*UniformAllAxisSeedPreparation.axisCount n≤envelope c n
 volume:len n≤envelope c n
 code:53≤envelope c n

lemma fits(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n):Fits c n:=by
 have original:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤ slab c n:=
  (UniformAllAxisSeedPreparation.word_setup hn).2.2.trans (canonical_below c n)
 have reserve:=UniformKernelSpectrumStorage.reserve c hn
 have source:=sources_before_directory n
 have adjacent:=UniformKernelSpectrumStorage.tables_adjacent c hn
 have arithmetic:=actual_arithmetic c n hn
 dsimp only at arithmetic
 have gap:slab c n≤UniformKernelSpectrumStorage.alphaBase c n:=by
  unfold UniformKernelSpectrumStorage.alphaBase
  omega
 constructor
 · exact original.trans gap
 · exact source.1.trans ((Nat.le_add_right _ _).trans (original.trans gap))
 · exact source.2.trans ((Nat.le_add_right _ _).trans (original.trans gap))
 · exact adjacent.1
 · exact adjacent.2
 · dsimp[addresses,envelope]
   omega
 · unfold envelope
   omega
 · unfold envelope
   omega

lemma nat_below(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n):
 UniformAllAxisSeedPreparation.directoryBase n≤(addresses c n).physicalAlpha:=by
 have h:=(fits c hn).directory
 dsimp[addresses] at *
 omega
lemma cache_before(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)
 (j:Fin (UniformJointCacheAllocation.ell n)):
 (UniformJointCacheAllocation.axis c n j).endNat≤(addresses c n).physicalAlpha:=
 UniformKernelSpectrumStorage.nat_caches_before c hn j
lemma merged_before(c:UniformJointAllocation.Constants){n:ℕ}(hn:0<n)
 (j:Fin (UniformJointCacheAllocation.ell n)):
 (UniformFourierAxisWorkspace.axis c n j).endNat≤(addresses c n).physicalAlpha:=
 UniformKernelSpectrumStorage.nat_merged_before c hn j
end
end ExactFourierCircuits.UniformFinalPhysicalTableGeometry
