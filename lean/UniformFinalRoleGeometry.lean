import UniformFinalRoleModel

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleGeometry
open UniformMachine UniformFinalRoleModel
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
lemma roles_two:2≤W:=by
 change 2≤ExplicitSeedBudget.paddedRoles
 norm_num[ExplicitSeedBudget.paddedRoles]
lemma geometry {n:ℕ} (hn:0<n):
 let U:=UniformJointAllocation.slab c n
 let B:=UniformJointAllocation.envelope c n
 W≤B∧42≤B∧2*U+W*V n≤B∧
 UniformInputPermutationPreparation.destination n+V n≤2*U∧
 UniformChirpKernelPreparation.kernelBase n+V n≤2*U∧
 UniformKernelSpectrumStorage.alphaBase c n+V n≤B∧
 UniformJointCacheWorkspace.stride n≤2*U:=by
 intro U B
 have h:=UniformJointAllocation.actual_arithmetic c n hn
 dsimp only at h
 rw[UniformActualGlobalConstants.roles_eq,Nat.mul_assoc]at h
 have low:=(UniformInputPermutationPreparation.word_setup hn).2.1
 have pow:=(UniformJointAllocationMachine.arithmetic c n).2.2.2.1
 have fit:=UniformAxisCachePreparationRetention.slab_above_seed_word c n
 have roles:W≤B:=UniformJointAllocation.roles_bound c n
 have table:=UniformKernelSpectrumStorage.tables_adjacent c hn
 have kb:UniformChirpKernelPreparation.kernelBase n+V n≤
  UniformInputPermutationPreparation.destination n+V n:=by
  unfold UniformInputPermutationPreparation.destination UniformNormalizationPreparation.normBase
  omega
 have large:=UniformJointAllocation.fixed_large c
 dsimp only[U,B,V,W,UniformJointCacheWorkspace.stride,UniformJointAllocation.envelope]at *
 unfold UniformKernelSpectrumStorage.betaInverseBase UniformKernelSpectrumStorage.base at table
 omega
lemma header_low {n:ℕ} (hn:0<n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s):
 s.natReg 105+12*s.natReg 102+4*s.natReg 101+4*s.natReg 103+100≤
 UniformJointAllocation.envelope c n:=by
 rw[metadata.saved.copyAddress,metadata.saved.count,metadata.saved.inputLength,metadata.saved.workingLength]
 have e:UniformInitialPreparation.ell n≤2*n:=by
  have h:=UniformWorkingLength.firstExceed_bound n
  unfold UniformInitialPreparation.ell UniformWorkingLength.axisCount
  omega
 have v:V n≤4*n:=(UniformWorkingLength.workingLength_upper hn).le
 have small:n+2≤UniformJointCacheWorkspace.stride n:=by
  simpa only[pow_one]using Nat.pow_le_pow_right (by omega:1≤n+2) (by decide:1≤19)
 dsimp only[V] at v
 have h:=UniformJointCacheWorkspace.ambient_budget c n
 change 2000*UniformJointCacheWorkspace.stride n≤UniformJointAllocation.envelope c n at h
 unfold UniformGlobalNatPreparation.destination UniformGlobalNatPreparation.amount
 omega
end
end ExactFourierCircuits.UniformFinalRoleGeometry
