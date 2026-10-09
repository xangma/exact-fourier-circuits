import UniformRoleInputMachine
import UniformFinalNumericJoin
import UniformFinalStartupSource

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleModel
open UniformMachine UniformPairMachine
noncomputable section
abbrev V (n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev W:ℕ:=UniformRecursiveSelfCallMachine.W
def kernel (n:ℕ) (j:Fin (V n)):Scalar:=
 UniformChirpKernelMachine.kernelScalar (OAI.ExactFourier.zeta (2*n)) n (V n) j.val
def data {n:ℕ} (x:Fin n→ℂ) (j:Fin (V n)):Scalar:=
 UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
  (UniformCRTTraversalCycle.alphaPermutation n j).val
def input {n:ℕ} (x:Fin n→ℂ) (mode:Bool):Fin (V n)→Scalar:=
 if mode then kernel n else data x
def values {n:ℕ} (x:Fin n→ℂ) (mode:Bool) (AP:Fin (V n)≃Fin (V n)):
 ℕ→Fin (V n)→Scalar:=UniformRoleInputMachine.roleValue (input x mode) (kernel n) AP
lemma kernel_prepared (n:ℕ) (j:Fin (V n)):(kernel n j).dependent=false:=
 UniformChirpKernelMachine.kernelScalar_prepared _ _ _ _
lemma prepared {n:ℕ} (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (i:ℕ) (j:Fin (V n)):
 (values x true AP i j).dependent=false:=by
 apply UniformRoleInputMachine.all_prepared
 · exact kernel_prepared n
 · exact kernel_prepared n
lemma kernel_one {n:ℕ} [NeZero (V n)] (AP:Fin (V n)≃Fin (V n)) (mode:Bool)
 (x:Fin n→ℂ) (j:Fin (V n)):
 (values x mode AP 1 j).value=UniformFinalNumericJoin.kernel (n:=n) (AP j):=by
 have h:=UniformChirpKernelMachine.kernelScalar_fin (OAI.ExactFourier.zeta (2*n)) n (V n)
  (UniformWorkingLength.workingLength_lower n) (AP j)
 simp only[values,UniformRoleInputMachine.roleValue,show (1:ℕ)≠0 by decide,ite_false,ite_true,kernel]
 rw[h]
 rfl
lemma data_zero {n:ℕ} [NeZero (V n)] (AP:Fin (V n)≃Fin (V n)) (x:Fin n→ℂ) (j:Fin (V n)):
 (values x false AP 0 j).value=
 UniformFinalNumericJoin.data x (UniformCRTTraversalCycle.alphaPermutation n j):=by
 exact UniformFinalNumericJoin.padded_input_value (UniformCRTTraversalCycle.alphaPermutation n) x j
end
end ExactFourierCircuits.UniformFinalRoleModel
