import UniformChirpOutputMachine
import UniformChirpPointwiseMachine
import UniformCRTTraversalCycle

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 (5.7) and
three-transform argument, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Joins physical CRT coordinates, the actual fixed/data spectra and final
normalized output. Conditional numeric helpers are discharged by the actual
clock and movement executions in UniformFinalDFTExecution.execution.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalNumericJoin
open UniformMachine UniformPairMachine OAI.ExactFourier
open scoped BigOperators
noncomputable section

/-- Physical input and output coordinates of a positive transform. -/
/- Paper stage: §5.2 (5.5), PDF p.22: physical input/output reindexing preserves sign and normalization. -/
def physicalFourier {L : ℕ} (AP BP : Fin L ≃ Fin L) : Matrix (Fin L) (Fin L) ℂ :=
  (fourierMatrix L).submatrix BP AP

/-- Reindexing changes physical addresses, not the Fourier sign or scale. -/
theorem physicalFourier_action {L : ℕ} (AP BP : Fin L ≃ Fin L) (f : Fin L → ℂ)
    (i : Fin L) :
    (physicalFourier AP BP).mulVec (fun j => f (AP j)) i =
      (fourierMatrix L).mulVec f (BP i) := by
  change (∑ j, fourierMatrix L (BP i) (AP j) * f (AP j)) =
    ∑ j, fourierMatrix L (BP i) j * f j
  exact AP.sum_comp (fun j => fourierMatrix L (BP i) j * f j)

/-- The physical MSB codec may be any equivalence to the normal CRT ordinal. -/
def inputCoordinate (n : ℕ) (rho : Fin (UniformCRTTraversalCycle.len n) ≃
    Fin (UniformCRTTraversalCycle.len n)) := rho.trans (UniformCRTTraversalCycle.alphaPermutation n)
def outputCoordinate (n : ℕ) (rho : Fin (UniformCRTTraversalCycle.len n) ≃
    Fin (UniformCRTTraversalCycle.len n)) := rho.trans (UniformCRTTraversalCycle.betaPermutation n)

theorem crt_physical_entry (n : ℕ) (rho : Fin (UniformCRTTraversalCycle.len n) ≃
    Fin (UniformCRTTraversalCycle.len n)) (i j : Fin (UniformCRTTraversalCycle.len n)) :
    physicalFourier (inputCoordinate n rho) (outputCoordinate n rho) i j =
      ∏ a, zeta (UniformCRTTraversalCycle.radices n a) ^
        ((UniformCRTTraversalCycle.ordinalEquiv n (rho i) a).val *
         (UniformCRTTraversalCycle.ordinalEquiv n (rho j) a).val) := by
  have h := UniformCRTTraversalCycle.permutation_fourier_entry n (rho j) (rho i)
  change zeta (UniformCRTTraversalCycle.len n) ^
    ((UniformCRTTraversalCycle.betaPermutation n (rho i)).val *
     (UniformCRTTraversalCycle.alphaPermutation n (rho j)).val) = _
  rw [Nat.mul_comm]
  change fourierMatrix (UniformCRTTraversalCycle.len n)
    (UniformCRTTraversalCycle.alphaPermutation n (rho j))
    (UniformCRTTraversalCycle.betaPermutation n (rho i)) = _
  rw [h]
  apply Finset.prod_congr rfl
  intro a _
  rw [Nat.mul_comm]

/-- This identifies the actual MSB-reindexed all-axis DFT matrix, not merely
its dimensions, with the AP-input/BP-output physical Fourier matrix. -/
theorem crt_physical_matrix (n : ℕ) (rho : Fin (UniformCRTTraversalCycle.len n) ≃
    Fin (UniformCRTTraversalCycle.len n)) :
    physicalFourier (inputCoordinate n rho) (outputCoordinate n rho) =
      Matrix.reindex ((rho.trans (UniformCRTTraversalCycle.ordinalEquiv n)).symm)
        ((rho.trans (UniformCRTTraversalCycle.ordinalEquiv n)).symm)
        (PiTensor.matrix (fun a => fourierMatrix (UniformCRTTraversalCycle.radices n a))) := by
  ext i j
  exact crt_physical_entry n rho i j

/-- Standard finite coordinates for the already proved cyclic transform. -/
def finite {L : ℕ} [NeZero L] (f : ZMod L → ℂ) (i : Fin L) : ℂ :=
  f (FourierCRT.finZMod L i)

theorem toZMod_finite {L : ℕ} [NeZero L] (f : ZMod L → ℂ) : UniformCyclic.toZMod (finite f) = f := by
  funext z
  simp [UniformCyclic.toZMod, finite]

theorem fourier_finite {L : ℕ} [NeZero L] (f : ZMod L → ℂ) (i : Fin L) :
    (fourierMatrix L).mulVec (finite f) i = finite (UniformCyclic.positiveDFT f) i := by
  rw [← UniformCyclic.positiveDFT_fin, toZMod_finite]
  rfl

def kernel {n L : ℕ} [NeZero L] : Fin L → ℂ :=
  finite (UniformCyclic.chirpKernel (zeta (2*n)) n)
def data {n L : ℕ} [NeZero L] (x : Fin n → ℂ) : Fin L → ℂ :=
  finite (UniformCyclic.paddedChirp (zeta (2*n)) x)
def kernelSpectrum {n L : ℕ} [NeZero L] : Fin L → ℂ :=
  finite (UniformCyclic.positiveDFT (UniformCyclic.chirpKernel (zeta (2*n)) n))
def dataSpectrum {n L : ℕ} [NeZero L] (x : Fin n → ℂ) : Fin L → ℂ :=
  finite (UniformCyclic.positiveDFT (UniformCyclic.paddedChirp (zeta (2*n)) x))
def spectralProduct {n L : ℕ} [NeZero L] (x : Fin n → ℂ) : Fin L → ℂ :=
  fun i => dataSpectrum x i * kernelSpectrum (n:=n) i

theorem kernel_transform {n L : ℕ} [NeZero L] (AP BP : Fin L ≃ Fin L) (i : Fin L) :
    (physicalFourier AP BP).mulVec (fun j => kernel (n:=n) (AP j)) i =
      kernelSpectrum (n:=n) (BP i) := by
  rw [physicalFourier_action]
  exact fourier_finite (UniformCyclic.chirpKernel (zeta (2*n)) n) _
theorem data_transform {n L : ℕ} [NeZero L] (AP BP : Fin L ≃ Fin L)
    (x : Fin n → ℂ) (i : Fin L) :
    (physicalFourier AP BP).mulVec (fun j => data x (AP j)) i = dataSpectrum x (BP i) := by
  rw [physicalFourier_action]
  exact fourier_finite (UniformCyclic.paddedChirp (zeta (2*n)) x) _

/-- Exactly the matrix action to be supplied by each actual finite clock run. -/
def TransformValues {L : ℕ} (AP BP : Fin L ≃ Fin L)
    (v w : Fin L → Scalar) : Prop :=
  ∀ i, (w i).value = (physicalFourier AP BP).mulVec (fun j => (v j).value) i

/-- Both actual CRT gather loops preserve whole Scalars and therefore their tags. -/
theorem reindex_product {L : ℕ} (AP BP : Fin L ≃ Fin L)
    (p standard next : Fin L → Scalar)
    (toStandard : ∀ i, standard i = p (BP.symm i))
    (toInput : ∀ i, next i = standard (AP i)) (i : Fin L) :
    next i = p (BP.symm (AP i)) := by rw [toInput, toStandard]

/-- Numeric three-transform join. The reindexing equalities describe the actual
CRT copies, and the transform premises are the three actual clock postconditions. -/
/- Paper stage: §5.3, three-transform argument, PDF p.23: pure algebraic helper, conditional on three transform and movement postconditions. -/
theorem three_transforms {n L : ℕ} [NeZero L] (AP BP : Fin L ≃ Fin L)
    (x : Fin n → ℂ) (kin din ks ds p standard next ts out : Fin L → Scalar)
    (kernelInput : ∀ i, (kin i).value = kernel (n:=n) (AP i))
    (dataInput : ∀ i, (din i).value = data x (AP i))
    (kernelRun : TransformValues AP BP kin ks)
    (dataRun : TransformValues AP BP din ds)
    (pointwise : ∀ i, (p i).value = (ds i).value * (ks i).value)
    (toStandard : ∀ i, standard i = p (BP.symm i))
    (toInput : ∀ i, next i = standard (AP i))
    (thirdRun : TransformValues AP BP next ts)
    (finalStandard : ∀ i, out i = ts (BP.symm i)) :
    UniformChirpOutputMachine.FinalSpectrum x out := by
  have hk : ∀ i, (ks i).value = kernelSpectrum (n:=n) (BP i) := by
    intro i
    rw [kernelRun i]
    simpa only [kernelInput] using kernel_transform (n:=n) AP BP i
  have hd : ∀ i, (ds i).value = dataSpectrum x (BP i) := by
    intro i
    rw [dataRun i]
    simpa only [dataInput] using data_transform AP BP x i
  have hp : ∀ i, (p i).value = spectralProduct x (BP i) := by
    intro i
    rw [pointwise i, hd i, hk i]
    rfl
  have hn : ∀ i, (next i).value = spectralProduct x (AP i) := by
    intro i
    rw [reindex_product AP BP p standard next toStandard toInput, hp]
    simp only [Equiv.apply_symm_apply]
  intro i
  rw [finalStandard i, thirdRun (BP.symm i)]
  simp only [hn]
  rw [physicalFourier_action, Equiv.apply_symm_apply]
  change (fourierMatrix L).mulVec (finite (fun t =>
    UniformCyclic.positiveDFT (UniformCyclic.paddedChirp (zeta (2*n)) x) t *
    UniformCyclic.positiveDFT (UniformCyclic.chirpKernel (zeta (2*n)) n) t)) i = _
  exact fourier_finite _ i


/-- The actual input producer's mixed tags are retained; only values enter DFT algebra. -/
theorem padded_input_value {n L : ℕ} [NeZero L] (AP : Fin L ≃ Fin L)
    (x : Fin n → ℂ) (i : Fin L) :
    (UniformPaddedInputMachine.paddedScalar (zeta (2*n)) x (AP i).val).value = data x (AP i) :=
  UniformPaddedInputMachine.paddedScalar_cyclic _ _ _

/-- Numeric projection of present physical cells, as used by the actual clock. -/
/- Paper stage: Implementation heap bookkeeping for §5.3, PDF p.23: present scalar cells and their values, with no Fourier result assumed by the definition. -/
def NumericValues {L : ℕ} (A : ℕ) (f : Fin L → ℂ) (s : State) : Prop :=
  ∀ i, (s.scalarHeap (A+i.val)).map Scalar.value = some (f i)
def scalars (L A : ℕ) (s : State) (i : Fin L) : Scalar :=
  (s.scalarHeap (A+i.val)).getD Scalar.zero

theorem numeric_present {L A : ℕ} {f : Fin L → ℂ} {s : State}
    (h : NumericValues A f s) (i : Fin L) :
    s.scalarHeap (A+i.val) = some (scalars L A s i) := by
  cases hs : s.scalarHeap (A+i.val) with
  | none => have hi := h i; simp only [hs, Option.map_none] at hi; contradiction
  | some v => simp [scalars, hs]

theorem numeric_value {L A : ℕ} {f : Fin L → ℂ} {s : State}
    (h : NumericValues A f s) (i : Fin L) : (scalars L A s i).value = f i := by
  have hi := h i
  rw [numeric_present h i] at hi
  exact Option.some.inj hi

theorem numeric_of_values {L A : ℕ} (v : Fin L → Scalar) (s : State)
    (h : UniformChirpOutputMachine.Values L A v s) :
    NumericValues A (fun i => (v i).value) s := by
  intro i
  rw [h i]
  rfl

/-- An actual finite transform's numeric heap postcondition. This is the sole
Fourier execution boundary; it contains no readiness or desired final spectrum. -/
def HeapTransform {L : ℕ} (AP BP : Fin L ≃ Fin L) (A D : ℕ) (s u : State) : Prop :=
  NumericValues D ((physicalFourier AP BP).mulVec (fun i => (scalars L A s i).value)) u

theorem heap_transform {L A D : ℕ} (AP BP : Fin L ≃ Fin L) (f : Fin L → ℂ)
    (s u : State) (input : NumericValues A (fun i => f (AP i)) s)
    (run : HeapTransform AP BP A D s u) :
    NumericValues D (fun i => (fourierMatrix L).mulVec f (BP i)) u := by
  have hv : (fun i => (scalars L A s i).value) = fun i => f (AP i) :=
    funext (numeric_value input)
  intro i
  simpa only [hv, physicalFourier_action] using run i

/-- A real scalar copy of an all-prepared transform bank remains prepared. -/
theorem prepared_copy {L A D : ℕ} (f : Fin L → ℂ) (s u : State)
    (input : NumericValues A f s)
    (tags : ∀ i, (scalars L A s i).dependent = false)
    (copied : ∀ i : Fin L, u.scalarHeap (D+i.val) = s.scalarHeap (A+i.val)) :
    ∀ i, u.scalarHeap (D+i.val) = some (prepared (f i)) := by
  intro i
  rw [copied i, numeric_present input i]
  have value := numeric_value input i
  have tag := tags i
  congr 1
  cases hs : scalars L A s i with
  | mk a b =>
    simp only [hs] at value tag
    subst a
    subst b
    rfl

theorem prepared_multiplication (v : Scalar) (c : ℂ) :
    evalField .mul v (prepared c) = some (UniformChirpPointwiseMachine.productScalar v c) := by
  simp [evalField, prepared, UniformChirpPointwiseMachine.productScalar]

/-- Pure heap join for the actual three transforms, saved prepared kernel,
pointwise multiplication, two CRT copies before the third transform, and final
CRT copy. Every source is an actual state; no final Fourier value is assumed. -/
/- Paper stage: §5.3, PDF p.23: same-state heap join derives saved prepared spectrum and third output from actual producer postconditions. -/
theorem three_transform_heaps {n L : ℕ} [NeZero L]
    (AP BP : Fin L ≃ Fin L) (x : Fin n → ℂ) (AK A DK Q T : ℕ)
    (kernelIn kernelOut dataIn dataOut productOut thirdIn thirdOut finalOut : State)
    (kernelInput : NumericValues AK (fun i => kernel (n:=n) (AP i)) kernelIn)
    (kernelRun : HeapTransform AP BP AK DK kernelIn kernelOut)
    (kernelTags : ∀ i, (scalars L DK kernelOut i).dependent = false)
    (kernelSaved : ∀ i : Fin L,
      dataOut.scalarHeap (Q+i.val) = kernelOut.scalarHeap (DK+i.val))
    (dataInput : NumericValues A (fun i => data x (AP i)) dataIn)
    (dataRun : HeapTransform AP BP A A dataIn dataOut)
    (pointwise : NumericValues A (fun i =>
      (scalars L A dataOut i).value * (scalars L Q dataOut i).value) productOut)
    (thirdReindex : ∀ i : Fin L,
      thirdIn.scalarHeap (A+i.val) = productOut.scalarHeap (A+(BP.symm (AP i)).val))
    (thirdRun : HeapTransform AP BP A A thirdIn thirdOut)
    (finalReindex : ∀ i : Fin L,
      finalOut.scalarHeap (T+i.val) = thirdOut.scalarHeap (A+(BP.symm i).val)) :
    (∀ i, dataOut.scalarHeap (Q+i.val) = some (prepared (kernelSpectrum (n:=n) (BP i)))) ∧
    UniformChirpOutputMachine.Values L T (scalars L T finalOut) finalOut ∧
    UniformChirpOutputMachine.FinalSpectrum x (scalars L T finalOut) := by
  have hk : NumericValues DK (fun i => kernelSpectrum (n:=n) (BP i)) kernelOut := by
    have run := heap_transform AP BP (kernel (n:=n)) kernelIn kernelOut kernelInput kernelRun
    intro i
    simpa only [kernel, kernelSpectrum, fourier_finite] using run i
  have saved := prepared_copy _ kernelOut dataOut hk kernelTags kernelSaved
  have hq : NumericValues Q (fun i => kernelSpectrum (n:=n) (BP i)) dataOut := by
    intro i
    rw [saved i]
    rfl
  have hd : NumericValues A (fun i => dataSpectrum x (BP i)) dataOut := by
    have run := heap_transform AP BP (data x) dataIn dataOut dataInput dataRun
    intro i
    simpa only [data, dataSpectrum, fourier_finite] using run i
  have product : NumericValues A (fun i => spectralProduct x (BP i)) productOut := by
    intro i
    simpa only [numeric_value hd, numeric_value hq, spectralProduct] using pointwise i
  have thirdInput : NumericValues A (fun i => spectralProduct x (AP i)) thirdIn := by
    intro i
    rw [thirdReindex i]
    simpa only [Equiv.apply_symm_apply] using product (BP.symm (AP i))
  have third := heap_transform AP BP (spectralProduct x) thirdIn thirdOut thirdInput thirdRun
  have output : NumericValues T (fun i => (fourierMatrix L).mulVec (spectralProduct x) i) finalOut := by
    intro i
    rw [finalReindex i]
    simpa only [Equiv.apply_symm_apply] using third (BP.symm i)
  refine ⟨saved, numeric_present output, ?_⟩
  intro i
  rw [numeric_value output]
  change (fourierMatrix L).mulVec (finite (fun t =>
    UniformCyclic.positiveDFT (UniformCyclic.paddedChirp (zeta (2*n)) x) t *
    UniformCyclic.positiveDFT (UniformCyclic.chirpKernel (zeta (2*n)) n) t)) i = _
  exact fourier_finite _ i

/-- Final output execution from the joined actual heap value, including the
literal 1/L normalization and negative-frequency lookup of the existing loop. -/
theorem output_of_numeric {n L : ℕ} [NeZero L] (hn : 0<n) (hL : 0<L)
    (hnL : 2*n≤L) (x : Fin n → ℂ) (B a T c : ℕ) (s : State)
    (hp : s.pc=0) (hcount : s.natReg 8=n) (hwidth : s.natReg 17=L)
    (ha : s.natReg 25=a) (hd : s.natReg 26=T) (hc : s.natReg 27=c)
    (hnorm : s.scalarHeap c=some (prepared (L:ℂ)⁻¹))
    (hcoeff : UniformChirpOutputMachine.Coefficients n a (zeta (2*n)) s)
    (output : NumericValues T (fun i => (fourierMatrix L).mulVec (spectralProduct x) i) s)
    (hB : 64≤B) (hab : a+2*n≤B) (hdb : T+L≤B) (hs : WordBound B s) : ∃ u,
    BoundedExecution UniformChirpOutputMachine.program n x B s (13*n+6) u ∧
    ComputesDFT n x u ∧ UniformChirpOutputMachine.Frame n s u ∧ u.pc=17 := by
  have spectrum : UniformChirpOutputMachine.FinalSpectrum x (scalars L T s) := by
    intro i
    rw [numeric_value output]
    change (fourierMatrix L).mulVec (finite (fun t =>
      UniformCyclic.positiveDFT (UniformCyclic.paddedChirp (zeta (2*n)) x) t *
      UniformCyclic.positiveDFT (UniformCyclic.chirpKernel (zeta (2*n)) n) t)) i = _
    exact fourier_finite _ i
  exact UniformChirpOutputMachine.output_execution_dft hn hL hnL x B a T c
    (scalars L T s) s hp hcount hwidth ha hd hc hnorm hcoeff
    (numeric_present output) spectrum hB hab hdb hs


/-- Selected working volumes satisfy the chirp support condition for every
positive input length. This closes the final numeric/output join, independently
of the caller's still separate construction of the three finite clock runs. -/
/- Paper stage: §5.1 (5.4), PDF p.21 and §5.3, PDF p.23: selected length closes the signed-support condition before the real output loop. -/
theorem computesDFT_of_three_transform_heaps {n L : ℕ} [NeZero L]
    (hn : 0<n) (selected : L = UniformWorkingLength.workingLength n)
    (AP BP : Fin L ≃ Fin L) (x : Fin n → ℂ) (AK A DK Q T B a c : ℕ)
    (kernelIn kernelOut dataIn dataOut productOut thirdIn thirdOut finalOut : State)
    (kernelInput : NumericValues AK (fun i => kernel (n:=n) (AP i)) kernelIn)
    (kernelRun : HeapTransform AP BP AK DK kernelIn kernelOut)
    (kernelTags : ∀ i, (scalars L DK kernelOut i).dependent = false)
    (kernelSaved : ∀ i : Fin L,
      dataOut.scalarHeap (Q+i.val) = kernelOut.scalarHeap (DK+i.val))
    (dataInput : NumericValues A (fun i => data x (AP i)) dataIn)
    (dataRun : HeapTransform AP BP A A dataIn dataOut)
    (pointwise : NumericValues A (fun i =>
      (scalars L A dataOut i).value * (scalars L Q dataOut i).value) productOut)
    (thirdReindex : ∀ i : Fin L,
      thirdIn.scalarHeap (A+i.val) = productOut.scalarHeap (A+(BP.symm (AP i)).val))
    (thirdRun : HeapTransform AP BP A A thirdIn thirdOut)
    (finalReindex : ∀ i : Fin L,
      finalOut.scalarHeap (T+i.val) = thirdOut.scalarHeap (A+(BP.symm i).val))
    (hp : finalOut.pc=0) (hcount : finalOut.natReg 8=n) (hwidth : finalOut.natReg 17=L)
    (ha : finalOut.natReg 25=a) (hd : finalOut.natReg 26=T) (hc : finalOut.natReg 27=c)
    (hnorm : finalOut.scalarHeap c=some (prepared (L:ℂ)⁻¹))
    (hcoeff : UniformChirpOutputMachine.Coefficients n a (zeta (2*n)) finalOut)
    (hB : 64≤B) (hab : a+2*n≤B) (hdb : T+L≤B) (hs : WordBound B finalOut) : ∃ u,
    BoundedExecution UniformChirpOutputMachine.program n x B finalOut (13*n+6) u ∧
    ComputesDFT n x u ∧ UniformChirpOutputMachine.Frame n finalOut u ∧ u.pc=17 := by
  have joined := three_transform_heaps AP BP x AK A DK Q T kernelIn kernelOut dataIn dataOut
    productOut thirdIn thirdOut finalOut kernelInput kernelRun kernelTags kernelSaved
    dataInput dataRun pointwise thirdReindex thirdRun finalReindex
  have hL : 0<L := by simpa only [selected] using UniformWorkingLength.workingLength_pos hn
  have hnL : 2*n≤L := by simpa only [selected] using UniformWorkingLength.workingLength_lower n
  exact UniformChirpOutputMachine.output_execution_dft hn hL hnL x B a T c
    (scalars L T finalOut) finalOut hp hcount hwidth ha hd hc hnorm hcoeff
    joined.2.1 joined.2.2 hB hab hdb hs

end
end ExactFourierCircuits.UniformFinalNumericJoin
