import UniformSynchronizedLayers
import UniformMasterRootSeedDAG
import UniformGlobalLocalPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMasterSynchronizedLayers
open OAI.ExactFourier UniformLocalFourierLayers UniformSynchronizedLayers
noncomputable section
open scoped BigOperators

abbrev size (n : ℕ) (i : axes n) := radix n i-1+1

theorem size_eq (n : ℕ) (i : axes n) : size n i=radix n i :=
  Nat.sub_add_cancel (UniformSelectedCRT.radix_pos n i)

theorem radix_divides (n : ℕ) (i : axes n) : radix n i∣UniformWorkingLength.workingLength n := by
  rw [←UniformSelectedCRT.radices_product]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

def localSchedules (n : ℕ) (hn : 0<n) (i : axes n) : List (Layer (size n i)) :=
  UniformMasterRootSeedDAG.selectedSchedule n (UniformWorkingLength.workingLength n) (radix n i-1) hn
    (by change size n i≤_;rw [size_eq];exact UniformGlobalLocalPreparation.radix_le_length n i)
    (by change size n i ∣ _;rw [size_eq];exact radix_divides n i)

theorem localSchedules_matrix (n : ℕ) (hn : 0<n) (i : axes n) :
    matrix (localSchedules n hn i)=fourierMatrix (size n i) := by
  unfold localSchedules UniformMasterRootSeedDAG.selectedSchedule UniformMasterRootSeedDAG.localSchedule
  exact UniformLocalPreparationReferences.fourierSchedule_matrix _ _ _ _ _ _ _ _ _
    (UniformMasterRootSeedDAG.masterSeed_cachesGood _ _)
    (UniformMasterRootSeedDAG.masterSeed_admissible _ _
      (UniformBatching.masterRootOrder_pos hn (UniformWorkingLength.workingLength_pos hn))
      (UniformMasterRootSeedDAG.selected_axis_divides
        (by change size n i ∣ _;rw [size_eq];exact radix_divides n i)))

theorem localSchedules_length (n : ℕ) (hn : 0<n) (i : axes n) :
    (localSchedules n hn i).length≤UniformCommonSlots.slotCount n := by
  have h:=UniformMasterRootSeedDAG.localSchedule_slots
    (UniformBatching.masterRootOrder n (UniformWorkingLength.workingLength n)) (radix n i-1)
    (UniformBatching.masterRootOrder_pos hn (UniformWorkingLength.workingLength_pos hn))
    (UniformMasterRootSeedDAG.selected_axis_divides (by change size n i ∣ _;rw [size_eq];exact radix_divides n i))
    (UniformMasterRootSeedDAG.selected_dyadic_divides (by omega)
      (by change size n i≤_;rw [size_eq];exact UniformGlobalLocalPreparation.radix_le_length n i))
  change (localSchedules n hn i).length≤_ at h
  have hs:=UniformCommonSlots.localSlots_bound hn i
  change UniformLocalFourierWord.sufficientSlots (radix n i)≤_ at hs
  rw [←size_eq n i] at hs
  exact h.trans hs

def schedule (n : ℕ) (hn : 0<n) :=
  tensorSchedule (localSchedules n hn) (localSchedules_length n hn)

theorem schedule_length (n : ℕ) (hn : 0<n) :
    (schedule n hn).length=UniformCommonSlots.slotCount n := tensorSchedule_length _ _

/-- All axis coefficient schedules derive from the SAME specified master-root
input. No assumed prepared table, root-reference list or Fourier action remains.
This is a typed schedule identity; its RAM printer and execution remain separate. -/
theorem schedule_product (n : ℕ) (hn : 0<n) :
    (schedule n hn).reverse.prod=PiTensor.matrix (fun i : axes n=>fourierMatrix (size n i)) := by
  rw [schedule,tensorSchedule_product]
  apply congrArg PiTensor.matrix
  funext i
  exact localSchedules_matrix n hn i

def coordinates (n : ℕ) : (∀i : axes n,Fin (size n i)) ≃ (∀i : axes n,Fin (radix n i)) :=
  Equiv.piCongrRight (fun i=>finCongr (size_eq n i))

theorem schedule_radices (n : ℕ) (hn : 0<n) :
    Matrix.reindex (coordinates n) (coordinates n) (schedule n hn).reverse.prod=
      PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i)) := by
  rw [schedule_product]
  ext x y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,PiTensor.matrix,fourierMatrix]
  apply Finset.prod_congr rfl
  intro i _
  simp [coordinates,size_eq]

theorem schedule_action (n : ℕ) (hn : 0<n) (x : (∀i : axes n,Fin (radix n i))→ℂ) :
    (Matrix.reindex (coordinates n) (coordinates n) (schedule n hn).reverse.prod).mulVec x=
      (PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i))).mulVec x := by
  rw [schedule_radices]

/-- The slot product on the actual mixed-radix ordinal array. -/
def ordinalMatrix (n : ℕ) (hn : 0<n) :
    Matrix (Fin (UniformWorkingLength.workingLength n)) (Fin (UniformWorkingLength.workingLength n)) ℂ :=
  Matrix.reindex (UniformCRTTraversalCycle.ordinalEquiv n).symm
    (UniformCRTTraversalCycle.ordinalEquiv n).symm
    (Matrix.reindex (coordinates n) (coordinates n) (schedule n hn).reverse.prod)

theorem ordinalMatrix_entry (n : ℕ) (hn : 0<n)
    (k j : Fin (UniformWorkingLength.workingLength n)) :
    ordinalMatrix n hn k j=fourierMatrix (UniformWorkingLength.workingLength n)
      (UniformCRTTraversalCycle.betaPermutation n k) (UniformCRTTraversalCycle.alphaPermutation n j) := by
  rw [ordinalMatrix,schedule_radices]
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,PiTensor.matrix,fourierMatrix]
  have hp:=UniformCRTTraversalCycle.permutation_fourier_entry n j k
  simpa only [fourierMatrix,Nat.mul_comm] using hp.symm

/-- The actual alpha input gather and independent beta output map close the
mathematical all-length working Fourier transform of this master-root schedule. -/
theorem ordinalMatrix_action (n : ℕ) (hn : 0<n)
    (x : Fin (UniformWorkingLength.workingLength n)→ℂ)
    (k : Fin (UniformWorkingLength.workingLength n)) :
    (ordinalMatrix n hn).mulVec (x ∘ UniformCRTTraversalCycle.alphaPermutation n) k=
      (fourierMatrix (UniformWorkingLength.workingLength n)).mulVec x
        (UniformCRTTraversalCycle.betaPermutation n k) := by
  simp only [Matrix.mulVec,dotProduct,Function.comp_apply,ordinalMatrix_entry]
  exact (UniformCRTTraversalCycle.alphaPermutation n).sum_comp
    (fun j : Fin (UniformWorkingLength.workingLength n)=>
      fourierMatrix (UniformWorkingLength.workingLength n) (UniformCRTTraversalCycle.betaPermutation n k) j*x j)

theorem inverse_beta_restores (n : ℕ) (hn : 0<n)
    (x : Fin (UniformWorkingLength.workingLength n)→ℂ)
    (j : Fin (UniformWorkingLength.workingLength n)) :
    (ordinalMatrix n hn).mulVec (x ∘ UniformCRTTraversalCycle.alphaPermutation n)
        ((UniformCRTTraversalCycle.betaPermutation n).symm j)=
      (fourierMatrix (UniformWorkingLength.workingLength n)).mulVec x j := by
  rw [ordinalMatrix_action,Equiv.apply_symm_apply]

end
end ExactFourierCircuits.UniformMasterSynchronizedLayers
