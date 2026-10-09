import UniformAlternateFourierSchedule
import UniformMasterSynchronizedLayers

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAlternateSynchronizedSchedule
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformSynchronizedLayers

def axisLayers (n : ℕ) (i : axes n) := UniformAlternateFourierSchedule.specified (radix n i)

theorem local_length {n : ℕ} (hn : 0<n) (i : axes n) :
    (axisLayers n i).length≤UniformCommonSlots.slotCount n := by
  rw [axisLayers,UniformAlternateFourierSchedule.specified_length]
  exact localSchedules_length hn i

def schedule (n : ℕ) (hn : 0<n) := tensorSchedule (axisLayers n) (local_length hn)

theorem schedule_length (n : ℕ) (hn : 0<n) :
    (schedule n hn).length=UniformCommonSlots.slotCount n := tensorSchedule_length _ _

/-- A concrete alternate schedule, matching standard swapped transpose macros,
has the same Fourier tensor endpoint and the same synchronized slot count. -/
theorem schedule_product (n : ℕ) (hn : 0<n) :
    (schedule n hn).reverse.prod=PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i)) := by
  rw [schedule,tensorSchedule_product]
  apply congrArg PiTensor.matrix
  funext i
  exact UniformAlternateFourierSchedule.specified_matrix _

theorem selected_product (n : ℕ) (hn : 0<n) :
    (schedule n hn).reverse.prod=(selectedSchedule n hn).reverse.prod := by
  rw [schedule_product,selectedSchedule_product]

def ordinal (n : ℕ) (hn : 0<n) :=
  Matrix.reindex (UniformCRTTraversalCycle.ordinalEquiv n).symm
    (UniformCRTTraversalCycle.ordinalEquiv n).symm (schedule n hn).reverse.prod

theorem ordinal_eq (n : ℕ) (hn : 0<n) :
    ordinal n hn=UniformMasterSynchronizedLayers.ordinalMatrix n hn := by
  rw [ordinal,schedule_product,UniformMasterSynchronizedLayers.ordinalMatrix,
    UniformMasterSynchronizedLayers.schedule_radices]

theorem inverse_beta_restores (n : ℕ) (hn : 0<n)
    (x : Fin (UniformWorkingLength.workingLength n)→ℂ)
    (j : Fin (UniformWorkingLength.workingLength n)) :
    (ordinal n hn).mulVec (x ∘ UniformCRTTraversalCycle.alphaPermutation n)
      ((UniformCRTTraversalCycle.betaPermutation n).symm j)=
        (fourierMatrix (UniformWorkingLength.workingLength n)).mulVec x j := by
  rw [ordinal_eq]
  exact UniformMasterSynchronizedLayers.inverse_beta_restores n hn x j

end
end ExactFourierCircuits.UniformAlternateSynchronizedSchedule
