import DFTModelOuterTailPaired
import UniformFinalOuterProgram
import DFTModelChirpCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterTail
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- These are exactly the original source's final three stages, in order. -/
theorem original_stages (table : UniformMachine.Program) :
    stages=(UniformFinalOuterProgram.stagesFor table).drop 17 := rfl

/-- The existing charged typed chirp producer supplies the coefficient tape
read by this suffix; no independent coefficient action is postulated. -/
theorem produced_coefficients {n : ℕ} (hn : 0<n) (j : ℕ) (hj : j<n) :
    (run DFTModelChirp.program (n,OAI.ExactFourier.zeta (2*n))).val.look (2*j) 0=
      UniformChirp.chirp (OAI.ExactFourier.zeta (2*n)) j := by
  rw [DFTModelChirp.specified_value n hn]
  exact DFTModelChirp.bank_even n j _ hj

end
end ExactFourierCircuits.DFTModelOuterTail
