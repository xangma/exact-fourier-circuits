import DFTModelSavingNativeSmallChild
import DFTModelSavingCostSetup
import DFTModelSavingBinaryCost

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeSmallBilling
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelClockControl DFTModelAffine
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.program DFTModelSavingProgram.ordinary
  DFTModelSavingProgram.body

/-- Fuel is a peak charge. In the finite branch the actual closed compiler
adds at most eighteen work steps to its one ordinary paired computation. -/
lemma program_work (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (small : k<UniformRecursiveSavingProgram.threshold) :
    (run DFTModelSavingProgram.program ((k,I),v)).work≤
      (run DFTModelSavingProgram.ordinary ((k,I),v)).work+18 := by
  rw [DFTModelSavingProgram.program_run]
  cases k with
  | zero=>
    change (run DFTModelSavingProgram.ordinary ((0,I),v)).work+1+7≤_
    omega
  | succ k=>
    change (Code.run DFTModelSavingProgram.body
      (depthRun (DFTModelSavingProgram.ordinary.run ()) DFTModelSavingProgram.body.run k)
      ((k+1,I),v)).work+1+7≤_
    rw [DFTModelSavingCost.body_run,ite_eq_left small]
    change (run DFTModelSavingProgram.ordinary ((k+1,I),v)).work+1+9+1+7≤_
    omega

/-- The billing is relative to the real positive-depth base execution time,
including its entry and finish. It does not use the recursive time budget. -/
theorem native_work {k : ℕ} (f f0 : Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
    (small : k<UniformRecursiveSavingProgram.threshold) :
    (run DFTModelSavingProgram.program ((k,Complex.I),paired f f0)).work≤
      33*(4+UniformRecursiveSmallBase.baseTicks UniformRecursiveSelfCallMachine.W k) := by
  have first:=program_work k Complex.I (paired f f0) small
  have ordinary:=DFTModelSavingBinary.program_native_work f f0
    (show 0<UniformRecursiveSelfCallMachine.W from by
      change 0<2^ExplicitSeedBudget.roleBits
      exact Nat.two_pow_pos _)
  have ordinaryBound : (run DFTModelSavingProgram.ordinary ((k,Complex.I),paired f f0)).work≤
      32*(UniformRecursiveSelfCallMachine.W*UniformBinaryBatchCMachine.arrayCost k+5) := by
    rw [DFTModelSavingProgram.ordinary]
    exact ordinary
  unfold UniformRecursiveSmallBase.baseTicks
  omega

end
end ExactFourierCircuits.DFTModelSavingNativeSmallBilling
