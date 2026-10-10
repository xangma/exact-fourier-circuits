import DFTModelSavingFuelWork
import DFTModelSavingResidualBilledData

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeRecursiveIH
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open DFTModelSavingResidualNativeGroup
noncomputable section
attribute [local irreducible] P.program DFTModelSavingProgram.program

/-- Transfer the actual strong induction result to the exact depthRun handler
used by the parent syntax. This retains source runs, output tags and ticks;
the bounded fuel discrepancy is absorbed by the real call overhead. -/
theorem billed (parent fuel n B reserve stack stackTop K : ℕ) (cost : ℕ→ℕ)
    (x : Fin n→ℂ) (I : ℂ) (enough : parent≤fuel+1) (cap : 3≤K)
    (before : BilledPairSmallerBodies parent n B reserve stack stackTop K 0 cost x I
      (run DFTModelSavingProgram.program)) :
    BilledPairSmallerBodies parent n B reserve stack stackTop K K cost x I
      (DFTModelSavingSelfCall.evaluate fuel) := by
  intro q smaller A F depth input input0 s s0 same pc bits base size fresh sp dp data data0 positive
    low endData roomStack endStack code room square constants bound
  obtain ⟨u,u0,ticks,actual,zero,matched,paired,work⟩:=before q smaller A F depth input input0 s s0
    same pc bits base size fresh sp dp data data0 positive low endData roomStack endStack code room square constants bound
  have transfer:=DFTModelSavingSelfCall.fuel_closed_all q fuel (by omega) I
    (DFTModelRecursiveScalarSource.paired input input0)
  refine ⟨u,u0,ticks,actual,zero,matched,?_,?_⟩
  · intro i j
    rw [transfer.1]
    exact paired i j
  · have a:=transfer.2
    omega

end
end ExactFourierCircuits.DFTModelSavingNativeRecursiveIH
