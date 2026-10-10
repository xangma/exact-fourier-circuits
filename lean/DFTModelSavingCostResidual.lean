import DFTModelSavingResidualGeometry
import DFTModelResidualClosedLinearWork

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelResidualClosedBasis (Meta)
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program DFTModelSavingResidualSetup.program
  DFTModelResidualClosedRole.gather DFTModelResidualClosedAddresses.program
  DFTModelSavingResidualFinish.program DFTModelSavingResidualBatch.program
  UniformBatching.width

/-- The generated address tape fixes the real complete-batch size. No child
length or computed child action is assumed. -/
theorem residual_geometry (h : Handler Port) (ctx : Meta.T) (a raw k : ℕ)
    (I : ℂ) (old : Tape Tagged.T) :
    let x:Input.T:=(ctx,(a,(raw,((k,I),old))))
    let L:=(run DFTModelResidualClosedAddresses.program ctx).val.len
    let T:=UniformBatching.width*2^ctx.1
    (arguments x).2.1=L/T ∧ (arguments x).2.2.1=T ∧
      (returned h x).len=(L/T)*T := by
  dsimp only
  rw [args_value,DFTModelResidualClosedRole.gather_value,DFTModelResidualMovement.gather_value]
  refine ⟨rfl,rfl,?_⟩
  rw [returned,DFTModelSavingResidualBatch.length,args_value,
    DFTModelResidualClosedRole.gather_value,DFTModelResidualMovement.gather_value]
  rfl

/-- Charged local work plus one occurrence of each actual paired child call.
This bound is unconditional in the child handler's output or tags. -/
theorem residual_work (h : Handler Port) (ctx : Meta.T) (a raw k : ℕ)
    (I : ℂ) (old : Tape Tagged.T) :
    let x:Input.T:=(ctx,(a,(raw,((k,I),old))))
    let L:=(run DFTModelResidualClosedAddresses.program ctx).val.len
    let T:=UniformBatching.width*2^ctx.1
    (Code.run DFTModelSavingResidual.program h x).work≤
      (run DFTModelResidualClosedAddresses.program ctx).work+181*L+104*old.len+
        21*(L/T)+22*ctx.2.1+8*ctx.1+301+
          ∑g∈Finset.range (arguments x).2.1,
            (h ((arguments x).1,DFTModelClockBatch.sliced (arguments x).2.2.1 g
              (arguments x).2.2.2 Tagged.blank)).work := by
  dsimp only
  let x:Input.T:=(ctx,(a,(raw,((k,I),old))))
  let L:=(run DFTModelResidualClosedAddresses.program ctx).val.len
  let T:=UniformBatching.width*2^ctx.1
  have geometry:=residual_geometry h ctx a raw k I old
  have setup:=DFTModelSavingResidualSetup.work ctx a raw k I old
  rw [DFTModelResidualClosedRole.gather_work] at setup
  have batch:=(DFTModelSavingResidualBatch.work Params Tagged h (arguments x).1
    (arguments x).2.1 (arguments x).2.2.1 (arguments x).2.2.2)
  have finish:=DFTModelSavingResidualFinish.work (prepared x).1 (prepared x).2.1
    (prepared x).2.2 (returned h x)
  have arg: (run batchArgs (prepared x)).work=53 := by
    rcases prepared x with ⟨f,N,T⟩
    exact congrArg Bill.work (batchArgs_run f N T)
  have preparedEq : prepared x=
    ((run initial x).val,(2^ctx.1,UniformBatching.width*2^ctx.1)) :=
      DFTModelSavingResidualSetup.value ctx a raw k I old
  rw [preparedEq,initial_value,DFTModelResidualClosedRole.gather_value] at finish
  dsimp only [Bill.val] at finish
  have mul:(L/T)*T≤L:=Nat.div_mul_le_self L T
  have gl:(arguments x).2.1=L/T:=geometry.1
  have gt:(arguments x).2.2.1=T:=geometry.2.1
  have rl:(returned h x).len=(L/T)*T:=geometry.2.2
  rw [rl] at finish
  rw [work_exact,arg]
  change (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h
    ((arguments x).1,((arguments x).2.1,((arguments x).2.2.1,(arguments x).2.2.2)))).work=_ at batch
  rw [batch]
  rw [preparedEq,initial_value,DFTModelResidualClosedRole.gather_value]
  dsimp only [Bill.val,x,L,T] at *
  rw [gl,gt]
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
