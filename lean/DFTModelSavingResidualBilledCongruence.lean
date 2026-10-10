import DFTModelSavingResidualCongruence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualBilledCongruence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelClockBatch.calls DFTModelClockBatch.flatten
  DFTModelSavingResidualFinish.program DFTModelSavingResidualSetup.program

theorem batch_work_congr (h h' : Handler Port) (q G T : ℕ) (I : ℂ)
  (bank : Tape Tagged.T)
  (same : ∀ (J : ℂ) (v : Tape Tagged.T), (h ((q,J),v)).work=(h' ((q,J),v)).work) :
  (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h ((q,I),(G,(T,bank)))).work=
  (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h' ((q,I),(G,(T,bank)))).work := by
  have sum : (∑g∈Finset.range G,(h ((q,I),DFTModelClockBatch.sliced T g bank Tagged.blank)).work)=
    ∑g∈Finset.range G,(h' ((q,I),DFTModelClockBatch.sliced T g bank Tagged.blank)).work := by
    exact Finset.sum_congr rfl (fun _ _=>same I _)
  rw [DFTModelSavingResidualBatch.work,DFTModelSavingResidualBatch.work,sum]

/-- The actual residual bill depends only on child values and work at its
physically derived exponent. No peak or validity congruence is asserted. -/
theorem work_congr (h h' : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T)
  (sameValue : ∀ (J : ℂ) (v : Tape Tagged.T), (h ((ctx.1,J),v)).val=(h' ((ctx.1,J),v)).val)
  (sameWork : ∀ (J : ℂ) (v : Tape Tagged.T), (h ((ctx.1,J),v)).work=(h' ((ctx.1,J),v)).work) :
  (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).work=
  (Code.run DFTModelSavingResidual.program h' (ctx,(a,(raw,((k,I),old))))).work := by
  have ret : returned h (ctx,(a,(raw,((k,I),old))))=
    returned h' (ctx,(a,(raw,((k,I),old)))) := by
    rw [returned,returned,args_value]
    exact DFTModelSavingResidualCongruence.batch_value_congr h h' ctx.1 _ _ I _ sameValue
  have bill : (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h
    (arguments (ctx,(a,(raw,((k,I),old)))))).work=
    (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h'
      (arguments (ctx,(a,(raw,((k,I),old)))))).work := by
    rw [args_value]
    exact batch_work_congr h h' ctx.1 _ _ I _ sameWork
  rw [DFTModelSavingResidual.work_exact,DFTModelSavingResidual.work_exact,ret,bill]

theorem value_work_congr (h h' : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T)
  (same : ∀ (J : ℂ) (v : Tape Tagged.T),
    (h ((ctx.1,J),v)).val=(h' ((ctx.1,J),v)).val ∧
    (h ((ctx.1,J),v)).work=(h' ((ctx.1,J),v)).work) :
  (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).val=
    (Code.run DFTModelSavingResidual.program h' (ctx,(a,(raw,((k,I),old))))).val ∧
  (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).work=
    (Code.run DFTModelSavingResidual.program h' (ctx,(a,(raw,((k,I),old))))).work :=
  ⟨DFTModelSavingResidualCongruence.value_congr h h' ctx a raw k I old (fun J v=>(same J v).1),
    work_congr h h' ctx a raw k I old (fun J v=>(same J v).1) (fun J v=>(same J v).2)⟩

end
end ExactFourierCircuits.DFTModelSavingResidualBilledCongruence
