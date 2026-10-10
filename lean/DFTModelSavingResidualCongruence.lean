import DFTModelSavingResidualGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualCongruence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
noncomputable section
attribute [local irreducible] DFTModelClockBatch.calls DFTModelClockBatch.flatten
  DFTModelSavingResidualFinish.program DFTModelSavingResidualSetup.program

 theorem batch_value_congr (h h' : Handler Port) (q G T : ℕ) (I : ℂ)
  (bank : Tape Tagged.T)
  (same : ∀ (J : ℂ) (v : Tape Tagged.T), (h ((q,J),v)).val=(h' ((q,J),v)).val) :
  (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h ((q,I),(G,(T,bank)))).val=
  (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h' ((q,I),(G,(T,bank)))).val := by
  have calls : (Code.run (DFTModelClockBatch.calls Params Tagged) h ((q,I),(G,(T,bank)))).val=
    (Code.run (DFTModelClockBatch.calls Params Tagged) h' ((q,I),(G,(T,bank)))).val := by
    rw [DFTModelClockBatch.calls_value,DFTModelClockBatch.calls_value]
    exact congrArg (Tape.tab G) (funext (fun g=>same I _))
  simp only [DFTModelSavingResidualBatch.program,Code.run,
    DFTModelClockBatch.geometry,DFTModelClockBatch.arrange,Atom.run,Bill.pass,Bill.pay,Bill.one,calls]

theorem value_congr (h h' : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T)
  (same : ∀ (J : ℂ) (v : Tape Tagged.T), (h ((ctx.1,J),v)).val=(h' ((ctx.1,J),v)).val) :
  (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).val=
  (Code.run DFTModelSavingResidual.program h' (ctx,(a,(raw,((k,I),old))))).val := by
  rw [DFTModelSavingResidual.value,DFTModelSavingResidual.value]
  have ret : returned h (ctx,(a,(raw,((k,I),old))))=
    returned h' (ctx,(a,(raw,((k,I),old)))) := by
    rw [returned,returned,args_value]
    exact batch_value_congr h h' ctx.1 _ _ I _ same
  rw [ret]

end
end ExactFourierCircuits.DFTModelSavingResidualCongruence
