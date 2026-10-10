import DFTModelSavingResidualPeak
import DFTModelResidualClosedLinearWork

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualBounds
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry
open scoped BigOperators
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelSavingResidualSetup.program DFTModelSavingResidualFinish.program
  DFTModelSavingResidualBatch.program DFTModelResidualClosedRole.gather
  DFTModelResidualClosedAddresses.program

 theorem finish_work (h : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T) :
  (run DFTModelSavingResidualFinish.program
    (DFTModelSavingResidual.prepared (ctx,(a,(raw,((k,I),old)))),returned h (ctx,(a,(raw,((k,I),old)))))).work ≤
    45*(returned h (ctx,(a,(raw,((k,I),old))))).len+
    18*(run DFTModelResidualClosedAddresses.program ctx).val.len+104*old.len+90 := by
  have bound:=DFTModelSavingResidualFinish.work
    (DFTModelSavingResidual.prepared (ctx,(a,(raw,((k,I),old))))).1
    (DFTModelSavingResidual.prepared (ctx,(a,(raw,((k,I),old))))).2.1
    (DFTModelSavingResidual.prepared (ctx,(a,(raw,((k,I),old))))).2.2
    (returned h (ctx,(a,(raw,((k,I),old)))))
  rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,DFTModelSavingResidualSetup.initial_value,
    DFTModelResidualClosedRole.gather_value] at bound
  rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
    DFTModelSavingResidualSetup.initial_value,DFTModelResidualClosedRole.gather_value]
  exact bound

 theorem returned_length (h : Handler Port) (q w r : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a raw k : ℕ) (I : ℂ)
  (old : Tape Tagged.T) (qp : 1 ≤ q)
  (source : ∀ i : Fin (w+1), bits.look i.val 0=(v i).val) (nonzero : v≠0)
  (fits : UniformBatching.roleBits ≤ q*w+r) :
  (returned h ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).len=2^(q*(w+1)+r) := by
  obtain ⟨_,_,_,_,len,_⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v bits a old qp source nonzero
  rw [returned,DFTModelSavingResidualBatch.length,args_value,len,(partition q w r fits).1]
  exact (partition q w r fits).2

/-- Actual whole-direction work: one q-XOR table, linear native-bank movement,
one complete-W call per group, and one flatten. The child work is counted once
for the single paired Tagged computation. -/
 theorem source_work (h : Handler Port) (q w r : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a raw k : ℕ) (I : ℂ)
  (old : Tape Tagged.T) (qp : 1 ≤ q)
  (source : ∀ i : Fin (w+1), bits.look i.val 0=(v i).val) (nonzero : v≠0)
  (fits : UniformBatching.roleBits ≤ q*w+r) :
  (Code.run DFTModelSavingResidual.program h ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).work ≤
    (300*(w+1)+240*r+832)*2^(q*(w+1)+r)+(86*q+36)*(2^q*2^q)+
    104*old.len+21*2^(q*w+r-UniformBatching.roleBits)+22*(w+1)+8*q+410+
    ∑g∈Finset.range (2^(q*w+r-UniformBatching.roleBits)),
      (h ((q,I),DFTModelClockBatch.sliced (UniformBatching.width*2^q) g
        (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2 Tagged.blank)).work := by
  obtain ⟨_,_,al,_table⟩:=DFTModelResidualClosedAddresses.source q w r v bits qp source nonzero
  obtain ⟨_,_,_,_,gl,_⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v bits a old qp source nonzero
  have aw:=DFTModelResidualClosedLinearWork.source_work q w r v bits qp source nonzero
  have gw:=DFTModelResidualClosedRole.gather_work Tagged (q,(w+1,(r,bits))) a old
  rw [al] at gw
  have sw:=DFTModelSavingResidualSetup.work (q,(w+1,(r,bits))) a raw k I old
  have fw:=finish_work h (q,(w+1,(r,bits))) a raw k I old
  rw [returned_length h q w r v bits a raw k I old qp source nonzero fits,al] at fw
  have bw:=DFTModelSavingResidualBatch.work Params Tagged h (q,I)
    (2^(q*w+r-UniformBatching.roleBits)) (UniformBatching.width*2^q)
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2
  rw [(partition q w r fits).2] at bw
  rw [work_exact]
  have argwork : (run batchArgs (DFTModelSavingResidual.prepared ((q,(w+1,(r,bits))),(a,(raw,((k,I),old)))))).work=53 := by
    rw [DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,DFTModelSavingResidualSetup.batchArgs_run]
  rw [argwork,args_value,gl,(partition q w r fits).1,bw]
  dsimp only [Prod.fst,Prod.snd] at sw
  have expand : (300*(w+1)+240*r+832)*2^(q*(w+1)+r)=
      (300*(w+1)+240*r+651)*2^(q*(w+1)+r)+181*2^(q*(w+1)+r) := by ring
  rw [expand]
  dsimp only [run] at gl gw aw sw fw ⊢
  omega

end
end ExactFourierCircuits.DFTModelSavingResidualBounds
