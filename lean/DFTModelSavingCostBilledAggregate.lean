import DFTModelSavingCostBilled

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program UniformBatching.width

/-- Aggregate form for actual operational group loops, whose returned child
elapsed time is the sum of their existential execution witnesses. -/
lemma absorb_billed_aggregate (A K V G localTicks work childTicks : ℕ)
    (coefficient : A≤K) (localBound : V+G≤localTicks)
    (children : work≤K*childTicks+K*G) :
    A*V+work≤K*(localTicks+childTicks) := by
  have scaled:=Nat.mul_le_mul_right V coefficient
  have duration:=Nat.mul_le_mul_left K localBound
  nlinarith only [scaled,duration,children]

/-- The measured 169-instruction group wrappers supply the call reserve;
the independently executed gather/scatter supplies at least the native volume. -/
lemma native_group_local (V G prefixTicks tailTicks : ℕ) (tail : V≤tailTicks) :
    V+G≤prefixTicks+(169*G+1)+tailTicks := by omega

/-- Direct actual residual work bound using the aggregate returned by the
billed native group loop. No source upper-budget replaces childTicks. -/
theorem residual_source_aggregate_work (h : Handler Port) (q w r : ℕ)
    (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ)
    (a raw k K localTicks childTicks : ℕ) (I : ℂ) (old : Tape Tagged.T)
    (qp : 1≤q) (wide : 2≤w)
    (source : ∀i:Fin (w+1),bits.look i.val 0=(v i).val) (nonzero : v≠0)
    (len : old.len=UniformBatching.width*2^(q*(w+1)+r))
    (coefficient : 322*(w+1)+240*r+1284+104*UniformBatching.width≤K)
    (localBound : 2^(q*(w+1)+r)+(arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1≤localTicks)
    (children : (∑g∈Finset.range (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,
      (h ((arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).1,
        DFTModelClockBatch.sliced (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.1 g
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.2 Tagged.blank)).work)≤
        K*childTicks+K*(arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1) :
    (Code.run DFTModelSavingResidual.program h ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).work≤
      K*(localTicks+childTicks) := by
  have cap:=residual_source_work h q w r v bits a raw k I old qp wide source nonzero
  dsimp only at cap
  rw [len] at cap
  have billed:=absorb_billed_aggregate
    (322*(w+1)+240*r+1284+104*UniformBatching.width) K (2^(q*(w+1)+r))
    (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1 localTicks _ childTicks
    coefficient localBound children
  calc
    _≤_ := cap
    _=(322*(w+1)+240*r+1284+104*UniformBatching.width)*2^(q*(w+1)+r)+_ := by ring
    _≤_ := billed

end
end ExactFourierCircuits.DFTModelSavingCost
