import DFTModelSavingCostResidualSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program UniformBatching.width

/-- Sum the work of the same paired calls against their actual durations.
The additive allowance is paid once per call, not once per affine channel. -/
lemma billed_sum (K a G : ℕ) (work ticks : ℕ→ℕ)
    (child : ∀g<G,work g≤K*ticks g+a) :
    (∑g∈Finset.range G,work g)≤K*(∑g∈Finset.range G,ticks g)+a*G := by
  calc
    _≤∑g∈Finset.range G,(K*ticks g+a) :=
      Finset.sum_le_sum (fun g hg=>child g (Finset.mem_range.mp hg))
    _=_ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
      Finset.card_range,smul_eq_mul];ring

/-- A single fixed multiplicative constant survives a recursion step. The
source local duration includes both the native volume and the call overhead. -/
lemma absorb_billed_children (A K V G localTicks : ℕ) (work ticks : ℕ→ℕ)
    (coefficient : A≤K) (localBound : V+G≤localTicks)
    (child : ∀g<G,work g≤K*ticks g+K) :
    A*V+(∑g∈Finset.range G,work g)≤K*(localTicks+∑g∈Finset.range G,ticks g) := by
  have sum:=billed_sum K K G work ticks child
  have scaled:=Nat.mul_le_mul_left V coefficient
  have duration:=Nat.mul_le_mul_left K localBound
  nlinarith only [sum,scaled,duration]

/-- Actual typed residual execution, compared to the measured durations of
its same complete-W child calls. The local-duration inequality is an explicit
obligation for the operational source caller, not an assumed action result. -/
theorem residual_source_billed_work (h : Handler Port) (q w r : ℕ)
    (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a raw k K localTicks : ℕ)
    (I : ℂ) (old : Tape Tagged.T) (qp : 1≤q) (wide : 2≤w)
    (source : ∀i:Fin (w+1),bits.look i.val 0=(v i).val) (nonzero : v≠0)
    (len : old.len=UniformBatching.width*2^(q*(w+1)+r))
    (ticks : ℕ→ℕ)
    (coefficient : 322*(w+1)+240*r+1284+104*UniformBatching.width≤K)
    (localBound : 2^(q*(w+1)+r)+(arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1≤localTicks)
    (child : ∀g<(arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,
      (h ((arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).1,
        DFTModelClockBatch.sliced (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.1 g
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.2 Tagged.blank)).work≤K*ticks g+K) :
    (Code.run DFTModelSavingResidual.program h ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).work≤
      K*(localTicks+∑g∈Finset.range (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,ticks g) := by
  have cap:=residual_source_work h q w r v bits a raw k I old qp wide source nonzero
  dsimp only at cap
  rw [len] at cap
  have billed:=absorb_billed_children
    (322*(w+1)+240*r+1284+104*UniformBatching.width) K (2^(q*(w+1)+r))
    (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1 localTicks
    (fun g=>(h ((arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).1,
      DFTModelClockBatch.sliced (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.1 g
        (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.2 Tagged.blank)).work)
    ticks coefficient localBound child
  calc
    _≤_ := cap
    _=(322*(w+1)+240*r+1284+104*UniformBatching.width)*2^(q*(w+1)+r)+_ := by ring
    _≤_ := billed

end
end ExactFourierCircuits.DFTModelSavingCost
