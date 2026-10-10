import DFTModelSavingCostResidual

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelResidualClosedAddresses.program
  DFTModelSavingResidual.program UniformBatching.width

/-- At the actual fixed block width (at least three), the materialized q-XOR
cost is absorbed by the native volume. -/
theorem xor_work_volume (q w r : ℕ) (wide : 2≤w) :
    (86*q+36)*(2^q*2^q)≤122*2^(q*(w+1)+r) := by
  have qp : q≤2^q := Nat.le_of_lt q.lt_two_pow_self
  have pp : 1≤2^q := Nat.two_pow_pos q
  have coefficient : 86*q+36≤122*2^q := by omega
  have cubic : (2^q*2^q)*2^q=2^(q+q+q) := by simp only [pow_add]
  have power : 2^(q+q+q)≤2^(q*(w+1)+r) := by
    apply Nat.pow_le_pow_right (by decide)
    nlinarith
  calc
    _≤(122*2^q)*(2^q*2^q) := Nat.mul_le_mul_right _ coefficient
    _=122*2^(q+q+q) := by rw [←cubic];ring
    _≤_ := Nat.mul_le_mul_left 122 power

/-- Concrete native direction allowance, retaining the very same complete-W
child calls. No child output length, prepared flags, or action is an input. -/
theorem residual_source_work (h : Handler Port) (q w r : ℕ)
    (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a raw k : ℕ)
    (I : ℂ) (old : Tape Tagged.T) (qp : 1≤q) (wide : 2≤w)
    (source : ∀i:Fin (w+1),bits.look i.val 0=(v i).val) (nonzero : v≠0) :
    let x:Input.T:=((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))
    (Code.run DFTModelSavingResidual.program h x).work≤
      (322*(w+1)+240*r+1284)*2^(q*(w+1)+r)+104*old.len+
        ∑g∈Finset.range (arguments x).2.1,
          (h ((arguments x).1,DFTModelClockBatch.sliced (arguments x).2.2.1 g
            (arguments x).2.2.2 Tagged.blank)).work := by
  dsimp only
  have cost:=residual_work h (q,(w+1,(r,bits))) a raw k I old
  have address:=DFTModelResidualClosedLinearWork.source_work q w r v bits qp source nonzero
  have xor:=xor_work_volume q w r wide
  obtain ⟨p,hp,len,table⟩:=DFTModelResidualClosedAddresses.source q w r v bits qp source nonzero
  dsimp only at cost
  rw [len] at cost
  have div : 2^(q*(w+1)+r)/(UniformBatching.width*2^q)≤2^(q*(w+1)+r) := Nat.div_le_self _ _
  have positive : 1≤2^(q*(w+1)+r) := Nat.two_pow_pos _
  have qv : q≤2^(q*(w+1)+r) := by
    have qk : q≤q*(w+1)+r := by nlinarith
    exact qk.trans (Nat.le_of_lt (q*(w+1)+r).lt_two_pow_self)
  have mw : 22*(w+1)≤22*(w+1)*2^(q*(w+1)+r) := Nat.le_mul_of_pos_right _ positive
  nlinarith

/-- The sole recursive port is called once per complete batch; a bound on its
actual work is summed without duplicating the two affine channels. -/
theorem residual_source_child_work (h : Handler Port) (q w r : ℕ)
    (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a raw k C : ℕ)
    (I : ℂ) (old : Tape Tagged.T) (qp : 1≤q) (wide : 2≤w)
    (source : ∀i:Fin (w+1),bits.look i.val 0=(v i).val) (nonzero : v≠0)
    (fits : UniformBatching.roleBits≤q*w+r)
    (children : ∀g<(arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,
      (h ((arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).1,
        DFTModelClockBatch.sliced
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.1 g
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.2 Tagged.blank)).work≤C) :
    (Code.run DFTModelSavingResidual.program h
      ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).work≤
      (322*(w+1)+240*r+1284)*2^(q*(w+1)+r)+104*old.len+
        2^(q*w+r-UniformBatching.roleBits)*C := by
  have cost:=residual_source_work h q w r v bits a raw k I old qp wide source nonzero
  have sum : (∑g∈Finset.range (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,
      (h ((arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).1,
        DFTModelClockBatch.sliced
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.1 g
          (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.2.2 Tagged.blank)).work)≤
      (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1*C := by
    calc
      _≤∑g∈Finset.range (arguments ((q,(w+1,(r,bits))),(a,(raw,((k,I),old))))).2.1,C :=
        Finset.sum_le_sum (fun g hg=>children g (Finset.mem_range.mp hg))
      _=_ := by simp
  have group:=(DFTModelSavingResidualGeometry.source_arguments q w r v bits a raw k I old qp source nonzero fits).2.1
  dsimp only at cost
  rw [group] at sum cost
  exact cost.trans (Nat.add_le_add_left sum _)

end
end ExactFourierCircuits.DFTModelSavingCost
