import DFTModelSavingResidualAction
import DFTModelResidualClosedPaired

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualPaired
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry DFTModelSavingResidualAction
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelSavingResidualBatch.program DFTModelResidualClosedRole.gather

/-- Internal recursive induction property with the actual and zero-source
child output witnesses. No ordinary tensor tag-fold identity is imposed. -/
def Children (h : Handler Port) (q : ℕ) (I : ℂ) (G : ℕ) (bank : Tape Tagged.T)
  (actual zero : ℕ → ℕ → Scalar) : Prop :=
  ∀ g, g < G → ∀ j, j < UniformBatching.width*2^q →
    (h ((q,I),DFTModelClockBatch.sliced (UniformBatching.width*2^q) g bank Tagged.blank)).val.look
      j Tagged.blank=encodePaired (actual g j) (zero g j)

/-- The same real residual code transports the paired child witnesses,
including their conservative actual tags, through the generated native basis
permutation and the internally computed inverse orientation. -/
theorem endpoint (h : Handler Port) (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
  (bits : Tape ℕ) (a k : ℕ) (I : ℂ) (inverse : Bool) (old : Tape Tagged.T) (qp : 1 ≤ q)
  (source : ∀ i : Fin (w+1), bits.look i.val 0=(v i).val) (hv : BinaryFrames.dot v v=1)
  (fits : UniformBatching.roleBits ≤ q*w+r)
  (room : a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ≤ old.len)
  (actual zero : ℕ → ℕ → Scalar)
  (ih : Children h q I (2^(q*w+r-UniformBatching.roleBits))
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2 actual zero) :
  ∃ p : Fin (w+1), ∃ hp : v p=1,
    (∀ j : Fin (2^(q*(w+1)+r)),
      (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2.look
        j.val Tagged.blank=old.look (a*2^(q*(w+1)+r)+
          (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank) ∧
    (∀ j : Fin (2^(q*(w+1)+r)),
      (Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
        (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank=
      encodePaired
        (actual (effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val/(UniformBatching.width*2^q))
          (effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val%(UniformBatching.width*2^q)))
        (zero (effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val/(UniformBatching.width*2^q))
          (effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val%(UniformBatching.width*2^q)))) ∧
    (∀ j : Fin old.len, ¬(a*2^(q*(w+1)+r) ≤ j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r)) →
      (Code.run DFTModelSavingResidual.program h
        ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
        j.val Tagged.blank=old.look j.val Tagged.blank) := by
  obtain ⟨p,hp,gather,inside,outside⟩:=DFTModelSavingResidualGeometry.endpoint
    h q w r v bits a k I inverse old qp source hv fits room
  have nz : v≠0 := by intro z;rw [z] at hv;simp [BinaryFrames.dot] at hv
  obtain ⟨_,_,_,_,gl,_⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v bits a old qp source nz
  refine ⟨p,hp,gather,?_,outside⟩
  intro j
  rw [inside j]
  let ix:=effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val
  have live : ix<2^(q*(w+1)+r):=effectiveIndex_lt _ _ _ _
    (Nat.two_pow_pos _) (size_divides q w r) j.isLt
  have extent : ix<2^(q*w+r-UniformBatching.roleBits)*(UniformBatching.width*2^q):=by
    rw [(partition q w r fits).2];exact live
  change (returned h _).look ix Tagged.blank=_
  rw [returned,args_value,gl,(partition q w r fits).1,
    DFTModelSavingResidualBatch.lookup Params Tagged h (q,I) _ _ _ ⟨ix,extent⟩]
  exact ih _ (Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using extent)) _
    (Nat.mod_lt _ (Nat.mul_pos
      (by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _) (Nat.two_pow_pos _)))

end
end ExactFourierCircuits.DFTModelSavingResidualPaired
