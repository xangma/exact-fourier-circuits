import DFTModelSavingResidualNative
import DFTModelSavingResidualPaired

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualSource
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelSavingResidualGeometry DFTModelSavingResidualChild DFTModelSavingResidualNative
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelResidualClosedRole.gather

/-- Both affine channels have the exact native signed residual action of the
original direction, including spectators and the weight-three orientation.
The child continuation is an internal smaller-exponent hypothesis. -/
theorem native_channels (h : Handler Port) (q w r : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (bits : Tape ℕ) (a k : ℕ) (I : ℂ)
  (inverse : Bool) (old : Tape Tagged.T) (qp : 1 ≤ q)
  (source : ∀ i : Fin (w+1), bits.look i.val 0=(v i).val) (hv : BinaryFrames.dot v v=1)
  (fits : UniformBatching.roleBits ≤ q*w+r)
  (room : a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ≤ old.len)
  (ih : Channels h q I (2^(q*w+r-UniformBatching.roleBits))
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,bits))),(a,old))).val.2.2) :
  (∀ z : Fin (2^(q*(w+1)+r)),
    ((Code.run DFTModelSavingResidual.program h
      ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
        (a*2^(q*(w+1)+r)+z.val) Tagged.blank).2=
      ((signedMatrix q w r v hv inverse).mulVec
        (fun s=>(old.look (a*2^(q*(w+1)+r)+s.val) Tagged.blank).2.1) z,
       (signedMatrix q w r v hv inverse).mulVec
        (fun s=>(old.look (a*2^(q*(w+1)+r)+s.val) Tagged.blank).2.2) z)) ∧
  (∀ j : Fin old.len, ¬(a*2^(q*(w+1)+r) ≤ j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r)) →
    (Code.run DFTModelSavingResidual.program h
      ((q,(w+1,(r,bits))),(a,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),old))))).val.2.look
      j.val Tagged.blank=old.look j.val Tagged.blank) := by
  obtain ⟨p,hp,inside,outside⟩:=DFTModelSavingResidualAction.channels
    h q w r v bits a k I inverse old qp source hv fits room ih
  refine ⟨?_,outside⟩
  intro z
  let F:=DFTModelResidualBasisGeometry.permutation q w r v p hp
  have actual:=inside (F.symm z)
  have left:=fiber_formula q w r v hv p hp inverse
    (fun s=>(old.look (a*2^(q*(w+1)+r)+s.val) Tagged.blank).2.1) (F.symm z)
  have right:=fiber_formula q w r v hv p hp inverse
    (fun s=>(old.look (a*2^(q*(w+1)+r)+s.val) Tagged.blank).2.2) (F.symm z)
  rw [left,right] at actual
  simpa only [show DFTModelResidualBasisGeometry.permutation q w r v p hp=F from rfl,
    Equiv.apply_symm_apply] using actual

/-- The source residual loop's concrete directionMatrix is the same matrix,
not a separately supplied action or an alternative scalar tag fold. -/
theorem direction_matrix (q w r : ℕ) {old new : FramedScheduleWords.Label (w+1)}
  (edge : FramedScheduleWords.NestedEdge old new) (j : Fin edge.dimension) :
  UniformRecursiveResidualDirectionLoop.directionMatrix q w r edge j=
    signedMatrix q w r (UniformFixedNetwork.edgeVectors edge j)
      (UniformResidualFibers.edgeVector_norm edge j) (UniformFixedNetwork.edgeInverse edge) := rfl

end
end ExactFourierCircuits.DFTModelSavingResidualSource
