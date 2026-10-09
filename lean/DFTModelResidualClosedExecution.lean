import DFTModelResidualClosedPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedExecution
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualClosedBasis (Meta)
noncomputable section
attribute [local irreducible] DFTModelResidualClosedAddresses.program DFTModelResidualMovement.gather

/-- All generated metadata premises of the internal bounds are discharged
from actual raw direction reads. The direction tape is the remaining caller input. -/
theorem source_bounds (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1))) (raw:Tape ℕ)
    (qp:1 ≤ q) (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).work ≤
      DFTModelResidualClosedBounds.budget q (w+1) r ∧
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).peak ≤
      DFTModelResidualClosedPeak.budget q (w+1) r ∧
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).valid := by
  obtain ⟨p,hp,prepared,_⟩:=DFTModelResidualClosedBasis.source_images q w r v raw source nonzero
  have images:=DFTModelResidualBasisGeometry.program_images q w r v p hp
  have cover:q*(w+1)+r ≤ q*((w+1)+r):=by nlinarith
  have small:∀i,i<q*(w+1)+r →
      (run DFTModelResidualBasisImages.program
        (q,(w+1,(r,((UniformBinaryXorCoordinates.encode v).val,p.val))))).val.look i 0<2^(q*((w+1)+r)) := by
    intro i hi
    rw [images ⟨i,hi⟩]
    exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) cover)
  have binary:∀i,i<w+1 → raw.look i 0<2 := by
    intro i hi;rw [source ⟨i,hi⟩];exact (v ⟨i,hi⟩).isLt
  exact ⟨DFTModelResidualClosedBounds.program_work q w r _ _ raw p.isLt prepared small,
    DFTModelResidualClosedPeak.program_peak q w r v p hp raw qp prepared binary,
    DFTModelResidualClosedBounds.program_valid _⟩

theorem gather_valid (t:Ty) (ctx:Meta.T) (bank:Tape t.T) :
    (run (DFTModelResidualClosedMovement.gather t) (ctx,bank)).valid := by
  have pc:=DFTModelResidualClosedBounds.program_valid ctx
  have gv:=DFTModelResidualMovement.gather_valid t
    (run DFTModelResidualClosedAddresses.program ctx).val bank
  simpa only [DFTModelResidualClosedMovement.gather,DFTModelResidualClosedMovement.prepare,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,and_true,true_and] using And.intro pc gv


theorem gather_peak (t:Ty) (ctx:Meta.T) (bank:Tape t.T) :
    (run (DFTModelResidualClosedMovement.gather t) (ctx,bank)).peak ≤
      (run DFTModelResidualClosedAddresses.program ctx).peak+
        (run DFTModelResidualClosedAddresses.program ctx).val.len := by
  have gp:=DFTModelResidualMovement.gather_peak t
    (run DFTModelResidualClosedAddresses.program ctx).val bank
  simp only [DFTModelResidualClosedMovement.gather,DFTModelResidualClosedMovement.prepare,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (Code.run (DFTModelResidualMovement.gather t) ()
    ((Code.run DFTModelResidualClosedAddresses.program () ctx).val,bank)).peak=
      (Code.run DFTModelResidualClosedAddresses.program () ctx).val.len at gp
  omega

end
end ExactFourierCircuits.DFTModelResidualClosedExecution
