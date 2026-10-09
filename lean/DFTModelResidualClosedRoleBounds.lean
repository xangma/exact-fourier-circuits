import DFTModelResidualClosedRole
import DFTModelResidualClosedExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedRoleBounds
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualClosedBasis (Meta)
open DFTModelResidualClosedRoleStages DFTModelResidualClosedRole
noncomputable section
attribute [local irreducible] DFTModelResidualClosedAddresses.program
  DFTModelResidualMovement.gather DFTModelResidualMovement.scatter slice replace

theorem gather_valid (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) :
    (run (gather t) (ctx,(a,bank))).valid := by
  have pc:=DFTModelResidualClosedBounds.program_valid ctx
  have sv:=slice_valid t ctx a bank (run DFTModelResidualClosedAddresses.program ctx).val
  have gv:=DFTModelResidualMovement.gather_valid t
    (run DFTModelResidualClosedAddresses.program ctx).val
    (run (slice t) ((ctx,(a,bank)),(run DFTModelResidualClosedAddresses.program ctx).val)).val
  simpa only [gather,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,and_true,true_and]
    using And.intro pc (And.intro sv gv)

theorem gather_peak (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) :
    (run (gather t) (ctx,(a,bank))).peak ≤
      (run DFTModelResidualClosedAddresses.program ctx).peak+
        a*(run DFTModelResidualClosedAddresses.program ctx).val.len+
        (run DFTModelResidualClosedAddresses.program ctx).val.len := by
  have sp:=slice_peak t ctx a bank (run DFTModelResidualClosedAddresses.program ctx).val
  have gp:=DFTModelResidualMovement.gather_peak t
    (run DFTModelResidualClosedAddresses.program ctx).val
    (run (slice t) ((ctx,(a,bank)),(run DFTModelResidualClosedAddresses.program ctx).val)).val
  simp only [gather,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (Code.run (slice t) () ((ctx,(a,bank)),
    (Code.run DFTModelResidualClosedAddresses.program () ctx).val)).peak ≤
      a*(Code.run DFTModelResidualClosedAddresses.program () ctx).val.len+
        (Code.run DFTModelResidualClosedAddresses.program () ctx).val.len at sp
  change (Code.run (DFTModelResidualMovement.gather t) ()
    ((Code.run DFTModelResidualClosedAddresses.program () ctx).val,
      (Code.run (slice t) () ((ctx,(a,bank)),
        (Code.run DFTModelResidualClosedAddresses.program () ctx).val)).val)).peak=
      (Code.run DFTModelResidualClosedAddresses.program () ctx).val.len at gp
  omega

theorem scatter_valid (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ) (child:Tape t.T) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).valid := by
  have sv:=DFTModelResidualMovement.scatter_valid t p child
  have rv:=replace_valid t ctx a old (run (DFTModelResidualMovement.scatter t) (p,child)).val
  simpa only [scatter,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,and_true,true_and]
    using And.intro sv rv

theorem scatter_peak (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ) (child:Tape t.T) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).peak ≤ a*p.len+p.len+old.len+1 := by
  have sp:=DFTModelResidualMovement.scatter_peak t p child
  have rp:=replace_peak t ctx a old (run (DFTModelResidualMovement.scatter t) (p,child)).val
  rw [native_len] at rp
  simp only [scatter,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (Code.run (DFTModelResidualMovement.scatter t) () (p,child)).peak=p.len at sp
  change (Code.run (replace t) ()
    ((ctx,(a,old)),(Code.run (DFTModelResidualMovement.scatter t) () (p,child)).val)).peak ≤
      a*p.len+p.len+old.len+1 at rp
  omega

/-- Work includes one role extraction, one gather, one scatter and one whole
parent-bank replacement. The q-XOR table is constructed only in gather. -/
theorem source_gather_bounds (t:Ty) (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1)))
    (raw:Tape ℕ) (a:ℕ) (bank:Tape t.T) (qp:1 ≤ q)
    (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).work ≤
      DFTModelResidualClosedBounds.budget q (w+1) r+50*2^(q*(w+1)+r)+24 ∧
    (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).peak ≤
      DFTModelResidualClosedPeak.budget q (w+1) r+a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ∧
    (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).valid := by
  obtain ⟨_,_,len,_⟩:=DFTModelResidualClosedAddresses.source q w r v raw qp source nonzero
  obtain ⟨work,peak,_⟩:=DFTModelResidualClosedExecution.source_bounds q w r v raw qp source nonzero
  have gw:=DFTModelResidualClosedRole.gather_work t (q,(w+1,(r,raw))) a bank
  have gp:=gather_peak t (q,(w+1,(r,raw))) a bank
  rw [len] at gw gp
  exact ⟨by omega,by omega,gather_valid _ _ _ _⟩

end
end ExactFourierCircuits.DFTModelResidualClosedRoleBounds
