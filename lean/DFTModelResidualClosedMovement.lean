import DFTModelResidualClosedAddresses
import DFTModelResidualMovement

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualClosedMovement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualClosedBasis (Meta)
noncomputable section

abbrev Input (t : Ty) := p Meta (Ty.a t)
/-- The child receives one complete element per coordinate; metadata and the
computed address tape remain outside the child bank. -/
abbrev Context (t : Ty) := p Meta (p (Ty.a w) (Ty.a t))

def prepare (t : Ty) : Prog false (Input t) (Context t) := .fork (.atom .fst)
  (.fork (.comp (.atom .fst) DFTModelResidualClosedAddresses.program) (.atom .snd))
def gather (t : Ty) : Prog false (Input t) (Context t) := .comp (prepare t)
  (.fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.atom .snd) (DFTModelResidualMovement.gather t))))
def scatter (t : Ty) : Prog false (Context t) (Ty.a t) :=
  .comp (.atom .snd) (DFTModelResidualMovement.scatter t)

attribute [local irreducible] DFTModelResidualClosedAddresses.program
  DFTModelResidualMovement.gather DFTModelResidualMovement.scatter

theorem gather_value (t : Ty) (ctx : Meta.T) (v : Tape t.T) :
    (run (gather t) (ctx,v)).val=
      (ctx,((run DFTModelResidualClosedAddresses.program ctx).val,
        (run (DFTModelResidualMovement.gather t)
          ((run DFTModelResidualClosedAddresses.program ctx).val,v)).val)) := rfl

theorem gather_work (t : Ty) (ctx : Meta.T) (v : Tape t.T) :
    (run (gather t) (ctx,v)).work=
      (run DFTModelResidualClosedAddresses.program ctx).work+
        17*(run DFTModelResidualClosedAddresses.program ctx).val.len+21 := by
  have h:=DFTModelResidualMovement.gather_work t
    (run DFTModelResidualClosedAddresses.program ctx).val v
  simp only [gather,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (Code.run (DFTModelResidualMovement.gather t) ()
    ((Code.run DFTModelResidualClosedAddresses.program () ctx).val,v)).work=
    17*(Code.run DFTModelResidualClosedAddresses.program () ctx).val.len+6 at h
  omega

theorem scatter_work (t : Ty) (ctx : Meta.T) (a : Tape ℕ) (v : Tape t.T) :
    (run (scatter t) (ctx,(a,v))).work=18*a.len+11 := by
  change 1+(run (DFTModelResidualMovement.scatter t) (a,v)).work+1=_
  rw [DFTModelResidualMovement.scatter_work]
  omega

theorem scatter_peak (t : Ty) (ctx : Meta.T) (a : Tape ℕ) (v : Tape t.T) :
    (run (scatter t) (ctx,(a,v))).peak=a.len := by
  change max (max 0 (run (DFTModelResidualMovement.scatter t) (a,v)).peak) 0=_
  rw [DFTModelResidualMovement.scatter_peak]
  simp

theorem scatter_valid (t : Ty) (ctx : Meta.T) (a : Tape ℕ) (v : Tape t.T) :
    (run (scatter t) (ctx,(a,v))).valid :=
  ⟨trivial,DFTModelResidualMovement.scatter_valid t a v⟩

/-- Raw direction reads generate the permutation internally. Gather preserves
whole elements, including both affine channels and the exact conservative tag. -/
theorem source_gather (t : Ty) (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
    (raw : Tape ℕ) (bank : Tape t.T) (qp : 1 ≤ q)
    (data : ∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero : v≠0) :
    ∃p:Fin (w+1),∃hp:v p=1,
      (run (gather t) ((q,(w+1,(r,raw))),bank)).val.1=(q,(w+1,(r,raw))) ∧
      (run (gather t) ((q,(w+1,(r,raw))),bank)).val.2.1.len=2^(q*(w+1)+r) ∧
      (run (gather t) ((q,(w+1,(r,raw))),bank)).val.2.2.len=2^(q*(w+1)+r) ∧
      ∀j:Fin (2^(q*(w+1)+r)),
        (run (gather t) ((q,(w+1,(r,raw))),bank)).val.2.1.look j.val 0=
          (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val ∧
        (run (gather t) ((q,(w+1,(r,raw))),bank)).val.2.2.look j.val t.blank=
          bank.look (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val t.blank := by
  obtain ⟨p,hp,len,addresses⟩:=DFTModelResidualClosedAddresses.source q w r v raw qp data nonzero
  rw [gather_value,DFTModelResidualMovement.gather_value]
  refine ⟨p,hp,rfl,len,by simpa only [Tape.tab] using len,?_⟩
  intro j
  refine ⟨addresses j,?_⟩
  change (Tape.tab (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.len
    (fun k=>bank.look ((run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.look k 0) t.blank)).look j.val t.blank=_
  have jl:j.val < (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.len := by rw [len];exact j.isLt
  simp only [Tape.look,Tape.tab,jl,↓reduceDIte]
  have aa:=addresses j
  simpa only [Tape.look,jl,↓reduceDIte] using congrArg (fun k=>bank.look k t.blank) aa

/-- Actual inverse-coordinate scatter consumes the very address tape retained
by gather; source and zero-input channels are not recomputed independently. -/
theorem source_scatter (t : Ty) (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1)))
    (raw : Tape ℕ) (bank child : Tape t.T) (qp : 1 ≤ q)
    (data : ∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero : v≠0) :
    ∃p:Fin (w+1),∃hp:v p=1,∀j:Fin (2^(q*(w+1)+r)),
      (run (scatter t) ((q,(w+1,(r,raw))),
        ((run (gather t) ((q,(w+1,(r,raw))),bank)).val.2.1,child))).val.look
          (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val t.blank=
        child.look j.val t.blank := by
  obtain ⟨p,hp,len,addresses⟩:=DFTModelResidualClosedAddresses.source q w r v raw qp data nonzero
  refine ⟨p,hp,?_⟩
  intro j
  rw [gather_value]
  exact DFTModelResidualMovement.scatter_value t
    (DFTModelResidualBasisGeometry.permutation q w r v p hp)
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val child len addresses j

end
end ExactFourierCircuits.DFTModelResidualClosedMovement
