import DFTModelResidualClosedRoleBounds
import DFTModelAffinePaired

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedPaired
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
noncomputable section

/-- The offset is the value of the paired zero-source execution. This is
stronger than arbitrary affine representation of only the actual value. -/
def Bank (actual zero:ℕ → Scalar) (bank:Tape Tagged.T) : Prop :=
  ∀j,j<bank.len → bank.look j Tagged.blank=encodePaired (actual j) (zero j)

theorem gather_paired (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1))) (raw:Tape ℕ)
    (a:ℕ) (bank:Tape Tagged.T) (actual zero:ℕ → Scalar) (qp:1 ≤ q)
    (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0)
    (room:a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ≤ bank.len) (paired:Bank actual zero bank) :
    ∃p:Fin (w+1),∃hp:v p=1,∀j:Fin (2^(q*(w+1)+r)),
      (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,raw))),(a,bank))).val.2.2.look j.val Tagged.blank=
        encodePaired
          (actual (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val))
          (zero (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val)) := by
  obtain ⟨p,hp,_,_,_,lookup⟩:=DFTModelResidualClosedRole.source_gather Tagged q w r v raw a bank qp source nonzero
  refine ⟨p,hp,?_⟩
  intro j
  rw [(lookup j).2]
  apply paired
  have h:=(DFTModelResidualBasisGeometry.permutation q w r v p hp j).isLt
  omega

theorem scatter_paired {L:ℕ} (ctx:DFTModelResidualClosedBasis.Meta.T) (a:ℕ)
    (old:Tape Tagged.T) (addresses:Tape ℕ) (child:Tape Tagged.T)
    (actual zero:ℕ → Scalar) (phi:Fin L≃Fin L) (len:addresses.len=L)
    (table:∀j:Fin L,addresses.look j.val 0=(phi j).val) (room:a*L+L ≤ old.len)
    (paired:∀j:Fin L,child.look j.val Tagged.blank=encodePaired (actual j.val) (zero j.val)) :
    ∀j:Fin L,(run (DFTModelResidualClosedRole.scatter Tagged)
      ((ctx,(a,old)),(addresses,child))).val.look (a*L+(phi j).val) Tagged.blank=
        encodePaired (actual j.val) (zero j.val) := by
  intro j
  rw [DFTModelResidualClosedRole.scatter_permutation Tagged ctx a L old addresses child phi len table room j]
  exact paired j

end
end ExactFourierCircuits.DFTModelResidualClosedPaired
