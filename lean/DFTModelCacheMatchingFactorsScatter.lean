import DFTModelCacheMatchingFactorsProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] program scalar

/-- The same physical permutation is applied independently to all nine lanes. -/
def lifted {r : ℕ} (phi : Fin r≃Fin r) : Fin (9*r)≃Fin (9*r) :=
  finProdFinEquiv.symm.trans
    (((Equiv.refl (Fin 9)).prodCongr phi).trans finProdFinEquiv)

theorem lifted_value {r : ℕ} (phi : Fin r≃Fin r) (j : Fin (9*r)) :
    (lifted phi j).val=j.val/r*r+(phi j.modNat).val := by
  change (phi j.modNat).val+r*(j.val/r)=_
  simp only [Nat.mul_comm,Nat.add_comm]

theorem lifted_pair {r : ℕ} (phi : Fin r≃Fin r) (l : Fin 9) (j : Fin r) :
    lifted phi (finProdFinEquiv (l,j))=finProdFinEquiv (l,phi j) := by
  exact congrArg finProdFinEquiv
    (congrArg ((Equiv.refl (Fin 9)).prodCongr phi) (finProdFinEquiv.symm_apply_apply (l,j)))

def addressTape (r : ℕ) (p : Tape ℕ) : Tape ℕ :=
  Tape.tab (9*r) (fun j=>j/r*r+p.look (j%r) 0)
def valueTape (r : ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) : Tape ℂ :=
  Tape.tab (9*r) (packedValue r z i ai)

theorem sow_congr {α : Type} (L C : ℕ) (z : α) (f g : ℕ→ℕ×α)
    (h : ∀j<C,f j=g j) : Tape.sow L C z f=Tape.sow L C z g := by
  induction C with
  | zero => rfl
  | succ C ih =>
    change (Tape.sow L C z f).set (f C).1 (f C).2=
      (Tape.sow L C z g).set (g C).1 (g C).2
    rw [ih (fun j hj=>h j (by omega)),h C (by omega)]

/-- This equality only reuses scatter's proved semantics. The actual producer
is one sow, and does not construct these two mathematical reference tapes. -/
theorem program_scatter (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    (run program (args r p z i ai)).val=
      (run (DFTModelResidualMovement.scatter sc)
        (addressTape r p,valueTape r z i ai)).val := by
  rw [program_value]
  change _=(Bill.sow (9*r) (9*r) 0
    (fun j=>run (DFTModelResidualMovement.scatterCell sc)
      ((addressTape r p,valueTape r z i ai),j))).val
  rw [DFTModelCRT.sow_value]
  apply sow_congr
  intro j h
  rw [DFTModelResidualMovement.scatterCell_run]
  simp [addressTape,valueTape,Tape.look,Tape.tab,h]

theorem at_packed {r : ℕ} (phi : Fin r≃Fin r) (p : Tape ℕ)
    (table : ∀j:Fin r,p.look j.val 0=(phi j).val)
    (z : Tape (ℂ × ℂ)) (i ai : ℂ) (l : Fin 9) (j : Fin r) :
    (run program (args r p z i ai)).val.look (l.val*r+(phi j).val) 0=
      packedValue r z i ai (l.val*r+j.val) := by
  have address : ∀a:Fin (9*r),(addressTape r p).look a.val 0=(lifted phi a).val := by
    intro a
    rw [lifted_value]
    simp only [addressTape,Tape.look,Tape.tab,a.isLt,dite_true]
    exact congrArg (fun x=>a.val/r*r+x) (table a.modNat)
  have h:=DFTModelResidualMovement.scatter_value sc (lifted phi)
    (addressTape r p) (valueTape r z i ai) rfl address (finProdFinEquiv (l,j))
  rw [program_scatter]
  rw [lifted_pair] at h
  have encoded : (finProdFinEquiv (l,j)).val=l.val*r+j.val := by
    change j.val+r*l.val=_
    simp only [Nat.mul_comm,Nat.add_comm]
  have encoded' : (finProdFinEquiv (l,phi j)).val=l.val*r+(phi j).val := by
    change (phi j).val+r*l.val=_
    simp only [Nat.mul_comm,Nat.add_comm]
  rw [encoded'] at h
  have valid:l.val*r+j.val<9*r:=encoded ▸ (finProdFinEquiv (l,j)).isLt
  rw [show (valueTape r z i ai).look (finProdFinEquiv (l,j)).val sc.blank=
      packedValue r z i ai (l.val*r+j.val) by
    simp [valueTape,Tape.look,Tape.tab,encoded,valid]] at h
  exact h

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors
