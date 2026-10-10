import DFTModelSavingResidualBoolean
import DFTModelRecursiveScalarSource
import DFTModelSavingYLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelSavingResidualBoolean
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section

/-- A pointwise algebraic decomposition of arbitrary Boolean-tagged cells;
it imposes no canonical tag pattern and assumes no source execution. -/
def actualCell (t : Tagged.T) : Scalar:=⟨t.2.1+t.2.2,decide (t.1≠0)⟩
def zeroCell (t : Tagged.T) : Scalar:=⟨t.2.1,false⟩

lemma encode_cells (t : Tagged.T) (small : t.1<2) :
    encodePaired (actualCell t) (zeroCell t)=t := by
  rcases t with ⟨f,a,b⟩
  change f<2 at small
  have flagEq : DFTModelAffine.flag (decide (f≠0))=f := by
    cases f with
    | zero => rfl
    | succ f =>
      have fz : f=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ small))
      subst f
      rfl
  change (DFTModelAffine.flag (decide (f≠0)),a,(a+b)-a)=(f,a,b)
  rw [flagEq]
  congr 2
  ring

lemma exists_paired {R V : ℕ} (v : Tape Tagged.T) (len : v.len=R*V)
    (before : Boolean v) :
    ∃f f0 : Fin R→Fin V→Scalar,v=paired f f0 := by
  let f:=fun i : Fin R=>fun j : Fin V=>actualCell (v.look (i.val*V+j.val) Tagged.blank)
  let f0:=fun i : Fin R=>fun j : Fin V=>zeroCell (v.look (i.val*V+j.val) Tagged.blank)
  refine ⟨f,f0,?_⟩
  apply DFTModelSavingY.tape_ext (a:=v) (b:=paired f f0) Tagged.blank len
  intro j
  by_cases hj : j<R*V
  · let ij:=(finProdFinEquiv : Fin R×Fin V≃Fin (R*V)).symm ⟨j,hj⟩
    have addr : ij.1.val*V+ij.2.val=j := by
      have e:=congrArg Fin.val ((finProdFinEquiv : Fin R×Fin V≃Fin (R*V)).apply_symm_apply ⟨j,hj⟩)
      simpa only [ij,finProdFinEquiv,Equiv.coe_fn_mk,Prod.fst,Prod.snd,Nat.mul_comm,Nat.add_comm] using e
    rw [←addr,paired_lookup]
    exact (encode_cells _ (look_boolean before _)).symm
  · rw [Tape.look_of_le _ _ (by omega),Tape.look_of_le _ _ (by change R*V ≤ j;omega)]

end
end ExactFourierCircuits.DFTModelSavingPeak
