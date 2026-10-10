import DFTModelSavingNativeDirectionBilledWork
import DFTModelSavingNativeDirectionLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelSavingDirection.rowBill

def prefixWork {d:ℕ} (h:Handler DFTModelSavingResidual.Port)(r:ℕ)(raw:Tape ℕ)
 (initial:Node.T)(L:List (Fin d)):ℕ:=
 (L.map (fun j => (DFTModelSavingDirection.rowBill h r j.val raw initial
  (DFTModelSavingDirection.steps h r raw initial j.val).val).work+1)).sum

lemma prefixWork_nil {d:ℕ} (h:Handler DFTModelSavingResidual.Port)(r:ℕ)(raw:Tape ℕ)(initial:Node.T):
 prefixWork h r raw initial ([]:List (Fin d))=0:=rfl
lemma prefixWork_cons {d:ℕ} (h:Handler DFTModelSavingResidual.Port)(r:ℕ)(raw:Tape ℕ)(initial:Node.T)
 (j:Fin d)(L:List (Fin d)):
 prefixWork h r raw initial (j::L)=
 (DFTModelSavingDirection.rowBill h r j.val raw initial
  (DFTModelSavingDirection.steps h r raw initial j.val).val).work+1+prefixWork h r raw initial L:=rfl

lemma steps_succ_value (h:Handler DFTModelSavingResidual.Port)(r j:ℕ)(raw:Tape ℕ)(initial:Node.T):
 (DFTModelSavingDirection.steps h r raw initial (j+1)).val=
 (DFTModelSavingDirection.rowBill h r j raw initial (DFTModelSavingDirection.steps h r raw initial j).val).val:=rfl

lemma row_work_initial (h:Handler DFTModelSavingResidual.Port)(r j:ℕ)(raw:Tape ℕ)(old old' current:Node.T):
 (DFTModelSavingDirection.rowBill h r j raw old current).work=
 (DFTModelSavingDirection.rowBill h r j raw old' current).work:=by
 unfold DFTModelSavingDirection.rowBill
 simp only [Bill.pay]

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
