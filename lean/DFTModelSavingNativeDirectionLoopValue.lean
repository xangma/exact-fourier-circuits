import DFTModelSavingNativeDirectionExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program

/-- The original argument affects charges only, never the returned value. -/
theorem row_initial (h:Handler DFTModelSavingResidual.Port) (r i:ℕ) (raw:Tape ℕ)
 (old old' node:Node.T) :
 (DFTModelSavingDirection.rowBill h r i raw old node).val=
 (DFTModelSavingDirection.rowBill h r i raw old' node).val:=by
 unfold DFTModelSavingDirection.rowBill
 simp only [Bill.pay]

def rows {d:ℕ} (h:Handler DFTModelSavingResidual.Port) (r:ℕ) (raw:Tape ℕ)
 (L:List (Fin d)) (node:Node.T) : Node.T :=
 L.foldl (fun current i=>(DFTModelSavingDirection.rowBill h r i.val raw current current).val) node

theorem steps_fold {α:Type} (x:α) (f:ℕ→α→Bill α) (n:ℕ) :
 (Bill.steps x f n).val=(List.range n).foldl (fun y i=>(f i y).val) x:=by
 induction n with
 | zero=>rfl
 | succ n ih=>
  change (f n (Bill.steps x f n).val).val=_
  rw [ih,List.range_succ,List.foldl_append]
  rfl

theorem fold_congr {α β:Type} (L:List β) (x:α) (f g:α→β→α) (same:∀a b,f a b=g a b) :
 L.foldl f x=L.foldl g x:=by
 induction L generalizing x with
 | nil=>rfl
 | cons b L ih=>simp only [List.foldl_cons,same];exact ih _

attribute [local irreducible] DFTModelSavingDirection.rowBill

theorem rows_all (d:ℕ) (h:Handler DFTModelSavingResidual.Port) (r:ℕ) (raw:Tape ℕ)
 (node:Node.T) : rows h r raw (List.finRange d) node=
 (DFTModelSavingDirection.steps h r raw node d).val:=by
 unfold rows DFTModelSavingDirection.steps
 rw [steps_fold,←List.map_coe_finRange_eq_range]
 rw [List.foldl_map]
 apply fold_congr
 intro a b
 exact row_initial h r b.val raw a node a

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
