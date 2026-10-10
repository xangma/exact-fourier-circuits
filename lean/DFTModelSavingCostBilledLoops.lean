import DFTModelSavingCostBilled
import DFTModelSavingCostDispatch
import DFTModelSavingCostPadding
import DFTModelSavingDirection
import DFTModelSavingPadding

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.residual
  DFTModelSavingRecords.padding

lemma direction_steps_actual_work (h : Handler DFTModelSavingRecords.Port)
    (rest count : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (DFTModelSavingDirection.steps h rest raw node count).work=1+
      ∑j∈Finset.range count,
        ((DFTModelSavingDirection.rowBill h rest j raw node
          (DFTModelSavingDirection.steps h rest raw node j).val).work+1) := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    change (DFTModelSavingDirection.steps h rest raw node count).work+
      (DFTModelSavingDirection.rowBill h rest count raw node
        (DFTModelSavingDirection.steps h rest raw node count).val).work+1=_
    rw [ih,Finset.sum_range_succ]
    ring

lemma padding_steps_actual_work (h : Handler DFTModelSavingRecords.Port)
    (rest count : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (DFTModelSavingPadding.steps h rest raw node count).work=1+
      ∑j∈Finset.range count,
        ((DFTModelSavingPadding.roleBill h rest j raw node
          (DFTModelSavingPadding.steps h rest raw node j).val).work+1) := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    change (DFTModelSavingPadding.steps h rest raw node count).work+
      (DFTModelSavingPadding.roleBill h rest count raw node
        (DFTModelSavingPadding.steps h rest raw node count).val).work+1=_
    rw [ih,Finset.sum_range_succ]
    ring

/-- Exact selected macro billing, including per-record stream overhead. -/
lemma direction_dispatch_actual_work (h : Handler DFTModelSavingRecords.Port)
    (R rest : ℕ) (raw : Tape ℕ) (node : Node.T) (opcode : raw.look 0 0=0) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22=45+
      ∑j∈Finset.range (raw.look 6 0),
        ((DFTModelSavingDirection.rowBill h rest j raw node
          (DFTModelSavingDirection.steps h rest raw node j).val).work+1) := by
  rw [dispatch_work,opcode,ite_eq_left rfl,DFTModelSavingDirection.residual_run]
  change (DFTModelSavingDirection.steps h rest raw node (raw.look 6 0)).work+13+9+22=_
  rw [direction_steps_actual_work]
  ring

/-- Exact selected padding billing; each role freshly executes the unit
printer before its genuine m-direction residual loop. -/
lemma padding_dispatch_actual_work (h : Handler DFTModelSavingRecords.Port)
    (R rest : ℕ) (raw : Tape ℕ) (node : Node.T) (opcode : raw.look 0 0=5) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22=110+
      ∑j∈Finset.range (raw.look 4 0),
        ((DFTModelSavingPadding.roleBill h rest j raw node
          (DFTModelSavingPadding.steps h rest raw node j).val).work+1) := by
  rw [dispatch_work,opcode]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  rw [DFTModelSavingPadding.padding_run]
  change (DFTModelSavingPadding.steps h rest raw node (raw.look 4 0)).work+13+74+22=_
  rw [padding_steps_actual_work]
  ring

lemma join_actual_rows (control K prefixTicks count : ℕ) (work ticks : ℕ→ℕ)
    (fixed : control≤K) (positive : 1≤prefixTicks)
    (rows : ∀j<count,work j≤K*ticks j) :
    control+(∑j∈Finset.range count,work j)≤K*(prefixTicks+∑j∈Finset.range count,ticks j) := by
  have sum:=billed_sum K 0 count work ticks (fun j hj=>by simpa using rows j hj)
  have first:=Nat.mul_le_mul_left K positive
  nlinarith only [sum,first,fixed]

/-- The actual selected direction loop folded against the corresponding
operational row durations, with its one record-control prefix. -/
theorem direction_dispatch_billed (h : Handler DFTModelSavingRecords.Port)
    (R rest K prefixTicks : ℕ) (raw : Tape ℕ) (node : Node.T)
    (ticks : ℕ→ℕ) (opcode : raw.look 0 0=0) (fixed : 45≤K) (positive : 1≤prefixTicks)
    (rows : ∀j<raw.look 6 0,
      (DFTModelSavingDirection.rowBill h rest j raw node
        (DFTModelSavingDirection.steps h rest raw node j).val).work+1≤K*ticks j) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22≤
      K*(prefixTicks+∑j∈Finset.range (raw.look 6 0),ticks j) := by
  rw [direction_dispatch_actual_work h R rest raw node opcode]
  exact join_actual_rows 45 K prefixTicks _ _ ticks fixed positive rows

lemma padding_role_rows_actual_work (h : Handler DFTModelSavingRecords.Port)
    (rest i : ℕ) (raw : Tape ℕ) (initial node : Node.T) :
    let unit:=run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)
    (DFTModelSavingPadding.roleBill h rest i raw initial node).work+1=unit.work+51+
      ∑j∈Finset.range (unit.val.look 6 0),
        ((DFTModelSavingDirection.rowBill h rest j unit.val node
          (DFTModelSavingDirection.steps h rest unit.val node j).val).work+1) := by
  dsimp only
  rw [padding_role_work_exact,DFTModelSavingDirection.residual_run]
  change (DFTModelSavingDirection.steps h rest _ node _).work+13+(_+36)+1=_
  rw [direction_steps_actual_work]
  ring

/-- Fresh unit syntax is paid by the actual role-control prefix. The m true
unit directions retain the same per-row measured costs and the same K. -/
theorem padding_role_rows_billed (h : Handler DFTModelSavingRecords.Port)
    (rest i K prefixTicks : ℕ) (raw : Tape ℕ) (initial node : Node.T)
    (ticks : ℕ→ℕ) (fixed : unitAllowance+51≤K) (positive : 1≤prefixTicks)
    (rows : ∀j<(run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val.look 6 0,
      (DFTModelSavingDirection.rowBill h rest j
        (run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val node
        (DFTModelSavingDirection.steps h rest
          (run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val node j).val).work+1≤K*ticks j) :
    (DFTModelSavingPadding.roleBill h rest i raw initial node).work+1≤
      K*(prefixTicks+∑j∈Finset.range
        ((run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val.look 6 0),ticks j) := by
  rw [padding_role_rows_actual_work]
  have cost:=unit_work_bound (raw.look 1 0) (raw.look 3 0+i)
  exact join_actual_rows _ K prefixTicks _ _ ticks
    ((Nat.add_le_add_right cost 51).trans fixed) positive rows

/-- All padding roles are folded in the actual ascending order. -/
theorem padding_dispatch_billed (h : Handler DFTModelSavingRecords.Port)
    (R rest K prefixTicks : ℕ) (raw : Tape ℕ) (node : Node.T)
    (ticks : ℕ→ℕ) (opcode : raw.look 0 0=5) (fixed : 110≤K) (positive : 1≤prefixTicks)
    (roles : ∀j<raw.look 4 0,
      (DFTModelSavingPadding.roleBill h rest j raw node
        (DFTModelSavingPadding.steps h rest raw node j).val).work+1≤K*ticks j) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22≤
      K*(prefixTicks+∑j∈Finset.range (raw.look 4 0),ticks j) := by
  rw [padding_dispatch_actual_work h R rest raw node opcode]
  exact join_actual_rows 110 K prefixTicks _ _ ticks fixed positive roles

end
end ExactFourierCircuits.DFTModelSavingCost
