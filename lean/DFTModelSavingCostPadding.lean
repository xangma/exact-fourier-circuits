import DFTModelSavingCostPaddingSource
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit DFTModelSavingRecords.residual
  DFTModelSavingRecords.padding ExplicitSeedBudget.m

def unitAllowance : ℕ := DFTModelCacheRecords.recordCost UniformRecursiveSavingProgram.unitRecord

theorem unit_work_bound (q a : ℕ) : (run DFTModelCacheRecords.unit (q,a)).work≤unitAllowance :=
  DFTModelCacheRecords.unit_work q a

attribute [local irreducible] unitAllowance DFTModelCacheRecords.recordCost
  UniformRecursiveSavingProgram.unitRecord

def paddingRoleAllowance (q m r L C : ℕ) : ℕ :=
  51+unitAllowance+directionAllowance q m r L C*m

theorem padding_role_work_exact (r i : ℕ) (raw : Tape ℕ) (old node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) :
    (DFTModelSavingPadding.roleBill h r i raw old node).work=
      (Code.run DFTModelSavingRecords.residual h
        (r,((run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).val,node))).work+
      ((run DFTModelCacheRecords.unit (raw.look 1 0,raw.look 3 0+i)).work+36) := rfl

theorem padding_steps_zero (r : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) :
    (DFTModelSavingPadding.steps h r raw node 0).work=1 := rfl

theorem padding_steps_succ (r n : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) :
    (DFTModelSavingPadding.steps h r raw node (n+1)).work=
      (DFTModelSavingPadding.steps h r raw node n).work+
      (DFTModelSavingPadding.roleBill h r n raw node
        (DFTModelSavingPadding.steps h r raw node n).val).work+1 := rfl

attribute [local irreducible] DFTModelSavingPadding.roleBill DFTModelSavingPadding.steps

theorem padding_role_work (q w r i k C : ℕ) (I : ℂ) (raw : Tape ℕ)
    (initial : Node.T) (bank : Tape Tagged.T) (h : Handler DFTModelSavingRecords.Port)
    (columns : raw.look 1 0=q) (widthEq : w+1=ExplicitSeedBudget.m)
    (qp : 1≤q) (wide : 2≤w) (fits : UniformBatching.roleBits≤q*w+r)
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (DFTModelSavingPadding.roleBill h r i raw initial ((k,I),bank)).work≤
      paddingRoleAllowance q (w+1) r bank.len C-1 := by
  let a:=raw.look 3 0+i
  let unitTape:=(run DFTModelCacheRecords.unit (q,a)).val
  have source : DFTModelSavingDirection.RawSource
      (macroRecord q (singletonEmbedding a)
        (.edge _ _ (0:Fin 1) (UniformRecursivePaddingUnitEdge.unitEdge (w+1)))) unitTape := by
    rw [widthEq]
    exact unit_source q a
  have cost:=direction_work q r (singletonEmbedding a) (0:Fin 1)
    (UniformRecursivePaddingUnitEdge.unitEdge (w+1)) unitTape source k C I bank h qp wide fits children
  have unitCost:=unit_work_bound q a
  rw [padding_role_work_exact,columns]
  dsimp only [a,unitTape] at cost unitCost
  change _≤14+directionAllowance q (w+1) r bank.len C*(w+1) at cost
  dsimp only [paddingRoleAllowance]
  omega

/-- Every padding role freshly prints its unit frame and invokes the same-q
residual loop. Its m*G child count is preserved exactly. -/
theorem padding_work (q w r k C : ℕ) (I : ℂ) (raw : Tape ℕ) (bank : Tape Tagged.T)
    (h : Handler DFTModelSavingRecords.Port) (columns : raw.look 1 0=q)
    (widthEq : w+1=ExplicitSeedBudget.m) (qp : 1≤q) (wide : 2≤w)
    (fits : UniformBatching.roleBits≤q*w+r)
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run DFTModelSavingRecords.padding h (r,(raw,((k,I),bank)))).work≤
      14+paddingRoleAllowance q (w+1) r bank.len C*(raw.look 4 0) := by
  have stepsCost : ∀n,
      (DFTModelSavingPadding.steps h r raw ((k,I),bank) n).work≤
        1+paddingRoleAllowance q (w+1) r bank.len C*n := by
    intro n
    induction n with
    | zero => rw [padding_steps_zero];simp
    | succ n ih =>
      have shape:=DFTModelSavingPadding.steps_preserved h r n k I raw bank
      have same : (DFTModelSavingPadding.steps h r raw ((k,I),bank) n).val=
        ((k,I),(DFTModelSavingPadding.steps h r raw ((k,I),bank) n).val.2) := Prod.ext shape.1 rfl
      have roleCost:=padding_role_work q w r n k C I raw ((k,I),bank)
        (DFTModelSavingPadding.steps h r raw ((k,I),bank) n).val.2 h columns widthEq qp wide fits children
      rw [shape.2] at roleCost
      rw [padding_steps_succ]
      rw [same,Nat.mul_add,Nat.mul_one]
      have pos : 1≤paddingRoleAllowance q (w+1) r bank.len C := by
        unfold paddingRoleAllowance
        omega
      omega
  rw [DFTModelSavingPadding.padding_run]
  have cost:=stepsCost (raw.look 4 0)
  change (DFTModelSavingPadding.steps h r raw ((k,I),bank) (raw.look 4 0)).work+13≤_
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
