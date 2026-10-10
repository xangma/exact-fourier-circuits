import DFTModelSavingResidualGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualBoolean
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelSavingResidualBatch.program DFTModelSavingResidualFinish.program
  DFTModelSavingResidualFlip.program DFTModelResidualClosedRole.scatter

def Boolean (v : Tape Tagged.T) : Prop := ∀ i, i < v.len → (v.look i Tagged.blank).1 < 2

theorem look_boolean {v : Tape Tagged.T} (h : Boolean v) (i : ℕ) : (v.look i Tagged.blank).1 < 2 := by
  by_cases live : i < v.len
  · exact h i live
  · rw [Tape.look_of_le _ _ (by omega)]
    decide

theorem tab_boolean (L : ℕ) (f : ℕ → Tagged.T) (h : ∀ i, i < L → (f i).1 < 2) :
  Boolean (Tape.tab L f) := by
  intro i hi
  rw [Tape.look_of_lt _ _ hi]
  exact h i hi

theorem set_boolean {v : Tape Tagged.T} (h : Boolean v) (i : ℕ) (x : Tagged.T) (small : x.1 < 2) :
  Boolean (v.set i x) := by
  intro j hj
  change j < v.len at hj
  simp only [Tape.look,Tape.set,hj,↓reduceDIte]
  by_cases same : j=i
  · simp only [same,ite_true];exact small
  · simp only [same,ite_false]
    simpa only [Tape.look,hj,↓reduceDIte] using h j hj

 theorem scatter_steps (p : Tape ℕ) (v : Tape Tagged.T) (h : Boolean v) (m : ℕ) :
  Boolean (DFTModelResidualMovement.scatterSteps Tagged p v m).val := by
  induction m with
  | zero=>exact tab_boolean _ _ (fun _ _=>by decide)
  | succ m ih=>
    change Boolean ((DFTModelResidualMovement.scatterSteps Tagged p v m).val.set
      (run (DFTModelResidualMovement.scatterCell Tagged) ((p,v),m)).val.1
      (run (DFTModelResidualMovement.scatterCell Tagged) ((p,v),m)).val.2)
    rw [DFTModelResidualMovement.scatterCell_run]
    exact set_boolean ih _ _ (look_boolean h m)

 theorem movement_scatter (p : Tape ℕ) (v : Tape Tagged.T) (h : Boolean v) :
  Boolean (run (DFTModelResidualMovement.scatter Tagged) (p,v)).val :=
  scatter_steps p v h p.len

 theorem role_scatter (ctx : DFTModelResidualClosedBasis.Meta.T) (a : ℕ)
  (old : Tape Tagged.T) (p : Tape ℕ) (v : Tape Tagged.T) (before : Boolean old) (after : Boolean v) :
  Boolean (run (DFTModelResidualClosedRole.scatter Tagged) ((ctx,(a,old)),(p,v))).val := by
  have next:=movement_scatter p v after
  rw [DFTModelResidualClosedRole.scatter_value,DFTModelResidualClosedRoleStages.replace_value]
  apply tab_boolean
  intro i _
  split
  · exact look_boolean next _
  · exact look_boolean before _

 theorem flip_boolean (N flag : ℕ) (v : Tape Tagged.T) (h : Boolean v) :
  Boolean (run (DFTModelSavingResidualFlip.program Tagged) (N,(flag,v))).val := by
  rw [DFTModelSavingResidualFlip.program_value]
  split
  · exact h
  · exact tab_boolean _ _ (fun _ _=>look_boolean h _)

 theorem batch_boolean (h : Handler Port) (p : Params.T) (G T : ℕ) (bank : Tape Tagged.T)
  (children : ∀ g, g < G → Boolean (h (p,DFTModelClockBatch.sliced T g bank Tagged.blank)).val) :
  Boolean (Code.run (DFTModelSavingResidualBatch.program Params Tagged) h (p,(G,(T,bank)))).val := by
  intro j hj
  rw [DFTModelSavingResidualBatch.length] at hj
  rw [DFTModelSavingResidualBatch.lookup Params Tagged h p G T bank ⟨j,hj⟩]
  exact look_boolean (children _ (Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hj))) _

/-- Entire arbitrary Boolean-tagged parent banks stay Boolean; the only child
hypothesis is Boolean output of the actual called children. Numerical action,
raw-direction validity and canonical per-role tag folds are not premises. -/
 theorem program_boolean (h : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T) (before : Boolean old)
  (children : ∀ g, g < (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2.len/
      (UniformBatching.width*2^ctx.1) → Boolean
    (h ((ctx.1,I),DFTModelClockBatch.sliced (UniformBatching.width*2^ctx.1) g
      (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2 Tagged.blank)).val) :
  Boolean (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).val.2 := by
  have child : Boolean (returned h (ctx,(a,(raw,((k,I),old))))) := by
    rw [returned,args_value]
    exact batch_boolean h _ _ _ _ children
  rw [DFTModelSavingResidual.value,DFTModelSavingResidual.prepared,DFTModelSavingResidualSetup.value,
    DFTModelSavingResidualSetup.initial_value,DFTModelSavingResidualFinish.value,
    DFTModelResidualClosedRole.gather_value]
  exact role_scatter ctx a old _ _ before (flip_boolean _ _ _ child)

/-- All indices are covered, including out-of-bounds blank reads. -/
def BooleanTape (v : Tape Tagged.T) : Prop := ∀ j, (v.look j Tagged.blank).1 ≤ 1

theorem boolean_iff (v : Tape Tagged.T) : Boolean v ↔ BooleanTape v := by
  constructor
  · intro h j
    exact Nat.le_of_lt_succ (look_boolean h j)
  · intro h j _
    exact Nat.lt_succ_of_le (h j)

theorem gather_boolean (ctx : DFTModelResidualClosedBasis.Meta.T) (a : ℕ)
  (old : Tape Tagged.T) (before : Boolean old) :
  Boolean (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2 := by
  rw [DFTModelResidualClosedRole.gather_value,DFTModelResidualMovement.gather_value]
  apply tab_boolean
  intro i _
  have slice : Boolean (run (DFTModelResidualClosedRoleStages.slice Tagged)
    ((ctx,(a,old)),(run DFTModelResidualClosedAddresses.program ctx).val)).val := by
    rw [DFTModelResidualClosedRoleStages.slice_value]
    exact tab_boolean _ _ (fun _ _=>look_boolean before _)
  exact look_boolean slice _

theorem sliced_boolean (T g : ℕ) (v : Tape Tagged.T) (before : Boolean v) :
  Boolean (DFTModelClockBatch.sliced T g v Tagged.blank) :=
  tab_boolean _ _ (fun _ _=>look_boolean before _)

theorem program_booleanTape (h : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T) (before : BooleanTape old)
  (children : ∀ g, g < (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2.len/
      (UniformBatching.width*2^ctx.1) → BooleanTape
    (h ((ctx.1,I),DFTModelClockBatch.sliced (UniformBatching.width*2^ctx.1) g
      (run (DFTModelResidualClosedRole.gather Tagged) (ctx,(a,old))).val.2.2 Tagged.blank)).val) :
  BooleanTape (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).val.2 :=
  (boolean_iff _).mp (program_boolean h ctx a raw k I old ((boolean_iff _).mpr before)
    (fun g hg=>(boolean_iff _).mpr (children g hg)))

theorem program_booleanTape_of_child (h : Handler Port) (ctx : DFTModelResidualClosedBasis.Meta.T)
  (a raw k : ℕ) (I : ℂ) (old : Tape Tagged.T) (before : BooleanTape old)
  (children : ∀ (J : ℂ) (v : Tape Tagged.T), BooleanTape v → BooleanTape (h ((ctx.1,J),v)).val) :
  BooleanTape (Code.run DFTModelSavingResidual.program h (ctx,(a,(raw,((k,I),old))))).val.2 := by
  apply program_booleanTape h ctx a raw k I old before
  intro g _
  apply children I _
  exact (boolean_iff _).mp (sliced_boolean _ _ _ (gather_boolean ctx a old ((boolean_iff _).mpr before)))

end
end ExactFourierCircuits.DFTModelSavingResidualBoolean
