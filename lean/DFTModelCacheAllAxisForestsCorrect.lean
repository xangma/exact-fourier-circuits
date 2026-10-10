import DFTModelCacheAllAxisForestsProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheAllAxisForests
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] program setup body DFTModelCacheAxisRoots.program
  DFTModelRoot.program DFTModelCacheSpectrumForest.program

theorem axisCount_eq (n : ℕ) : UniformAllAxisSeedPreparation.axisCount n=
    UniformWorkingLength.axisCount n+1 := rfl

theorem radix_eq (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    UniformAllAxisSeedPreparation.radix n j=UniformCRTTraversalCycle.radices n j := rfl

theorem root_lookup (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    (DFTModelCacheAxisRoots.values n).look j.val (0,0)=
      (UniformAllAxisSeedPreparation.radix n j,
        OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) := by
  rw [Tape.look_of_lt _ _ j.isLt]
  rfl

def values (n : ℕ) : Output.T :=
  (DFTModelCacheAxisRoots.values n,
    Tape.tab (UniformAllAxisSeedPreparation.axisCount n) (fun i=>
      (run DFTModelCacheSpectrumForest.program
        (((DFTModelCacheAxisRoots.values n).look i (0,0) |>.1,0),
          (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val))

theorem program_value (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n := by
  rw [program,comp_run,setup_run]
  change (run body _).val=_
  rw [DFTModelCacheAxisRoots.selected_value n hn,
    (DFTModelRoot.actual_master_order n hn).1,body_value]
  rfl

theorem program_valid (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid := by
  rw [program,comp_run,setup_run]
  change ((run DFTModelCacheAxisRoots.program _).valid ∧
    (run DFTModelRoot.program n).valid) ∧ (run body _).valid
  refine ⟨⟨DFTModelCacheAxisRoots.selected_valid n hn _,
    (DFTModelRoot.actual_master_order n hn).2.1⟩,?_⟩
  rw [DFTModelCacheAxisRoots.selected_value n hn,(DFTModelRoot.actual_master_order n hn).1]
  apply body_valid
  intro i hi
  let j : Fin (UniformAllAxisSeedPreparation.axisCount n):=⟨i,hi⟩
  rw [root_lookup n j]
  exact DFTModelCacheSpectrumForest.selected_valid n hn j 0

theorem program_lengths (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.1.len=
        UniformAllAxisSeedPreparation.axisCount n ∧
      (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.len=
        UniformAllAxisSeedPreparation.axisCount n := by
  rw [program_value n hn]
  exact ⟨rfl,rfl⟩

/-- Full-axis indexing includes the generated final binary row. -/
theorem axis_value (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look j.val
        DFTModelCacheSpectrumForest.Output.blank=
      (run DFTModelCacheSpectrumForest.program
        ((UniformAllAxisSeedPreparation.radix n j,0),
          (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val := by
  rw [program_value n hn]
  change (Tape.tab _ _).look _ _=_
  rw [Tape.look_of_lt _ _ j.isLt]
  change (run DFTModelCacheSpectrumForest.program
    ((((DFTModelCacheAxisRoots.values n).look j.val (0,0)).1,0),
      (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val=_
  rw [root_lookup n j]

theorem axis_directory (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    ((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look j.val
        DFTModelCacheSpectrumForest.Output.blank).1=
      DFTModelCacheTraversal.ofList
        ((UniformLocalCacheTreeMachine.walk (2*UniformAllAxisSeedPreparation.radix n j+1) 0 0
          [⟨UniformAllAxisSeedPreparation.radix n j,0,0,0⟩]).1.map DFTModelCacheTraversal.nodeEncode) := by
  rw [axis_value n hn j,DFTModelCacheSpectrumForest.directory_value]

/-- Each output rectangle is genuinely visited and its seven spectrum blocks
are produced by the fixed rectangle program, using the computed master order. -/
theorem axis_sharedBank (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n))
    (i : Fin (((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look
      j.val DFTModelCacheSpectrumForest.Output.blank).2.len)) :
    ∃q,DFTModelCacheRectanglePreparation.ProducedRow (UniformAllAxisSeedPreparation.radix n j) q ∧
      (((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look
        j.val DFTModelCacheSpectrumForest.Output.blank).2.pos i).1=DFTModelCacheDescriptor.rowEncode q ∧
      (((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look
        j.val DFTModelCacheSpectrumForest.Output.blank).2.pos i).2.1=DFTModelCacheRectanglePreparation.height q ∧
      (((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look
        j.val DFTModelCacheSpectrumForest.Output.blank).2.pos i).2.2.len=7*DFTModelCacheRectanglePreparation.width q ∧
      ∀k:Fin (UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)),
        (((run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val.2.look
          j.val DFTModelCacheSpectrumForest.Output.blank).2.pos i).2.2.look k.val 0=
          UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
            (DFTModelCacheSpectrum.rankKernels (UniformAllAxisSeedPreparation.radix n j)
              (DFTModelCacheRectanglePreparation.parameters (UniformAllAxisSeedPreparation.radix n j) q)
              (DFTModelCacheRectanglePreparation.height q)
              (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j))) k := by
  revert i
  rw [axis_value n hn j]
  intro i
  exact DFTModelCacheSpectrumForest.program_sharedBank _ _ _
    (DFTModelCacheRectanglePreparation.selected_master n hn j) i

end
end ExactFourierCircuits.DFTModelCacheAllAxisForests
