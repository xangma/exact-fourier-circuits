import DFTModelCacheSpectrumForestProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheSpectrumForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] program cell DFTModelCacheTraversal.program
  DFTModelCacheRectanglePreparation.program

theorem program_length (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).val.2.len=
      (run DFTModelCacheTraversal.program (r,o)).val.2.len := by
  rw [program_run]
  exact congrArg Tape.len (ModelEquivalenceInterpreter.tab_value _ _ _)

/-- The node tape is retained exactly, and each bank is computed by the real
row producer at the corresponding actual flattened descriptor index. -/
theorem program_value (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).val=
      ((run DFTModelCacheTraversal.program (r,o)).val.1,
        Tape.tab (run DFTModelCacheTraversal.program (r,o)).val.2.len (fun i=>
          (run DFTModelCacheRectanglePreparation.program
            ((r,(run DFTModelCacheTraversal.program (r,o)).val.2.look i
              DFTModelCacheDescriptor.Row7.blank),(D,z))).val)) := by
  rw [program_run]
  have tab:=ModelEquivalenceInterpreter.tab_value
    (run DFTModelCacheTraversal.program (r,o)).val.2.len
    DFTModelCacheRectanglePreparation.Output.blank (fun i=>
      run cell ((((r,o),(D,z)),(run DFTModelCacheTraversal.program (r,o)).val),i))
  change (_, (Bill.tab _ _ _).val)=_
  rw [tab]
  congr 1
  apply congrArg (Tape.tab _)
  funext i
  rw [cell_run]
  rfl

theorem directory_value (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).val.1=
      DFTModelCacheTraversal.ofList
        ((UniformLocalCacheTreeMachine.walk (2*r+1) 0 0 [⟨r,o,0,0⟩]).1.map
          DFTModelCacheTraversal.nodeEncode) := by
  rw [program_value,DFTModelCacheTraversal.program_value]

theorem program_lengths (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).val.1.len≤2*r+1 ∧
      (run program ((r,o),(D,z))).val.2.len≤r^2 := by
  have bounds:=DFTModelCacheTraversal.program_lengths r o
  rw [program_value]
  exact bounds

theorem program_cell (r o D : ℕ) (z : ℂ)
    (i : Fin (run program ((r,o),(D,z))).val.2.len) :
    ∃q,DFTModelCacheRectanglePreparation.ProducedRow r q ∧
      (run program ((r,o),(D,z))).val.2.pos i=
        (run DFTModelCacheRectanglePreparation.program
          ((r,DFTModelCacheDescriptor.rowEncode q),(D,z))).val := by
  have hi:i.val<(run DFTModelCacheTraversal.program (r,o)).val.2.len := by
    have length:=program_length r o D z
    have h:=i.isLt
    omega
  obtain ⟨q,source,eq⟩:=traversal_produced r o ⟨i.val,hi⟩
  refine ⟨q,source,?_⟩
  have cells:=congrArg (fun t:Output.T=>t.2.look i.val
    DFTModelCacheRectanglePreparation.Output.blank) (program_value r o D z)
  rw [Tape.look_of_lt _ _ i.isLt] at cells
  refine cells.trans ?_
  change (Tape.tab (run DFTModelCacheTraversal.program (r,o)).val.2.len (fun k=>
    (run DFTModelCacheRectanglePreparation.program
      ((r,(run DFTModelCacheTraversal.program (r,o)).val.2.look k
        DFTModelCacheDescriptor.Row7.blank),(D,z))).val)).look i.val
      DFTModelCacheRectanglePreparation.Output.blank=_
  simp only [Tape.look,Tape.tab,dite_eq_left hi]
  rw [eq]

theorem program_valid (r o D : ℕ) (master : DFTModelCacheRectanglePreparation.Master r D) :
    (run program ((r,o),(D,OAI.ExactFourier.zeta D))).valid := by
  rw [program_run]
  refine ⟨DFTModelCacheTraversal.program_valid r o,?_,trivial⟩
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).mpr
  intro i hi
  obtain ⟨q,source,eq⟩:=traversal_produced r o ⟨i,hi⟩
  rw [cell_run,Tape.look_of_lt _ _ hi,eq]
  exact DFTModelCacheRectanglePreparation.program_valid source master

/-- Every output row keeps its true native descriptor, computed height, and
all seven original shared-bank blocks, in the original traversal row order. -/
theorem program_sharedBank (r o D : ℕ)
    (master : DFTModelCacheRectanglePreparation.Master r D)
    (i : Fin (run program ((r,o),(D,OAI.ExactFourier.zeta D))).val.2.len) :
    ∃q,DFTModelCacheRectanglePreparation.ProducedRow r q ∧
      ((run program ((r,o),(D,OAI.ExactFourier.zeta D))).val.2.pos i).1=
        DFTModelCacheDescriptor.rowEncode q ∧
      ((run program ((r,o),(D,OAI.ExactFourier.zeta D))).val.2.pos i).2.1=
        DFTModelCacheRectanglePreparation.height q ∧
      ((run program ((r,o),(D,OAI.ExactFourier.zeta D))).val.2.pos i).2.2.len=
        7*DFTModelCacheRectanglePreparation.width q ∧
      ∀k:Fin (UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)),
        ((run program ((r,o),(D,OAI.ExactFourier.zeta D))).val.2.pos i).2.2.look k.val 0=
          UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
            (DFTModelCacheSpectrum.rankKernels r
              (DFTModelCacheRectanglePreparation.parameters r q)
              (DFTModelCacheRectanglePreparation.height q) (OAI.ExactFourier.zeta r)) k := by
  obtain ⟨q,source,output⟩:=program_cell r o D (OAI.ExactFourier.zeta D) i
  refine ⟨q,source,?_,?_,?_,?_⟩
  · rw [output,DFTModelCacheRectanglePreparation.program_value]
  · rw [output,DFTModelCacheRectanglePreparation.program_value]
  · rw [output]
    exact DFTModelCacheRectanglePreparation.program_length _ source
  · intro k
    rw [output]
    exact DFTModelCacheRectanglePreparation.program_sharedBank source master k

end
end ExactFourierCircuits.DFTModelCacheSpectrumForest
