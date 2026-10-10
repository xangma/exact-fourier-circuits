import DFTModelCacheRectanglePreparationNode
import DFTModelCacheDescriptorNodePeak

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDescriptor (Row7 rowEncode)
open scoped BigOperators
noncomputable section
attribute [local irreducible] nodeProgram nodeCell program DFTModelCacheDescriptor.node

def rowBudget (r D : ℕ) := 100100*(r+1)^2+80*(Nat.log2 (D+1)+1)
def nodeBudget (r v D : ℕ) :=4000*(v+1)^4+v^2*(rowBudget r D+28)+19

theorem program_uniform_work {r D : ℕ} {q : UniformLocalRectangleDescriptors.Row} (z : ℂ)
    (source : ProducedRow r q) :
    (run program ((r,rowEncode q),(D,z))).work≤rowBudget r D := by
  have work:=program_work (D:=D) z source
  have radixLog : Nat.log2 (D/r+1)≤Nat.log2 (D+1) := by
    simpa only [Nat.log2_eq_log_two] using
      (Nat.log_mono_right (b:=2) (Nat.add_le_add_right (Nat.div_le_self D r) 1))
  have fftLog : Nat.log2 (D/width q+1)≤Nat.log2 (D+1) := by
    simpa only [Nat.log2_eq_log_two] using
      (Nat.log_mono_right (b:=2) (Nat.add_le_add_right (Nat.div_le_self D (width q)) 1))
  dsimp only [rowBudget]
  omega

theorem node_length_bound (v o : ℕ) :
    (run DFTModelCacheDescriptor.node (v,o)).val.2.len≤v^2 := by
  have length:=congrArg (fun x=>x.2.len) (DFTModelCacheDescriptor.node_value v o)
  simp only [DFTModelCacheDescriptor.listTape,List.length_map] at length
  rw [length]
  have decomposition:=UniformLocalCacheTreeCoverage.task_decomposition
    (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task) 0
  have bound:=UniformLocalCacheTreeMachine.ofPlan_rectangles_length
    (UniformBalancedToeplitz.plan v) o
  rw [decomposition,List.length_append] at bound
  omega

theorem nodeProgram_work (r v o D : ℕ) (z : ℂ) (vr : v≤r) :
    (run nodeProgram (r,((v,o),(D,z)))).work≤nodeBudget r v D := by
  rw [nodeProgram_run]
  let nr:=(run DFTModelCacheDescriptor.node (v,o)).val
  let L:=nr.2.len
  have producer:=DFTModelCacheDescriptor.node_work v o
  have count:=node_length_bound v o
  have cells : ∀i∈Finset.range L,
      (run nodeCell (((r,((v,o),(D,z))),nr),i)).work≤rowBudget r D+24 := by
    intro i hi
    have hi':i<(run DFTModelCacheDescriptor.node (v,o)).val.2.len:=Finset.mem_range.mp hi
    obtain ⟨q,source,eq⟩:=node_produced r v o vr ⟨i,hi'⟩
    rw [nodeCell_run]
    change (run program ((r,nr.2.look i Row7.blank),(D,z))).work+24≤_
    rw [Tape.look_of_lt _ _ hi',eq]
    exact Nat.add_le_add_right (program_uniform_work z source) 24
  have sum:=Finset.sum_le_sum cells
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  change (run DFTModelCacheDescriptor.node (v,o)).work+
    ((Bill.tab L Output.blank (fun i=>run nodeCell (((r,((v,o),(D,z))),nr),i))).work+1)+16≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have scaled:=Nat.mul_le_mul_right (rowBudget r D+28) count
  dsimp only [nodeBudget]
  nlinarith

theorem nodeProgram_peak (r v o D : ℕ) (z : ℂ) (vr : v≤r) :
    (run nodeProgram (r,((v,o),(D,z)))).peak ≤ max (D+2) (4000*(r+1)^2) := by
  rw [nodeProgram_run]
  let nr:=(run DFTModelCacheDescriptor.node (v,o)).val
  let L:=nr.2.len
  let B:=max (D+2) (4000*(r+1)^2)
  have producer: (run DFTModelCacheDescriptor.node (v,o)).peak≤B := by
    have bound:=DFTModelCacheDescriptor.node_peak v o
    have growth:4000*(v+1)^2≤4000*(r+1)^2:=by nlinarith
    exact (bound.trans growth).trans (le_max_right _ _)
  have count:L≤B := by
    have bound:=node_length_bound v o
    have growth:v^2≤4000*(r+1)^2:=by nlinarith
    exact (bound.trans growth).trans (le_max_right _ _)
  have cells : (Finset.range L).sup
      (fun i=>(run nodeCell (((r,((v,o),(D,z))),nr),i)).peak)≤B := by
    apply Finset.sup_le
    intro i hi
    have hi':i<(run DFTModelCacheDescriptor.node (v,o)).val.2.len:=Finset.mem_range.mp hi
    obtain ⟨q,source,eq⟩:=node_produced r v o vr ⟨i,hi'⟩
    rw [nodeCell_run]
    change max (run program ((r,nr.2.look i Row7.blank),(D,z))).peak 0≤_
    rw [Tape.look_of_lt _ _ hi',eq,max_zero]
    have bound:=program_peak (D:=D) z source
    have widthBound:width q≤8*r:=(produced_width source).2.2
    have growth:r+7*width q+7≤4000*(r+1)^2:=by nlinarith
    exact bound.trans (max_le_max (le_refl _) growth)
  change max (max (run DFTModelCacheDescriptor.node (v,o)).peak
    (max (Bill.tab L Output.blank
      (fun i=>run nodeCell (((r,((v,o),(D,z))),nr),i))).peak 0)) L≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  exact max_le (max_le producer (max_le (max_le count cells) (Nat.zero_le _))) count

theorem nodeProgram_cutoff (r v o D : ℕ) (z : ℂ) :
    (run nodeProgram (r,((v,o),(D,z)))).val.1=UniformWorkspacePlanner.selected v := by
  rw [nodeProgram_run]
  exact congrArg Prod.fst (DFTModelCacheDescriptor.node_value v o)

/-- Every bank in the combined output carries its exact original descriptor
and computed height, and equals the native shared bank on all seven blocks. -/
theorem nodeProgram_sharedBank (r v o D : ℕ) (vr : v≤r) (master : Master r D)
    (i : Fin (run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.len) :
    ∃q,ProducedRow r q ∧
      ((run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.pos i).1=rowEncode q ∧
      ((run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.pos i).2.1=height q ∧
      ((run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.pos i).2.2.len=7*width q ∧
      ∀k:Fin (UniformToeplitzCrossDAG.bankSize (height q)),
        ((run nodeProgram (r,((v,o),(D,OAI.ExactFourier.zeta D)))).val.2.pos i).2.2.look k.val 0=
          UniformToeplitzCrossDAG.sharedBank (height q)
            (DFTModelCacheSpectrum.rankKernels r (parameters r q) (height q)
              (OAI.ExactFourier.zeta r)) k := by
  obtain ⟨q,source,output⟩:=nodeProgram_specification r v o D vr i
  refine ⟨q,source,?_,?_,?_,?_⟩
  · rw [output,program_value]
  · rw [output,program_value]
  · rw [output]
    exact program_length _ source
  · intro k
    rw [output]
    exact program_sharedBank source master k

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
