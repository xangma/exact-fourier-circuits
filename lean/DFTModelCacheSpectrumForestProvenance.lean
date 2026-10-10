import DFTModelCacheTraversalWordBound
import DFTModelCacheRectanglePreparationBounds

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.1–3.5, pp.13–18: provenance of the actual balanced descriptor forest.
This module supplies no descriptor, coefficient bank, or action to the code. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
open UniformLocalCacheTreeExecution
open UniformLocalRectangleDescriptors (Row)
noncomputable section

theorem walk_width (r o fuel k R : ℕ) (tasks : List Task) (good : Good r o tasks) :
    ∀q∈(walk fuel k R tasks).1,q.task.width≤r ∧ q.task.offset+q.task.width≤o+r := by
  induction fuel generalizing k R tasks with
  | zero => simp [walk]
  | succ fuel ih =>
    cases tasks with
    | nil => simp [walk]
    | cons t ts =>
      intro q hq
      simp only [walk,List.mem_cons] at hq
      rcases hq with rfl|hq
      · exact good t (by simp)
      · exact ih _ _ _ (good.children k) q hq

theorem rectangle_produced (r o : ℕ) (q : Row)
    (member : q∈(ofPlan (UniformBalancedToeplitz.plan r) o).rectangles) :
    DFTModelCacheRectanglePreparation.ProducedRow r q := by
  rw [←root_walk_rows r o 0] at member
  obtain ⟨L,hL,hq⟩:=List.mem_flatten.mp member
  obtain ⟨visit,hvisit,rfl⟩:=List.mem_map.mp hL
  have fit:=walk_width r o (2*r+1) 0 0 [⟨r,o,0,0⟩]
    (by intro t ht;simp only [List.mem_singleton] at ht;subst t;exact ⟨le_rfl,le_rfl⟩)
    visit hvisit
  exact ⟨visit.task.width,visit.task.offset,fit.1,hq⟩

theorem traversal_produced (r o : ℕ)
    (i : Fin (run DFTModelCacheTraversal.program (r,o)).val.2.len) :
    ∃q,DFTModelCacheRectanglePreparation.ProducedRow r q ∧
      (run DFTModelCacheTraversal.program (r,o)).val.2.pos i=
        DFTModelCacheDescriptor.rowEncode q := by
  let rows:=(ofPlan (UniformBalancedToeplitz.plan r) o).rectangles
  have produced:=DFTModelCacheTraversal.program_value r o
  have bound:i.val<rows.length := by
    change i.val<(ofPlan (UniformBalancedToeplitz.plan r) o).rectangles.length
    have length:=congrArg (fun x=>x.2.len) produced
    simp only [DFTModelCacheTraversal.ofList,List.length_map] at length
    have hi:=i.isLt
    omega
  let q:=rows[i.val]'bound
  refine ⟨q,rectangle_produced r o q (List.getElem_mem bound),?_⟩
  have bank: (run DFTModelCacheTraversal.program (r,o)).val.2=
      DFTModelCacheTraversal.ofList (rows.map DFTModelCacheTraversal.rectangleEncode) :=
    congrArg Prod.snd produced
  have cell:=congrArg (fun t:Tape DFTModelCacheDescriptor.Row7.T=>
    t.look i.val DFTModelCacheDescriptor.Row7.blank) bank
  rw [Tape.look_of_lt _ _ i.isLt] at cell
  refine cell.trans ?_
  have hm:i.val<(DFTModelCacheTraversal.ofList
      (rows.map DFTModelCacheTraversal.rectangleEncode)).len := by
    simpa only [DFTModelCacheTraversal.ofList,List.length_map] using bound
  rw [Tape.look_of_lt _ _ hm]
  change (rows.map DFTModelCacheTraversal.rectangleEncode)[i.val]'_=
    DFTModelCacheDescriptor.rowEncode q
  rw [List.getElem_map]
  rfl

end
end ExactFourierCircuits.DFTModelCacheSpectrumForest
