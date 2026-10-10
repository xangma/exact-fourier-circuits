import DFTModelCacheDirectLeafForest

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] forest node forestCell DFTModelCacheTraversal.program Bill.tab

theorem visit_bounds (r o : ℕ) (q : UniformLocalCacheTreeMachine.Visit)
    (hq : q∈visits r o) : q.task.width≤r ∧ q.task.offset+q.task.width≤o+r :=
  DFTModelCacheSpectrumForest.walk_width r o (2*r+1) 0 0 [⟨r,o,0,0⟩]
    (by intro t ht;simp only[List.mem_singleton] at ht;subst t;exact ⟨le_rfl,le_rfl⟩) q hq

theorem forest_valid (r o K : ℕ) : (run forest (r,(o,K))).valid := by
  rw[forest_run]
  change (run DFTModelCacheTraversal.program (r,o)).valid ∧
    ((Bill.tab _ Orientations.blank _).valid ∧ True)
  refine ⟨DFTModelCacheTraversal.program_valid r o,?_,trivial⟩
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro i hi
  obtain ⟨q,_,eq⟩:=node_produced r o ⟨i,hi⟩
  rw[forestCell_run]
  change (run node ((run DFTModelCacheTraversal.program (r,o)).val.1.look i _,K)).valid
  rw[Tape.look_of_lt _ _ hi,eq]
  exact node_valid q K

def forestWorkBudget (r : ℕ) : ℕ :=
  100000*(r+1)^5+(2*r+1)*(1000*(r+1)^3+50)+19
def forestPeakBudget (r o K : ℕ) : ℕ :=
  max (DFTModelCacheTraversal.peakBudget r o) (o+r+K+2*(r+1)^2+2)

theorem forest_work (r o K : ℕ) :
    (run forest (r,(o,K))).work≤forestWorkBudget r := by
  rw[forest_run]
  let t:=(run DFTModelCacheTraversal.program (r,o)).val
  let L:=t.1.len
  have tw:=DFTModelCacheTraversal.program_work r o
  have count:L≤2*r+1 := (DFTModelCacheTraversal.program_lengths r o).1
  have cells:∀i∈Finset.range L,
      (run forestCell (((r,(o,K)),t),i)).work≤1000*(r+1)^3+46 := by
    intro i hi
    have hi':i<(run DFTModelCacheTraversal.program (r,o)).val.1.len := Finset.mem_range.mp hi
    obtain ⟨q,hq,eq⟩:=node_produced r o ⟨i,hi'⟩
    have width:=(visit_bounds r o q hq).1
    have pw:=Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 3
    rw[forestCell_run]
    change (run node (t.1.look i _,K)).work+18≤_
    rw[Tape.look_of_lt _ _ hi',eq]
    have h:=node_work q K
    nlinarith
  have sum:=Finset.sum_le_sum cells
  simp only[Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  change (run DFTModelCacheTraversal.program (r,o)).work+
    ((Bill.tab L Orientations.blank (fun i=>run forestCell (((r,(o,K)),t),i))).work+1)+16≤_
  rw[ModelEquivalenceInterpreter.tab_work]
  have scaled:=Nat.mul_le_mul_right (1000*(r+1)^3+50) count
  dsimp only[forestWorkBudget]
  nlinarith

theorem forest_peak (r o K : ℕ) :
    (run forest (r,(o,K))).peak≤forestPeakBudget r o K := by
  rw[forest_run]
  let t:=(run DFTModelCacheTraversal.program (r,o)).val
  let L:=t.1.len
  let B:=forestPeakBudget r o K
  have tp:(run DFTModelCacheTraversal.program (r,o)).peak≤B :=
    (DFTModelCacheTraversal.program_peak r o).trans (le_max_left _ _)
  have count:L≤B := by
    have h:=(DFTModelCacheTraversal.program_lengths r o).1
    have fit:2*r+1≤o+r+K+2*(r+1)^2+2 := by nlinarith
    exact h.trans (fit.trans (le_max_right _ _))
  have cells:(Finset.range L).sup
      (fun i=>(run forestCell (((r,(o,K)),t),i)).peak)≤B := by
    apply Finset.sup_le
    intro i hi
    have hi':i<(run DFTModelCacheTraversal.program (r,o)).val.1.len := Finset.mem_range.mp hi
    obtain ⟨q,hq,eq⟩:=node_produced r o ⟨i,hi'⟩
    have fit:=visit_bounds r o q hq
    have pw:=Nat.pow_le_pow_left (Nat.add_le_add_right fit.1 1) 2
    rw[forestCell_run]
    change max (run node (t.1.look i _,K)).peak 0≤_
    rw[Tape.look_of_lt _ _ hi',eq,max_zero]
    have h:=node_peak q K
    have toBound:q.task.offset+K+2*(q.task.width+1)^2≤o+r+K+2*(r+1)^2+2 := by nlinarith
    exact h.trans (toBound.trans (le_max_right _ _))
  change max (max (run DFTModelCacheTraversal.program (r,o)).peak
    (max (Bill.tab L Orientations.blank (fun i=>run forestCell (((r,(o,K)),t),i))).peak 0)) L≤B
  rw[ModelEquivalenceInterpreter.tab_peak]
  exact max_le (max_le tp (max_le (max_le count cells) (Nat.zero_le _))) count

theorem leaf_value_lengths (K : ℕ) (q : UniformLocalCacheTreeMachine.Visit) :
    (leafValue K q).1.len=UniformDirectLeafForestModel.operations q ∧
    (leafValue K q).2.len=UniformDirectLeafForestModel.operations q := by
  by_cases h:q.task.width≤1 ∨ UniformWorkspacePlanner.selected q.task.width=0
  · simp [leafValue,leaf,UniformDirectLeafForestModel.operations,UniformDirectLeafForestModel.leaf,
      h,DFTModelCacheTraversal.ofList,UniformTransposeDescriptorMachine.leafRecords_length,
      UniformDirectLeafCacheLoopBoot.size]
  · simp [leafValue,leaf,UniformDirectLeafForestModel.operations,UniformDirectLeafForestModel.leaf,
      h,DFTModelCacheTraversal.ofList]

theorem both_records_count (r o K : ℕ) :
    ((visits r o).map (fun q=>(leafValue K q).1.len+(leafValue K q).2.len)).sum=
      2*UniformJointCacheTime.leafOperations (UniformBalancedToeplitz.plan r) := by
  have counts : ((visits r o).map (fun q=>(leafValue K q).1.len+(leafValue K q).2.len))=
      (visits r o).map (fun q=>2*UniformDirectLeafForestModel.operations q) := by
    apply List.map_congr_left
    intro q _
    rw[(leaf_value_lengths K q).1,(leaf_value_lengths K q).2]
    omega
  rw[counts,List.sum_map_mul_left]
  change 2*UniformDirectLeafForestModel.demand (visits r o)=_
  rw[visits,UniformDirectLeafForestModel.root_demand]

/-- The closed forest retains the real node and rectangle tapes, including
the exact native both-orientation leaf operation count. It creates no factors. -/
theorem forest_lengths (r o K : ℕ) :
    (run forest (r,(o,K))).val.1.1.len≤2*r+1 ∧
    (run forest (r,(o,K))).val.1.2.len≤r^2 ∧
    (run forest (r,(o,K))).val.2.len=(visits r o).length := by
  rw[forest_value]
  exact ⟨(DFTModelCacheTraversal.program_lengths r o).1,
    (DFTModelCacheTraversal.program_lengths r o).2,by simp[DFTModelCacheTraversal.ofList]⟩

end
end ExactFourierCircuits.DFTModelCacheDirectLeaf
