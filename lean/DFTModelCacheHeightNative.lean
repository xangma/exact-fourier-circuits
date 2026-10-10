import DFTModelCacheHeightRaw

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightRaw
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformToeplitzCrossDAG
noncomputable section

/-- The native entry is the real per-height 132-instruction wrapper. Its ordinary
input banks are the topology/order/directory, not the selected rows or colors. -/
theorem native_execution (a e d T Q R D A C Z P F U B m:ℕ)
 (enabled:Bool) (x:Fin m→ℂ) (s:UniformMachine.State)
 (header:UniformCrossDepthReplayPreparation.Header (dag a e).size d T Q R D A C P e
   (UniformRadixTwoDAG.width (DFTModelCacheTopology.exponent a e)) F U enabled s)
 (pc:s.pc=0) (wb:WordBound B s)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6)
 (bank:UniformDAGBucketMachine.Bank Q
   (UniformDAGBucketMachine.order (dag a e).size
     (UniformDAGBucketMachine.typedDepth (dag a e).program)) s)
 (directory:UniformDAGBucketMachine.Directory R (dag a e).size ((dag a e).size+2)
   (UniformDAGBucketMachine.typedDepth (dag a e).program) s)
 (tape:UniformToeplitzCrossTopologyMachine.RowTable
   (UniformToeplitzCrossTopologyMachine.crossRows (DFTModelCacheTopology.exponent a e) a e) T s)
 (hT:T+5*(dag a e).size≤D) (hQ:Q+(dag a e).size≤D)
 (hR:R+(dag a e).size+2≤D) (hD:D+6*(dag a e).size≤F) (hF:F+2*(dag a e).size≤U)
 (budget:UniformCrossDepthReplayPreparation.wordBudget (dag a e).size T Q R D A C P e
   (UniformRadixTwoDAG.width (DFTModelCacheTopology.exponent a e)) F U≤B):
 ∃u ticks,
 BoundedExecution UniformCrossDepthReplayPreparation.program m x B s ticks u ∧
 ticks≤64*(dag a e).size+200*(2*(dag a e).size+1)^2+31 ∧ u.pc=131 ∧
 DFTModelCacheHeight.ProducedRows D
   (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e))).val.2 u ∧
 u.natReg 800=(run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e))).val.2.len ∧
 (∀i:Fin (UniformCrossDepthReplayPreparation.bucket (dag a e).program enabled d).length,
  u.natHeap (F+i.val)=some (UniformColoring.coloring
   (UniformCrossDepthReplayPreparation.shiftedEdges A
    (UniformCrossDepthReplayPreparation.bucket (dag a e).program enabled d)) 6 i)) ∧
 UniformCrossDepthReplayPreparation.OutsideNat D F U (dag a e).size s u ∧
 UniformCrossDepthReplayPreparation.Frame s u := by
 obtain ⟨u,ticks,actual,time,terminal,table,count,colors,_bounds,_safe,outside,frame⟩:=
  UniformCrossDepthReplayPreparation.cross_bucket_execution
   (DFTModelCacheTopology.exponent a e) a e d T Q R D A C Z P F U B m
   (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
   enabled x s header pc wb height bank directory tape hT hQ hR hD hF budget
 have value:=program_value a e A C Z P d enabled height
 refine ⟨u,ticks,actual,time,terminal,?_,?_,colors,outside,frame⟩
 · rw [value]
   exact DFTModelCacheHeight.producedRows_table D _ u table
 · rw [value]
   simpa only [DFTModelCacheHeight.rowTape,Tape.tab,List.length_map,
     dag,DFTModelCacheBucketRaw.dag,DFTModelCacheTopologyDepth.dag] using count

/-- The produced occurrence list has the actual degree-six native graph.
This is independent of coefficient values and never merges duplicate rows. -/
theorem native_degree (a e A d:ℕ) (enabled:Bool):
 UniformColoring.DegreeBound
  (UniformCrossDepthReplayPreparation.shiftedEdges A
   (UniformCrossDepthReplayPreparation.bucket (dag a e).program enabled d)) 6 :=
 UniformCrossDepthReplayPreparation.shiftedEdges_degree A 6 _
  (UniformCrossDepthReplayPreparation.cross_bucket_degree
   (DFTModelCacheTopology.exponent a e) a e d
   (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2 enabled)

end
end ExactFourierCircuits.DFTModelCacheHeightRaw
