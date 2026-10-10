import DFTModelCacheSpectrumForestProvenance
import UniformLocalRectangleBankMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
open UniformLocalRectangleDescriptors (Row)
noncomputable section

/-- Rooted traversal, unlike an arbitrary local ProducedRow, bounds the
physical offset. The source is the actual balanced forest rectangle list. -/
theorem rectangle_extent (r o:ℕ) (q:Row)
 (member:q∈(ofPlan (UniformBalancedToeplitz.plan r) o).rectangles) :
 q.offset+q.width≤o+r := by
 rw [←root_walk_rows r o 0] at member
 obtain ⟨L,hL,hq⟩:=List.mem_flatten.mp member
 obtain ⟨visit,hvisit,rfl⟩:=List.mem_map.mp hL
 have fit:=DFTModelCacheSpectrumForest.walk_width r o (2*r+1) 0 0 [⟨r,o,0,0⟩]
  (by intro t ht;simp only [List.mem_singleton] at ht;subst t;exact ⟨le_rfl,le_rfl⟩)
  visit hvisit
 unfold currentRows at hq
 split at hq
 · simp only [List.not_mem_nil] at hq
 · rename_i h
   have geometry:=UniformLocalRectangleBankMachine.rows_geometry visit.task.width visit.task.offset q
    (by omega) (by omega) hq
   rw [geometry.2.2.2.2.2.2.2.1,geometry.2.2.2.2.2.2.2.2]
   exact fit.2

theorem rooted_source (r ambient:ℕ) (q:Row)
 (member:q∈(ofPlan (UniformBalancedToeplitz.plan r) 0).rectangles)
 (ambientBound:r≤ambient) :
 DFTModelCacheRectanglePreparation.ProducedRow r q ∧ q.offset+q.width≤ambient := by
 refine ⟨DFTModelCacheSpectrumForest.rectangle_produced r 0 q member,?_⟩
 have extent:=rectangle_extent r 0 q member
 omega

end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
