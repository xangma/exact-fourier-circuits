import UniformActualCalendarRectangleFactors
import UniformCalendarSelectedColors
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarForwardCodes
open UniformReplayPrint UniformDAGLayers UniformCrossDepthReplayPreparation
open UniformForwardMatchingFactorPreparation
open UniformCalendarSelectedColors UniformCalendarStableDepth
noncomputable section
variable {B : ℕ} (c : Config) (l : Layout c B)
 (ha : c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he : c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)→ℂ)

def selectedCode (i : Fin (rows c l ha he).length) :=
 (UniformChunkMatchingPreparation.crossWord c.chunk ha he).get
  (UniformColorLayerTableMachine.selectionIndex _ c.chunk.color
   (UniformChunkMatchingPreparation.colors (UniformChunkMatchingPreparation.crossWord c.chunk ha he))
   (selectedIndex c l ha he i))

lemma row_values (i : Fin (rows c l ha he).length) :
 ((rows c l ha he).get i).dst=c.offset+
  UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity (selectedCode c l ha he i).dst ∧
 ((rows c l ha he).get i).src=c.offset+
  UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity (selectedCode c l ha he i).src ∧
 selectedValue c l ha he bank i=(selectedCode c l ha he i).coefficient.eval bank:=by
 have ep:=endpoints c l ha he i
 refine ⟨?_,?_,rfl⟩
 · simpa only[selectedCode,selectedEdge,UniformChunkMatchingPreparation.physicalEdges,
    UniformChunkMatchingPreparation.selectedEdges,UniformColorLayerTableMachine.selectedEdges,
    UniformChunkMatchingPreparation.edges,UniformCrossDepthReplayPreparation.shiftedEdges,
    List.get_eq_getElem,Nat.zero_add] using ep.1
 · simpa only[selectedCode,selectedEdge,UniformChunkMatchingPreparation.physicalEdges,
    UniformChunkMatchingPreparation.selectedEdges,UniformColorLayerTableMachine.selectedEdges,
    UniformChunkMatchingPreparation.edges,UniformCrossDepthReplayPreparation.shiftedEdges,
    List.get_eq_getElem,Nat.zero_add] using ep.2

def occurrences : List (Nat × (Nat × Complex)) :=
 List.ofFn (fun i:Fin (rows c l ha he).length=>
  (((rows c l ha he).get i).dst,((rows c l ha he).get i).src,selectedValue c l ha he bank i))

/-- Exact occurrence list of the real forward factor producer: endpoints and
selected typed coefficients agree with the render's indexed color matching. -/
theorem occurrences_color (bound : c.chunk.color<11) :
 occurrences c l ha he bank=
 (((colorBlocks (UniformChunkMatchingPreparation.crossWord c.chunk ha he) 6)[c.chunk.color]?).getD []).map
  (fun code=>(c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity code.dst,
   c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity code.src,code.coefficient.eval bank)):=by
 rw[←chosen_eq_color _ _ bound]
 apply List.ext_getElem
 · simp only[occurrences,List.length_ofFn,List.length_map,chosen]
   exact rows_length c l ha he
 · intro i left right
   simp only[occurrences,List.getElem_ofFn,List.getElem_map,chosen,List.getElem_ofFn]
   have ri:i<(rows c l ha he).length:=by simpa only[occurrences,List.length_ofFn] using left
   have values:=row_values c l ha he bank ⟨i,ri⟩
   exact Prod.ext values.1 (Prod.ext values.2.1 values.2.2)

lemma layer_forward {r n a : ℕ} (D : UniformToeplitzCrossDAG.DAG r n a)
 (H : ℕ) (slot : UniformLocalCacheChronology.Slot)
 (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=false) :
 UniformLocalCacheChronology.layer D H slot=
 chosen (bucket D.program slot.enabled slot.depth) slot.color:=by
 simp only[UniformLocalCacheChronology.layer,broadcast,inverse,Bool.false_eq_true,ite_false]
 rw[bucket_at D.program slot.enabled H slot.depth depth]
 exact (chosen_eq_color _ _ color).symm

end
end ExactFourierCircuits.UniformActualCalendarForwardCodes
