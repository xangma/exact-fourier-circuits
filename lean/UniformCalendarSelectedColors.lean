import UniformCalendarStableDepth
import UniformChunkMatchingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarSelectedColors
open UniformColoring UniformDAGLayers UniformReplayPrint
open UniformColorLayerTableMachine
noncomputable section

lemma range_values (M : ℕ) : (List.finRange M).map Fin.val=List.range M:=by
 apply List.ext_getElem <;>simp

/-- The literal ordinal filter and the renderer's finite color list retain
exactly the same indexed occurrences in their original order. -/
lemma selection_fins (M k : ℕ) (color : ℕ→ℕ) :
 List.ofFn (selectionIndex M k color)=
  (List.finRange M).filter (fun i=>decide (color i.val=k)):=by
 apply Fin.val_injective.list_map
 calc
  (List.ofFn (selectionIndex M k color)).map Fin.val=selected M k color:=by
   rw[List.map_ofFn]
   exact List.ofFn_getElem
  _=((List.finRange M).map Fin.val).filter (fun i=>decide (color i=k)):=by rw[range_values];rfl
  _=((List.finRange M).filter (fun i=>decide (color i.val=k))).map Fin.val:=List.filter_map

lemma shifted_edges {r : ℕ} (W : List (ShearCode ℕ r)) :
 UniformChunkMatchingPreparation.edges W=printedEdges W:=by
 funext i
 simp only[UniformChunkMatchingPreparation.edges,UniformCrossDepthReplayPreparation.shiftedEdges,
   printedEdges,shearEdge,List.get_eq_getElem,Nat.zero_add]

lemma selected_color {r : ℕ} (W : List (ShearCode ℕ r)) (k : ℕ) :
 List.ofFn (selectionIndex W.length k (UniformChunkMatchingPreparation.colors W))=
 layer (printedEdges W) 6 k:=by
 rw[selection_fins]
 unfold UniformChunkMatchingPreparation.colors
 rw[shifted_edges]
 rfl

def chosen {r : ℕ} (W : List (ShearCode ℕ r)) (k : ℕ) :=
 List.ofFn (fun i:Fin (selected W.length k (UniformChunkMatchingPreparation.colors W)).length=>
  W.get (selectionIndex W.length k (UniformChunkMatchingPreparation.colors W) i))

/-- Every concrete selected typed coefficient and endpoint is the literal
renderer's matching slot, including empty colors. -/
theorem chosen_eq_color {r : ℕ} (W : List (ShearCode ℕ r)) (k : ℕ) (bound : k<11) :
 chosen W k=((colorBlocks W 6)[k]?).getD []:=by
 have mapped:=congrArg (List.map W.get) (selected_color W k)
 rw[List.map_ofFn] at mapped
 rw[show chosen W k=(layer (printedEdges W) 6 k).map W.get from mapped]
 simp only[colorBlocks,layers,List.getElem?_map]
 rw[List.getElem?_eq_getElem (by simpa only[List.length_range] using bound)]
 simp only[Option.map_some,Option.getD_some,List.getElem_range]

end
end ExactFourierCircuits.UniformCalendarSelectedColors
