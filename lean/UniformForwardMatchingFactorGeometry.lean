import UniformForwardMatchingFactorPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformInPlaceMachine (Row)
noncomputable section
variable {B:ℕ}
def rows (c:Config) (l:Layout c B)
 (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height):List Row:=
 (UniformChunkMatchingPreparation.mappedRows c.chunk l.chunk.capacity
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative)).map
   (UniformTranslatedMatchingRows.translated c.offset)
lemma rows_length (c:Config) (l:Layout c B) (ha he):
 (rows c l ha he).length=(UniformChunkMatchingPreparation.indices c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)).length:=by
 rw[rows,List.length_map,UniformPackedMatchingShearMachine.mappedRows_length]
def coefficient (c:Config) (l:Layout c B) (ha he):Fin (rows c l ha he).length→
 UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize c.chunk.height.K):=
 fun i=>UniformPackedMatchingShearMachine.selectedLabels c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he) i.val
lemma coefficient_address (c:Config) (l:Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 ((rows c l ha he)[i.val]'i.isLt).coefficient=
 UniformMatchingConjugateLoadMachine.address c.chunk.height.C c.negative c.chunk.height.P (coefficient c l ha he i):=by
 have hi:i.val<(UniformChunkMatchingPreparation.mappedRows c.chunk l.chunk.capacity
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative)).length:=by
  simpa only[rows,List.length_map] using i.isLt
 simp only[rows,List.getElem_map,UniformTranslatedMatchingRows.translated]
 exact UniformPackedMatchingShearMachine.mappedRows_reference c.chunk l.chunk.capacity _ _ _ _ i.val hi

def selectedIndex (c:Config) (l:Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 Fin (UniformChunkMatchingPreparation.indices c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)).length:=
 ⟨i.val,by rw[←rows_length c l ha he];exact i.isLt⟩
def selectedEdge (c:Config) (l:Layout c B) (ha he) (i:Fin (rows c l ha he).length):UniformColoring.Edge:=
 UniformChunkMatchingPreparation.physicalEdges l.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.cross_domain c.chunk ha he) (selectedIndex c l ha he i)
lemma endpoints (c:Config) (l:Layout c B) (ha he) (i:Fin (rows c l ha he).length):
 ((rows c l ha he)[i.val]'i.isLt).dst=c.offset+(selectedEdge c l ha he i).left ∧
 ((rows c l ha he)[i.val]'i.isLt).src=c.offset+(selectedEdge c l ha he i).right:=by
 have hi:i.val<(UniformChunkMatchingPreparation.selectedRows c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative)).length:=by
  simpa only[rows,UniformChunkMatchingPreparation.mappedRows,List.length_map] using i.isLt
 have align:=UniformChunkMatchingPreparation.selected_align c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative) (selectedIndex c l ha he i)
 simp only[rows,UniformChunkMatchingPreparation.mappedRows,List.getElem_map,
  UniformTranslatedMatchingRows.translated,UniformChunkRowTableMachine.mappedRow]
 constructor
 · exact congrArg (fun t=>c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity t) align.1
 · exact congrArg (fun t=>c.offset+UniformChunkMatchingPreparation.coordinate c.chunk l.chunk.capacity t) align.2
lemma rows_geometry (c:Config) (l:Layout c B) (ha he):
 UniformGlobalMatchingPoolPreparation.Bounds c.ambient (rows c l ha he) ∧
 UniformGlobalMatchingPoolPreparation.Different (rows c l ha he) ∧
 UniformGlobalMatchingPoolPreparation.Matching (rows c l ha he):=by
 have range:=UniformChunkMatchingPreparation.physical_range l.chunk
  (UniformChunkMatchingPreparation.cross_domain c.chunk ha he)
 have matching:=UniformChunkMatchingPreparation.physical_matching l.chunk
  (UniformChunkMatchingPreparation.cross_domain c.chunk ha he)
  (UniformChunkMatchingPreparation.cross_degree c.chunk ha he)
 refine ⟨?_,?_,?_⟩
 · intro i;rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2]
   have h:=range (selectedIndex c l ha he i);have extent:=l.extent
   change (selectedEdge c l ha he i).left<c.chunk.radix ∧(selectedEdge c l ha he i).right<c.chunk.radix at h
   constructor <;>omega
 · intro i;rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2]
   exact fun h=>(selectedEdge c l ha he i).different (Nat.add_left_cancel h)
 · intro i j ne
   rw[(endpoints c l ha he i).1,(endpoints c l ha he i).2,
      (endpoints c l ha he j).1,(endpoints c l ha he j).2]
   have ij:selectedIndex c l ha he i≠selectedIndex c l ha he j:=by
    intro h;apply ne;apply Fin.ext
    exact congrArg (fun k:Fin (UniformChunkMatchingPreparation.indices c.chunk
      (UniformChunkMatchingPreparation.crossWord c.chunk ha he)).length=>k.val) h
   have no:=matching _ _ ij
   exact ⟨fun h=>no (Or.inl (Or.inl (Nat.add_left_cancel h).symm)),
    fun h=>no (Or.inl (Or.inr (Nat.add_left_cancel h).symm)),
    fun h=>no (Or.inr (Or.inl (Nat.add_left_cancel h).symm)),
    fun h=>no (Or.inr (Or.inr (Nat.add_left_cancel h).symm))⟩
lemma coefficient_value (c:Config) (l:Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K)→ℂ) (i:Fin (rows c l ha he).length):
 UniformMatchingConjugateLoadMachine.value c.chunk.height.K bank (coefficient c l ha he i)=
 (UniformMatchingCoefficientValueBridge.selectedReference c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he) (selectedIndex c l ha he i)).eval bank:=
 UniformMatchingCoefficientValueBridge.cross_selected_value c.chunk ha he bank (selectedIndex c l ha he i)
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
