import DFTModelCacheAmbientPoolCorrect
import UniformForwardMatchingFactorValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheAmbientPool
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheSelectedCoefficients (Row physicalRows physicalRows_lookup)
open UniformColoring UniformMatchingAxisTableMachine
open UniformGlobalMatchingScaleBankBridge (rowEdges rowEdges_matching rowEdges_range)
namespace F
abbrev Config := UniformForwardMatchingFactorPreparation.Config
abbrev Layout := UniformForwardMatchingFactorPreparation.Layout
end F
noncomputable section
attribute [local irreducible] program translate DFTModelCacheMatchingProduced.program

/-- Exact original three-word occurrence rows, in their published order. -/
def localRows {B:ℕ} (c:F.Config) (l:F.Layout c B) (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height) : List UniformInPlaceMachine.Row :=
 UniformChunkMatchingPreparation.mappedRows c.chunk l.chunk.capacity
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative)

private theorem tape_ext (a b:Tape Row.T) (len:a.len=b.len)
 (values:∀j:ℕ,j<a.len→a.look j Row.blank=b.look j Row.blank) : a=b := by
 cases a with
 | mk al ap =>
  cases b with
  | mk bl bp =>
   dsimp only at len
   subst bl
   congr 1
   funext i
   have h:=values i.val i.isLt
   simpa only [Tape.look, dite_eq_left i.isLt] using h

theorem translated_physicalRows (o:ℕ) (rs:List UniformInPlaceMachine.Row) :
 translatedTape o (physicalRows rs)=physicalRows (rs.map (UniformTranslatedMatchingRows.translated o)) := by
 apply tape_ext
 · simp only [translatedTape,physicalRows,Tape.tab,List.length_map]
 · intro j hj
   have h:j<rs.length:=hj
   simp [translatedTape,physicalRows,Tape.look,Tape.tab,h,
    shifted,UniformTranslatedMatchingRows.translated]

theorem physical_rows (rs:List UniformInPlaceMachine.Row)
 (different:UniformGlobalMatchingPoolPreparation.Different rs) :
 DFTModelCacheMatchingNat.Rows (rowEdges rs different) (physicalRows rs) := by
 refine ⟨rfl,?_⟩
 intro i
 change ((physicalRows rs).look i.val Row.blank).1=_ ∧
  ((physicalRows rs).look i.val Row.blank).2.1=_
 rw [physicalRows_lookup rs i]
 exact ⟨rfl,rfl⟩

theorem forward_argument {B:ℕ} (c:F.Config) (l:F.Layout c B) (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (raw:DFTModelCacheSpectrum.Input.T) :
 argumentValue (args c.offset c.ambient c.chunk.height.K c.chunk.height.C c.negative
  c.chunk.height.P raw (physicalRows (localRows c l ha he)))=
 DFTModelCacheMatchingProduced.args c.ambient c.chunk.height.K c.chunk.height.C c.negative
  c.chunk.height.P raw (physicalRows (UniformForwardMatchingFactorPreparation.rows c l ha he)) := by
 unfold argumentValue args DFTModelCacheMatchingProduced.args DFTModelCacheSelectedCoefficients.producedArgs
 rw [translated_physicalRows]
 rfl

/-- Run the genuine original415 from its physical caller contract. The typed
code independently generates the ambient pool; source comparison includes the
prepared flag at every cell. Initial height/coefficient provenance is explicit. -/
theorem forward_execution {n B:ℕ} (c:F.Config) (l:F.Layout c B) (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (seedRadix D:ℕ) (p:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape p seedRadix)
 (width:p.N=UniformRadixTwoDAG.width c.chunk.height.K) (hD:0<D)
 (radixDiv:seedRadix∣D) (fftDiv:UniformRadixTwoDAG.width c.chunk.height.K∣D) (h4:4∣D)
 (radix:2≤c.ambient)
 (positive:c.chunk.height.C+UniformToeplitzCrossDAG.bankSize c.chunk.height.K≤c.negative)
 (negative:c.negative+UniformToeplitzCrossDAG.bankSize c.chunk.height.K≤c.chunk.height.P)
 (x:Fin n→ℂ) (s:UniformMachine.State)
 (headers:UniformForwardMatchingFactorPreparation.Header c s)
 (slot:UniformForwardMatchingFactorPreparation.Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates
   (UniformToeplitzCrossDAG.sharedBank c.chunk.height.K
    (DFTModelCacheSpectrum.rankKernels seedRadix p c.chunk.height.K (OAI.ExactFourier.zeta seedRadix))) s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=0) (wb:UniformMachine.WordBound B s) :
 let raw:=(DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D))
 let input:=args c.offset c.ambient c.chunk.height.K c.chunk.height.C c.negative c.chunk.height.P
  raw (physicalRows (localRows c l ha he))
 ∃u t,UniformMachine.BoundedExecution UniformForwardMatchingFactorPreparation.program n x B s t u ∧
 t≤4*c.chunk.height.K+180*c.chunk.radix+45*c.ambient+
  136*(UniformForwardMatchingFactorPreparation.rows c l ha he).length+148 ∧
 u.pc=414 ∧(run program input).valid ∧(run program input).val.2.2.len=9*c.ambient ∧
 ∀lane:Fin 9,∀d:Fin c.ambient,
  u.scalarHeap (c.pool+lane.val*c.ambient+d.val)=some (UniformPairMachine.prepared
   ((run program input).val.2.2.look (lane.val*c.ambient+d.val) 0)) := by
 dsimp only
 let bank:=UniformToeplitzCrossDAG.sharedBank c.chunk.height.K
  (DFTModelCacheSpectrum.rankKernels seedRadix p c.chunk.height.K (OAI.ExactFourier.zeta seedRadix))
 obtain ⟨u,t,actual,cost,up,result⟩:=UniformForwardMatchingFactorPreparation.execution c l ha he x bank s
  headers slot processed sources constants pc wb
 let rs:=UniformForwardMatchingFactorPreparation.rows c l ha he
 have geometry:=UniformForwardMatchingFactorPreparation.rows_geometry c l ha he
 let labels:=UniformForwardMatchingFactorPreparation.coefficient c l ha he
 have rowLabels:DFTModelCacheSelectedCoefficients.RowSource c.chunk.height.C c.negative c.chunk.height.P
  (physicalRows rs) labels := by
  refine ⟨rfl,?_⟩
  intro i
  rw [physicalRows_lookup rs i]
  exact UniformForwardMatchingFactorPreparation.coefficient_address c l ha he i
 have child:=DFTModelCacheMatchingProduced.mixed_specification c.ambient seedRadix D p shape
  c.chunk.height.K c.chunk.height.C c.negative c.chunk.height.P width hD radixDiv fftDiv h4
  (physicalRows rs) (rowEdges rs geometry.2.1) (physical_rows rs geometry.2.1)
  (rowEdges_matching rs geometry.2.1 geometry.2.2) (rowEdges_range c.ambient rs geometry.2.1 geometry.1)
  radix labels rowLabels positive negative
 rw [program_run,forward_argument]
 refine ⟨u,t,actual,cost,up,⟨translate_valid _ _,child.2.1⟩,child.2.2.2.2.1,?_⟩
 intro lane d
 rw [child.2.2.2.2.2 lane d]
 exact UniformGlobalMatchingScaleBankBridge.pool_coefficients geometry.2.1 geometry.2.2 result.factors lane d

end
end ExactFourierCircuits.DFTModelCacheAmbientPool
