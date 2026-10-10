import DFTModelCacheSelectedPhysicalRowsCaller
import UniformSeedChunkPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- The genuine SeedChunk caller uses precisely the raw producer's exponent. -/
theorem seed_chunk_exponent (n:ℕ) (j:Fin (UniformAllAxisSeedPreparation.axisCount n))
 (c:UniformSeedChunkPreparation.Config) :
 (c.chunk n j).height.K=DFTModelCacheTopology.exponent c.seed.a c.seed.e := rfl

/-- The native186 caller installs A=0 in its actual per-height132 header.
This is the data-base field of header_spec, not an inferred row relabeling. -/
theorem native_height_zero (p:UniformCrossHeightPreparationMachine.Parameters)
 (d:ℕ) (s:UniformMachine.State) (cursor:UniformCrossHeightPreparationMachine.Cursor p d s) :
 (UniformTensorMonomialMachine.applyBlock UniformCrossHeightPreparationMachine.headerOps s).natReg 906=0 :=
 (UniformCrossHeightPreparationMachine.header_spec p d s cursor).dataBase

def nativeInput (p:UniformChunkMatchingPreparation.Parameters) (C T P:ℕ)
 (raw:DFTModelCacheSpectrum.Input.T) : Input.T :=
 (((p.height.K,(C,(T,P))),raw),
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p,
   DFTModelCacheHeightColorCaller.input p.color p.height.a p.height.e 0 C P p.depth p.height.enabled))

attribute [local irreducible] Code.run program DFTModelCacheHeightColorCaller.program
 DFTModelCacheSelectedPhysicalRowsProduced.program

/-- Any negative-bank placement is valid for the forward generated rows:
the original raw height theorem proves their independence from that location. -/
theorem generated_rows (a e C T P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) :
 DFTModelCacheHeightColorCaller.producedRows a e 0 C P d enabled=
 DFTModelCacheHeight.rowTape
  ((DFTModelCacheHeightColorCaller.bucket a e d enabled).map
   (UniformCrossShearTableMachine.shiftedRow 0
    (UniformCrossShearTableMachine.locations
     (UniformToeplitzCrossDAG.bankSize (DFTModelCacheTopology.exponent a e)) C T P))) :=
 DFTModelCacheHeightRaw.program_value a e 0 C T P d enabled height

theorem selected_native (p:UniformChunkMatchingPreparation.Parameters)
 (computed:p.height.K=DFTModelCacheTopology.exponent p.height.a p.height.e)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (height:p.depth≤8*p.height.K+6) (C T P:ℕ) :
 (run DFTModelCacheHeightColorCaller.program
  (DFTModelCacheHeightColorCaller.input p.color p.height.a p.height.e 0 C P p.depth p.height.enabled)).val.2.2=
 DFTModelCacheSelectedPhysicalRows.rowTape
  (UniformChunkMatchingPreparation.selectedRows p (UniformChunkMatchingPreparation.crossWord p ha he)
   (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize p.height.K) C T P)) := by
 have hd:p.depth≤8*DFTModelCacheTopology.exponent p.height.a p.height.e+6:=by simpa only [computed] using height
 rw [DFTModelCacheHeightColorCaller.selected_value _ _ _ _ _ _ _ _ hd]
 have normalize (K:ℕ) (eqn:K=DFTModelCacheTopology.exponent p.height.a p.height.e)
  (a:p.height.a≤UniformRadixTwoDAG.width K) (e:p.height.e≤UniformRadixTwoDAG.width K) :
  DFTModelCacheSelectedPhysicalRows.rowTape
   (UniformChunkMatchingPreparation.selectedRows p
    (UniformCrossDepthReplayPreparation.bucket
     (UniformToeplitzCrossDAG.crossDAG K p.height.a p.height.e a e).program p.height.enabled p.depth)
    (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize K) C T P))=
  DFTModelCacheSelectedPhysicalRows.rowTape
   (UniformChunkMatchingPreparation.selectedRows p
    (DFTModelCacheHeightColorCaller.bucket p.height.a p.height.e p.depth p.height.enabled)
    (UniformCrossShearTableMachine.locations
     (UniformToeplitzCrossDAG.bankSize (DFTModelCacheTopology.exponent p.height.a p.height.e)) C T P)) := by
  subst K
  rfl
 unfold UniformChunkMatchingPreparation.crossWord
 rw [normalize p.height.K computed ha he]
 change Tape.tab _ _=DFTModelCacheSelectedPhysicalRows.rowTape
  (UniformChunkMatchingPreparation.selectedRows p
   (DFTModelCacheHeightColorCaller.bucket p.height.a p.height.e p.depth p.height.enabled) _)
 let W:=DFTModelCacheHeightColorCaller.bucket p.height.a p.height.e p.depth p.height.enabled
 let loc:=UniformCrossShearTableMachine.locations
  (UniformToeplitzCrossDAG.bankSize (DFTModelCacheTopology.exponent p.height.a p.height.e)) C T P
 have rows:=generated_rows p.height.a p.height.e C T P p.depth p.height.enabled hd
 have lookup (j:ℕ) (hj:j<W.length) :
  (DFTModelCacheHeightColorCaller.producedRows p.height.a p.height.e 0 C P p.depth p.height.enabled).look
   j DFTModelCacheColor.Row.blank=
  DFTModelCacheSelectedPhysicalRows.encode (UniformChunkMatchingPreparation.rowFunction W loc j) := by
  rw [rows]
  unfold DFTModelCacheHeight.rowTape
  rw [Tape.look_of_lt _ _ (by simpa only [Tape.tab,List.length_map] using hj)]
  dsimp only [Tape.tab]
  change ((W.map (UniformCrossShearTableMachine.shiftedRow 0 loc)).map DFTModelCacheHeight.row3)[j]?.getD
   DFTModelCacheHeight.Row.blank=DFTModelCacheSelectedPhysicalRows.encode
    (UniformChunkMatchingPreparation.rowFunction W loc j)
  simp only [List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some,
   UniformChunkMatchingPreparation.rowFunction,dite_eq_left hj]
  rfl
 have edgeEq:UniformColoring.printedEdges W=UniformCrossDepthReplayPreparation.shiftedEdges 0 W := by
  funext i
  simp only [UniformColoring.printedEdges,UniformColoring.shearEdge,
   UniformCrossDepthReplayPreparation.shiftedEdges,Nat.zero_add]
 have selected:
  UniformColorLayerTableMachine.selected W.length p.color
   (UniformColoring.greedy (DFTModelCacheHeightColorCaller.edges p.height.a p.height.e p.depth p.height.enabled) 11 W.length)=
  UniformChunkMatchingPreparation.indices p W := by
  change UniformColorLayerTableMachine.selected W.length p.color
   (UniformColoring.greedy (UniformColoring.printedEdges W) 11 W.length)=
   UniformColorLayerTableMachine.selected W.length p.color
    (UniformColoring.greedy (UniformCrossDepthReplayPreparation.shiftedEdges 0 W) 11 W.length)
  rw [edgeEq]
 change Tape.tab _ _=DFTModelCacheSelectedPhysicalRows.rowTape
  ((UniformChunkMatchingPreparation.indices p W).map (UniformChunkMatchingPreparation.rowFunction W loc))
 rw [selected]
 have maps:
  (UniformChunkMatchingPreparation.indices p W).map (fun j=>
   (DFTModelCacheHeightColorCaller.producedRows p.height.a p.height.e 0 C P p.depth p.height.enabled).look j DFTModelCacheColor.Row.blank)=
  ((UniformChunkMatchingPreparation.indices p W).map (UniformChunkMatchingPreparation.rowFunction W loc)).map
   DFTModelCacheSelectedPhysicalRows.encode := by
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  exact lookup j (List.mem_range.mp (List.mem_filter.mp hj).1)
 rw [maps]
 unfold DFTModelCacheSelectedPhysicalRows.rowTape DFTModelCacheSelectedCoefficients.physicalRows
 simp only [List.length_map]
 congr 1
 funext j
 simp only [List.getElem?_map]
 cases (UniformChunkMatchingPreparation.indices p W)[j]? <;> rfl

theorem native_argument (p:UniformChunkMatchingPreparation.Parameters)
 (computed:p.height.K=DFTModelCacheTopology.exponent p.height.a p.height.e)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (height:p.depth≤8*p.height.K+6) (C T P:ℕ) (raw:DFTModelCacheSpectrum.Input.T) :
 argumentValue (nativeInput p C T P raw)
  (run DFTModelCacheHeightColorCaller.program (nativeInput p C T P raw).2.2).val=
 DFTModelCacheSelectedPhysicalRowsProduced.nativeInput p
  (UniformChunkMatchingPreparation.crossWord p ha he) C T P raw := by
 dsimp only [argumentValue,nativeInput,DFTModelCacheSelectedPhysicalRowsProduced.nativeInput]
 rw [selected_native p computed ha he height C T P]

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
