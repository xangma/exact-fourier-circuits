import UniformMatchingActionBridge
import UniformDAGLayers

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalReplayBridge
open UniformMachine UniformReplayPrint OAI.ExactFourier
noncomputable section

abbrev Port (p : UniformChunkMatchingPreparation.Parameters) :=
 {z : ℕ // UniformChunkPortMachine.Domain p.height.e
  (UniformCrossHeightPreparationMachine.gates p.height) p.height.a z}

def portEmbedding {p : UniformChunkMatchingPreparation.Parameters} {B : ℕ}
 (l : UniformChunkMatchingPreparation.Layout p B) : Port p ↪ ℕ where
 toFun := fun z => UniformChunkMatchingPreparation.coordinate p l.capacity z.val
 inj' := by
  intro z w same
  apply Subtype.ext
  exact UniformChunkPortMachine.mapped_injective p.radix p.source p.height.e p.target p.height.a
   (UniformCrossHeightPreparationMachine.gates p.height) l.sourceRange l.targetRange l.separated l.capacity
   z.property w.property same

def naturalEmbedding (p : UniformChunkMatchingPreparation.Parameters) : Port p ↪ ℕ :=
 ⟨Subtype.val,Subtype.val_injective⟩

/-- Actual selected occurrences, with their logical port-domain proofs. -/
def logicalWord {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 List (ShearCode (Port p) R) :=
 List.ofFn (fun i : Fin (UniformChunkMatchingPreparation.indices p W).length =>
  let edge:=UniformChunkMatchingPreparation.selectedEdges p W i
  let domain:=UniformChunkMatchingPreparation.selected_edge_domain dom i
  let index:=UniformColorLayerTableMachine.selectionIndex W.length p.color
    (UniformChunkMatchingPreparation.colors W) i
  ⟨⟨edge.left,domain.1⟩,⟨edge.right,domain.2⟩,fun h => edge.different (congrArg Subtype.val h),
   W[index.val].coefficient⟩)

def selectedWord {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) : List (ShearCode ℕ R) :=
 List.ofFn (fun i : Fin (UniformChunkMatchingPreparation.indices p W).length =>
  W[(UniformColorLayerTableMachine.selectionIndex W.length p.color
    (UniformChunkMatchingPreparation.colors W) i).val])

theorem physicalWord_relabel {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 UniformSixCDirtyReplayMachine.physicalWord l W dom =
 (logicalWord p W dom).map (UniformDAGLayers.relabelCode (portEmbedding l)) := by
 simp only [UniformSixCDirtyReplayMachine.physicalWord,logicalWord,List.map_ofFn]
 rfl

theorem selectedWord_relabel {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (dom : UniformChunkMatchingPreparation.CodesDomain p W) :
 selectedWord p W = (logicalWord p W dom).map (UniformDAGLayers.relabelCode (naturalEmbedding p)) := by
 simp only [selectedWord,logicalWord,List.map_ofFn]
 apply congrArg List.ofFn
 funext i
 simp [UniformDAGLayers.relabelCode,naturalEmbedding,UniformChunkMatchingPreparation.selectedEdges,
  UniformColorLayerTableMachine.selectedEdges,UniformChunkMatchingPreparation.edges,
  UniformCrossDepthReplayPreparation.shiftedEdges]


theorem edges_printed {R : ℕ} (W : List (ShearCode ℕ R)) :
 UniformChunkMatchingPreparation.edges W = UniformColoring.printedEdges W := by
 funext i
 simp [UniformChunkMatchingPreparation.edges,UniformCrossDepthReplayPreparation.shiftedEdges,
  UniformColoring.printedEdges,UniformColoring.shearEdge]

theorem layer_values {M : ℕ} (E : Fin M→UniformColoring.Edge) (c : ℕ) :
 (UniformColoring.layer E 6 c).map Fin.val =
 UniformColorLayerTableMachine.selected M c (UniformColoring.greedy E 11 M) := by
 change ((List.finRange M).filter (fun i => decide (UniformColoring.greedy E 11 M i.val=c))).map Fin.val = _
 have range : (List.finRange M).map Fin.val = List.range M := by
  apply List.ext_getElem <;> simp
 change ((List.finRange M).filter ((fun j => decide (UniformColoring.greedy E 11 M j=c)) ∘ Fin.val)).map Fin.val = _
 rw [←List.filter_map,range]
 rfl

theorem selected_indices {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) :
 List.ofFn (fun i : Fin (UniformChunkMatchingPreparation.indices p W).length =>
   UniformColorLayerTableMachine.selectionIndex W.length p.color
    (UniformChunkMatchingPreparation.colors W) i) =
 UniformColoring.layer (UniformColoring.printedEdges W) 6 p.color := by
 apply (List.map_injective_iff.mpr Fin.val_injective)
 rw [layer_values]
 rw [List.map_ofFn]
 change List.ofFn (fun i : Fin (UniformColorLayerTableMachine.selected W.length p.color
   (UniformChunkMatchingPreparation.colors W)).length =>
   (UniformColorLayerTableMachine.selected W.length p.color (UniformChunkMatchingPreparation.colors W))[i.val]) = _
 rw [List.ofFn_getElem]
 simp only [UniformChunkMatchingPreparation.colors,edges_printed]

theorem selectedWord_layer {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) :
 selectedWord p W =
 (UniformColoring.layer (UniformColoring.printedEdges W) 6 p.color).map W.get := by
 rw [←selected_indices]
 simp only [selectedWord,List.map_ofFn]
 apply congrArg List.ofFn
 funext i
 rfl


theorem colorBlocks_ofFn {R : ℕ} (W : List (ShearCode ℕ R)) :
 UniformDAGLayers.colorBlocks W 6 =
 List.ofFn (fun c : Fin 11 =>
  (UniformColoring.layer (UniformColoring.printedEdges W) 6 c.val).map W.get) := by
 simp only [UniformDAGLayers.colorBlocks,UniformColoring.layers,List.map_map]
 exact (UniformCrossDepthReplayPreparation.ofFn_nat 11 _).symm

theorem selectedWord_colorBlock {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (hc : p.color<11) :
 selectedWord p W = (UniformDAGLayers.colorBlocks W 6)[p.color]'(by
  rw [UniformDAGLayers.colorBlocks_length];exact hc) := by
 simp only [colorBlocks_ofFn,List.getElem_ofFn]
 exact selectedWord_layer p W

/-- Literal depth/color order used by the actual div/mod-by-eleven cursor. -/
def sweepWords {R n t : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (prog : UniformReplayPrint.Program R n t) (enabled : Bool) (H : ℕ) :
 List (List (ShearCode ℕ R)) :=
 List.ofFn (fun i : Fin ((H+1)*11) =>
  selectedWord {p with depth:=i.val/11,color:=i.val%11}
   (UniformCrossDepthReplayPreparation.bucket prog enabled (i.val/11)))

theorem sweepWords_eq {R n t : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (prog : UniformReplayPrint.Program R n t) (enabled : Bool) (H : ℕ) :
 sweepWords p prog enabled H =
 UniformCrossDepthReplayPreparation.activeLayers prog enabled H := by
 unfold sweepWords
 rw [List.ofFn_mul]
 simp only [UniformCrossDepthReplayPreparation.activeLayers,
   UniformDAGLayers.coloredBuckets,UniformCrossDepthReplayPreparation.activeBuckets,
   List.flatMap_def,List.map_ofFn]
 apply congrArg List.flatten
 apply congrArg List.ofFn
 funext i
 dsimp only [Function.comp_apply]
 rw [colorBlocks_ofFn]
 apply congrArg List.ofFn
 funext j
 have mod : (i.val*11+j.val)%11=j.val := by omega
 have div : (i.val*11+j.val)/11=i.val := by omega
 simp only [mod,div]
 exact selectedWord_layer _ _


theorem reverseLayers_ofFn {R M : ℕ} (F : Fin M→List (ShearCode ℕ R)) :
 UniformDAGLayers.reverseLayers (List.ofFn F) =
 List.ofFn (fun i => reverseCode (F i.rev)) := by
 apply List.ext_getElem
 · simp [UniformDAGLayers.reverseLayers]
 · intro i hi hj
   simp only [UniformDAGLayers.reverseLayers,List.getElem_map,List.getElem_reverse,
    List.length_ofFn,List.getElem_ofFn,Fin.rev]
   apply congrArg reverseCode
   apply congrArg F
   apply Fin.ext
   change M-1-i=M-(i+1)
   omega

/-- The inverse cursor visits the same layers in descending ordinal order,
and executes the literal inverse word inside each layer. -/
def inverseSweepWords {R n t : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (prog : UniformReplayPrint.Program R n t) (enabled : Bool) (H : ℕ) :
 List (List (ShearCode ℕ R)) :=
 List.ofFn (fun i : Fin ((H+1)*11) =>
  reverseCode (selectedWord {p with depth:=i.rev.val/11,color:=i.rev.val%11}
   (UniformCrossDepthReplayPreparation.bucket prog enabled (i.rev.val/11))))

theorem inverseSweepWords_eq {R n t : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (prog : UniformReplayPrint.Program R n t) (enabled : Bool) (H : ℕ) :
 inverseSweepWords p prog enabled H =
 UniformDAGLayers.reverseLayers (UniformCrossDepthReplayPreparation.activeLayers prog enabled H) := by
 rw [←sweepWords_eq p prog enabled H]
 unfold inverseSweepWords sweepWords
 exact (reverseLayers_ofFn (fun i : Fin ((H+1)*11) =>
   selectedWord {p with depth:=i.val/11,color:=i.val%11}
    (UniformCrossDepthReplayPreparation.bucket prog enabled (i.val/11)))).symm

theorem reverse_ordinal {M : ℕ} (i : Fin M) : i.rev.val=M-1-i.val := by
 simp [Fin.rev]
 omega

/-- A canonical equivalent schedule; the actual broadcast caller must still
be shown to have these colored broadcast actions. -/
def replayWords {R n a : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (D : UniformToeplitzCrossDAG.DAG R n a) (H : ℕ) : List (List (ShearCode ℕ R)) :=
 sweepWords p D.program true H ++ UniformDAGLayers.colorBlocks (UniformDAGLayers.natBroadcast D true) 6 ++
 inverseSweepWords p D.program true H ++ sweepWords p D.program false H ++
 UniformDAGLayers.reverseLayers (UniformDAGLayers.colorBlocks (UniformDAGLayers.natBroadcast D false) 6) ++
 inverseSweepWords p D.program false H

theorem replayWords_eq {R n a : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (D : UniformToeplitzCrossDAG.DAG R n a) (H : ℕ) :
 replayWords p D H = UniformCrossDepthReplayPreparation.activeReplay D H := by
 simp only [replayWords,UniformCrossDepthReplayPreparation.activeReplay,sweepWords_eq,
  inverseSweepWords_eq]


/-- The actual broadcast helper executes its inverse rows in reverse order.
The positive phase therefore has the forward broadcast coefficients in
reverse order; the negative phase is its literal inverse word. -/
def literalReplayWords {R n a : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (D : UniformToeplitzCrossDAG.DAG R n a) (H : ℕ) : List (List (ShearCode ℕ R)) :=
 sweepWords p D.program true H ++ [(UniformDAGLayers.natBroadcast D true).reverse] ++
 inverseSweepWords p D.program true H ++ sweepWords p D.program false H ++
 [reverseCode (UniformDAGLayers.natBroadcast D false)] ++ inverseSweepWords p D.program false H

theorem literalReplayWords_action {R n a H : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (D : UniformToeplitzCrossDAG.DAG R n a) (bank : Fin R→ℂ)
 (depth : UniformToeplitzCrossDAG.DepthBound D H)
 (uses : ∀v,UniformToeplitzCrossDAG.physicalUseCount D v≤6) (v : ℕ→ℂ) :
 runShears ((literalReplayWords p D H).flatten.map (ShearCode.eval bank)) v =
 runShears ((UniformDAGLayers.natReplayCode D).map (ShearCode.eval bank)) v := by
 have hs (enabled : Bool) := UniformCrossDepthReplayPreparation.activeLayers_action D bank enabled depth uses
 have hrs (enabled : Bool) := UniformDAGLayers.reverseCode_action_congr bank
  (UniformCrossDepthReplayPreparation.activeLayers D.program enabled H).flatten
  (UniformDAGLayers.natSweep D.program enabled) (hs enabled)
 have hb (u : ℕ→ℂ) := UniformLayeredReplay.run_perm bank
  (List.reverse_perm (UniformDAGLayers.natBroadcast D true))
  (UniformLayeredReplay.safe_perm (List.reverse_perm _).symm
   ((UniformDAGLayers.natBroadcast_onLevel D true).safe)) u
 rw [UniformDAGLayers.natReplayCode_phases]
 simp only [literalReplayWords,sweepWords_eq,inverseSweepWords_eq,List.flatten_append,
  List.flatten_cons,List.flatten_nil,List.append_nil,UniformDAGLayers.reverseLayers_flatten,
  List.map_append,runShears_append]
 rw [hs true,hb,hrs true,hs false,hrs false]


/-- The driver's explicit logical ordering has the corrected cross matrix
and restores every dirty source/gate value. Operational driver integration
is a separate obligation. -/
theorem literalCross_matrix (p : UniformChunkMatchingPreparation.Parameters)
 (K a e : ℕ) (ha : 0<a) (he : 0<e)
 (size : 2*(a+e)≤UniformRadixTwoDAG.width K) (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (recurrence : ∀i j,i+1<a→j+1<e→M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) (X : ℕ→ℂ) :
 runShears ((literalReplayWords p (UniformToeplitzCrossDAG.crossDAG K a e (by omega) (by omega))
  (8*K+6)).flatten.map (ShearCode.eval
   (UniformToeplitzCrossDAG.sharedBank K (UniformToeplitzCrossDAG.rankKernels K a e M v w)))) X ∘
 UniformDAGLayers.replayEmbedding e
   (UniformToeplitzCrossDAG.crossDAG K a e (by omega) (by omega)).size a =
 Sum.elim (Sum.elim (fun i : Fin e=>X i.val)
   (fun j : Fin (UniformToeplitzCrossDAG.crossDAG K a e (by omega) (by omega)).size=>X (e+1+j.val)))
   (fun j : Fin a=>X (e+1+(UniformToeplitzCrossDAG.crossDAG K a e (by omega) (by omega)).size+j.val)+
     Matrix.mulVec (fun i : Fin a=>fun j : Fin e=>M i.val j.val) (fun i=>X i.val) j) := by
 have ha' : a≤UniformRadixTwoDAG.width K := by omega
 have he' : e≤UniformRadixTwoDAG.width K := by omega
 have depth:=UniformToeplitzCrossDAG.crossDAG_depth K a e ha' he'
 have uses:=UniformToeplitzCrossDAG.crossDAG_physicalFanout K a e ha' he'
 rw [literalReplayWords_action _ _ _ depth uses]
 have result:=UniformDAGLayers.cross_replayLayers_matrix K a e ha he size M v w recurrence X
 rw [UniformDAGLayers.replayLayers_action _ _ depth (by omega) uses] at result
 exact result

/-- Pull back the physical matching action through its actual injective port
map. This is an action conclusion, never an operational entry assumption. -/
theorem physicalWord_action {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) (bank : Fin R→ℂ) (v : ℕ→ℂ) :
 runShears ((UniformSixCDirtyReplayMachine.physicalWord l W dom).map (ShearCode.eval bank)) v ∘
  portEmbedding l =
 runShears ((selectedWord p W).map (ShearCode.eval bank))
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.capacity) ∘ naturalEmbedding p := by
 rw [physicalWord_relabel,selectedWord_relabel]
 rw [UniformDAGLayers.relabel_run,UniformDAGLayers.relabel_run]
 rfl

theorem physicalWord_inverse_action {R B : ℕ} {p : UniformChunkMatchingPreparation.Parameters}
 (l : UniformChunkMatchingPreparation.Layout p B) (W : List (ShearCode ℕ R))
 (dom : UniformChunkMatchingPreparation.CodesDomain p W) (bank : Fin R→ℂ) (v : ℕ→ℂ) :
 runShears ((reverseCode (UniformSixCDirtyReplayMachine.physicalWord l W dom)).map (ShearCode.eval bank)) v ∘
  portEmbedding l =
 runShears ((reverseCode (selectedWord p W)).map (ShearCode.eval bank))
  (v ∘ UniformChunkMatchingPreparation.coordinate p l.capacity) ∘ naturalEmbedding p := by
 rw [physicalWord_relabel,selectedWord_relabel,←UniformDAGLayers.relabel_reverseCode,
   ←UniformDAGLayers.relabel_reverseCode]
 rw [UniformDAGLayers.relabel_run,UniformDAGLayers.relabel_run]
 rfl

end
end ExactFourierCircuits.UniformPhysicalReplayBridge
