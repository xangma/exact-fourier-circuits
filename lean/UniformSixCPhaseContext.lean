import UniformSixCTraversal
import UniformSixCBroadcast
import UniformMatchingActionBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCPhaseContext
open UniformMachine UniformReplayPrint UniformAssembly OAI.ExactFourier
open UniformTensorMonomialMachine (setPC)
open UniformSixCTraversal

def layerParameters (p:UniformChunkMatchingPreparation.Parameters) (backwards:Bool) (i:ℕ) :=
 {p with
  depth := layerDepth backwards ((8*p.height.K+7)*11) i
  color := layerColor backwards ((8*p.height.K+7)*11) i}
noncomputable section
lemma atLayout {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformChunkMatchingPreparation.Layout p B) (backwards:Bool) (i:ℕ)
 (hi:i<(8*p.height.K+7)*11) : UniformChunkMatchingPreparation.Layout (layerParameters p backwards i) B:=by
 constructor
 all_goals first
 | exact l.code | exact l.radixPositive | exact l.sourceRange | exact l.targetRange
 | exact l.separated | exact l.capacity | exact l.oldRows | exact l.oldColors | exact l.oldDirectory
 | exact l.borrowFresh | exact l.selectedFresh | exact l.ordinalFresh | exact l.mappedFresh
 | exact l.permutationFresh | exact l.widthsFresh | exact l.markersFresh | exact l.finalBound
 | exact depth_bound backwards (8*p.height.K+7) i hi
 | exact color_bound backwards ((8*p.height.K+7)*11) i

def atPacking {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool) (i:ℕ)
 (hi:i<(8*p.height.K+7)*11) : UniformMatchingPackingPreparation.Layout (layerParameters p backwards i) B:=
 ⟨atLayout l.matching backwards i hi,l.packing,l.bound,l.oneAxis,l.axisRow,l.volume,l.code⟩

/-- Unchanged caller geometry and high allocation fields. Depth/color are
explicitly excluded because the actual division/remainder instructions set them. -/
def StaticEq (s u:State) : Prop := ∀q,
 ((UniformSixCDepthColorController.readonly q=true ∧ q≠1191 ∧ q≠1192) ∨ (3001≤q ∧ q≤3020)) →
 u.natReg q=s.natReg q
lemma StaticEq.refl (s:State) : StaticEq s s:=fun _ _=>rfl
lemma StaticEq.trans {s u v:State} (h:StaticEq s u) (h':StaticEq u v) : StaticEq s v:=
 fun q hq=>(h' q hq).trans (h q hq)
lemma StaticEq.withPC {s u:State} (h:StaticEq s u) (pc:ℕ) : StaticEq s (setPC u pc):=h
lemma StaticEq.of_frames {s u:State}
 (low:∀q,UniformSixCDepthColorController.readonly q=true→u.natReg q=s.natReg q)
 (high:∀q,3001≤q→u.natReg q=s.natReg q) : StaticEq s u:=by
 intro q h;rcases h with h|h
 · exact low q h.1
 · exact high q h.1
lemma decoded_static (backwards:Bool) (s:State) : StaticEq s (decoded backwards s):=by
 intro q h
 have range:=h
 simp only [UniformSixCDepthColorController.readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
 have ne:q≠1191 ∧ q≠1192:=by omega
 cases h with
 | inl h=>exact decoded_readonly backwards s q h.1 ne.1 ne.2
 | inr h=>exact decoded_high backwards s q h.1 (by omega)
lemma tick_static (backwards:Bool) (s:State) : StaticEq s (tickState backwards s):=by
 intro q h
 have range:=h
 simp only [UniformSixCDepthColorController.readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
 exact tick_high backwards s q (by omega)
lemma boot_static (s:State) : StaticEq s (UniformTensorMonomialMachine.applyBlock UniformSixCDepthColorController.traversalBoot s):=by
 intro q h
 rcases h with h|h
 · exact traversal_boot_readonly s q h.1
 · exact traversal_boot_high s q h.1 h.2
/-- Ordinary persistent headers, excluding the two internally computed cursors. -/
structure MatchingBaseHeader (p:UniformChunkMatchingPreparation.Parameters) (s:State) : Prop where
 height : UniformCrossHeightPreparationMachine.Header p.height s
 radix : s.natReg 1180=p.radix
 source : s.natReg 1181=p.source
 target : s.natReg 1182=p.target
 borrowed : s.natReg 1183=p.borrowed
 selected : s.natReg 1184=p.selected
 ordinals : s.natReg 1185=p.ordinals
 mapped : s.natReg 1186=p.mapped
 permutation : s.natReg 1187=p.permutation
 widths : s.natReg 1188=p.widths
 markers : s.natReg 1189=p.markers
 axis : s.natReg 1190=p.axis
structure BaseHeader {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (s:State) : Prop where
 matching : MatchingBaseHeader p s
 suffix : s.natReg 1400=l.packing.suffix
 stack : s.natReg 1401=l.packing.stack
 inverse : s.natReg 1402=l.packing.inverse
 source : s.natReg 1403=l.packing.source
 destination : s.natReg 1404=l.packing.destination
lemma BaseHeader.of_header {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {s:State}
 (h:UniformMatchingPackingPreparation.Header l s) : BaseHeader l s:=
 ⟨⟨h.matching.height,h.matching.radix,h.matching.source,h.matching.target,h.matching.borrowed,h.matching.selected,h.matching.ordinals,h.matching.mapped,h.matching.permutation,h.matching.widths,h.matching.markers,h.matching.axis⟩,
  h.suffix,h.stack,h.inverse,h.source,h.destination⟩
lemma BaseHeader.transport {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {s u:State}
 (h:BaseHeader l s) (same:StaticEq s u) : BaseHeader l u:=by
 have low:∀q,UniformSixCDepthColorController.readonly q=true→q≠1191→q≠1192→u.natReg q=s.natReg q:=
  fun q read nd nc=>same q (Or.inl ⟨read,nd,nc⟩)
 refine ⟨⟨h.matching.height.transport_register (by intro q lo hi;exact low q (by simp [UniformSixCDepthColorController.readonly];omega) (by omega) (by omega)),
  (low 1180 (by decide) (by decide) (by decide)).trans h.matching.radix,
  (low 1181 (by decide) (by decide) (by decide)).trans h.matching.source,
  (low 1182 (by decide) (by decide) (by decide)).trans h.matching.target,
  (low 1183 (by decide) (by decide) (by decide)).trans h.matching.borrowed,
  (low 1184 (by decide) (by decide) (by decide)).trans h.matching.selected,
  (low 1185 (by decide) (by decide) (by decide)).trans h.matching.ordinals,
  (low 1186 (by decide) (by decide) (by decide)).trans h.matching.mapped,
  (low 1187 (by decide) (by decide) (by decide)).trans h.matching.permutation,
  (low 1188 (by decide) (by decide) (by decide)).trans h.matching.widths,
  (low 1189 (by decide) (by decide) (by decide)).trans h.matching.markers,
  (low 1190 (by decide) (by decide) (by decide)).trans h.matching.axis⟩,
  (low 1400 (by decide) (by decide) (by decide)).trans h.suffix,
  (low 1401 (by decide) (by decide) (by decide)).trans h.stack,
  (low 1402 (by decide) (by decide) (by decide)).trans h.inverse,
  (low 1403 (by decide) (by decide) (by decide)).trans h.source,
  (low 1404 (by decide) (by decide) (by decide)).trans h.destination⟩
lemma atHeader {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool) (i:ℕ)
 (hi:i<(8*p.height.K+7)*11) {s u:State}
 (h:BaseHeader l s) (same:StaticEq s u)
 (depth:u.natReg 1191=(layerParameters p backwards i).depth)
 (color:u.natReg 1192=(layerParameters p backwards i).color) :
 UniformMatchingPackingPreparation.Header (atPacking l backwards i hi) u:=by
 have low:∀q,UniformSixCDepthColorController.readonly q=true→q≠1191→q≠1192→u.natReg q=s.natReg q:=
  fun q hr hd hc=>same q (Or.inl ⟨hr,hd,hc⟩)
 refine ⟨⟨h.matching.height.transport_register (by
  intro q lo hi;exact low q (by simp [UniformSixCDepthColorController.readonly];omega) (by omega) (by omega)),
  ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,depth,color⟩,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.radix
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.source
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.target
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.borrowed
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.selected
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.ordinals
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.mapped
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.permutation
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.widths
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.markers
 | exact (low _ (by decide) (by decide) (by decide)).trans h.matching.axis
 | exact (low _ (by decide) (by decide) (by decide)).trans h.suffix
 | exact (low _ (by decide) (by decide) (by decide)).trans h.stack
 | exact (low _ (by decide) (by decide) (by decide)).trans h.inverse
 | exact (low _ (by decide) (by decide) (by decide)).trans h.source
 | exact (low _ (by decide) (by decide) (by decide)).trans h.destination

/-- Physical source presence is retained through the phase. Data tags may grow;
this contract makes no numeric action assertion and no free heap assignment. -/
def Present (base L:ℕ) (s:State) : Prop := ∀j,j<L→∃v,s.scalarHeap (base+j)=some v
def data (base L:ℕ) (s:State) (j:Fin L) : Scalar := (s.scalarHeap (base+j.val)).getD Scalar.zero
lemma data_ready {base L:ℕ} {s:State} (h:Present base L s) (j:Fin L) :
 s.scalarHeap (base+j.val)=some (data base L s j):=by
 obtain ⟨v,hv⟩:=h j.val j.isLt
 simp [data,hv]
def numeric (base L:ℕ) (s:State) : ℕ→ℂ:=fun j=>if h:j<L then (data base L s ⟨j,h⟩).value else 0
lemma present_ready (L:UniformSectorPackingMachine.Layout) (s:State) (h:Present L.source L.total s) :
 UniformSectorPackingMachine.SourceReady L (data L.source L.total s) s:=data_ready h

/-- Zero-count layouts record only ordinary bank separation and word bounds.
The actual matching capacity is proved from the generated edges, below. -/
structure Allocation {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config) (R:ℕ) : Prop where
 rows : c.inverse.forward=p.mapped
 volume : c.inverse.packing.total=p.radix
 source : c.inverse.packing.source=l.packing.source
 sameForward : c.forward=UniformSixCDepthColorController.config l c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates c.inverse.mu c.inverse.conjugateMu
 forwardZero : UniformPackedMatchingShearMachine.Layout c.forward 0 R B
 inverseZero : UniformSixCInverseMatchingPreparation.Layout c.inverse 0 R B
 forwardRows : p.mapped+6*UniformCrossHeightPreparationMachine.gates p.height≤B
 inverseRows : c.inverse.forward+6*UniformCrossHeightPreparationMachine.gates p.height≤c.inverse.inverseRows
 permutation : c.inverse.inverseRows+6*UniformCrossHeightPreparationMachine.gates p.height≤c.inverse.permutation
 freshSuffix : p.borrowed≤c.inverse.packing.suffix
 freshStack : p.borrowed≤c.inverse.packing.stack
 freshInverse : p.borrowed≤c.inverse.packing.inverse

lemma forwardLayout {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height) :
 UniformPackedMatchingShearMachine.Layout
  (UniformSixCDepthColorController.config l c.inverse.positive c.inverse.negative c.inverse.constants
   c.inverse.conjugates c.inverse.mu c.inverse.conjugateMu)
  (UniformChunkMatchingPreparation.indices p W).length R B:=by
 let f:=a.forwardZero
 have cap:=UniformMatchingActionBridge.actual_capacity l W dom degree
 have len:=UniformChunkMatchingPreparation.selected_count p W
 have rows:(UniformSixCDepthColorController.config l c.inverse.positive c.inverse.negative c.inverse.constants
   c.inverse.conjugates c.inverse.mu c.inverse.conjugateMu).rows=p.mapped:=rfl
 rw [a.sameForward] at f
 exact ⟨f.coefficient,cap,f.packedFresh,f.destinationFresh,f.disjoint,f.packedBound,
  f.destinationBound,f.inverseBound,by rw [rows];nlinarith [a.forwardRows],f.code⟩
lemma inverseLayout {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height) :
 UniformSixCInverseMatchingPreparation.Layout c.inverse
  (UniformSixCDirtyReplayMachine.physicalWord l.matching W dom).length R B:=by
 let f:=a.inverseZero
 have cap:=UniformMatchingAxisTableMachine.matching_capacity p.radix _
  (UniformSixCDirtyReplayMachine.physicalWord_matching l.matching W dom degree)
  (UniformSixCDirtyReplayMachine.physicalWord_range l.matching W dom)
 have len:=UniformChunkMatchingPreparation.selected_count p W
 rw [UniformSixCDirtyReplayMachine.physicalWord_length] at cap ⊢
 have packed:UniformPackedMatchingShearMachine.Layout c.inverse.packed
   (UniformChunkMatchingPreparation.indices p W).length R B:=by
  refine ⟨f.packed.coefficient,by simpa only [UniformSixCInverseMatchingPreparation.Config.packed,a.volume] using cap,
   f.packed.packedFresh,f.packed.destinationFresh,f.packed.disjoint,f.packed.packedBound,f.packed.destinationBound,
   f.packed.inverseBound,?_,f.packed.code⟩
  change c.inverse.inverseRows+3*(UniformChunkMatchingPreparation.indices p W).length≤B
  have h:=a.permutation
  have:=f.permutationBelow;have:=f.widthsBelow;have:=f.markersBelow
  have endpoint:=c.inverse.packing.rowsBelow;rw [f.axisRow] at endpoint
  have end2:=c.inverse.packing.suffixBelow;have end3:=c.inverse.packing.stackBelow
  have end4:=c.inverse.packing.inverseBound
  rw [f.budget] at end4
  nlinarith
 exact ⟨f.budget,f.oneAxis,f.axisRow,f.radix,by nlinarith [a.inverseRows],by nlinarith [a.permutation],
  f.permutationBelow,f.widthsBelow,f.markersBelow,packed,f.code⟩
/-- The actual descending body regenerates this color, physically reverses and
negates the rows, derives packing, executes six-C updates, and scatters. -/
theorem inverse_body {p:UniformChunkMatchingPreparation.Parameters} {B R n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B)
 (c:UniformSixCDirtyReplayMachine.Config) (a:Allocation l c R)
 (W:List (ShearCode ℕ R)) (bank:Fin R→ℂ) (s:State)
 (head:UniformChunkMatchingPreparation.Header p s) (high:UniformSixCDirtyReplayMachine.Header c s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0
   (UniformCrossShearTableMachine.locations R c.inverse.positive c.inverse.negative c.inverse.constants))) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K row.coefficient)
 (present:Present c.inverse.packing.source c.inverse.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (pc:s.pc=0) (bound:WordBound B s) (code:918≤B) :
 ∃u t,BoundedExecution UniformSixCDepthColorController.inverseProgram n x B s t u ∧
 t≤4*p.height.K+630*p.radix+213 ∧ u.pc=917 ∧
 Present c.inverse.packing.source c.inverse.packing.total u ∧
 (∀j,j<c.inverse.packing.total→(u.scalarHeap (c.inverse.packing.source+j)).map Scalar.value=some
  (runShears ((reverseCode (UniformSixCDirtyReplayMachine.physicalWord l.matching W dom)).map (ShearCode.eval bank))
   (numeric c.inverse.packing.source c.inverse.packing.total s) j)) ∧
 StaticEq s u ∧ (∀q,3001≤q→u.natReg q=s.natReg q) ∧ (∀q,q<p.borrowed→u.natHeap q=s.natHeap q) ∧
 UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank u ∧ UniformHadamardPairMachine.Constants u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q):=by
 let v:=data c.inverse.packing.source c.inverse.packing.total s
 let W':=UniformSixCDirtyReplayMachine.physicalWord l.matching W dom
 let il:=inverseLayout l c a W dom degree size
 have hm:=UniformSixCDirtyReplayMachine.physicalWord_matching l.matching W dom degree
 have hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total
  (UniformSixCInverseMatchingPreparation.forwardEdges W'):=by
  rw [a.volume];exact UniformSixCDirtyReplayMachine.physicalWord_range l.matching W dom
 let revM:=UniformSixCInverseMatchingPreparation.reverse_matching W' hm
 let revR:=UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W' hr
 obtain ⟨t,u,m,cost,run,up,res,uhn,ulow,unh,heap,out,roots⟩:=
  UniformSixCDepthColorController.inverse_execution x W l.matching c a.rows a.volume dom il degree good bank v s
   head high size record table colors (present_ready c.inverse.packing s present) src constants pc bound code
 have act:=UniformMatchingActionBridge.inverse_matching_action c.inverse W' revM revR il.radix bank
  (UniformSixCDirtyReplayMachine.physicalWord_leaf l.matching W dom good) v
 refine ⟨u,t,run,cost,up,?_,?_,StaticEq.of_frames ulow uhn,uhn,?_,?_,res.constants,out,roots,heap⟩
 · intro j hj
   exact ⟨_,res.destination ⟨j,hj⟩⟩
 · intro j hj
   have destination:=res.destination ⟨j,hj⟩
   change u.scalarHeap (c.inverse.packing.source+j)=some _ at destination
   rw [destination]
   simp only [Option.map_some]
   change some (UniformMatchingActionBridge.unpackValues
    (UniformSixCInverseMatchingPreparation.unpacking c.inverse W' revM revR il.radix)
    (UniformPackedMatchingShearMachine.matchingAction p.height.K bank
     (UniformSixCInverseMatchingPreparation.inverseLabels W') 0 W'.length
     (UniformSixCInverseMatchingPreparation.packedInput c.inverse W' revM revR il.radix v)) ⟨j,hj⟩)=_
   rw [act]
   rfl
 · intro q hq
   have borrowMapped:p.borrowed≤p.mapped:=by
    have:=l.matching.borrowFresh;have:=l.matching.selectedFresh;have:=l.matching.ordinalFresh;omega
   have below:q<c.inverse.inverseRows:=by have:=a.inverseRows;rw [a.rows] at this;omega
   exact unh q (Or.inl hq) (Or.inl below) (Or.inl (by have:=a.freshSuffix;omega))
    (Or.inl (by have:=a.freshStack;omega)) (Or.inl (by have:=a.freshInverse;omega))
 · constructor
   · intro i;exact res.coefficients.positive i
   · intro i;exact res.coefficients.negative i
   · intro i;exact res.coefficients.conjugate i
   · intro i hi;exact res.coefficients.constants i hi

lemma atAllocation {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) (backwards:Bool) (i:ℕ) (hi:i<(8*p.height.K+7)*11) :
 Allocation (atPacking l backwards i hi) c R:=by
 exact ⟨a.rows,a.volume,a.source,a.sameForward,a.forwardZero,a.inverseZero,a.forwardRows,a.inverseRows,
  a.permutation,a.freshSuffix,a.freshStack,a.freshInverse⟩

lemma args_from_dirty {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) (s:State) (h:UniformSixCDirtyReplayMachine.Header c s) :
 UniformSixCDepthColorController.Args (UniformSixCDepthColorController.config l c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates c.inverse.mu c.inverse.conjugateMu) s:=by
 rw [←a.sameForward]
 intro i;fin_cases i
 all_goals simp only [UniformSixCDepthColorController.fields,UniformSixCDirtyReplayMachine.Config.forward,
  List.getElem_cons_zero,List.getElem_cons_succ]
 all_goals first
 | exact h.length | exact h.packed | exact h.source | exact h.inverse | exact h.rows
 | exact h.positive | exact h.negative | exact h.constants | exact h.conjugates | exact h.mu | exact h.conjugateMu

lemma originalValues_packed {L:ℕ} (phi:Fin L≃Fin L) (v:Fin L→Scalar) :
 UniformMatchingActionBridge.originalValues phi (UniformSixCDepthColorController.packedValues phi v)=
 fun j=>if h:j<L then (v ⟨j,h⟩).value else 0:=by
 funext j
 by_cases h:j<L
 · simp [UniformMatchingActionBridge.originalValues,UniformMatchingActionBridge.unpackValues,
    UniformSixCDepthColorController.packedValues,h]
 · simp [UniformMatchingActionBridge.originalValues,h]

lemma forward_action {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K row.coefficient)
 (bank:Fin R→ℂ) (v:Fin l.packing.total→Scalar) (j:Fin l.packing.total) :
 (UniformPackedMatchingShearMachine.matchingAction p.height.K bank
  (UniformSixCDepthColorController.labels p W) 0 (UniformChunkMatchingPreparation.indices p W).length
  (UniformSixCDepthColorController.packedValues (UniformSixCDepthColorController.phi l W dom degree) v)
  ((UniformSixCDepthColorController.phi l W dom degree).symm j).val).value=
 runShears ((UniformSixCDirtyReplayMachine.physicalWord l.matching W dom).map (ShearCode.eval bank))
  (fun z=>if h:z<l.packing.total then (v ⟨z,h⟩).value else 0) j.val:=by
 have all:=UniformMatchingActionBridge.actual_matching_action l W dom degree bank good
  (UniformSixCDepthColorController.packedValues (UniformSixCDepthColorController.phi l W dom degree) v)
 have phieq:UniformMatchingActionBridge.actualPhi l W dom degree=UniformSixCDepthColorController.phi l W dom degree:=rfl
 rw [phieq,originalValues_packed] at all
 exact congrFun all j

/-- One concrete generated forward body with full natural-coordinate action.
It reads actual physical Height rows/colors/count and regenerates all matching
and packing tables before the six-C update. -/
theorem forward_body {p:UniformChunkMatchingPreparation.Parameters} {B R n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B)
 (c:UniformSixCDirtyReplayMachine.Config) (a:Allocation l c R)
 (W:List (ShearCode ℕ R)) (bank:Fin R→ℂ) (s:State)
 (head:UniformMatchingPackingPreparation.Header l s) (high:UniformSixCDirtyReplayMachine.Header c s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0
   (UniformCrossShearTableMachine.locations R c.inverse.positive c.inverse.negative c.inverse.constants))) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K row.coefficient)
 (present:Present l.packing.source l.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (pc:s.pc=0) (bound:WordBound B s) (code:796≤B) :
 ∃u t,BoundedExecution UniformSixCDepthColorController.forwardProgram n x B s t u ∧
 t≤4*p.height.K+596*p.radix+155 ∧ u.pc=795 ∧
 Present l.packing.source l.packing.total u ∧
 (∀j,j<l.packing.total→(u.scalarHeap (l.packing.source+j)).map Scalar.value=some
  (runShears ((UniformSixCDirtyReplayMachine.physicalWord l.matching W dom).map (ShearCode.eval bank))
   (numeric l.packing.source l.packing.total s) j)) ∧
 StaticEq s u ∧ (∀q,3001≤q→u.natReg q=s.natReg q) ∧ (∀q,q<p.borrowed→u.natHeap q=s.natHeap q) ∧
 UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank u ∧ UniformHadamardPairMachine.Constants u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.forward q→u.scalarHeap q=s.scalarHeap q):=by
 let v:=data l.packing.source l.packing.total s
 obtain ⟨u,t,run,cost,up,destination,usrc,uconst,uhn,ulow,unh,out,roots,heap⟩:=
  UniformSixCDepthColorController.forward_execution x W l c.inverse.positive c.inverse.negative c.inverse.constants
   c.inverse.conjugates c.inverse.mu c.inverse.conjugateMu (forwardLayout l c a W dom degree size) bank v s
   head (args_from_dirty l c a s high) size record table colors dom degree
   (present_ready l.packing s present) src constants pc bound code
 refine ⟨u,t,run,cost,up,?_,?_,StaticEq.of_frames ulow uhn,uhn,?_,usrc,uconst,out,roots,?_⟩
 · intro j hj
   exact ⟨_,destination ⟨j,hj⟩⟩
 · intro j hj
   rw [destination ⟨j,hj⟩]
   simp only [Option.map_some]
   rw [forward_action l W dom degree good bank v ⟨j,hj⟩]
   rfl
 · intro q hq;exact unh q (Or.inl hq)
 · rw [a.sameForward];exact heap

/-- Description of the actual current body word. The RAM cursor computes the
ordinal; the list below never enters the machine as a supplied traversal tape. -/
def layerWord {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (i:Fin ((8*p.height.K+7)*11)) :
 List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)):=
 let q:=layerParameters p backwards i.val
 let inner:=UniformSixCDirtyReplayMachine.physicalWord (atLayout l.matching backwards i.val i.isLt)
  (UniformChunkMatchingPreparation.crossWord q ha he) (UniformChunkMatchingPreparation.cross_domain q ha he)
 if backwards then UniformReplayPrint.reverseCode inner else inner

def phaseWord {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :=
 (List.finRange ((8*p.height.K+7)*11)).flatMap (layerWord l backwards ha he)
lemma phaseWord_eq {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 phaseWord l backwards ha he=(List.finRange ((8*p.height.K+7)*11)).flatMap (fun i=>
  let q:=layerParameters p backwards i.val
  let W:=UniformSixCDirtyReplayMachine.physicalWord (atLayout l.matching backwards i.val i.isLt)
   (UniformChunkMatchingPreparation.crossWord q ha he) (UniformChunkMatchingPreparation.cross_domain q ha he)
  if backwards then UniformReplayPrint.reverseCode W else W):=rfl

end
end ExactFourierCircuits.UniformSixCPhaseContext
