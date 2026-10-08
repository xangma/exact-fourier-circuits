import UniformSixCPhaseContext
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCLayerStep
open UniformMachine UniformReplayPrint UniformAssembly OAI.ExactFourier
open UniformSixCPhaseContext UniformSixCTraversal
open UniformTensorMonomialMachine (setPC)
noncomputable section

lemma processed_prefix {p:UniformChunkMatchingPreparation.Parameters} {B Z G:ℕ}
 {printed:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize p.height.K) p.height.e G}
 {s u:State} (l:UniformChunkMatchingPreparation.Layout p B)
 (size:G=UniformCrossHeightPreparationMachine.gates p.height)
 (h:UniformCrossHeightPreparationMachine.Processed p.height Z printed (UniformCrossHeightPreparationMachine.height p.height) s)
 (out:∀q,q<p.borrowed→u.natHeap q=s.natHeap q) :
 UniformCrossHeightPreparationMachine.Processed p.height Z printed (UniformCrossHeightPreparationMachine.height p.height) u:=by
 intro d hd
 obtain ⟨table,col,rec⟩:=h d hd
 have len:=(UniformCrossHeightPreparationMachine.bucket_length printed p.height.enabled d).trans
  (by rw [size]:2*G≤2*UniformCrossHeightPreparationMachine.gates p.height)
 have rr:=l.oldRows;have cc:=l.oldColors;have dd:=l.oldDirectory
 have rh:UniformCrossHeightPreparationMachine.rowBase p.height d+3*(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.rowBase] at rr ⊢;nlinarith
 have ch:UniformCrossHeightPreparationMachine.colorBase p.height d+(UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.colorBase] at cc ⊢;nlinarith
 have dh:UniformCrossHeightPreparationMachine.recordBase p.height d+3≤p.borrowed:=by
  simp only [UniformCrossHeightPreparationMachine.recordBase] at dd ⊢;omega
 refine ⟨?_,?_,?_⟩
 · intro i hi
   have hi' : i < (UniformCrossDepthReplayPreparation.bucket printed p.height.enabled d).length := by simpa using hi
   unfold UniformCrossShearTableMachine.RowFields
   rw [out _ (by omega),out _ (by omega),out _ (by omega)]
   exact table i hi
 · intro i
   rw [out _ (by have:=i.isLt;omega)]
   exact col i
 · unfold UniformCrossHeightPreparationMachine.Record
   rw [out _ (by omega),out _ (by omega),out _ (by omega)]
   exact rec

structure Context {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (origin s:State) : Prop where
 static : StaticEq origin s
 preserved : ∀q,q<p.borrowed→s.natHeap q=origin.natHeap q
 present : Present l.packing.source l.packing.total s
 sources : UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank s
 constants : UniformHadamardPairMachine.Constants s
 outputs : s.outputs=origin.outputs
 roots : s.rootOrders=origin.rootOrders
lemma Context.high {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s:State}
 (h:Context l c bank origin s) (base:UniformSixCDirtyReplayMachine.Header c origin) :
 UniformSixCDirtyReplayMachine.Header c s:=base.transport (fun q lo hi=>h.static q (Or.inr ⟨lo,hi⟩))

lemma Context.transport {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s u:State}
 (h:Context l c bank origin s) (regs:StaticEq s u) (nh:u.natHeap=s.natHeap)
 (sh:u.scalarHeap=s.scalarHeap) (out:u.outputs=s.outputs) (root:u.rootOrders=s.rootOrders) :
 Context l c bank origin u:=by
 refine ⟨h.static.trans regs,?_,?_,?_,?_,out.trans h.outputs,root.trans h.roots⟩
 · intro q hq;rw [nh];exact h.preserved q hq
 · intro j hj;rw [sh];exact h.present j hj
 · rcases h.sources with ⟨pos,neg,conj,cc⟩
   exact ⟨by simpa only [sh] using pos,by simpa only [sh] using neg,
    by simpa only [sh] using conj,by simpa only [UniformReplayCoefficientMachine.Constants,sh] using cc⟩
 · simpa only [UniformHadamardPairMachine.Constants,sh] using h.constants
lemma Context.withPC {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s:State}
 (h:Context l c bank origin s) (pc:ℕ) : Context l c bank origin (setPC s pc):=
 h.transport (StaticEq.refl s) rfl rfl rfl rfl

structure BodyResult {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (backwards:Bool) (W:List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (origin s u:State) (t:ℕ) : Prop where
 run : BoundedExecution (UniformSixCDepthColorController.traversalBody backwards) n x B s t u
 cost : t≤4*p.height.K+630*p.radix+213
 pc : u.pc=(UniformSixCDepthColorController.traversalBody backwards).length-1
 context : Context l c bank origin u
 numeric : ∀j,j<l.packing.total→(u.scalarHeap (l.packing.source+j)).map Scalar.value=
  some (runShears (W.map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) j)
 cursorRegs : ∀q,3021≤q→q≤3027→u.natReg q=s.natReg q
 heap : ∀q,UniformPackedMatchingShearMachine.HeapStable c.forward q→
  UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q

/-- Concrete invocation from the actual Height186 output. The current logical
bucket, domain, coefficients, greedy degree and capacity are derived here. -/
theorem actual_body {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (allocation:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positive:c.inverse.positive=p.height.C) (constants:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (backwards:Bool) (i:Fin ((8*p.height.K+7)*11)) (origin s:State)
 (header:BaseHeader l origin)
 (high:UniformSixCDirtyReplayMachine.Header c origin)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) origin)
 (ctx:Context l c bank origin s)
 (depth:s.natReg 1191=(layerParameters p backwards i.val).depth)
 (color:s.natReg 1192=(layerParameters p backwards i.val).color)
 (pc:s.pc=0) (bound:WordBound B s) (code:918≤B) :
 ∃u t,BodyResult x l c bank backwards (layerWord l backwards ha he i) origin s u t:=by
 let q:=layerParameters p backwards i.val
 let ll:=atPacking l backwards i.val i.isLt
 let al:=atAllocation l c allocation backwards i.val i.isLt
 let W:=UniformChunkMatchingPreparation.crossWord q ha he
 let dom:=UniformChunkMatchingPreparation.cross_domain q ha he
 let degree:=UniformChunkMatchingPreparation.cross_degree q ha he
 have hhead:=atHeader l backwards i.val i.isLt header ctx.static depth color
 have pp:=processed_prefix l.matching (UniformCrossHeightPreparationMachine.cross_size p.height ha he) processed ctx.preserved
 obtain ⟨table,col,record⟩:=pp q.depth ll.matching.depthBound
 have size:W.length≤2*UniformCrossHeightPreparationMachine.gates q.height:=by
  change (UniformCrossDepthReplayPreparation.bucket (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled q.depth).length≤2*UniformCrossHeightPreparationMachine.gates p.height
  simpa only [UniformCrossHeightPreparationMachine.cross_size p.height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length
    (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled q.depth
 have cols:∀j:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase q.height q.depth+j.val)=
  some (UniformChunkMatchingPreparation.colors W j.val):=fun j=>col j
 have tt:UniformCrossShearTableMachine.Table (UniformCrossHeightPreparationMachine.rowBase q.height q.depth)
   (W.map (UniformCrossShearTableMachine.shiftedRow 0
    (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize p.height.K)
     c.inverse.positive c.inverse.negative c.inverse.constants))) s:=by
  rw [positive,constants];exact table
 have good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf q.height.K row.coefficient:=
  UniformMatchingCoefficientValueBridge.crossWord_leaf q ha he
 have hh:=ctx.high high
 cases backwards with
 | false=>
  obtain ⟨u,t,run,cost,up,present,values,static,highRegs,nh,src,hc,out,roots,heap⟩:=
   forward_body x ll c al W bank s hhead hh size record tt cols dom degree good ctx.present ctx.sources ctx.constants pc bound (by omega)
  change t≤4*p.height.K+596*p.radix+155 at cost
  refine ⟨u,t,⟨run,by omega,?_,⟨ctx.static.trans static,?_,present,src,hc,out.trans ctx.outputs,roots.trans ctx.roots⟩,?_,?_,?_⟩⟩
  · rw [UniformSixCDepthColorController.traversalBody_length];exact up
  · intro z hz;exact (nh z hz).trans (ctx.preserved z hz)
  · change ∀j,j<l.packing.total→(u.scalarHeap (l.packing.source+j)).map Scalar.value=some (runShears ((UniformSixCDirtyReplayMachine.physicalWord ll.matching W dom).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) j)
    exact values
  · intro z lo _;exact highRegs z (by omega)
  · intro z f _;exact heap z f
 | true=>
  have totals:c.inverse.packing.total=l.packing.total:=allocation.volume.trans l.volume.symm
  have present:Present c.inverse.packing.source c.inverse.packing.total s:=by rw [allocation.source,totals];exact ctx.present
  obtain ⟨u,t,run,cost,up,present,values,static,highRegs,nh,src,hc,out,roots,heap⟩:=
   inverse_body x ll c al W bank s hhead.matching hh size record tt cols dom degree good present ctx.sources ctx.constants pc bound code
  refine ⟨u,t,⟨run,cost,?_,⟨ctx.static.trans static,?_,?_,src,hc,out.trans ctx.outputs,roots.trans ctx.roots⟩,?_,?_,?_⟩⟩
  · rw [UniformSixCDepthColorController.traversalBody_length];exact up
  · intro z hz;exact (nh z hz).trans (ctx.preserved z hz)
  · simpa only [allocation.source,totals] using present
  · change ∀j,j<l.packing.total→(u.scalarHeap (l.packing.source+j)).map Scalar.value=some (runShears ((reverseCode (UniformSixCDirtyReplayMachine.physicalWord ll.matching W dom)).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) j)
    rw [allocation.source,totals] at values
    exact values
  · intro z lo _;exact highRegs z (by omega)
  · intro z _ f;exact heap z f
end
end ExactFourierCircuits.UniformSixCLayerStep
