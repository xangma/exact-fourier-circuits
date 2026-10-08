import UniformSixCWholeReplay
import UniformSixCPhysicalAction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCCorrectedReplay
open UniformMachine UniformReplayPrint OAI.ExactFourier
open UniformSixCReplayDescriptor UniformSixCPhaseContext UniformSixCWholeReplay
noncomputable section
abbrev Registers (p:UniformChunkMatchingPreparation.Parameters) :=
 (Fin p.height.e ⊕ Fin (UniformCrossHeightPreparationMachine.gates p.height)) ⊕ Fin p.height.a

def logicalIndex (p:UniformChunkMatchingPreparation.Parameters) : Registers p ↪ ℕ :=
 UniformDAGLayers.replayEmbedding p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a

lemma logicalIndex_domain (p:UniformChunkMatchingPreparation.Parameters) (i:Registers p) :
 UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a (logicalIndex p i):=by
 rcases i with (i|i)|i
 · exact Or.inl i.isLt
 · apply Or.inr
   change p.height.e+1≤p.height.e+1+i.val ∧ p.height.e+1+i.val<p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height+p.height.a
   have:=i.isLt;omega
 · apply Or.inr
   change p.height.e+1≤p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height+i.val ∧ p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height+i.val<p.height.e+1+UniformCrossHeightPreparationMachine.gates p.height+p.height.a
   have:=i.isLt;omega

def replayPort (p:UniformChunkMatchingPreparation.Parameters) (i:Registers p) : UniformPhysicalReplayBridge.Port p :=
 ⟨logicalIndex p i,logicalIndex_domain p i⟩

def physicalIndex {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (i:Registers p) :=
 UniformPhysicalReplayBridge.portEmbedding l.matching (replayPort p i)

/-- Literal physical six-phase shears implement the corrected cross and restore
arbitrary dirty source/gate values, through the producer-derived coordinates. -/
theorem fullWord_cross_matrix {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:0<p.height.a) (he:0<p.height.e)
 (size:2*(p.height.a+p.height.e)≤UniformRadixTwoDAG.width p.height.K)
 (M:ℕ→ℕ→ℂ) (v w:ℕ→ℂ)
 (recurrence:∀i j,i+1<p.height.a→j+1<p.height.e→M (i+1) (j+1)=M i j+v (i+1)*w (j+1))
 (X:ℕ→ℂ) :
 runShears ((fullWord l (by change p.height.a≤UniformRadixTwoDAG.width p.height.K;omega)
  (by change p.height.e≤UniformRadixTwoDAG.width p.height.K;omega)).map
   (ShearCode.eval (UniformToeplitzCrossDAG.sharedBank p.height.K
    (UniformToeplitzCrossDAG.rankKernels p.height.K p.height.a p.height.e M v w)))) X ∘ physicalIndex l =
 Sum.elim (Sum.elim (fun i:Fin p.height.e=>X (physicalIndex l (.inl (.inl i))))
  (fun j:Fin (UniformCrossHeightPreparationMachine.gates p.height)=>X (physicalIndex l (.inl (.inr j)))))
  (fun j:Fin p.height.a=>X (physicalIndex l (.inr j))+
   Matrix.mulVec (fun i:Fin p.height.a=>fun j:Fin p.height.e=>M i.val j.val)
    (fun i=>X (physicalIndex l (.inl (.inl i)))) j):=by
 have ha':p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height:=by
  change p.height.a≤UniformRadixTwoDAG.width p.height.K;omega
 have he':p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height:=by
  change p.height.e≤UniformRadixTwoDAG.width p.height.K;omega
 let bank:=UniformToeplitzCrossDAG.sharedBank p.height.K (UniformToeplitzCrossDAG.rankKernels p.height.K p.height.a p.height.e M v w)
 have action:=UniformSixCPhysicalAction.fullWord_action l ha' he' bank X
 have matrix:=UniformPhysicalReplayBridge.literalCross_matrix p p.height.K p.height.a p.height.e ha he size M v w recurrence
  (X ∘ UniformChunkMatchingPreparation.coordinate p l.matching.capacity)
 rw [UniformCrossHeightPreparationMachine.cross_size p.height ha' he'] at matrix
 funext i
 have actual:=congrFun action (replayPort p i)
 have logical:=congrFun matrix i
 exact actual.trans logical

lemma physicalIndex_bound {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (i:Registers p) : physicalIndex l i<l.packing.total:=by
 rw [l.volume]
 exact UniformChunkPortMachine.mapped_inRange p.radix p.source p.height.e p.target p.height.a
  (UniformCrossHeightPreparationMachine.gates p.height) (logicalIndex p i)
  l.matching.sourceRange l.matching.targetRange l.matching.separated l.matching.capacity (logicalIndex_domain p i)

lemma numeric_physical {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (s:State) (i:Registers p) :
 numeric l.packing.source l.packing.total s (physicalIndex l i)=
 (data l.packing.source l.packing.total s ⟨physicalIndex l i,physicalIndex_bound l i⟩).value:=by
 simp only [numeric,dite_eq_left (physicalIndex_bound l i)]

/-- Every coordinate outside the actual source/gate/target port image is
unchanged numerically, including unused tail coordinates. -/
theorem fullWord_outside {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (X:ℕ→ℂ) (q:ℕ)
 (outside:∀i:UniformPhysicalReplayBridge.Port p,q≠UniformPhysicalReplayBridge.portEmbedding l.matching i) :
 runShears ((fullWord l ha he).map (ShearCode.eval bank)) X q=X q:=by
 rw [←UniformSixCPhysicalAction.fullPorts_physical]
 exact UniformDAGLayers.relabel_run_outside _ bank _ X q outside

/-- Actual initialized5375 run with typed corrected-cross action. Dirty input and
all gate workspaces are numerically restored; target accumulators add M*x.
The physical typed tape/order/directory and original coefficient bank remain
honest preparation entries. No generated matching/packing/inverse action is
assumed, and conservative data flags need not be restored. -/
theorem execution_cross_matrix {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positive:c.inverse.positive=p.height.C) (constant:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (apos:0<p.height.a) (epos:0<p.height.e)
 (size:2*(p.height.a+p.height.e)≤UniformRadixTwoDAG.width p.height.K)
 (M:ℕ→ℕ→ℂ) (v w:ℕ→ℂ)
 (recurrence:∀i j,i+1<p.height.a→j+1<p.height.e→M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) (s:State)
 (head:BaseHeader l s) (high:UniformSixCDirtyReplayMachine.Header c s)
 (layout:UniformCrossHeightPreparationMachine.Layout p.height)
 (budget:UniformCrossHeightPreparationMachine.wordBudget p.height≤B)
 (source:UniformCrossHeightPreparationMachine.Source p.height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program s)
 (present:Present l.packing.source l.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates (UniformToeplitzCrossDAG.sharedBank p.height.K (UniformToeplitzCrossDAG.rankKernels p.height.K p.height.a p.height.e M v w)) s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=0) (bound:WordBound B s)
 (code:5375≤B) (count:(8*p.height.K+7)*11≤B) :
 ∃u t,BoundedExecution UniformSixCFullProgram.program n x B s t u ∧
 t≤2*heightCost p+2*halfCost p+3 ∧ u.pc=5374 ∧
 numeric l.packing.source l.packing.total u ∘ physicalIndex l=
 Sum.elim (Sum.elim
  (fun i:Fin p.height.e=>numeric l.packing.source l.packing.total s (physicalIndex l (.inl (.inl i))))
  (fun j:Fin (UniformCrossHeightPreparationMachine.gates p.height)=>numeric l.packing.source l.packing.total s (physicalIndex l (.inl (.inr j)))))
  (fun j:Fin p.height.a=>numeric l.packing.source l.packing.total s (physicalIndex l (.inr j))+
   Matrix.mulVec (fun i:Fin p.height.a=>fun j:Fin p.height.e=>M i.val j.val)
    (fun i=>numeric l.packing.source l.packing.total s (physicalIndex l (.inl (.inl i)))) j) ∧
 (∀q,(∀i:UniformPhysicalReplayBridge.Port p,q≠UniformPhysicalReplayBridge.portEmbedding l.matching i)→
  numeric l.packing.source l.packing.total u q=numeric l.packing.source l.packing.total s q) ∧
 UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates (UniformToeplitzCrossDAG.sharedBank p.height.K (UniformToeplitzCrossDAG.rankKernels p.height.K p.height.a p.height.e M v w)) u ∧
 UniformHadamardPairMachine.Constants u ∧ Present l.packing.source l.packing.total u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,3001≤j→j≤3020→u.natReg j=s.natReg j) ∧
 (∀j,UniformPackedMatchingShearMachine.HeapStable c.forward j→UniformPackedMatchingShearMachine.HeapStable c.inverse.packed j→u.scalarHeap j=s.scalarHeap j):=by
 let bank:=UniformToeplitzCrossDAG.sharedBank p.height.K
  (UniformToeplitzCrossDAG.rankKernels p.height.K p.height.a p.height.e M v w)
 obtain ⟨u,t,run,cost,up,values,usources,hc,hp,out,roots,saved,external⟩:=
  UniformSixCWholeReplay.execution x l c a positive constant ha he bank s head high layout budget source
   present src constants pc bound code count
 refine ⟨u,t,run,cost,up,?_,?_,usources,hc,hp,out,roots,saved,external⟩
 · rw [values]
   exact fullWord_cross_matrix l apos epos size M v w recurrence (numeric l.packing.source l.packing.total s)
 · intro q hq
   rw [values]
   exact fullWord_outside l ha he bank (numeric l.packing.source l.packing.total s) q hq
end
end ExactFourierCircuits.UniformSixCCorrectedReplay
