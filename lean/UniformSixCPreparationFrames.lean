import UniformSixCReplayDescriptor
import UniformSixCLayerStep
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCPreparationFrames
open UniformMachine UniformReplayPrint UniformSixCPhaseContext UniformSixCLayerStep UniformSixCReplayDescriptor
open UniformTensorMonomialMachine (setPC)
noncomputable section
lemma enabledAllocation {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) (enabled:Bool) : Allocation (enabledPacking l enabled) c R:=by
 exact ⟨a.rows,a.volume,a.source,a.sameForward,a.forwardZero,a.inverseZero,a.forwardRows,a.inverseRows,a.permutation,a.freshSuffix,a.freshStack,a.freshInverse⟩
lemma enabledHeightLayout (v:UniformCrossHeightPreparationMachine.Parameters)
 (h:UniformCrossHeightPreparationMachine.Layout v) (enabled:Bool) :
 UniformCrossHeightPreparationMachine.Layout {v with enabled:=enabled}:=by
 exact ⟨h.tape,h.order,h.directory,h.rows,h.colors,h.palette⟩
lemma flagHeightHeader {v:UniformCrossHeightPreparationMachine.Parameters} {s:State}
 (h:UniformCrossHeightPreparationMachine.Header v s) (enabled:Bool) :
 UniformCrossHeightPreparationMachine.Header {v with enabled:=enabled}
  (writeNat s 1061 (if enabled then 1 else 0)):=by
 constructor
 · simpa [writeNat,next] using h.exponent
 · simpa [writeNat,next] using h.targets
 · simpa [writeNat,next] using h.inputs
 · simpa [writeNat,next] using h.tape
 · simpa [writeNat,next] using h.order
 · simpa [writeNat,next] using h.sourceDirectory
 · simpa [writeNat,next] using h.rows
 · simpa [writeNat,next] using h.colors
 · simpa [writeNat,next] using h.palette
 · simpa [writeNat,next] using h.directory
 · simpa [writeNat,next] using h.coefficients
 · simp [writeNat,next]
 · simpa [writeNat,next] using h.constants
lemma flagBaseHeader {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) {s:State} (h:BaseHeader l s) (enabled:Bool) :
 BaseHeader (enabledPacking l enabled) (writeNat s 1061 (if enabled then 1 else 0)):=by
 refine ⟨⟨flagHeightHeader h.matching.height enabled,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
 all_goals first
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.radix
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.source
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.target
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.borrowed
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.selected
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.ordinals
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.mapped
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.permutation
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.widths
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.markers
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.matching.axis
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.suffix
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.stack
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.inverse
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.source
 | simpa [writeNat,next,enabledPacking,enabledParameters] using h.destination
lemma heightBaseHeader {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {s u:State} (h:BaseHeader l s)
 (frame:UniformCrossHeightPreparationMachine.Frame s u) : BaseHeader l u:=by
 have eq:∀q,UniformCrossHeightPreparationMachine.Protected q→u.natReg q=s.natReg q:=frame.2.2.2.2
 refine ⟨⟨h.matching.height.transport frame,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.radix
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.source
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.target
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.borrowed
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.selected
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.ordinals
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.mapped
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.permutation
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.widths
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.markers
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.matching.axis
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.suffix
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.stack
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.inverse
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.source
 | exact (eq _ (by simp [UniformCrossHeightPreparationMachine.Protected,UniformCrossDepthReplayPreparation.Protected])).trans h.destination
lemma initialContext {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (s:State)
 (present:Present l.packing.source l.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) : Context l c bank s s:=
 ⟨StaticEq.refl s,fun _ _=>rfl,present,src,constants,rfl,rfl⟩
lemma sources_heap {R K C T P V:ℕ} {bank:Fin R→ℂ} {s u:State}
 (h:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s) (sh:u.scalarHeap=s.scalarHeap) :
 UniformMatchingConjugateLoadMachine.Sources K C T P V bank u:=by
 rcases h with ⟨pos,neg,conj,const⟩
 exact ⟨by simpa only [sh] using pos,by simpa only [sh] using neg,by simpa only [sh] using conj,
  by simpa only [UniformReplayCoefficientMachine.Constants,sh] using const⟩
lemma present_heap {base L:ℕ} {s u:State} (h:Present base L s) (sh:u.scalarHeap=s.scalarHeap) : Present base L u:=by
 intro j hj;rw [sh];exact h j hj
lemma constants_heap {s u:State} (h:UniformHadamardPairMachine.Constants s) (sh:u.scalarHeap=s.scalarHeap) :
 UniformHadamardPairMachine.Constants u:=by simpa only [UniformHadamardPairMachine.Constants,sh] using h
end
end ExactFourierCircuits.UniformSixCPreparationFrames
