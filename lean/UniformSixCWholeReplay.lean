import UniformSixCContinuousReplay
import UniformSixCPreparationFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCWholeReplay
open UniformMachine UniformReplayPrint UniformAssembly OAI.ExactFourier
open UniformSixCPhaseContext UniformSixCTraversal UniformSixCLayerStep UniformSixCPhaseLoop
open UniformSixCReplayDescriptor UniformSixCPreparationFrames UniformSixCContinuousReplay
open UniformTensorMonomialMachine (setPC)
noncomputable section
def heightCost (p:UniformChunkMatchingPreparation.Parameters) :=
 4*p.height.K+27+(8*p.height.K+7)*(64*UniformCrossHeightPreparationMachine.gates p.height+
  200*(2*UniformCrossHeightPreparationMachine.gates p.height+1)^2+56)
def halfCost (p:UniformChunkMatchingPreparation.Parameters) := 2*phaseCost p+461*p.radix+14*p.height.a+149
lemma dirty_height {c:UniformSixCDirtyReplayMachine.Config} {s u:State}
 (h:UniformSixCDirtyReplayMachine.Header c s) (f:UniformCrossHeightPreparationMachine.Frame s u) :
 UniformSixCDirtyReplayMachine.Header c u:=h.transport (by
  intro j lo hi
  exact f.2.2.2.2 j (by unfold UniformCrossHeightPreparationMachine.Protected UniformCrossDepthReplayPreparation.Protected;omega))
lemma dirty_flag {c:UniformSixCDirtyReplayMachine.Config} {s:State}
 (h:UniformSixCDirtyReplayMachine.Header c s) (b:Bool) :
 UniformSixCDirtyReplayMachine.Header c (writeNat s 1061 (if b then 1 else 0)):=h.transport (by
 intro j lo hi;simp (disch:=omega) [writeNat,next])
lemma base_withPC {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {s:State} (h:BaseHeader l s) (pc:ℕ) : BaseHeader l (setPC s pc):=
 h.transport (StaticEq.refl s)

/-- Genuine Height186 regeneration from the typed tape and bucket order.
All local rows/colors/records are output conclusions, not entries. -/
theorem height_call {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (q:UniformMachine.Program) (base finish:ℕ)
 (code:CodeAt UniformCrossHeightPreparationMachine.program q base finish)
 (codeB:base+186≤B) (finishB:finish≤B) (s:State)
 (head:BaseHeader l s) (high:UniformSixCDirtyReplayMachine.Header c s)
 (layout:UniformCrossHeightPreparationMachine.Layout p.height)
 (budget:UniformCrossHeightPreparationMachine.wordBudget p.height≤B)
 (source:UniformCrossHeightPreparationMachine.Source p.height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program s)
 (present:Present l.packing.source l.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=base) (bound:WordBound B s) :
 ∃u t,BoundedRuns q n x B s t u ∧ t≤heightCost p ∧ u.pc=finish ∧
 BaseHeader l u ∧ UniformSixCDirtyReplayMachine.Header c u ∧ Context l c bank u u ∧
 UniformCrossHeightPreparationMachine.Cursor p.height (UniformCrossHeightPreparationMachine.height p.height) u ∧
 UniformCrossHeightPreparationMachine.Source p.height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program u ∧
 UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) u ∧ UniformCrossHeightPreparationMachine.Frame s u:=by
 have tape:UniformToeplitzCrossTopologyMachine.RowTable
  (UniformToeplitzCrossTopologyMachine.crossRows p.height.K p.height.a p.height.e) p.height.T (setPC s 0):=by
  rw [UniformToeplitzCrossTopologyMachine.crossRows_typed p.height.K p.height.a p.height.e ha he]
  exact source.tape
 obtain ⟨u,t,run,cost,up,cur,usource,processed,out,frame⟩:=UniformCrossHeightPreparationMachine.cross_execution p.height
  c.inverse.negative B n ha he x (setPC s 0) (base_withPC head 0).matching.height rfl
  (changePC_bound B s 0 bound (Nat.zero_le _)) layout budget source.bank source.directory tape
 have placed:=UniformBoundedAssembly.boundedExecution_placed code
  (by simpa only [UniformCrossHeightPreparationMachine.program_length] using codeB) finishB run
 rw [placed_reset s base pc] at placed
 let z:=setPC u finish
 have ff:UniformCrossHeightPreparationMachine.Frame s z:=frame
 have pp:Present l.packing.source l.packing.total z:=present_heap present ff.1
 have ss:=sources_heap src ff.1
 have hc:=constants_heap constants ff.1
 have processZ:UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program (UniformCrossHeightPreparationMachine.height p.height) z:=
  processed_prefix (u:=z) l.matching (UniformCrossHeightPreparationMachine.cross_size p.height ha he) processed (fun _ _=>rfl)
 exact ⟨z,t,placed,cost,rfl,heightBaseHeader head ff,dirty_height high ff,initialContext l c bank z pp ss hc,
  cur.withPC,usource.withPC,processZ,ff⟩
lemma source_flag {p:UniformChunkMatchingPreparation.Parameters} {s:State}
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (h:UniformCrossHeightPreparationMachine.Source p.height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program s) (enabled:Bool) :
 UniformCrossHeightPreparationMachine.Source (enabledParameters p enabled).height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (writeNat s 1061 (if enabled then 1 else 0)):=⟨h.bank,h.directory,h.tape⟩

/-- Complete fixed5375 execution. The only physical preparation entries are
ordinary typed tape/order/directory and original coefficient/data banks. Every
Height row/color, matching row, permutation, signed broadcast and inverse is
produced in the charged continuous run. -/
theorem execution {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positive:c.inverse.positive=p.height.C) (constant:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (s:State)
 (head:BaseHeader l s) (high:UniformSixCDirtyReplayMachine.Header c s)
 (layout:UniformCrossHeightPreparationMachine.Layout p.height)
 (budget:UniformCrossHeightPreparationMachine.wordBudget p.height≤B)
 (source:UniformCrossHeightPreparationMachine.Source p.height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program s)
 (present:Present l.packing.source l.packing.total s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s) (pc:s.pc=0) (bound:WordBound B s)
 (code:5375≤B) (count:(8*p.height.K+7)*11≤B) :
 ∃u t,BoundedExecution UniformSixCFullProgram.program n x B s t u ∧
 t≤2*heightCost p+2*halfCost p+3 ∧ u.pc=5374 ∧
 numeric l.packing.source l.packing.total u=
 runShears ((fullWord l ha he).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank u ∧
 UniformHadamardPairMachine.Constants u ∧ Present l.packing.source l.packing.total u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,3001≤j→j≤3020→u.natReg j=s.natReg j) ∧
 (∀j,UniformPackedMatchingShearMachine.HeapStable c.forward j→UniformPackedMatchingShearMachine.HeapStable c.inverse.packed j→u.scalarHeap j=s.scalarHeap j):=by
 let f:=writeNat s 1061 1
 have fBound:WordBound B f:=writeNat_bound B s 1061 1 bound (by omega) (by omega)
 have flag:BoundedRuns UniformSixCFullProgram.program n x B s 1 f:=.next bound
  (by simp [step,pc,UniformSixCFullProgram.true_at,f]) (.refl fBound)
 let lt:=enabledPacking l true
 let lf:=enabledPacking l false
 have hft:BaseHeader lt f:=flagBaseHeader l head true
 have hfh:UniformSixCDirtyReplayMachine.Header c f:=dirty_flag high true
 have sf:=source_flag ha he source true
 obtain ⟨h1,t1,r1,c1,pc1,head1,high1,ctx1,cursor1,source1,processed1,frame1⟩:=
  height_call (p:=enabledParameters p true) x lt c ha he bank UniformSixCFullProgram.program 1 187
   UniformSixCFullProgram.heightTrue_code (by omega) (by omega) f hft hfh
   (enabledHeightLayout p.height layout true) budget sf present (sources_heap src (show f.scalarHeap=s.scalarHeap from rfl)) constants
   (by simp [f,writeNat,next,pc]) fBound
 obtain ⟨m1,t2,r2,c2,pc2,ctx2,val2,heap2⟩:=
  half_execution (p:=enabledParameters p true) x lt c (enabledAllocation l c a true) positive constant ha he bank true
   UniformSixCFullProgram.program 187 998 1752 2687 UniformSixCFullProgram.forwardOne_code
   UniformSixCFullProgram.broadcastOne_code UniformSixCFullProgram.inverseOne_code (by omega) (by omega) (by omega) (by omega)
   h1 h1 head1 high1 cursor1.gateCount processed1 ctx1 pc1 r1.final_bound count
 let ff:=writeNat m1 1061 0
 have ffBound:WordBound B ff:=writeNat_bound B m1 1061 0 r2.final_bound (by omega) (by omega)
 have flagFalse:BoundedRuns UniformSixCFullProgram.program n x B m1 1 ff:=.next r2.final_bound
  (by simp [step,pc2,UniformSixCFullProgram.false_at,ff]) (.refl ffBound)
 have headff:BaseHeader lf ff:=flagBaseHeader lt (head1.transport ctx2.static) false
 have highff:UniformSixCDirtyReplayMachine.Header c ff:=dirty_flag (ctx2.high high1) false
 have dd:p.height.D≤p.borrowed:=by
  have:=l.matching.oldRows
  unfold UniformCrossHeightPreparationMachine.rowBase at this;omega
 have sm1:UniformCrossHeightPreparationMachine.Source (enabledParameters p true).height
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program m1:=
  source1.transport (UniformCrossHeightPreparationMachine.cross_size p.height ha he)
   (enabledHeightLayout p.height layout true) (fun j hj=>ctx2.preserved j (by change j<p.borrowed;change j<p.height.D at hj;omega))
 have sff:=source_flag (p:=enabledParameters p true) ha he sm1 false
 obtain ⟨h2,t3,r3,c3,pc3,head2,high2,ctx3,cursor2,source2,processed2,frame2⟩:=
  height_call (p:=enabledParameters p false) x lf c ha he bank UniformSixCFullProgram.program 2688 2874
   UniformSixCFullProgram.heightFalse_code (by omega) (by omega) ff headff highff
   (enabledHeightLayout p.height layout false) budget sff ctx2.present (sources_heap ctx2.sources (show ff.scalarHeap=m1.scalarHeap from rfl)) ctx2.constants
   (by simp [ff,writeNat,next,pc2]) ffBound
 obtain ⟨u,t4,r4,c4,pc4,ctx4,val4,heap4⟩:=
  half_execution (p:=enabledParameters p false) x lf c (enabledAllocation l c a false) positive constant ha he bank false
   UniformSixCFullProgram.program 2874 3685 4439 5374 UniformSixCFullProgram.forwardTwo_code
   UniformSixCFullProgram.broadcastTwo_code UniformSixCFullProgram.inverseTwo_code (by omega) (by omega) (by omega) (by omega)
   h2 h2 head2 high2 cursor2.gateCount processed2 ctx3 pc3 r3.final_bound count
 have stop:BoundedExecution UniformSixCFullProgram.program n x B u 1 u:=.halt r4.final_bound
  (by simp [step,pc4,UniformSixCFullProgram.halt_at])
 refine ⟨u,1+t1+t2+1+t3+t4+1,((((flag.trans r1).trans r2).trans flagFalse).trans r3 |>.trans r4).executes stop,
  ?_,pc4,?_,ctx4.sources,ctx4.constants,ctx4.present,?_,?_,?_,?_⟩
 · change t1≤heightCost p at c1
   change t2≤halfCost p at c2
   change t3≤heightCost p at c3
   change t4≤halfCost p at c4
   omega
 · let first:List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)):=halfWord (p:=enabledParameters p true) lt true ha he
   let second:List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)):=halfWord (p:=enabledParameters p false) lf false ha he
   have concat:fullWord l ha he=first++second:=rfl
   have v1:numeric l.packing.source l.packing.total m1=runShears (first.map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total h1):=val2
   have v2:numeric l.packing.source l.packing.total u=runShears (second.map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total h2):=val4
   have h2num:numeric l.packing.source l.packing.total h2=numeric l.packing.source l.packing.total m1:=numeric_heap _ _ frame2.1
   have h1num:numeric l.packing.source l.packing.total h1=numeric l.packing.source l.packing.total s:=numeric_heap _ _ frame1.1
   rw [concat,List.map_append,runShears_append]
   exact v2.trans ((congrArg (runShears (second.map (ShearCode.eval bank))) h2num).trans
    ((congrArg (runShears (second.map (ShearCode.eval bank))) v1).trans
     (congrArg (fun v=>runShears (second.map (ShearCode.eval bank)) (runShears (first.map (ShearCode.eval bank)) v)) h1num)))
 · exact ctx4.outputs.trans (frame2.2.2.1.trans (ctx2.outputs.trans frame1.2.2.1))
 · exact ctx4.roots.trans (frame2.2.2.2.1.trans (ctx2.roots.trans frame1.2.2.2.1))
 · intro j lo hi
   have e2:=ctx4.static j (Or.inr ⟨lo,hi⟩)
   have e3:=frame2.2.2.2.2 j (by unfold UniformCrossHeightPreparationMachine.Protected UniformCrossDepthReplayPreparation.Protected;omega)
   have e4:=ctx2.static j (Or.inr ⟨lo,hi⟩)
   have e5:=frame1.2.2.2.2 j (by unfold UniformCrossHeightPreparationMachine.Protected UniformCrossDepthReplayPreparation.Protected;omega)
   have nf:ff.natReg j=m1.natReg j:=by simp (disch:=omega) [ff,writeNat,next]
   have nt:f.natReg j=s.natReg j:=by simp (disch:=omega) [f,writeNat,next]
   exact e2.trans (e3.trans (nf.trans (e4.trans (e5.trans nt))))
 · intro j forward inverse
   exact (heap4 j forward inverse).trans ((congrFun frame2.1 j).trans
    ((heap2 j forward inverse).trans (congrFun frame1.1 j)))
end
end ExactFourierCircuits.UniformSixCWholeReplay
