import UniformSixCPhaseLoop
import UniformSixCFullProgram
import UniformSixCReplayDescriptor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCContinuousReplay
open UniformMachine UniformReplayPrint UniformAssembly OAI.ExactFourier
open UniformSixCPhaseContext UniformSixCTraversal UniformSixCLayerStep UniformSixCPhaseLoop UniformSixCReplayDescriptor
open UniformTensorMonomialMachine (setPC)
noncomputable section
lemma broadcast_layout {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c R) : UniformSixCInverseMatchingPreparation.Layout c.inverse p.height.a R B:=by
 let f:=a.inverseZero
 let z:=f.packed
 have ag: p.height.a≤UniformCrossHeightPreparationMachine.gates p.height:=by
  unfold UniformCrossHeightPreparationMachine.gates;nlinarith
 have cap:2*p.height.a≤c.inverse.packing.total:=by rw [a.volume];have:=l.matching.capacity;omega
 have rowBound:c.inverse.packed.rows+3*p.height.a≤B:=by
  change c.inverse.inverseRows+3*p.height.a≤B
  have hb:=c.inverse.packing.rowsBelow
  have hp:=c.inverse.packing.suffixBelow
  have sp:=c.inverse.packing.stackBelow
  have final:=f.packed.inverseBound
  change c.inverse.packing.inverse+c.inverse.packing.total≤B at final
  have hh:=a.permutation
  have h1:=f.permutationBelow;have h2:=f.widthsBelow;have h3:=f.markersBelow
  rw [f.axisRow] at hb
  omega
 let packed:UniformPackedMatchingShearMachine.Layout c.inverse.packed p.height.a R B:=
  ⟨z.coefficient,cap,z.packedFresh,z.destinationFresh,z.disjoint,z.packedBound,z.destinationBound,z.inverseBound,rowBound,z.code⟩
 exact ⟨f.budget,f.oneAxis,f.axisRow,f.radix,by have:=a.inverseRows;omega,
  by have:=a.permutation;omega,f.permutationBelow,f.widthsBelow,f.markersBelow,packed,f.code⟩
lemma broadcast_header {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s:State}
 (head:BaseHeader l origin) (high:UniformSixCDirtyReplayMachine.Header c origin)
 (gates:origin.natReg 1072=UniformCrossHeightPreparationMachine.gates p.height)
 (ctx:Context l c bank origin s) : UniformSixCBroadcast.Header (geometry l.matching) c s:=by
 have low:∀q,UniformSixCDepthColorController.readonly q=true→q≠1191→q≠1192→s.natReg q=origin.natReg q:=
  fun q h d e=>ctx.static q (Or.inl ⟨h,d,e⟩)
 exact ⟨ctx.high high,(low 1181 (by decide) (by decide) (by decide)).trans head.matching.source,
  (low 1052 (by decide) (by decide) (by decide)).trans head.matching.height.inputs,
  (low 1182 (by decide) (by decide) (by decide)).trans head.matching.target,
  (low 1051 (by decide) (by decide) (by decide)).trans head.matching.height.targets,
  (low 1072 (by decide) (by decide) (by decide)).trans gates,
  (low 1183 (by decide) (by decide) (by decide)).trans head.matching.borrowed⟩
lemma numeric_values {R:ℕ} (W:List (ShearCode ℕ R)) (bank:Fin R→ℂ) (base L:ℕ) (s u:State)
 (range:∀row∈W,row.dst<L) (present:Present base L u)
 (val:∀j,j<L→(u.scalarHeap (base+j)).map Scalar.value=some (runShears (W.map (ShearCode.eval bank)) (numeric base L s) j)) :
 numeric base L u=runShears (W.map (ShearCode.eval bank)) (numeric base L s):=by
 funext j
 by_cases hj:j<L
 · obtain ⟨v,hv⟩:=present j hj
   have h:=val j hj
   rw [hv] at h
   simp only [Option.map_some,Option.some.injEq] at h
   simpa only [numeric,data,dite_eq_left hj,hv,Option.getD_some] using h
 · rw [runShears_outside W bank _ range _ j (by omega)]
   simp only [numeric,dite_eq_right hj]

/-- A real signed broadcast: regenerate the borrowed port table and rows, then
execute inverse36/packing/six-C/scatter with its physically generated sign. -/
theorem broadcast_body {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (positive:Bool) (origin s:State) (head:BaseHeader l origin)
 (high:UniformSixCDirtyReplayMachine.Header c origin)
 (gates:origin.natReg 1072=UniformCrossHeightPreparationMachine.gates p.height)
 (ctx:Context l c bank origin s) (pc:s.pc=0) (bound:WordBound B s) (code:754≤B) :
 ∃u t,BoundedExecution (UniformSixCBroadcast.program positive) n x B s t u ∧
 t≤461*p.radix+14*p.height.a+149 ∧ u.pc=753 ∧ Context l c bank origin u ∧
 numeric l.packing.source l.packing.total u=
 runShears ((reverseCode (UniformSixCBroadcast.word positive (geometry l.matching)
  (UniformToeplitzCrossDAG.bankSize p.height.K))).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q):=by
 let g:=geometry l.matching
 let v:=data c.inverse.packing.source c.inverse.packing.total s
 have totals:c.inverse.packing.total=l.packing.total:=a.volume.trans l.volume.symm
 let bl:=broadcast_layout l c a
 have borrow:g.borrowed+g.gates≤c.inverse.forward:=by
  have:=l.matching.borrowFresh;have:=l.matching.selectedFresh;have:=l.matching.ordinalFresh
  change p.borrowed+UniformCrossHeightPreparationMachine.gates p.height≤c.inverse.forward
  rw [a.rows];exact (by omega)
 have source:UniformSectorPackingMachine.SourceReady c.inverse.packing v s:=by
  apply present_ready
  rw [a.source,totals];exact ctx.present
 obtain ⟨t,u,m,cost,run,up,res,highRegs,low,nh,sh,out,root⟩:=UniformSixCBroadcast.execution x positive g c a.volume borrow bl bank v s
  (broadcast_header l c head high gates ctx) ctx.sources ctx.constants source pc bound code
 have ur:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank u:=
  ⟨res.coefficients.positive,res.coefficients.negative,res.coefficients.conjugate,res.coefficients.constants⟩
 have present:Present c.inverse.packing.source c.inverse.packing.total u:=by
  intro j hj;exact ⟨_,res.destination ⟨j,hj⟩⟩
 have pp:Present l.packing.source l.packing.total u:=by simpa only [a.source,totals] using present
 have same:StaticEq s u:=by
  intro q h;rcases h with h|h
  · exact low q h.1
  · exact highRegs q h.1 (by omega)
 have context:Context l c bank origin u:=
  ⟨ctx.static.trans same,fun q hq=>(nh q hq).trans (ctx.preserved q hq),pp,ur,res.constants,
   out.trans ctx.outputs,root.trans ctx.roots⟩
 let W:=UniformSixCBroadcast.word positive g (UniformToeplitzCrossDAG.bankSize p.height.K)
 let hm:=UniformSixCInverseMatchingPreparation.reverse_matching W (UniformSixCBroadcast.word_matching positive g _)
 let hr:=UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W
  (by rw [a.volume];exact UniformSixCBroadcast.word_range positive g _)
 have act:=UniformMatchingActionBridge.inverse_matching_action c.inverse W hm hr bl.radix bank
  (UniformSixCBroadcast.word_good positive g _ p.height.K) v
 have vals:∀j,j<c.inverse.packing.total→(u.scalarHeap (c.inverse.packing.source+j)).map Scalar.value=
  some (runShears ((reverseCode W).map (ShearCode.eval bank)) (numeric c.inverse.packing.source c.inverse.packing.total s) j):=by
  intro j hj
  have destination:=res.destination ⟨j,hj⟩
  change u.scalarHeap (c.inverse.packing.source+j)=some _ at destination
  rw [destination]
  simp only [Option.map_some]
  change some (UniformMatchingActionBridge.unpackValues
   (UniformSixCInverseMatchingPreparation.unpacking c.inverse W hm hr bl.radix)
   (UniformPackedMatchingShearMachine.matchingAction p.height.K bank
    (UniformSixCInverseMatchingPreparation.inverseLabels W) 0 W.length
    (UniformSixCInverseMatchingPreparation.packedInput c.inverse W hm hr bl.radix v)) ⟨j,hj⟩)=_
  rw [act];rfl
 rw [a.source,totals] at vals
 have range:∀row∈reverseCode W,row.dst<l.packing.total:=by
  apply reverse_dest
  apply range_dest
  rw [l.volume]
  exact UniformSixCBroadcast.word_range positive g _
 exact ⟨u,t,run,cost,up,context,numeric_values (reverseCode W) bank _ _ s u range pp vals,sh⟩
def phaseCost (p:UniformChunkMatchingPreparation.Parameters) := ((8*p.height.K+7)*11)*(4*p.height.K+630*p.radix+220)+11

/-- Three actual machine phases in one larger literal program. CodeAt is only
syntactic placement; every heap/header/row/packing contract is derived internally. -/
theorem half_execution {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (a:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positiveAddr:c.inverse.positive=p.height.C) (constantAddr:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ) (positive:Bool)
 (q:UniformMachine.Program) (fbase bbase ibase finish:ℕ)
 (fc:CodeAt (UniformSixCDepthColorController.traversalProgram false) q fbase bbase)
 (bc:CodeAt (UniformSixCBroadcast.program positive) q bbase ibase)
 (ic:CodeAt (UniformSixCDepthColorController.traversalProgram true) q ibase finish)
 (fb:fbase+811≤B) (bb:bbase+754≤B) (ib:ibase+935≤B) (fin:finish≤B)
 (origin s:State) (head:BaseHeader l origin)
 (high:UniformSixCDirtyReplayMachine.Header c origin)
 (gates:origin.natReg 1072=UniformCrossHeightPreparationMachine.gates p.height)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) origin)
 (ctx:Context l c bank origin s) (pc:s.pc=fbase) (bound:WordBound B s)
 (count:(8*p.height.K+7)*11≤B) :
 ∃u t,BoundedRuns q n x B s t u ∧ t≤2*phaseCost p+461*p.radix+14*p.height.a+149 ∧
 u.pc=finish ∧ Context l c bank origin u ∧
 numeric l.packing.source l.packing.total u=
 runShears ((halfWord l positive ha he).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 (∀j,UniformPackedMatchingShearMachine.HeapStable c.forward j→UniformPackedMatchingShearMachine.HeapStable c.inverse.packed j→u.scalarHeap j=s.scalarHeap j):=by
 have bodyCode:918≤B:=by omega
 have fcode:(UniformSixCDepthColorController.traversalProgram false).length≤B:=by
  rw [UniformSixCDepthColorController.traversalProgram_length];simp only [Bool.false_eq_true,ite_false];omega
 have icode:(UniformSixCDepthColorController.traversalProgram true).length≤B:=by
  rw [UniformSixCDepthColorController.traversalProgram_length];simp only [ite_true];omega
 obtain ⟨u1,t1,r1,c1,pc1,ctx1,val1,heap1⟩:=UniformSixCPhaseLoop.execution x l c a positiveAddr constantAddr ha he bank
  false origin (setPC s 0) head high processed (ctx.withPC 0) rfl (changePC_bound B s 0 bound (by omega)) fcode bodyCode count
 have placed1:=UniformBoundedAssembly.boundedExecution_placed fc
  (by simpa only [UniformSixCDepthColorController.traversalProgram_length,Bool.false_eq_true,ite_false] using fb) (by omega) r1
 rw [placed_reset s fbase pc] at placed1
 let b:=setPC u1 bbase
 obtain ⟨u2,t2,r2,c2,pc2,ctx2,val2,heap2⟩:=broadcast_body x l c a bank positive origin (setPC b 0)
  head high gates (ctx1.withPC _ |>.withPC 0) rfl (changePC_bound B b 0 placed1.final_bound (by omega)) (by omega)
 have placed2:=UniformBoundedAssembly.boundedExecution_placed bc
  (by simpa only [UniformSixCBroadcast.program_length] using bb) (by omega) r2
 rw [placed_reset b bbase rfl] at placed2
 let d:=setPC u2 ibase
 obtain ⟨u3,t3,r3,c3,pc3,ctx3,val3,heap3⟩:=UniformSixCPhaseLoop.execution x l c a positiveAddr constantAddr ha he bank
  true origin (setPC d 0) head high processed (ctx2.withPC _ |>.withPC 0) rfl
  (changePC_bound B d 0 placed2.final_bound (by omega)) icode bodyCode count
 have placed3:=UniformBoundedAssembly.boundedExecution_placed ic
  (by simpa only [UniformSixCDepthColorController.traversalProgram_length,ite_true] using ib) fin r3
 rw [placed_reset d ibase rfl] at placed3
 refine ⟨setPC u3 finish,t1+t2+t3,(placed1.trans placed2).trans placed3,?_,rfl,ctx3.withPC _,?_,?_⟩
 · unfold phaseCost;omega
 · change numeric l.packing.source l.packing.total u3=_
   change numeric l.packing.source l.packing.total u1=runShears ((phaseWord l false ha he).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) at val1
   change numeric l.packing.source l.packing.total u2=runShears ((reverseCode (UniformSixCBroadcast.word positive (geometry l.matching) (UniformToeplitzCrossDAG.bankSize p.height.K))).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total u1) at val2
   change numeric l.packing.source l.packing.total u3=runShears ((phaseWord l true ha he).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total u2) at val3
   rw [halfWord,List.map_append,List.map_append,runShears_append,runShears_append,←val1,←val2]
   exact val3
 · intro j f inv
   exact (heap3 j f inv).trans ((heap2 j inv).trans (heap1 j f inv))
end
end ExactFourierCircuits.UniformSixCContinuousReplay
