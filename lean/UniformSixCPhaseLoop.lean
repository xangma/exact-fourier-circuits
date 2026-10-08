import UniformSixCLayerStep
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCPhaseLoop
open UniformMachine UniformReplayPrint UniformAssembly OAI.ExactFourier
open UniformSixCPhaseContext UniformSixCTraversal UniformSixCLayerStep UniformSixCDepthColorController
open UniformTensorMonomialMachine (setPC)
noncomputable section
lemma cursor_transport {K i:ℕ} {s u:State} (h:Cursor K i s)
 (same:∀q,3021≤q→q≤3027→u.natReg q=s.natReg q) : Cursor K i u:=by
 constructor
 · exact (same 3021 (by decide) (by decide)).trans h.index
 · exact (same 3022 (by decide) (by decide)).trans h.one
 · exact (same 3023 (by decide) (by decide)).trans h.eleven
 · exact (same 3027 (by decide) (by decide)).trans h.total
 · exact (same 3026 (by decide) (by decide)).trans h.zero
lemma decoded_context {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s:State}
 (h:Context l c bank origin s) (backwards:Bool) : Context l c bank origin (decoded backwards s):=by
 obtain ⟨nh,sh,out,root⟩:=decoded_heap backwards s
 exact h.transport (decoded_static backwards s) nh sh out root
lemma tick_context {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {origin s:State}
 (h:Context l c bank origin s) (backwards:Bool) : Context l c bank origin (tickState backwards s):=by
 obtain ⟨nh,sh,out,root⟩:=tick_heap backwards s
 exact h.transport (tick_static backwards s) nh sh out root
lemma numeric_heap {s u:State} (base L:ℕ) (heap:u.scalarHeap=s.scalarHeap) :
 numeric base L u=numeric base L s:=by unfold numeric data;rw [heap]
lemma runShears_outside {R:ℕ} (W:List (ShearCode ℕ R)) (bank:Fin R→ℂ) (L:ℕ)
 (range:∀row∈W,row.dst<L) (v:ℕ→ℂ) (j:ℕ) (hj:L≤j) :
 runShears (W.map (ShearCode.eval bank)) v j=v j:=by
 induction W generalizing v with
 | nil=>rfl
 | cons a rest ih=>
   simp only [List.map_cons,runShears_cons]
   rw [ih (fun row mem=>range row (List.mem_cons_of_mem a mem))]
   apply Shear.act_other
   change j≠a.dst
   have:=range a (by simp);omega
lemma range_dest {R L:ℕ} (W:List (ShearCode ℕ R))
 (h:UniformMatchingAxisTableMachine.InRange L (UniformSixCInverseMatchingPreparation.forwardEdges W)) :
 ∀row∈W,row.dst<L:=by
 intro row mem
 obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem mem
 exact (h ⟨i,hi⟩).1
lemma reverse_dest {R L:ℕ} (W:List (ShearCode ℕ R))
 (h:∀row∈W,row.dst<L) : ∀row∈reverseCode W,row.dst<L:=by
 intro row mem
 obtain ⟨a,ha,rfl⟩:=List.mem_map.mp mem
 exact h a (List.mem_reverse.mp ha)
lemma layerWord_range {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (i:Fin ((8*p.height.K+7)*11)) : ∀row∈layerWord l backwards ha he i,row.dst<l.packing.total:=by
 have hr:=UniformSixCDirtyReplayMachine.physicalWord_range
  (atLayout l.matching backwards i.val i.isLt)
  (UniformChunkMatchingPreparation.crossWord (layerParameters p backwards i.val) ha he)
  (UniformChunkMatchingPreparation.cross_domain (layerParameters p backwards i.val) ha he)
 have h:=range_dest _ (show UniformMatchingAxisTableMachine.InRange p.radix _ from hr)
 rw [←l.volume] at h
 cases backwards with
 | false=>exact h
 | true=>exact reverse_dest _ h
lemma body_numeric {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 {x:Fin n→ℂ} {l:UniformMatchingPackingPreparation.Layout p B} {c:UniformSixCDirtyReplayMachine.Config}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ} {backwards:Bool}
 {W:List (ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K))} {origin s u:State} {t:ℕ}
 (res:BodyResult x l c bank backwards W origin s u t) (range:∀row∈W,row.dst<l.packing.total) :
 numeric l.packing.source l.packing.total u=runShears (W.map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s):=by
 funext j
 by_cases hj:j<l.packing.total
 · obtain ⟨v,hv⟩:=res.context.present j hj
   have val:=res.numeric j hj
   rw [hv] at val
   simp only [Option.map_some,Option.some.injEq] at val
   simpa only [numeric,data,dite_eq_left hj,hv,Option.getD_some] using val
 · rw [runShears_outside W bank _ range _ j (by omega)]
   simp only [numeric,dite_eq_right hj]
lemma placed_reset (s:State) (base:ℕ) (pc:s.pc=base) : placed base (setPC s 0)=s:=by
 cases s;simpa only [placed,setPC,Nat.add_zero] using congrArg (fun pc=>State.mk pc _ _ _ _ _ _) pc.symm

/-- One real branch/decode/body/tick cycle. The concrete Height output supplies
its bucket; no layer table, callback or numeric action is an entry premise. -/
theorem iteration {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
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
 (ctx:Context l c bank origin s) (cur:Cursor p.height.K i.val s)
 (pc:s.pc=9) (bound:WordBound B s) (code:(traversalProgram backwards).length≤B) (bodyCode:918≤B) :
 ∃u t,BoundedRuns (traversalProgram backwards) n x B s t u ∧
 t≤4*p.height.K+630*p.radix+220 ∧ u.pc=9 ∧ Cursor p.height.K (i.val+1) u ∧
 Context l c bank origin u ∧
 numeric l.packing.source l.packing.total u=
  runShears ((layerWord l backwards ha he i).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.forward q→
  UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q):=by
 let a:=decoded backwards (setPC s 10)
 obtain ⟨enter,ap,ac⟩:=enter_iteration backwards x s cur i.isLt pc bound code
 have ca:Context l c bank origin (setPC a 0):=(decoded_context (ctx.withPC 10) backwards).withPC 0
 have regs:=decoded_registers backwards (show Cursor p.height.K i.val (setPC s 10) from ⟨cur.index,cur.one,cur.eleven,cur.total,cur.zero⟩)
 obtain ⟨u,t,res⟩:=actual_body x l c allocation positive constants ha he bank backwards i origin
  (setPC a 0) header high processed ca regs.1 regs.2 rfl
  (changePC_bound B a 0 enter.final_bound (Nat.zero_le _)) bodyCode
 have bodyEnd:traversalBodyBase backwards+(traversalBody backwards).length≤B:=by
  rw [traversalProgram_length] at code
  rw [traversalBody_length]
  cases backwards <;> simp_all only [traversalBodyBase,cursorHead_length,Bool.false_eq_true,ite_false,ite_true] <;> omega
 have tickEnd:traversalTickPC backwards≤B:=by exact bodyEnd
 have body:=UniformBoundedAssembly.boundedExecution_placed (traversal_body_code backwards)
  bodyEnd tickEnd res.run
 rw [placed_reset a _ ap] at body
 let z:=setPC u (traversalTickPC backwards)
 have cz:Cursor p.height.K i.val z:=cursor_transport ac res.cursorRegs
 have tick:=tick_execution backwards x z cz i.isLt rfl body.final_bound code
 have all:=enter.trans (body.trans tick)
 have vals:=body_numeric res (layerWord_range l backwards ha he i)
 have pure:numeric l.packing.source l.packing.total (setPC a 0)=numeric l.packing.source l.packing.total s:=
  numeric_heap _ _ (decoded_heap backwards (setPC s 10)).2.1
 refine ⟨tickState backwards z,1+(cursorHead backwards).length+t+2,all,?_,rfl,tick_cursor backwards cz,
  tick_context (res.context.withPC _) backwards,?_,?_⟩
 · have cost:=res.cost
   rw [cursorHead_length]
   cases backwards <;> simp_all only [Bool.false_eq_true,ite_false,ite_true] <;> omega
 · change numeric l.packing.source l.packing.total u=_
   rw [vals,pure]
 · intro q f inv
   change u.scalarHeap q=s.scalarHeap q
   exact (res.heap q f inv).trans (congrArg (fun h=>h q) (decoded_heap backwards (setPC s 10)).2.1)

def suffixWord {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) (i:ℕ) :=
 ((List.finRange ((8*p.height.K+7)*11)).drop i).flatMap (layerWord l backwards ha he)
lemma suffixWord_cons {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (i:Fin ((8*p.height.K+7)*11)) :
 suffixWord l backwards ha he i.val=layerWord l backwards ha he i++suffixWord l backwards ha he (i.val+1):=by
 unfold suffixWord
 rw [List.drop_eq_getElem_cons (by simp only [List.length_finRange];exact i.isLt),List.flatMap_cons]
 congr 2
 exact Fin.ext (by simp only [List.getElem_finRange,Fin.val_cast])
lemma suffixWord_last {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (backwards:Bool)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 suffixWord l backwards ha he ((8*p.height.K+7)*11)=[]:=by
 unfold suffixWord
 rw [List.drop_eq_nil_iff.mpr (by simp only [List.length_finRange];exact Nat.le_refl _),List.flatMap_nil]

/-- Universal bounded outer loop over the actual computed div/mod cursor. -/
theorem remaining {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (allocation:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positive:c.inverse.positive=p.height.C) (constants:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (backwards:Bool) (origin:State)
 (header:BaseHeader l origin)
 (high:UniformSixCDirtyReplayMachine.Header c origin)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) origin)
 (code:(traversalProgram backwards).length≤B) (bodyCode:918≤B)
 (fuel i:ℕ) (total:i+fuel=(8*p.height.K+7)*11) (s:State)
 (ctx:Context l c bank origin s) (cur:Cursor p.height.K i s)
 (pc:s.pc=9) (bound:WordBound B s) :
 ∃u t,BoundedExecution (traversalProgram backwards) n x B s t u ∧
 t≤fuel*(4*p.height.K+630*p.radix+220)+2 ∧ u.pc=traversalHaltPC backwards ∧
 Context l c bank origin u ∧
 numeric l.packing.source l.packing.total u=
  runShears ((suffixWord l backwards ha he i).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.forward q→
  UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q):=by
 induction fuel generalizing i s with
 | zero=>
   have eq:i=(8*p.height.K+7)*11:=by omega
   subst i
   have finish:=finish_iteration backwards x s cur pc bound code
   refine ⟨setPC s (traversalHaltPC backwards),2,finish,by omega,rfl,ctx.withPC _,?_,?_⟩
   · rw [suffixWord_last,List.map_nil,runShears_nil];rfl
   · intro q _ _;rfl
 | succ fuel ih=>
   have hi:i<(8*p.height.K+7)*11:=by omega
   obtain ⟨u,t,step,cost,up,uc,context,value,heap⟩:=iteration x l c allocation positive constants ha he bank
    backwards ⟨i,hi⟩ origin s header high processed ctx cur pc bound code bodyCode
   obtain ⟨v,tt,tail,tc,vp,vc,tv,vh⟩:=ih (i+1) (by omega) u context uc up step.final_bound
   refine ⟨v,t+tt,step.executes tail,?_,vp,vc,?_,?_⟩
   · nlinarith
   · rw [suffixWord_cons l backwards ha he ⟨i,hi⟩,List.map_append,runShears_append,←value]
     exact tv
   · intro q f inv;exact (vh q f inv).trans (heap q f inv)

/-- Complete actual initialized traversal, including boot, every branch and halt. -/
theorem execution {p:UniformChunkMatchingPreparation.Parameters} {B n:ℕ}
 (x:Fin n→ℂ) (l:UniformMatchingPackingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (allocation:Allocation l c (UniformToeplitzCrossDAG.bankSize p.height.K))
 (positive:c.inverse.positive=p.height.C) (constants:c.inverse.constants=p.height.P)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (backwards:Bool) (origin s:State) (header:BaseHeader l origin)
 (high:UniformSixCDirtyReplayMachine.Header c origin)
 (processed:UniformCrossHeightPreparationMachine.Processed p.height c.inverse.negative
  (UniformToeplitzCrossDAG.crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) origin)
 (ctx:Context l c bank origin s) (pc:s.pc=0) (bound:WordBound B s)
 (code:(traversalProgram backwards).length≤B) (bodyCode:918≤B) (count:(8*p.height.K+7)*11≤B) :
 ∃u t,BoundedExecution (traversalProgram backwards) n x B s t u ∧
 t≤((8*p.height.K+7)*11)*(4*p.height.K+630*p.radix+220)+11 ∧
 u.pc=traversalHaltPC backwards ∧ Context l c bank origin u ∧
 numeric l.packing.source l.packing.total u=
  runShears ((phaseWord l backwards ha he).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.forward q→
  UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨boot,ap,ac⟩:=traversal_boot_execution backwards x s ((ctx.static 1050 (Or.inl ⟨by decide,by decide,by decide⟩)).trans header.matching.height.exponent) count pc bound code
 obtain ⟨nh,sh,out,root⟩:=traversal_boot_heap s
 have cc:=ctx.transport (boot_static s) nh sh out root
 obtain ⟨u,t,run,cost,up,context,value,heap⟩:=remaining x l c allocation positive constants ha he bank backwards origin
  header high processed code bodyCode ((8*p.height.K+7)*11) 0 (by omega) _ cc ac ap boot.final_bound
 refine ⟨u,9+t,boot.executes run,by omega,up,context,?_,?_⟩
 · change numeric l.packing.source l.packing.total u=runShears ((suffixWord l backwards ha he 0).map (ShearCode.eval bank)) (numeric l.packing.source l.packing.total s)
   rw [←numeric_heap _ _ sh]
   exact value
 · intro q f inv;exact (heap q f inv).trans (congrArg (fun h=>h q) sh)
end
end ExactFourierCircuits.UniformSixCPhaseLoop
