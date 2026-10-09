import UniformConditionalSectorLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedSectorLoop
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformSameProgramSectorLoop (Cursor boot setup finish assembly)
noncomputable section

/-- This is an explicitly OPEN internal root obligation. It requires actual
bounded execution of the one supplied literal child with all-active prepared tags;
no handler is an instruction and no final DFT result follows without closing it. -/
def RootBody (child:Program) (W n B F reserve:ℕ) (cost:ℕ → ℕ) (x:Fin n → ℂ):Prop:=
 ∀q A (v:ℕ → ℕ → Scalar) (s:State),s.pc=0 → 
 UniformSectorChildEntryPreparation.ChildHeader q A (2^q) F s → s.natReg 4151=0 → 
 UniformProducedSectorChildABI.GroupedSource W A (2^q) v s → 
 3 ≤ A → A+W*2^q ≤ F → F+34*(q+1)+reserve*(q+1)*2^q ≤ B → (2^q)^2 ≤ B → 
 child.length+20 ≤ B → UniformBinaryCStageMachine.Constants s → WordBound B s → 
 (∀r,r < W → ∀j,j < 2^q → (v r j).dependent=false) →
 ∃u ticks,BoundedExecution child n x B s ticks u ∧ticks ≤ cost q ∧
 (∀r,r < W → ∀j:Fin (2^q),(u.scalarHeap (A+r*2^q+j.val)).isSome=true ∧
  (u.scalarHeap (A+r*2^q+j.val)).map Scalar.dependent=some false) ∧
 (∀z,z < F → u.natHeap z=s.natHeap z) ∧
 (∀z,z < F → (z < A ∨A+W*2^q ≤ z) → u.scalarHeap z=s.scalarHeap z) ∧
 (∀z,z=464 ∨(5890 ≤ z ∧z ≤ 5910) → u.natReg z=s.natReg z) ∧
 UniformBinaryCStageMachine.Constants u ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders

abbrev Geometry := UniformConditionalSectorLoop.Geometry

def Table (W E A:ℕ) (xs:List UniformSectorPacking.BlockState) (s:State):Prop:=
 ∀i,∀hi:i < xs.length,UniformSectorBatchDirectoryMachine.BatchCell W E A i (xs[i]'hi) s
def Pending (W A:ℕ) (xs:List UniformSectorPacking.BlockState) (v:ℕ → ℕ → Scalar) (i:ℕ) (s:State):Prop:=
 ∀j,∀hj:j < xs.length,i ≤ j → UniformProducedSectorChildABI.GroupedSource W (A+W*(xs[j]'hj).start)
  (xs[j]'hj).width (UniformAllSectorTransposeMachine.slice v (xs[j]'hj)) s
def Completed (W A:ℕ) (xs:List UniformSectorPacking.BlockState) (_v:ℕ → ℕ → Scalar) (i:ℕ) (s:State):Prop:=
 ∀j,∀hj:j < xs.length,j < i → ∀r,r < W → ∀t:Fin (2^(xs[j]'hj).pairs),
 (s.scalarHeap (A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t.val)).isSome=true ∧
 (s.scalarHeap (A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t.val)).map Scalar.dependent=some false
def budget (cost:ℕ → ℕ) (xs:List UniformSectorPacking.BlockState):ℕ:=
 (xs.map (fun st=>cost st.pairs+12)).sum+2
lemma budget_cons (cost:ℕ → ℕ) (st:UniformSectorPacking.BlockState) (xs:List UniformSectorPacking.BlockState):
 budget cost (st::xs)=cost st.pairs+12+budget cost xs:=by
 simp only[budget,List.map_cons,List.sum_cons];omega
lemma cursor_withPC {M E F i:ℕ} {s:State} (h:Cursor M E F i s) (pc:ℕ):Cursor M E F i (setPC s pc):=
 ⟨h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five⟩
lemma setup_cursor {M E F i:ℕ} {s:State} (h:Cursor M E F i s):Cursor M E F i (applyBlock setup s):=by
 constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five]
lemma root_cursor {M E F i:ℕ} {s u:State} (h:Cursor M E F i s)
 (kept:∀z,z=464 ∨(5890 ≤ z ∧z ≤ 5910) → u.natReg z=s.natReg z):Cursor M E F i u:=by
 constructor
 · exact (kept 5890 (Or.inr ⟨by omega,by omega⟩)).trans h.count
 · exact (kept 5891 (Or.inr ⟨by omega,by omega⟩)).trans h.one
 · exact (kept 5892 (Or.inr ⟨by omega,by omega⟩)).trans h.index
 · exact (kept 5893 (Or.inr ⟨by omega,by omega⟩)).trans h.directory
 · exact (kept 5894 (Or.inr ⟨by omega,by omega⟩)).trans h.fresh
 · exact (kept 5895 (Or.inr ⟨by omega,by omega⟩)).trans h.zero
 · exact (kept 5896 (Or.inr ⟨by omega,by omega⟩)).trans h.five
lemma finish_code (child:Program):BlockAt finish (assembly child) (17+child.length):=by
 have h:=UniformRankCrossPreparationMachine.block_of_segment finish
  (boot.map Op.code++[.branchLT 5892 5890 8 (child.length+19)]++setup.map Op.code++
   child.map (relocate 17 (17+child.length))) [.jump 7,.halt] (17+child.length)
  (by simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
   UniformSameProgramSectorLoop.setup_length,List.length_cons,List.length_nil])
 simpa only[assembly,List.append_assoc] using h
lemma jump_at (child:Program):(assembly child)[18+child.length]?=some (.jump 7):=by
 unfold assembly
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSameProgramSectorLoop.boot_length,UniformSameProgramSectorLoop.setup_length,
  UniformSameProgramSectorLoop.finish_length,List.length_cons,List.length_nil];omega)]
 simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
  UniformSameProgramSectorLoop.setup_length,UniformSameProgramSectorLoop.finish_length,
  List.length_cons,List.length_nil,show 18+child.length-(7+1+9+child.length+1)=0 by omega];rfl
lemma halt_at (child:Program):(assembly child)[19+child.length]?=some .halt:=by
 unfold assembly
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSameProgramSectorLoop.boot_length,UniformSameProgramSectorLoop.setup_length,
  UniformSameProgramSectorLoop.finish_length,List.length_cons,List.length_nil];omega)]
 simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
  UniformSameProgramSectorLoop.setup_length,UniformSameProgramSectorLoop.finish_length,
  List.length_cons,List.length_nil,show 19+child.length-(7+1+9+child.length+1)=1 by omega];rfl
lemma address_fit {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (i:ℕ) (hi:i < xs.length) (r t:ℕ)
 (hr:r < W) (ht:t < (xs[i]'hi).width):A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t < F:=by
 have fit:=g.fits i hi
 have wfit:=Nat.mul_le_mul_left W fit
 have rfit:=Nat.mul_le_mul_right (xs[i]'hi).width (show r+1 ≤ W by omega)
 have bank:=g.bank;nlinarith
lemma separate {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (i j:ℕ) (hi:i < xs.length) (hj:j < xs.length) (ne:j≠i)
 (r t:ℕ) (hr:r < W) (ht:t < (xs[j]'hj).width):
 A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t < A+W*(xs[i]'hi).start ∨
 A+W*(xs[i]'hi).start+W*(xs[i]'hi).width ≤ A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t:=by
 rcases lt_or_gt_of_ne ne with before|after
 · have h:=g.ordered j i hj hi before
   have x:=Nat.mul_le_mul_left W h
   have y:=Nat.mul_le_mul_right (xs[j]'hj).width (show r+1 ≤ W by omega)
   left;nlinarith
 · have h:=g.ordered i j hi hj after
   have x:=Nat.mul_le_mul_left W h
   right;nlinarith
lemma table_transfer {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (s u:State) (old:Table W E A xs s)
 (kept:∀z,z < F → u.natHeap z=s.natHeap z):Table W E A xs u:=by
 intro i hi
 rcases old i hi with ⟨h0,h1,h2,h3,h4⟩
 have bound:=g.directory
 exact ⟨(kept _ (by omega)).trans h0,(kept _ (by omega)).trans h1,
  (kept _ (by omega)).trans h2,(kept _ (by omega)).trans h3,(kept _ (by omega)).trans h4⟩
lemma completed_step {W B F reserve A E i:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (hi:i < xs.length) (v:ℕ → ℕ → Scalar) (s u:State)
 (old:Completed W A xs v i s)
 (fresh:∀r,r < W → ∀t:Fin (2^(xs[i]'hi).pairs),
  (u.scalarHeap (A+W*(xs[i]'hi).start+r*2^(xs[i]'hi).pairs+t.val)).isSome=true ∧
  (u.scalarHeap (A+W*(xs[i]'hi).start+r*2^(xs[i]'hi).pairs+t.val)).map Scalar.dependent=some false)
 (out:∀z,z < F → (z < A+W*(xs[i]'hi).start ∨A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs ≤ z) → 
  u.scalarHeap z=s.scalarHeap z):Completed W A xs v (i+1) u:=by
 intro j hj less r hr t
 by_cases eq:j=i
 · subst j
   simpa only[g.pow i hi] using fresh r hr t
 · have before:j < i:=by omega
   have ht:t.val < (xs[j]'hj).width:=by rw[g.pow j hj];exact t.isLt
   have h: u.scalarHeap (A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t.val)=
    s.scalarHeap (A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t.val):=out _ (address_fit g j hj r t.val hr ht)
     (by rw[←g.pow i hi];exact separate g i j hi hj eq r t.val hr ht)
   rw[h]
   exact old j hj before r hr t
lemma pending_step {W B F reserve A E i:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (hi:i < xs.length) (v:ℕ → ℕ → Scalar) (s u:State)
 (old:Pending W A xs v i s)
 (out:∀z,z < F → (z < A+W*(xs[i]'hi).start ∨A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs ≤ z) → 
  u.scalarHeap z=s.scalarHeap z):Pending W A xs v (i+1) u:=by
 intro j hj after r hr t ht
 exact (out _ (address_fit g j hj r t hr ht)
  (by rw[←g.pow i hi];exact separate g i j hi hj (by omega) r t hr ht)).trans
  (old j hj (by omega) r hr t ht)

def tick (child:Program) (s:State):State:=setPC
 (writeNat (setPC s (17+child.length)) 5892 (s.natReg 5892+s.natReg 5891)) 7
lemma tick_cursor {M E F i:ℕ} (child:Program) (s:State) (h:Cursor M E F i s):
 Cursor M E F (i+1) (tick child s):=by
 constructor <;>simp[tick,setPC,writeNat,next,h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five]
lemma global_separate {W B F reserve A E i:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (hi:i < xs.length) (z:ℕ) (outside:z < A ∨A+W*g.volume ≤ z):
 z < A+W*(xs[i]'hi).start ∨A+W*(xs[i]'hi).start+W*(xs[i]'hi).width ≤ z:=by
 have fits:=Nat.mul_le_mul_left W (g.fits i hi)
 rcases outside with h|h
 · left;omega
 · right;nlinarith

/-- One actual branch,9 generated row reads/root header moves,one execution
of the SAME child at its fixed site,and the charged increment/backedge.
The RootBody premise remains the explicitly named unclosed obligation. -/
theorem iteration {W B F reserve A E n i:ℕ} {xs:List UniformSectorPacking.BlockState}
 (child:Program) (g:Geometry W B F reserve A E xs) (cost:ℕ → ℕ) (v:ℕ → ℕ → Scalar)
 (x:Fin n → ℂ) (s:State) (hi:i < xs.length) (root:RootBody child W n B F reserve cost x)
 (prepared:∀r,r < W→∀j,j < g.volume→(v r j).dependent=false)
 (control:Cursor xs.length E F i s) (table:Table W E A xs s)
 (pending:Pending W A xs v i s) (done:Completed W A xs v i s)
 (constants:UniformBinaryCStageMachine.Constants s) (code:child.length+20 ≤ B)
 (pc:s.pc=7) (wb:WordBound B s):∃u ticks,
 BoundedRuns (assembly child) n x B s ticks u ∧ticks ≤ cost (xs[i]'hi).pairs+12 ∧u.pc=7 ∧
 Cursor xs.length E F (i+1) u ∧Table W E A xs u ∧Pending W A xs v (i+1) u ∧Completed W A xs v (i+1) u ∧
 UniformBinaryCStageMachine.Constants u ∧
 (∀z,z < F → u.natHeap z=s.natHeap z) ∧
 (∀z,z < F → (z < A ∨A+W*g.volume ≤ z) → u.scalarHeap z=s.scalarHeap z) ∧
 u.natReg 464=s.natReg 464 ∧
 (∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let entered:=setPC s 8
 have eb:=changePC_bound B s 8 wb (by omega)
 have branch:BoundedRuns (assembly child) n x B s 1 entered:=.next wb
  (by simp[step,pc,UniformSameProgramSectorLoop.branch_at,control.index,control.count,hi,entered,setPC]) (.refl eb)
 have baseBound:A+W*(xs[i]'hi).start ≤ B:=by
  have fit:=g.fits i hi;have bank:=g.bank;have fb:=g.frontier;nlinarith
 have safe:=UniformSameProgramSectorLoop.setup_safe (xs[i]'hi) (cursor_withPC control 8) hi
  (g.directory.trans g.frontier) (table i hi) (g.qBound i hi) (g.widthBound i hi) baseBound g.frontier
 have setupRun:=block_runs setup (assembly child) 8 n B x entered (UniformSameProgramSectorLoop.setup_code child)
  rfl eb (by rw[UniformSameProgramSectorLoop.setup_length];omega) safe.1 safe.2
 let entry:=setPC (applyBlock setup entered) 0
 have entryB:=changePC_bound B (applyBlock setup entered) 0 setupRun.final_bound (by omega)
 have raw:=UniformSameProgramSectorLoop.setup_header (xs[i]'hi) (cursor_withPC control 8) (table i hi)
 have header:UniformSectorChildEntryPreparation.ChildHeader (xs[i]'hi).pairs (A+W*(xs[i]'hi).start)
  (2^(xs[i]'hi).pairs) F entry:=by
  rw[←g.pow i hi]
  exact ⟨raw.1.exponent,raw.1.base,raw.1.width,raw.1.frontier⟩
 have grouped:UniformProducedSectorChildABI.GroupedSource W (A+W*(xs[i]'hi).start)
  (2^(xs[i]'hi).pairs) (UniformAllSectorTransposeMachine.slice v (xs[i]'hi)) entry:=by
  rw[←g.pow i hi]
  exact pending i hi (by omega)
 have bank:A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs ≤ F:=by
  rw[←g.pow i hi]
  have fit:=Nat.mul_le_mul_left W (g.fits i hi);have b:=g.bank;nlinarith
 obtain ⟨t,steps,childRun,cheap,values,nat,scalar,kept,newConstants,outputs,roots⟩:=root (xs[i]'hi).pairs
  (A+W*(xs[i]'hi).start) (UniformAllSectorTransposeMachine.slice v (xs[i]'hi)) entry rfl header raw.2 grouped
  (by have:=g.low;omega) bank (g.room i hi) (g.square i hi) code constants entryB (by
   intro r hr j hj
   dsimp only[UniformAllSectorTransposeMachine.slice]
   apply prepared r hr
   have fit:=g.fits i hi
   have width:=g.pow i hi
   omega)
 have moved:=UniformBoundedAssembly.boundedExecution_placed (UniformSameProgramSectorLoop.child_code child)
  (by omega) (by omega) childRun
 have atChild:placed 17 entry=applyBlock setup entered:=by
  have hp:(applyBlock setup entered).pc=17:=by rw[applyBlock_pc];rfl
  exact UniformMultiAxisSectorMetadataPreparation.placed_zero _ _ hp
 rw[atChild] at moved
 have cursor:=root_cursor (setup_cursor (cursor_withPC control 8)) kept
 have tableT:=table_transfer g entry t table nat
 have pendingT:=pending_step g hi v entry t pending scalar
 have doneT:=completed_step g hi v entry t done values scalar
 let ready:=setPC t (17+child.length)
 have readyCursor:Cursor xs.length E F i ready:=cursor_withPC cursor _
 have countBound:xs.length ≤ B:=by have:=g.directory;have:=g.frontier;omega
 have fsafe:readable finish ready ∧peak finish ready ≤ B:=by
  simp[finish,readable,peak,Op.readable,Op.peak,readyCursor.index,readyCursor.one];omega
 have finishRun:=block_runs finish (assembly child) (17+child.length) n B x ready (finish_code child)
  rfl moved.final_bound (by rw[UniformSameProgramSectorLoop.finish_length];omega) fsafe.1 fsafe.2
 let after:=applyBlock finish ready
 have afterPC:after.pc=18+child.length:=by
  rw[applyBlock_pc];simp only[ready,setPC,UniformSameProgramSectorLoop.finish_length];omega
 have same:tick child t=setPC after 7:=by
  simp[tick,after,ready,finish,applyBlock,Op.apply,setPC,writeNat,next]
 have back:BoundedRuns (assembly child) n x B after 1 (tick child t):=by
  rw[same]
  exact .next finishRun.final_bound (by rw[step,afterPC,jump_at];rfl)
   (.refl (changePC_bound B after 7 finishRun.final_bound (by omega)))
 refine ⟨tick child t,1+(9+(steps+(1+1))),?_,by omega,rfl,tick_cursor child t cursor,
  tableT,pendingT,doneT,newConstants,nat,?_,?_,?_,outputs,roots⟩
 · simpa only[UniformSameProgramSectorLoop.setup_length,UniformSameProgramSectorLoop.finish_length] using
    branch.trans (setupRun.trans (moved.trans (finishRun.trans back)))
 · intro z hz outside
   exact scalar z hz (by rw[←g.pow i hi];exact global_separate g hi z outside)
 · exact (kept 464 (Or.inl rfl)).trans (by simp[entry,entered,setup,applyBlock,Op.apply,setPC,writeNat,next])
 · intro q lo hi
   have k:=kept q (Or.inr ⟨by omega,hi⟩)
   simpa (disch:=omega) [tick,entry,entered,setup,applyBlock,Op.apply,setPC,writeNat,next] using k
lemma stop {B n M E F:ℕ} (child:Program) (x:Fin n → ℂ) (s:State)
 (h:Cursor M E F M s) (pc:s.pc=7) (wb:WordBound B s) (code:child.length+20 ≤ B):
 BoundedExecution (assembly child) n x B s 2 (setPC s (19+child.length)):=by
 let u:=setPC s (19+child.length)
 have ub:=changePC_bound B s (19+child.length) wb (by omega)
 have last:BoundedExecution (assembly child) n x B u 1 u:=.halt ub
  (by simp[step,u,setPC,halt_at])
 exact .next wb (by simp[step,pc,UniformSameProgramSectorLoop.branch_at,h.index,h.count,u,setPC,
  Nat.add_comm child.length 19]) last

/-- Complete actual finite traversal, conditional ONLY on the named root
execution obligation. Every row load, child call, branch and return is charged. -/
theorem loop (remaining:List UniformSectorPacking.BlockState)
 {W B F reserve A E n:ℕ} {xs:List UniformSectorPacking.BlockState}
 (child:Program) (g:Geometry W B F reserve A E xs) (cost:ℕ → ℕ) (v:ℕ → ℕ → Scalar) (x:Fin n → ℂ)
 (root:RootBody child W n B F reserve cost x) (code:child.length+20 ≤ B)
 (prepared:∀r,r < W→∀j,j < g.volume→(v r j).dependent=false):
 ∀i s,i ≤ xs.length → xs.drop i=remaining → s.pc=7 → WordBound B s → 
 Cursor xs.length E F i s → Table W E A xs s → Pending W A xs v i s → Completed W A xs v i s → 
 UniformBinaryCStageMachine.Constants s → ∃u ticks,
 BoundedExecution (assembly child) n x B s ticks u ∧ticks ≤ budget cost remaining ∧u.pc=19+child.length ∧
 Cursor xs.length E F xs.length u ∧Table W E A xs u ∧Completed W A xs v xs.length u ∧
 UniformBinaryCStageMachine.Constants u ∧
 (∀z,z < F → u.natHeap z=s.natHeap z) ∧
 (∀z,z < F → (z < A ∨A+W*g.volume ≤ z) → u.scalarHeap z=s.scalarHeap z) ∧
 u.natReg 464=s.natReg 464 ∧
 (∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 induction remaining with
 | nil=>
  intro i s le suffix pc wb control table pending done constants
  have length:=congrArg List.length suffix
  simp only[List.length_drop,List.length_nil] at length
  have eq:i=xs.length:=by omega
  subst i
  exact ⟨setPC s (19+child.length),2,stop child x s control pc wb code,by simp[budget],rfl,
   cursor_withPC control _,table,done,constants,fun _ _=>rfl,fun _ _ _=>rfl,rfl,fun _ _ _=>rfl,rfl,rfl⟩
 | cons st remaining ih=>
  intro i s le suffix pc wb control table pending done constants
  have length:=congrArg List.length suffix
  simp only[List.length_drop,List.length_cons] at length
  have hi:i < xs.length:=by omega
  obtain ⟨equal,tail⟩:=List.cons.inj (suffix.symm.trans (List.drop_eq_getElem_cons hi))
  subst st
  obtain ⟨t,steps,first,cheap,tp,tc,tt,pt,dt,ct,nt,st,num,saved,out,roots⟩:=
   iteration child g cost v x s hi root prepared control table pending done constants code pc wb
  obtain ⟨u,ticks,last,costTail,up,uc,ut,du,cu,nu,su,countU,savedU,outsU,rootsU⟩:=ih (i+1) t (by omega)
   tail.symm tp first.final_bound tc tt pt dt ct
  refine ⟨u,steps+ticks,first.executes last,?_,up,uc,ut,du,cu,?_,?_,countU.trans num,?_,outsU.trans out,rootsU.trans roots⟩
  · rw[budget_cons];omega
  · intro z hz;exact (nu z hz).trans (nt z hz)
  · intro z hz outside;exact (su z hz outside).trans (st z hz outside)
  · intro q lo hi;exact (savedU q lo hi).trans (saved q lo hi)

/-- Additive prepared-tag sector-loop invariant. Its internal RootBody must be
closed by the actual recursive all-active prepared-tag supplement. It asserts
no numerical cancellation or per-role independence of dependency flags. -/
theorem execution {W B F reserve A E n:ℕ} {xs:List UniformSectorPacking.BlockState}
 (child:Program) (g:Geometry W B F reserve A E xs) (cost:ℕ → ℕ) (v:ℕ → ℕ → Scalar)
 (x:Fin n → ℂ) (s:State) (root:RootBody child W n B F reserve cost x)
 (prepared:∀r,r < W→∀j,j < g.volume→(v r j).dependent=false)
 (code:child.length+20 ≤ B) (table:Table W E A xs s) (source:Pending W A xs v 0 s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (count:s.natReg 464=xs.length) (dir:s.natReg 4441=E) (fresh:s.natReg 5801=F)
 (pc:s.pc=0) (wb:WordBound B s):∃u ticks,
 BoundedExecution (assembly child) n x B s ticks u ∧ticks ≤ budget cost xs+7 ∧u.pc=19+child.length ∧
 Completed W A xs v xs.length u ∧Table W E A xs u ∧UniformBinaryCStageMachine.Constants u ∧
 (∀z,z < F → u.natHeap z=s.natHeap z) ∧
 (∀z,z < F → (z < A ∨A+W*g.volume ≤ z) → u.scalarHeap z=s.scalarHeap z) ∧
 u.natReg 464=xs.length ∧
 (∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 have safe:=UniformSameProgramSectorLoop.boot_safe wb (by omega)
 have bootRun:=block_runs boot (assembly child) 0 n B x s (UniformSameProgramSectorLoop.boot_code child)
  pc wb (by rw[UniformSameProgramSectorLoop.boot_length];omega) safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=7:=by rw[applyBlock_pc,pc,UniformSameProgramSectorLoop.boot_length]
 have control:=UniformSameProgramSectorLoop.boot_cursor xs.length E F s count dir fresh
 have empty:Completed W A xs v 0 a:=by intro j hj h;omega
 obtain ⟨u,ticks,tail,cheap,up,uc,ut,done,cu,nu,su,num,saved,outputs,roots⟩:=loop xs child g cost v x root code prepared
  0 a (by omega) (by simp) ap bootRun.final_bound control table source empty constants
 refine ⟨u,7+ticks,?_,by omega,up,done,ut,cu,nu,su,?_,?_,outputs,roots⟩
 · simpa only[UniformSameProgramSectorLoop.boot_length] using bootRun.executes tail
 · exact num.trans (by simpa[a,boot,applyBlock,Op.apply,writeNat,next] using count)
 · intro q lo hi
   exact (saved q lo hi).trans (by simp (disch:=omega) [a,boot,applyBlock,Op.apply,writeNat,next])
end
end ExactFourierCircuits.UniformPreparedSectorLoop
