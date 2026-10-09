import UniformScalarCopyMachine
import UniformSectorBatchDirectoryMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPaddingMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine
noncomputable section
/-- Nat4460=width,4461=present packed source,4462=fresh W-role buffer.
Only role0 is copied; the remaining roles are physically filled with prepared0.
Padding is performed once outside the recursive residual transforms. -/
def copySetup (W:ℕ):List Op:=[.literal 4464 0,.literal 4465 W,
 .add 147 4460 4464,.add 148 4461 4464,.add 149 4462 4464]
def zeroSetup:List Op:=[.literalScalar 126 0,.add 4467 4460 4464,
 .mul 4468 4465 4460,.literal 4469 1]
def body:List Op:=[.add 4470 4462 4467,.putScalar 4470 126,.add 4467 4467 4469]
def programFor (W:ℕ):Program:=(copySetup W).map Op.code++
 UniformScalarCopyMachine.program.map (relocate 5 15)++zeroSetup.map Op.code++
 [.branchLT 4467 4468 20 24]++body.map Op.code++[.jump 19,.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=25:=rfl
lemma copySetup_code (W:ℕ):BlockAt (copySetup W) (programFor W) 0:=by
 intro i hi;change i  <  5 at hi;interval_cases i <;>rfl
lemma copy_code (W:ℕ):CodeAt UniformScalarCopyMachine.program (programFor W) 5 15:=by
 exact UniformRankCrossPreparationMachine.segment_code ((copySetup W).map Op.code)
  (zeroSetup.map Op.code++[.branchLT 4467 4468 20 24]++body.map Op.code++[.jump 19,.halt])
  _ 5 15 rfl
lemma zeroSetup_code (W:ℕ):BlockAt zeroSetup (programFor W) 15:=by
 intro i hi;change i  <  4 at hi;interval_cases i <;>rfl
lemma body_code (W:ℕ):BlockAt body (programFor W) 20:=by
 intro i hi;change i  <  3 at hi;interval_cases i <;>rfl
lemma branch_at (W:ℕ):(programFor W)[19]?=some (.branchLT 4467 4468 20 24):=rfl
lemma jump_at (W:ℕ):(programFor W)[23]?=some (.jump 19):=rfl
lemma halt_at (W:ℕ):(programFor W)[24]?=some .halt:=rfl
structure Header (L a d:ℕ) (s:State):Prop where
 width:s.natReg 4460=L
 source:s.natReg 4461=a
 target:s.natReg 4462=d
structure Cursor (W L a d i:ℕ) (s:State):Prop where
 header:Header L a d s
 zero:s.natReg 4464=0
 roles:s.natReg 4465=W
 index:s.natReg 4467=i
 total:s.natReg 4468=W*L
 one:s.natReg 4469=1
 prepared:s.scalarReg 126=⟨0,false⟩
def padAt {L:ℕ} (v:Fin L  →  Scalar) (i:ℕ):Scalar:=if hi:i  <  L then v ⟨i,hi⟩ else ⟨0,false⟩
def Prefix {L:ℕ} (v:Fin L  →  Scalar) (d i:ℕ) (s:State):Prop:=
 ∀ j,j  <  i  →  s.scalarHeap (d+j)=some (padAt v j)
def Source {L:ℕ} (v:Fin L  →  Scalar) (a:ℕ) (s:State):Prop:=
 ∀ j:Fin L,s.scalarHeap (a+j.val)=some (v j)
def Outside (d total:ℕ) (s u:State):Prop:=
 ∀ q,(q  <  d ∨d+total  ≤  q)  →  u.scalarHeap q=s.scalarHeap q
def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32  →  q≠126  →  u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q  <  147 ∨154  ≤  q)  →  (q  <  4464 ∨4471  ≤  q)  →  u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq hj=>(k.2.2.2.1 q hq hj).trans (h.2.2.2.1 q hq hj),
 fun q hq hj=>(k.2.2.2.2 q hq hj).trans (h.2.2.2.2 q hq hj)⟩
lemma Cursor.withPC {W L a d i pc:ℕ} {s:State} (h:Cursor W L a d i s):
 Cursor W L a d i (setPC s pc):=
 ⟨⟨h.header.width,h.header.source,h.header.target⟩,h.zero,h.roles,h.index,h.total,h.one,h.prepared⟩

def nextState (s:State):State:=setPC (applyBlock body (setPC s 20)) 19
lemma body_cursor {W L a d i:ℕ} {s:State} (h:Cursor W L a d i s):
 Cursor W L a d (i+1) (nextState s):=by
 rcases h with ⟨⟨hl,ha,hd⟩,h0,hr,hi,ht,h1,hs⟩
 constructor
 · constructor <;> simp[nextState,body,applyBlock,Op.apply,writeNat,next,setPC,hl,ha,hd]
 all_goals simp[nextState,body,applyBlock,Op.apply,writeNat,next,setPC,h0,hr,hi,ht,h1,hs]
lemma body_heap {W L a d i:ℕ} {s:State} (h:Cursor W L a d i s):
 (nextState s).scalarHeap=Function.update s.scalarHeap (d+i) (some ⟨0,false⟩):=by
 simp[nextState,body,applyBlock,Op.apply,writeNat,next,setPC,h.header.target,h.index,h.prepared]
lemma body_frame (s:State):Frame s (nextState s):=by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · intro q hq hj;rfl
 · intro q hq hj
   simp (disch:=omega) [nextState,body,applyBlock,Op.apply,writeNat,next,setPC]
lemma body_prefix {W L a d i:ℕ} {v:Fin L  →  Scalar} {s:State}
 (h:Cursor W L a d i s) (hi:L  ≤  i) (old:Prefix v d i s):Prefix v d (i+1) (nextState s):=by
 intro j hj
 rw[body_heap h]
 by_cases eq:j=i
 · subst j;simp[padAt,show ¬i  <  L by omega]
 · rw[Function.update_of_ne (by omega)]
   exact old j (by omega)
lemma body_outside {W L a d i total:ℕ} {s:State} (h:Cursor W L a d i s) (hi:i  <  total):
 Outside d total s (nextState s):=by
 intro q hq
 rw[body_heap h,Function.update_of_ne (by rcases hq with hq|hq <;>omega)]
lemma iteration {W L a d i B n:ℕ} {s:State} (h:Cursor W L a d i s)
 (hi:i  <  W*L) (fit:d+W*L  ≤  B) (code:25  ≤  B) (x:Fin n  →  ℂ) (pc:s.pc=19) (wb:WordBound B s):
 BoundedRuns (programFor W) n x B s 5 (nextState s):=by
 let e:=setPC s 20
 have eb:=changePC_bound B s 20 wb (by omega)
 have first:BoundedRuns (programFor W) n x B s 1 e:=
  .next wb (by simp[step,pc,branch_at,h.index,h.total,hi,e,setPC]) (.refl eb)
 have safe:readable body e ∧peak body e  ≤  B:=by
  simp[readable,peak,body,Op.readable,Op.peak,Op.apply,writeNat,next,e,setPC,
   h.header.target,h.index,h.one]
  omega
 have run:=block_runs body (programFor W) 20 n B x e (body_code W) rfl eb
  (by change 20+3  ≤  B;omega) safe.1 safe.2
 have endPC:(applyBlock body e).pc=23:=by rw[applyBlock_pc];rfl
 have jump:BoundedRuns (programFor W) n x B (applyBlock body e) 1 (nextState s):=
  .next run.final_bound (by rw[step,endPC,jump_at];rfl)
   (.refl (changePC_bound B _ 19 run.final_bound (by omega)))
 simpa only[show body.length=3 from rfl] using first.trans (run.trans jump)

lemma loop (fuel:ℕ) {W L a d B n:ℕ} (v:Fin L  →  Scalar) (x:Fin n  →  ℂ)
 (fit:d+W*L  ≤  B) (code:25  ≤  B):
 ∀ i s,i+fuel=W*L  →  L  ≤  i  →  s.pc=19  →  WordBound B s  →  Cursor W L a d i s  →  Prefix v d i s  →  
 ∃u,BoundedExecution (programFor W) n x B s (5*fuel+2) u ∧u.pc=24 ∧
 Prefix v d (W*L) u ∧Frame s u ∧Outside d (W*L) s u:=by
 induction fuel with
 | zero=>
   intro i s len lower pc wb h written
   have last:i=W*L:=by omega
   let u:=setPC s 24
   have ub:=changePC_bound B s 24 wb (by omega)
   have first:BoundedRuns (programFor W) n x B s 1 u:=
    .next wb (by simp[step,pc,branch_at,h.index,h.total,last,u,setPC]) (.refl ub)
   have stop:BoundedExecution (programFor W) n x B u 1 u:=
    .halt ub (by simp[step,u,setPC,halt_at])
   refine ⟨u,?_,rfl,?_,Frame.refl s,fun _ _=>rfl⟩
   · simpa only[Nat.mul_zero,Nat.zero_add] using first.executes stop
   · simpa only[Prefix,u,setPC,last] using written
 | succ fuel ih=>
   intro i s len lower pc wb h written
   have hi:i  <  W*L:=by omega
   have run:=iteration h hi fit code x pc wb
   obtain ⟨u,rest,up,full,frame,out⟩:=ih (i+1) (nextState s) (by omega) (by omega)
    rfl run.final_bound (body_cursor h) (body_prefix h lower written)
   refine ⟨u,?_,up,full,(body_frame s).trans frame,?_⟩
   · convert run.executes rest using 1
     omega
   · intro q hq
     exact (out q hq).trans (body_outside h hi q hq)

lemma copySetup_frame (W:ℕ) (s:State):Frame s (applyBlock (copySetup W) s):=by
 refine ⟨rfl,rfl,rfl,fun _ _ _=>rfl,?_⟩
 intro q hq hj
 simp (disch:=omega) [copySetup,applyBlock,Op.apply,writeNat,next]
lemma copySetup_args {W L a d:ℕ} {s:State} (h:Header L a d s):
 (applyBlock (copySetup W) s).natReg 147=L ∧
 (applyBlock (copySetup W) s).natReg 148=a ∧
 (applyBlock (copySetup W) s).natReg 149=d:=by
 simp[copySetup,applyBlock,Op.apply,writeNat,next,h.width,h.source,h.target]
lemma copySetup_fixed {W L a d:ℕ} {s:State} (h:Header L a d s):
 Header L a d (applyBlock (copySetup W) s) ∧
 (applyBlock (copySetup W) s).natReg 4464=0 ∧
 (applyBlock (copySetup W) s).natReg 4465=W:=by
 refine ⟨?_,?_,?_⟩
 · constructor <;> simp[copySetup,applyBlock,Op.apply,writeNat,next,h.width,h.source,h.target]
 all_goals simp[copySetup,applyBlock,Op.apply,writeNat,next]
lemma copySetup_safe {W L a d B:ℕ} {s:State} (h:Header L a d s)
 (roles:W  ≤  B) (wb:WordBound B s):readable (copySetup W) s ∧peak (copySetup W) s  ≤  B:=by
 have hl:L  ≤  B:=by simpa only[h.width] using wb.2.1 4460
 have ha:a  ≤  B:=by simpa only[h.source] using wb.2.1 4461
 have hd:d  ≤  B:=by simpa only[h.target] using wb.2.1 4462
 simp[copySetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.width,h.source,h.target]
 omega
lemma zeroSetup_cursor {W L a d:ℕ} {s:State} (h:Header L a d s)
 (zero:s.natReg 4464=0) (roles:s.natReg 4465=W):
 Cursor W L a d L (applyBlock zeroSetup s):=by
 constructor
 · constructor <;> simp[zeroSetup,applyBlock,Op.apply,writeScalar,writeNat,next,h.width,h.source,h.target]
 all_goals simp[zeroSetup,applyBlock,Op.apply,writeScalar,writeNat,next,zero,roles,h.width]
lemma zeroSetup_frame (s:State):Frame s (applyBlock zeroSetup s):=by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · intro q hq hj;simp[zeroSetup,applyBlock,Op.apply,writeNat,writeScalar,next,hj]
 · intro q hq hj
   simp (disch:=omega) [zeroSetup,applyBlock,Op.apply,writeNat,writeScalar,next]
lemma zeroSetup_safe {W L a d B:ℕ} {s:State} (h:Header L a d s)
 (zero:s.natReg 4464=0) (roles:s.natReg 4465=W) (fit:d+W*L  ≤  B)
 (code:25  ≤  B) (wb:WordBound B s):readable zeroSetup s ∧peak zeroSetup s  ≤  B:=by
 have hl:L  ≤  B:=by simpa only[h.width] using wb.2.1 4460
 simp[zeroSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeScalar,writeNat,next,h.width,zero,roles]
 omega

/-- One real W-role-major child input. Arbitrary original Scalar tags are
preserved in role0; every padding cell is actually written as prepared0.
The copy, preparation, stores, loop branches and halt are charged. -/
theorem execution {W L a d B n:ℕ} (v:Fin L → Scalar) (x:Fin n → ℂ) (s:State)
 (h:Header L a d s) (source:Source v a s) (positive:0 < W) (roles:W  ≤  B)
 (sep:a+L  ≤  d) (fit:d+W*L  ≤  B) (code:25  ≤  B) (pc:s.pc=0) (wb:WordBound B s):
 ∃u,BoundedExecution (programFor W) n x B s (5*(W*L)+2*L+15) u ∧u.pc=24 ∧
 Prefix v d (W*L) u ∧Frame s u ∧Outside d (W*L) s u ∧
 (∀j:Fin L,u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)):=by
 have enough:L  ≤  W*L:=by nlinarith
 have safe:=copySetup_safe h roles wb
 have first:=block_runs (copySetup W) (programFor W) 0 n B x s (copySetup_code W) pc wb
  (by change 0+5  ≤  B;omega) safe.1 safe.2
 let ready:=setPC (applyBlock (copySetup W) s) 0
 have rb:=changePC_bound B (applyBlock (copySetup W) s) 0 first.final_bound (by omega)
 have args:=copySetup_args (W:=W) h
 have src:UniformScalarCopyMachine.Source L a ready.scalarHeap:=by
  intro j hj
  exact ⟨v ⟨j,hj⟩,source ⟨j,hj⟩⟩
 obtain ⟨c,copyRun,copied,_sourceKept,copyOut,copyFrame,copyNat⟩:=
  UniformScalarCopyMachine.execution n x L a d B ready src sep (by omega) (by omega)
   rfl args.1 args.2.1 args.2.2 rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (copy_code W)
  (by rw[UniformScalarCopyMachine.program_length];omega) (by omega) copyRun
 have firstPC:(applyBlock (copySetup W) s).pc=5:=by rw[applyBlock_pc,pc];rfl
 rw[show placed 5 ready=applyBlock (copySetup W) s by
  cases e:applyBlock (copySetup W) s
  simp_all[ready,setPC,placed]] at moved
 let afterCopy:=setPC c 15
 have fixed:=copySetup_fixed (W:=W) h
 have hc:Header L a d afterCopy:=
  ⟨(copyNat 4460 (by omega)).trans fixed.1.width,
   (copyNat 4461 (by omega)).trans fixed.1.source,
   (copyNat 4462 (by omega)).trans fixed.1.target⟩
 have hz:afterCopy.natReg 4464=0:=(copyNat 4464 (by omega)).trans fixed.2.1
 have hr:afterCopy.natReg 4465=W:=(copyNat 4465 (by omega)).trans fixed.2.2
 have zs:=zeroSetup_safe hc hz hr fit code moved.final_bound
 have zeros:=block_runs zeroSetup (programFor W) 15 n B x afterCopy (zeroSetup_code W) rfl
  moved.final_bound (by change 15+4  ≤  B;omega) zs.1 zs.2
 let b:=applyBlock zeroSetup afterCopy
 have bp:b.pc=19:=by rw[applyBlock_pc];rfl
 have initial:Prefix v d L b:=by
  intro j hj
  change c.scalarHeap (d+j)=some (padAt v j)
  rw[copied j hj]
  simpa only[padAt,dite_eq_left hj,ready,setPC,copySetup,applyBlock,Op.apply,writeNat,next] using source ⟨j,hj⟩
 obtain ⟨u,rest,up,full,frame,out⟩:=loop (W*L-L) v x fit code L b (by omega) (by omega)
  bp zeros.final_bound (zeroSetup_cursor hc hz hr) initial
 have frameCopy:Frame (applyBlock (copySetup W) s) afterCopy:=
  ⟨copyFrame.1,copyFrame.2.1,copyFrame.2.2.1,fun q hq _=>copyFrame.2.2.2 q hq,
   fun q hq _=>copyNat q hq⟩
 have frameAll:Frame s u:=(copySetup_frame W s).trans
  (frameCopy.trans ((zeroSetup_frame afterCopy).trans frame))
 have outside:Outside d (W*L) s u:=by
  intro q hq
  exact (out q hq).trans (copyOut q (by rcases hq with hq|hq <;>omega))
 refine ⟨u,?_,up,full,frameAll,outside,?_⟩
 · convert first.executes (moved.executes (zeros.executes rest)) using 1
   simp only[show (copySetup W).length=5 from rfl,show zeroSetup.length=4 from rfl]
   omega
 · intro j
   exact outside _ (Or.inl (by have hj:=j.isLt;omega))

lemma role_value {W L d:ℕ} {v:Fin L  →  Scalar} {s:State}
 (h:Prefix v d (W*L) s) (role:Fin W) (t:Fin L):
 s.scalarHeap (d+role.val*L+t.val)=some (if role.val=0 then v t else ⟨0,false⟩):=by
 have idx:role.val*L+t.val < W*L:=by nlinarith[role.isLt,t.isLt]
 have cell:=h (role.val*L+t.val) idx
 rw[show d+role.val*L+t.val=d+(role.val*L+t.val) by omega]
 rw[cell]
 congr 1
 unfold padAt
 by_cases eq:role.val=0
 · simp[eq]
 · have positive:1 ≤ role.val:=by omega
   have lo:L ≤ role.val*L+t.val:=by nlinarith
   simp[eq,show ¬role.val*L+t.val < L by omega]

end
end ExactFourierCircuits.UniformSectorPaddingMachine
