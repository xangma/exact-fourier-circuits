import UniformSectorBatchDirectoryMachine
import UniformScalarCopyMachine
import UniformNewtonTableMachine
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorTransposeMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine
open UniformSectorPacking (BlockState)
/-- The same literal34, specialized by a fixed direction, copies a generated
sector across all W roles. Forward produces contiguous W q-bit arrays. Reverse
places the arrays in a fresh higher role-major bank, retaining its spectators.
There is no per-call padding, scalar arithmetic, or child transform here. -/
def boot (W:ℕ):List Op:=[.literal 4550 W,.literal 4551 0,.literal 4552 1,
 .literal 4553 5,.literal 4554 0,.mul 4555 4533 4553,.add 4555 4532 4555,
 .getNat 4556 4555,.add 4555 4555 4552,.getNat 4557 4555,
 .add 4555 4555 4552,.getNat 4558 4555,.add 4555 4555 4552,
 .getNat 4559 4555,.add 147 4557 4551]
def setup (inverse:Bool):List Op:=if inverse then
 [.mul 4560 4554 4557,.add 148 4558 4560,.mul 4561 4554 4530,
  .add 149 4531 4561,.add 149 149 4559] else
 [.mul 4560 4554 4530,.add 148 4531 4560,.add 148 148 4559,
  .mul 4561 4554 4557,.add 149 4558 4561]
def programFor (W:ℕ) (inverse:Bool):Program:=(boot W).map Op.code++
 [.branchLT 4554 4550 16 33]++(setup inverse).map Op.code++
 UniformScalarCopyMachine.program.map (relocate 21 31)++
 [.natBinary .add 4554 4554 4552,.jump 15,.halt]
def program (inverse:Bool):Program:=programFor ExplicitSeedBudget.paddedRoles inverse
lemma setup_length (inverse:Bool):(setup inverse).length=5:=by cases inverse <;>rfl
lemma program_length (W:ℕ) (inverse:Bool):(programFor W inverse).length=34:=by
 cases inverse <;>rfl
lemma boot_code (W:ℕ) (inverse:Bool):BlockAt (boot W) (programFor W inverse) 0:=by
 intro i hi;change i < 15 at hi;interval_cases i <;>rfl
lemma setup_code (W:ℕ) (inverse:Bool):BlockAt (setup inverse) (programFor W inverse) 16:=by
 cases inverse <;>intro i hi <;>change i < 5 at hi <;>interval_cases i <;>rfl
lemma copy_code (W:ℕ) (inverse:Bool):CodeAt UniformScalarCopyMachine.program (programFor W inverse) 21 31:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((boot W).map Op.code++[Instruction.branchLT 4554 4550 16 33]++(setup inverse).map Op.code)
  [Instruction.natBinary .add 4554 4554 4552,.jump 15,.halt] UniformScalarCopyMachine.program 21 31
  (by cases inverse <;>rfl)
lemma branch_at (W:ℕ) (inverse:Bool):(programFor W inverse)[15]?=some (.branchLT 4554 4550 16 33):=rfl
lemma tick_at (W:ℕ) (inverse:Bool):(programFor W inverse)[31]?=some (.natBinary .add 4554 4554 4552):=by cases inverse <;>rfl
lemma jump_at (W:ℕ) (inverse:Bool):(programFor W inverse)[32]?=some (.jump 15):=by cases inverse <;>rfl
lemma halt_at (W:ℕ) (inverse:Bool):(programFor W inverse)[33]?=some .halt:=by cases inverse <;>rfl
noncomputable section
structure Geometry (W:ℕ) (inverse:Bool) where
 B:ℕ
 volume:ℕ
 native:ℕ
 directory:ℕ
 buffer:ℕ
 ordinal:ℕ
 sector:BlockState
 fit:sector.start+sector.width ≤ volume
 nativeFit:native+W*volume ≤ B
 bufferFit:buffer+W*volume ≤ B
 separation:if inverse then buffer+W*volume ≤ native else native+W*volume ≤ buffer
 readFit:directory+5*(ordinal+1) ≤ B
 roles:W ≤ B
 code:34 ≤ B

def sourceAddress {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r:ℕ):ℕ:=
 if inverse then g.buffer+W*g.sector.start+r*g.sector.width else g.native+r*g.volume+g.sector.start
def targetAddress {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r:ℕ):ℕ:=
 if inverse then g.native+r*g.volume+g.sector.start else g.buffer+W*g.sector.start+r*g.sector.width
lemma addresses {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r:ℕ) (hr:r < W):
 sourceAddress g r+g.sector.width ≤ targetAddress g r ∧targetAddress g r+g.sector.width ≤ g.B:=by
 have fit:=g.fit
 have native:=g.nativeFit
 have buffer:=g.bufferFit
 have separated:=g.separation
 have width:g.sector.width ≤ g.volume:=by omega
 have wfit:=Nat.mul_le_mul_left W fit
 have rwidth:=Nat.mul_le_mul_left (r+1) width
 have rvolume:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
 have rsmall:=Nat.mul_le_mul_right g.sector.width (show r+1 ≤ W by omega)
 cases inverse <;>simp only[sourceAddress,targetAddress,Bool.false_eq_true,ite_false,ite_true] at * <;>constructor <;>nlinarith
lemma source_before_target {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r t:ℕ) (hr:r < W) (_ht:t < W):
 sourceAddress g r+g.sector.width ≤ targetAddress g t:=by
 have fit:=g.fit
 have separated:=g.separation
 have wfit:=Nat.mul_le_mul_left W fit
 have rvolume:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
 have rsmall:=Nat.mul_le_mul_right g.sector.width (show r+1 ≤ W by omega)
 cases inverse <;>simp only[sourceAddress,targetAddress,Bool.false_eq_true,ite_false,ite_true] at * <;>nlinarith
lemma targets_ordered {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r t:ℕ) (hrt:r < t):
 targetAddress g r+g.sector.width ≤ targetAddress g t:=by
 have fit:=g.fit
 have width:g.sector.width ≤ g.volume:=by omega
 have rp:=Nat.mul_le_mul_right g.volume (show r+1 ≤ t by omega)
 have rw:=Nat.mul_le_mul_right g.sector.width (show r+1 ≤ t by omega)
 cases inverse <;>simp only[targetAddress,Bool.false_eq_true,ite_false,ite_true] <;>nlinarith
structure Header {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (s:State):Prop where
 volume:s.natReg 4530=g.volume
 native:s.natReg 4531=g.native
 directory:s.natReg 4532=g.directory
 ordinal:s.natReg 4533=g.ordinal
structure Cursor {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (r:ℕ) (s:State):Prop extends Header g s where
 roles:s.natReg 4550=W
 zero:s.natReg 4551=0
 one:s.natReg 4552=1
 five:s.natReg 4553=5
 index:s.natReg 4554=r
 exponent:s.natReg 4556=g.sector.pairs
 width:s.natReg 4557=g.sector.width
 base:s.natReg 4558=g.buffer+W*g.sector.start
 start:s.natReg 4559=g.sector.start
 length:s.natReg 147=g.sector.width
lemma Cursor.withPC {W r pc:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Cursor g r s):
 Cursor g r (setPC s pc):=
 ⟨⟨h.volume,h.native,h.directory,h.ordinal⟩,h.roles,h.zero,h.one,h.five,h.index,
  h.exponent,h.width,h.base,h.start,h.length⟩
lemma boot_cursor {W:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Header g s)
 (cell:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s):
 Cursor g 0 (applyBlock (boot W) s):=by
 rcases cell with ⟨hq,hw,ha,hs,_⟩
 simp only[Nat.add_assoc] at hq hw ha hs
 constructor
 · constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.volume,h.native,h.directory,h.ordinal]
 all_goals simp[boot,applyBlock,Op.apply,writeNat,next,h.directory,h.ordinal,hq,hw,ha,hs,
  Nat.mul_comm g.ordinal 5,Nat.add_assoc]
lemma boot_safe {W:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Header g s)
 (cell:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (wb:WordBound g.B s):readable (boot W) s ∧peak (boot W) s ≤ g.B:=by
 have qb: g.sector.pairs ≤ g.B:=(wb.2.2.1 _ _ cell.1).2
 have wb':g.sector.width ≤ g.B:=(wb.2.2.1 _ _ cell.2.1).2
 have ab:g.buffer+W*g.sector.start ≤ g.B:=(wb.2.2.1 _ _ cell.2.2.1).2
 have sb:g.sector.start ≤ g.B:=(wb.2.2.1 _ _ cell.2.2.2.1).2
 rcases cell with ⟨hq,hw,ha,hs,_⟩
 simp only[Nat.add_assoc] at hq hw ha hs
 constructor
 · simp[boot,readable,Op.readable,Op.apply,writeNat,next,h.directory,h.ordinal,hq,hw,ha,hs,
    Nat.mul_comm g.ordinal 5,Nat.add_assoc]
 · simp[boot,peak,Op.peak,Op.apply,writeNat,next,h.directory,h.ordinal,hq,hw,ha,hs,
    Nat.mul_comm g.ordinal 5,Nat.add_assoc]
   have:=g.readFit;have:=g.roles;have:=g.code;omega
lemma setup_headers {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Cursor g r s):
 (applyBlock (setup inverse) s).natReg 147=g.sector.width ∧
 (applyBlock (setup inverse) s).natReg 148=sourceAddress g r ∧
 (applyBlock (setup inverse) s).natReg 149=targetAddress g r:=by
 cases inverse <;>simp[setup,applyBlock,Op.apply,writeNat,next,sourceAddress,targetAddress,
  h.volume,h.native,h.index,h.width,h.base,h.start,h.length]
lemma setup_safe {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Cursor g r s) (hr:r < W):
 readable (setup inverse) s ∧peak (setup inverse) s ≤ g.B:=by
 have ab:=addresses g r hr
 cases inverse <;>simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.volume,h.native,h.index,h.width,h.base,h.start,sourceAddress,targetAddress] at * <;>omega

def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32 → u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q < 147 ∨154 ≤ q)→(q < 4550 ∨4562 ≤ q)→u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (a:Frame s u) (b:Frame u v):Frame s v:=
 ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,
 fun q h=>(b.2.2.2.1 q h).trans (a.2.2.2.1 q h),
 fun q h0 h1=>(b.2.2.2.2 q h0 h1).trans (a.2.2.2.2 q h0 h1)⟩
lemma boot_frame (W:ℕ) (s:State):Frame s (applyBlock (boot W) s):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma setup_frame (inverse:Bool) (s:State):Frame s (applyBlock (setup inverse) s):=by
 cases inverse
 all_goals refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 all_goals intro q h0 h1
 all_goals simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma copy_frame {s u:State} (a:UniformScalarCopyMachine.Frame s u) (b:UniformScalarCopyMachine.NatFrame s u):Frame s u:=
 ⟨a.1,a.2.1,a.2.2.1,a.2.2.2,fun q h0 _=>b q h0⟩
lemma copy_length {n t B:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformScalarCopyMachine.program n x B s t u):u.natReg 147=s.natReg 147:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (by simp[UniformScalarCopyMachine.program,UniformNewtonTableMachine.KeepsNat])

/-- Actual values and tags, indexed by role and the q-bit coordinate. -/
def Source {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (v:ℕ→ℕ→Scalar) (s:State):Prop:=
 ∀r,r < W→∀t,t < g.sector.width→s.scalarHeap (sourceAddress g r+t)=some (v r t)
def Filled {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (v:ℕ→ℕ→Scalar) (done:ℕ) (s:State):Prop:=
 ∀r,r < done→∀t,t < g.sector.width→s.scalarHeap (targetAddress g r+t)=some (v r t)
def Outside {W:ℕ} {inverse:Bool} (g:Geometry W inverse) (heap:ℕ→Option Scalar) (s:State):Prop:=
 ∀q,(∀r,r < W→q < targetAddress g r ∨targetAddress g r+g.sector.width ≤ q)→s.scalarHeap q=heap q
lemma Source.transfer {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {v:ℕ→ℕ→Scalar} {s u:State}
 (h:Source g v s) (hr:r < W) (out:UniformScalarCopyMachine.Outside (targetAddress g r) g.sector.width s.scalarHeap u):Source g v u:=by
 intro i hi t ht
 have prior:=source_before_target g i r hi hr
 exact (out _ (Or.inl (by omega))).trans (h i hi t ht)
lemma Filled.step {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {v:ℕ→ℕ→Scalar} {s u:State}
 (h:Filled g v r s) (fresh:∀t,t < g.sector.width→u.scalarHeap (targetAddress g r+t)=some (v r t))
 (out:UniformScalarCopyMachine.Outside (targetAddress g r) g.sector.width s.scalarHeap u):Filled g v (r+1) u:=by
 intro i hi t ht
 by_cases equal:i=r
 · subst i;exact fresh t ht
 · have before:i < r:=by omega
   have ordered:=targets_ordered g i r before
   exact (out _ (Or.inl (by omega))).trans (h i before t ht)
lemma setup_cursor {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Cursor g r s):
 Cursor g r (applyBlock (setup inverse) s):=by
 cases inverse
 all_goals constructor
 all_goals try (constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.volume,h.native,h.directory,h.ordinal])
 all_goals simp[setup,applyBlock,Op.apply,writeNat,next,h.roles,h.zero,h.one,h.five,h.index,
  h.exponent,h.width,h.base,h.start,h.length]
lemma copy_cursor {W r n B t:ℕ} {inverse:Bool} {g:Geometry W inverse} {s u:State} {x:Fin n→ℂ}
 (h:Cursor g r s) (run:BoundedExecution UniformScalarCopyMachine.program n x B s t u)
 (nat:UniformScalarCopyMachine.NatFrame s u):Cursor g r u:=by
 have kept:=copy_length run
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,kept.trans h.length⟩
 all_goals first | exact (nat _ (Or.inr (by omega))).trans h.volume |
  exact (nat _ (Or.inr (by omega))).trans h.native |
  exact (nat _ (Or.inr (by omega))).trans h.directory |
  exact (nat _ (Or.inr (by omega))).trans h.ordinal |
  exact (nat _ (Or.inr (by omega))).trans h.roles |
  exact (nat _ (Or.inr (by omega))).trans h.zero |
  exact (nat _ (Or.inr (by omega))).trans h.one |
  exact (nat _ (Or.inr (by omega))).trans h.five |
  exact (nat _ (Or.inr (by omega))).trans h.index |
  exact (nat _ (Or.inr (by omega))).trans h.exponent |
  exact (nat _ (Or.inr (by omega))).trans h.width |
  exact (nat _ (Or.inr (by omega))).trans h.base |
  exact (nat _ (Or.inr (by omega))).trans h.start
lemma setup_heap (inverse:Bool) (s:State):(applyBlock (setup inverse) s).scalarHeap=s.scalarHeap:=by
 cases inverse <;>rfl
lemma advanced_cursor {W r:ℕ} {inverse:Bool} {g:Geometry W inverse} {s:State} (h:Cursor g r s):
 Cursor g (r+1) (setPC (writeNat s 4554 (r+1)) 15):=by
 constructor
 · constructor <;>simp[setPC,writeNat,next,h.volume,h.native,h.directory,h.ordinal]
 all_goals simp[setPC,writeNat,next,h.roles,h.zero,h.one,h.five,h.exponent,h.width,h.base,h.start,h.length]
lemma advanced_frame (s:State) (r:ℕ):Frame s (setPC (writeNat s 4554 (r+1)) 15):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1
 simp (disch:=omega) [setPC,writeNat,next]

/-- Each real role iteration loads its current source/destination addresses,
executes all7w+4 copy instructions, advances and jumps. -/
lemma iteration {W r n:ℕ} {inverse:Bool} (g:Geometry W inverse) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (hr:r < W) (h:Cursor g r s) (source:Source g v s) (pc:s.pc=15) (wb:WordBound g.B s):
 ∃u,BoundedRuns (programFor W inverse) n x g.B s (7*g.sector.width+12) u ∧u.pc=15 ∧
 Cursor g (r+1) u ∧(∀t,t < g.sector.width→u.scalarHeap (targetAddress g r+t)=some (v r t)) ∧
 Frame s u ∧UniformScalarCopyMachine.Outside (targetAddress g r) g.sector.width s.scalarHeap u:=by
 let e:=setPC s 16
 have eb:=changePC_bound g.B s 16 wb (by have:=g.code;omega)
 have branch:BoundedRuns (programFor W inverse) n x g.B s 1 e:=.next wb
  (by simp[step,pc,branch_at,h.index,h.roles,hr,e,setPC]) (.refl eb)
 have safe:=setup_safe (h.withPC (pc:=16)) hr
 have start:=block_runs (setup inverse) (programFor W inverse) 16 n g.B x e (setup_code W inverse) rfl eb
  (by rw[setup_length];have:=g.code;omega) safe.1 safe.2
 let c:=applyBlock (setup inverse) e
 have cp:c.pc=21:=by rw[applyBlock_pc,setup_length];rfl
 let ready:=setPC c 0
 have readyHeap:ready.scalarHeap=s.scalarHeap:=setup_heap inverse e
 have src:UniformScalarCopyMachine.Source g.sector.width (sourceAddress g r) ready.scalarHeap:=by
  intro t ht
  exact ⟨v r t,(congrFun readyHeap _).trans (source r hr t ht)⟩
 have headers:=setup_headers (h.withPC (pc:=16))
 have ab:=addresses g r hr
 obtain ⟨t,copy,_copiedSource,sourceKept,out,frame,nat⟩:=UniformScalarCopyMachine.execution n x
  g.sector.width (sourceAddress g r) (targetAddress g r) g.B ready src ab.1 ab.2
  (by have:=g.code;omega) rfl headers.1 headers.2.1 headers.2.2
  (changePC_bound g.B c 0 start.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (copy_code W inverse)
  (by rw[UniformScalarCopyMachine.program_length];have:=g.code;omega) (by have:=g.code;omega) copy
 rw[UniformMultiAxisSectorMetadataPreparation.placed_zero c 21 cp] at moved
 let t':=setPC t 31
 have cursorT:Cursor g r t':=(copy_cursor ((setup_cursor (h.withPC (pc:=16))).withPC (pc:=0)) copy nat).withPC
 let a:=writeNat t' 4554 (r+1)
 have abnd:=writeNat_bound g.B t' 4554 (r+1) moved.final_bound
  (by have:=g.code;change 31+1 ≤ g.B;omega) (by have:=g.roles;omega)
 have ti:t.natReg 4554=r:=cursorT.index
 have oneT:t.natReg 4552=1:=cursorT.one
 have tick:BoundedRuns (programFor W inverse) n x g.B t' 1 a:=.next moved.final_bound
  (by simp[step,t',setPC,tick_at,evalNat,ti,oneT,a]) (.refl abnd)
 let u:=setPC a 15
 have jump:BoundedRuns (programFor W inverse) n x g.B a 1 u:=.next abnd
  (by simp[step,a,t',setPC,writeNat,next,jump_at,u])
  (.refl (changePC_bound g.B a 15 abnd (by have:=g.code;omega)))
 have run:=branch.trans (start.trans (moved.trans (tick.trans jump)))
 have fresh:∀j,j < g.sector.width→u.scalarHeap (targetAddress g r+j)=some (v r j):=by
  intro j hj
  exact (_copiedSource j hj).trans ((congrFun readyHeap _).trans (source r hr j hj))
 have frame0:Frame s t':=(setup_frame inverse e).trans (copy_frame frame nat)
 have frameU:Frame s u:=frame0.trans (advanced_frame t' r)
 have outU:UniformScalarCopyMachine.Outside (targetAddress g r) g.sector.width s.scalarHeap u:=by
  intro j hj;exact (out j hj).trans (congrFun readyHeap j)
 refine ⟨u,?_,rfl,advanced_cursor cursorT,fresh,frameU,outU⟩
 convert run using 1
 simp only[setup_length]
 omega
lemma loop (remaining:ℕ) {W n:ℕ} {inverse:Bool} (g:Geometry W inverse) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ):
 ∀r s,W=r+remaining→s.pc=15→WordBound g.B s→Cursor g r s→Source g v s→Filled g v r s→
 ∃u,BoundedExecution (programFor W inverse) n x g.B s (remaining*(7*g.sector.width+12)+2) u ∧
 u.pc=33 ∧Cursor g W u ∧Filled g v W u ∧Frame s u ∧Outside g s.scalarHeap u:=by
 induction remaining with
 | zero=>
   intro r s count pc wb cursor source filled
   have equal:r=W:=by omega
   let u:=setPC s 33
   have ub:=changePC_bound g.B s 33 wb (by have:=g.code;omega)
   have branch:BoundedRuns (programFor W inverse) n x g.B s 1 u:=.next wb
    (by simp[step,pc,branch_at,cursor.index,cursor.roles,equal,u,setPC]) (.refl ub)
   have stop:BoundedExecution (programFor W inverse) n x g.B u 1 u:=.halt ub
    (by simp[step,u,setPC,halt_at])
   refine ⟨u,by simpa using branch.executes stop,rfl,?_,?_,Frame.refl s,fun _ _=>rfl⟩
   · simpa only[equal] using cursor.withPC (pc:=33)
   · simpa only[Filled,u,setPC,equal] using filled
 | succ remaining ih=>
   intro r s count pc wb cursor source filled
   have hr:r < W:=by omega
   obtain ⟨t,first,tp,next,fresh,frame,out⟩:=iteration g v x s hr cursor source pc wb
   have src:=source.transfer hr out
   have fill:=filled.step fresh out
   obtain ⟨u,rest,up,done,values,frameU,outU⟩:=ih (r+1) t (by omega) tp first.final_bound next src fill
   refine ⟨u,?_,up,done,values,frame.trans frameU,?_⟩
   · convert first.executes rest using 1
     simp only[Nat.succ_mul]
     omega
   · intro q outside
     exact (outU q outside).trans (out q (outside r hr))

/-- Initialized complete sector transpose, including the genuine directory
loads. It charges all W block copies and every loop branch/advance/halt. -/
theorem execution {W n:ℕ} {inverse:Bool} (g:Geometry W inverse) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (h:Header g s) (cell:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (source:Source g v s) (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W inverse) n x g.B s (W*(7*g.sector.width+12)+17) u ∧
 u.pc=33 ∧Cursor g W u ∧Filled g v W u ∧Frame s u ∧Outside g s.scalarHeap u:=by
 have safe:=boot_safe h cell wb
 have first:=block_runs (boot W) (programFor W inverse) 0 n g.B x s (boot_code W inverse) pc wb
  (by have:=g.code;change 0+15 ≤ g.B;omega) safe.1 safe.2
 let b:=applyBlock (boot W) s
 have bp:b.pc=15:=by rw[applyBlock_pc,pc];rfl
 have bs:Source g v b:=source
 have empty:Filled g v 0 b:=by intro r hr;omega
 obtain ⟨u,rest,up,cursor,filled,frame,out⟩:=loop W g v x 0 b (by omega) bp first.final_bound
  (boot_cursor h cell) bs empty
 refine ⟨u,?_,up,cursor,filled,(boot_frame W s).trans frame,out⟩
 convert first.executes rest using 1
 change W*(7*g.sector.width+12)+17=15+(W*(7*g.sector.width+12)+2)
 omega

lemma source_retained {W:ℕ} {inverse:Bool} {g:Geometry W inverse} {s u:State}
 (out:Outside g s.scalarHeap u):∀r,r < W→∀t,t < g.sector.width→
 u.scalarHeap (sourceAddress g r+t)=s.scalarHeap (sourceAddress g r+t):=by
 intro r hr t ht
 apply out
 intro i hi
 exact Or.inl (by have:=source_before_target g r i hr hi;omega)
/-- Explicit W-role-major q-coordinate grouping. The exponent/width values
are physically read from the directory; for canonical sectors width=2^q. -/
theorem forward_values {W:ℕ} {g:Geometry W false} {v:ℕ→ℕ→Scalar} {u:State}
 (h:Filled g v W u):∀r,r < W→∀t,t < g.sector.width→
 u.scalarHeap (g.buffer+W*g.sector.start+r*g.sector.width+t)=some (v r t):=h

theorem reverse_values {W:ℕ} {g:Geometry W true} {v:ℕ→ℕ→Scalar} {u:State}
 (h:Filled g v W u):∀r,r < W→∀t,t < g.sector.width→
 u.scalarHeap (g.native+r*g.volume+g.sector.start+t)=some (v r t):=h
lemma native_spectators {W:ℕ} {g:Geometry W true} {s u:State} (out:Outside g s.scalarHeap u)
 (r j:ℕ) (_hr:r < W) (hj:j < g.volume) (unused:j < g.sector.start ∨g.sector.start+g.sector.width ≤ j):
 u.scalarHeap (g.native+r*g.volume+j)=s.scalarHeap (g.native+r*g.volume+j):=by
 apply out
 intro i hi
 change g.native+r*g.volume+j < g.native+i*g.volume+g.sector.start ∨
  g.native+i*g.volume+g.sector.start+g.sector.width ≤ g.native+r*g.volume+j
 by_cases equal:i=r
 · subst i;rcases unused with before|after
   · exact Or.inl (by omega)
   · exact Or.inr (by omega)
 · rcases lt_or_gt_of_ne equal with before|after
   · have ordered:=Nat.mul_le_mul_right g.volume (show i+1 ≤ r by omega)
     exact Or.inr (by have:=g.fit;nlinarith)
   · have ordered:=Nat.mul_le_mul_right g.volume (show r+1 ≤ i by omega)
     exact Or.inl (by nlinarith)
end
end ExactFourierCircuits.UniformSectorTransposeMachine
