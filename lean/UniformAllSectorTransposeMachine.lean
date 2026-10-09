import UniformSectorTransposeMachine
import UniformAllSectorPaddingMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllSectorTransposeMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPacking (BlockState)
def boot:List Op:=[.literal 4570 0,.literal 4571 1,.literal 4533 0]
def programFor (W:ℕ) (inverse:Bool):Program:=boot.map Op.code++[.branchLT 4533 464 4 40]++
 (UniformSectorTransposeMachine.programFor W inverse).map (relocate 4 38)++
 [.natBinary .add 4533 4533 4571,.jump 3,.halt]
def program (inverse:Bool):Program:=programFor ExplicitSeedBudget.paddedRoles inverse
lemma program_length (W:ℕ) (inverse:Bool):(programFor W inverse).length=41:=by cases inverse <;>rfl
lemma boot_code (W:ℕ) (inverse:Bool):BlockAt boot (programFor W inverse) 0:=by
 intro i hi;change i < 3 at hi;interval_cases i <;>rfl
lemma transpose_code (W:ℕ) (inverse:Bool):CodeAt (UniformSectorTransposeMachine.programFor W inverse) (programFor W inverse) 4 38:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[Instruction.branchLT 4533 464 4 40])
  [Instruction.natBinary .add 4533 4533 4571,.jump 3,.halt] _ 4 38 rfl
lemma branch_at (W:ℕ) (inverse:Bool):(programFor W inverse)[3]?=some (.branchLT 4533 464 4 40):=rfl
lemma advance_at (W:ℕ) (inverse:Bool):(programFor W inverse)[38]?=some (.natBinary .add 4533 4533 4571):=by cases inverse <;>rfl
lemma jump_at (W:ℕ) (inverse:Bool):(programFor W inverse)[39]?=some (.jump 3):=by cases inverse <;>rfl
lemma halt_at (W:ℕ) (inverse:Bool):(programFor W inverse)[40]?=some .halt:=by cases inverse <;>rfl
noncomputable section
structure Geometry (W:ℕ) (inverse:Bool) (xs:List BlockState) where
 B:ℕ
 volume:ℕ
 native:ℕ
 directory:ℕ
 buffer:ℕ
 fits:UniformAllSectorPaddingMachine.Fits xs volume
 ordered:UniformAllSectorPaddingMachine.Ordered xs
 nativeFit:native+W*volume ≤ B
 bufferFit:buffer+W*volume ≤ B
 separation:if inverse then buffer+W*volume ≤ native else native+W*volume ≤ buffer
 entry:directory+5*xs.length ≤ B
 roles:W ≤ B
 code:41 ≤ B

def Geometry.local {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (i:ℕ) (hi:i < xs.length):
 UniformSectorTransposeMachine.Geometry W inverse where
 B:=g.B
 volume:=g.volume
 native:=g.native
 directory:=g.directory
 buffer:=g.buffer
 ordinal:=i
 sector:=xs[i]'hi
 fit:=g.fits i hi
 nativeFit:=g.nativeFit
 bufferFit:=g.bufferFit
 separation:=g.separation
 readFit:=by have:=g.entry;omega
 roles:=g.roles
 code:=by have:=g.code;omega
structure Header {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (s:State):Prop where
 volume:s.natReg 4530=g.volume
 native:s.natReg 4531=g.native
 directory:s.natReg 4532=g.directory
 count:s.natReg 464=xs.length
structure Cursor {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (i:ℕ) (s:State):Prop extends Header g s where
 index:s.natReg 4533=i
 one:s.natReg 4571=1
lemma Cursor.withPC {W i pc:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {s:State}
 (h:Cursor g i s):Cursor g i (setPC s pc):=⟨⟨h.volume,h.native,h.directory,h.count⟩,h.index,h.one⟩
def Table {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (s:State):Prop:=
 ∀i,∀hi:i < xs.length,UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer i (xs[i]'hi) s
def slice (v:ℕ→ℕ→Scalar) (st:BlockState):ℕ→ℕ→Scalar:=fun r t=>v r (st.start+t)
def Source {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (v:ℕ→ℕ→Scalar) (s:State):Prop:=
 ∀i,∀hi:i < xs.length,UniformSectorTransposeMachine.Source (g.local i hi) (slice v (xs[i]'hi)) s
def Filled {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs) (v:ℕ→ℕ→Scalar) (done:ℕ) (s:State):Prop:=
 ∀i,∀hi:i < xs.length,i < done→UniformSectorTransposeMachine.Filled (g.local i hi) (slice v (xs[i]'hi)) W s

def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32 → u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q < 147 ∨154 ≤ q)→q≠4533→(q < 4550 ∨4562 ≤ q)→(q < 4570 ∨4572 ≤ q)→u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq=>(k.2.2.2.1 q hq).trans (h.2.2.2.1 q hq),
 fun q h0 h1 h2 h3=>(k.2.2.2.2 q h0 h1 h2 h3).trans (h.2.2.2.2 q h0 h1 h2 h3)⟩
lemma transpose_frame {s u:State} (h:UniformSectorTransposeMachine.Frame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun q h0 _ h2 _=>h.2.2.2.2 q h0 h2⟩
def tick (s:State):State:=setPC (writeNat (setPC s 38) 4533 (s.natReg 4533+s.natReg 4571)) 3
lemma tick_frame (s:State):Frame s (tick s):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2 h3
 simp[tick,setPC,writeNat,next,h1]
lemma cursor_after_transpose {W i:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {s u:State}
 (h:Cursor g i s) (frame:UniformSectorTransposeMachine.Frame s u):Cursor g i u:=by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
 all_goals first | exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.volume |
  exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.native |
  exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.directory |
  exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.count |
  exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.index |
  exact (frame.2.2.2.2 _ (by omega) (by omega)).trans h.one
lemma tick_cursor {W i:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {s:State}
 (h:Cursor g i s):Cursor g (i+1) (tick s):=by
 constructor
 · constructor <;>simp[tick,setPC,writeNat,next,h.volume,h.native,h.directory,h.count]
 all_goals simp[tick,setPC,writeNat,next,h.index,h.one]
lemma iteration {W i n:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs)
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State) (hi:i < xs.length) (h:Cursor g i s)
 (table:Table g s) (source:Source g v s) (pc:s.pc=3) (wb:WordBound g.B s):
 ∃u,BoundedRuns (programFor W inverse) n x g.B s (W*(7*(xs[i]'hi).width+12)+20) u ∧u.pc=3 ∧
 UniformSectorTransposeMachine.Filled (g.local i hi) (slice v (xs[i]'hi)) W u ∧Cursor g (i+1) u ∧Frame s u ∧
 UniformSectorTransposeMachine.Outside (g.local i hi) s.scalarHeap u:=by
 let entered:=setPC s 4
 have eb:=changePC_bound g.B s 4 wb (by have:=g.code;omega)
 have branch:BoundedRuns (programFor W inverse) n x g.B s 1 entered:=.next wb
  (by simp[step,pc,branch_at,h.index,h.count,hi,entered,setPC]) (.refl eb)
 let ready:=setPC s 0
 obtain ⟨t,run,tp,_localCursor,filled,frame,out⟩:=UniformSectorTransposeMachine.execution (g.local i hi)
  (slice v (xs[i]'hi)) x ready ⟨h.volume,h.native,h.directory,h.index⟩ (table i hi) (source i hi) rfl
  (changePC_bound g.B s 0 wb (by have:=g.code;omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (transpose_code W inverse)
  (by rw[UniformSectorTransposeMachine.program_length];change 4+34 ≤ g.B;have:=g.code;omega) (by change 38 ≤ g.B;have:=g.code;omega) run
 rw[show placed 4 ready=entered by cases s;rfl] at moved
 have cursor:=cursor_after_transpose h frame
 have countB:xs.length ≤ g.B:=by simpa only[h.count] using wb.2.1 464
 let a:=writeNat (setPC t 38) 4533 (i+1)
 have ab:=writeNat_bound g.B (setPC t 38) 4533 (i+1) moved.final_bound
  (by have:=g.code;change 38+1 ≤ g.B;omega) (by omega)
 have advance:BoundedRuns (programFor W inverse) n x g.B (setPC t 38) 1 a:=.next moved.final_bound
  (by simp[step,advance_at,setPC,evalNat,cursor.index,cursor.one,a]) (.refl ab)
 have same:tick t=setPC a 3:=by simp[tick,a,cursor.index,cursor.one]
 have last:BoundedRuns (programFor W inverse) n x g.B a 1 (tick t):=by
  rw[same]
  exact .next ab (by simp[step,a,setPC,writeNat,next,jump_at])
   (.refl (changePC_bound g.B a 3 ab (by have:=g.code;omega)))
 refine ⟨tick t,?_,rfl,filled,tick_cursor cursor,(transpose_frame frame).trans (tick_frame t),out⟩
 convert branch.trans (moved.trans (advance.trans last)) using 1
 change W*(7*(xs[i]'hi).width+12)+20=1+(W*(7*(xs[i]'hi).width+12)+17+(1+1))
 omega

lemma source_before_all_targets {W i j r t:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs)
 (hi:i < xs.length) (hj:j < xs.length) (hr:r < W) (_ht:t < W):
 UniformSectorTransposeMachine.sourceAddress (g.local j hj) r+(xs[j]'hj).width ≤
 UniformSectorTransposeMachine.targetAddress (g.local i hi) t:=by
 have fit:=g.fits j hj
 have wfit:=Nat.mul_le_mul_left W fit
 have rv:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
 have rw:=Nat.mul_le_mul_right (xs[j]'hj).width (show r+1 ≤ W by omega)
 have sep:=g.separation
 cases inverse <;>simp only[UniformSectorTransposeMachine.sourceAddress,UniformSectorTransposeMachine.targetAddress,
  Geometry.local,Bool.false_eq_true,ite_false,ite_true] at * <;>nlinarith
lemma Source.transfer {W i:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {v:ℕ→ℕ→Scalar} {s u:State}
 (hi:i < xs.length) (h:Source g v s) (out:UniformSectorTransposeMachine.Outside (g.local i hi) s.scalarHeap u):Source g v u:=by
 intro j hj r hr t ht
 change t < (xs[j]'hj).width at ht
 apply Eq.trans (out _ ?_) (h j hj r hr t ht)
 intro k hk
 exact Or.inl (by have:=source_before_all_targets g hi hj hr hk;omega)
lemma preserve_filled {W i:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {v:ℕ→ℕ→Scalar} {s u:State}
 (hi:i < xs.length) (old:Filled g v i s)
 (fresh:UniformSectorTransposeMachine.Filled (g.local i hi) (slice v (xs[i]'hi)) W u)
 (out:UniformSectorTransposeMachine.Outside (g.local i hi) s.scalarHeap u):Filled g v (i+1) u:=by
 intro j hj done r hr t ht
 change t < (xs[j]'hj).width at ht
 by_cases equal:j=i
 · subst j;exact fresh r hr t ht
 · have less:j < i:=by omega
   have before:=g.ordered j i hj hi less
   apply Eq.trans (out _ ?_) (old j hj less r hr t ht)
   intro k hk
   cases inverse
   · change g.buffer+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t < g.buffer+W*(xs[i]'hi).start+k*(xs[i]'hi).width ∨_
     have wb:=Nat.mul_le_mul_left W before
     have rb:=Nat.mul_le_mul_right (xs[j]'hj).width (show r+1 ≤ W by omega)
     exact Or.inl (by nlinarith)
   · change g.native+r*g.volume+(xs[j]'hj).start+t < g.native+k*g.volume+(xs[i]'hi).start ∨
      g.native+k*g.volume+(xs[i]'hi).start+(xs[i]'hi).width ≤ g.native+r*g.volume+(xs[j]'hj).start+t
     by_cases rk:r=k
     · subst k;exact Or.inl (by omega)
     · rcases lt_or_gt_of_ne rk with lower|upper
       · have b:=Nat.mul_le_mul_right g.volume (show r+1 ≤ k by omega)
         exact Or.inl (by have:=g.fits j hj;nlinarith)
       · have b:=Nat.mul_le_mul_right g.volume (show k+1 ≤ r by omega)
         exact Or.inr (by have:=g.fits i hi;nlinarith)
def cost (W:ℕ) (xs:List BlockState):ℕ:=(xs.map (fun st=>W*(7*st.width+12)+20)).sum+2
lemma cost_sum (W:ℕ) (xs:List BlockState):cost W xs=7*W*(xs.map BlockState.width).sum+(12*W+20)*xs.length+2:=by
 induction xs with
 | nil=>simp[cost]
 | cons st xs ih=>simp only[cost,List.map_cons,List.sum_cons,List.length_cons] at *;nlinarith[ih]
lemma cost_cons (W:ℕ) (st:BlockState) (xs:List BlockState):cost W (st::xs)=(W*(7*st.width+12)+20)+cost W xs:=by
 simp only[cost,List.map_cons,List.sum_cons];omega
def outputBase {W:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs):ℕ:=if inverse then g.native else g.buffer
lemma outside_local {W i:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs)
 (hi:i < xs.length) (q:ℕ) (outside:q < outputBase g ∨outputBase g+W*g.volume ≤ q):
 ∀r,r < W→q < UniformSectorTransposeMachine.targetAddress (g.local i hi) r ∨
 UniformSectorTransposeMachine.targetAddress (g.local i hi) r+(xs[i]'hi).width ≤ q:=by
 intro r hr
 have fit:=g.fits i hi
 have rw:=Nat.mul_le_mul_right (xs[i]'hi).width (show r+1 ≤ W by omega)
 have rv:=Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
 have wf:=Nat.mul_le_mul_left W fit
 cases inverse <;>simp only[outputBase,UniformSectorTransposeMachine.targetAddress,Geometry.local,
  Bool.false_eq_true,ite_false,ite_true] at *
 all_goals rcases outside with before|after
 all_goals first | exact Or.inl (by omega) | exact Or.inr (by nlinarith)
lemma loop (remaining:List BlockState) {W n:ℕ} {inverse:Bool} {xs:List BlockState}
 (g:Geometry W inverse xs) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ):
 ∀i s,i ≤ xs.length→xs.drop i=remaining→s.pc=3→WordBound g.B s→Cursor g i s→Table g s→Source g v s→Filled g v i s→
 ∃u,BoundedExecution (programFor W inverse) n x g.B s (cost W remaining) u ∧u.pc=40 ∧
 Filled g v xs.length u ∧Frame s u ∧
 UniformScalarCopyMachine.Outside (outputBase g) (W*g.volume) s.scalarHeap u:=by
 induction remaining with
 | nil=>
   intro i s le suffix pc wb cursor table source filled
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_nil] at length
   have last:i=xs.length:=by omega
   let u:=setPC s 40
   have ub:=changePC_bound g.B s 40 wb (by have:=g.code;omega)
   have branch:BoundedRuns (programFor W inverse) n x g.B s 1 u:=.next wb
    (by simp[step,pc,branch_at,cursor.index,cursor.count,last,u,setPC]) (.refl ub)
   have stop:BoundedExecution (programFor W inverse) n x g.B u 1 u:=.halt ub
    (by simp[step,u,setPC,halt_at])
   refine ⟨u,?_,rfl,?_,Frame.refl s,fun _ _=>rfl⟩
   · simpa only[cost,List.map_nil,List.sum_nil,Nat.zero_add] using branch.executes stop
   · simpa only[Filled,UniformSectorTransposeMachine.Filled,u,setPC,last] using filled
 | cons st remaining ih=>
   intro i s le suffix pc wb cursor table source filled
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_cons] at length
   have hi:i < xs.length:=by omega
   obtain ⟨equal,nextSuffix⟩:=List.cons.inj (suffix.symm.trans (List.drop_eq_getElem_cons hi))
   subst st
   obtain ⟨t,first,tp,fresh,next,frame,out⟩:=iteration g v x s hi cursor table source pc wb
   have tableT:Table g t:=by
    intro j hj
    simpa only[UniformSectorBatchDirectoryMachine.BatchCell,frame.1] using table j hj
   have sourceT:Source g v t:=source.transfer hi out
   have filledT:Filled g v (i+1) t:=preserve_filled hi filled fresh out
   obtain ⟨u,rest,up,done,frameU,outU⟩:=ih (i+1) t (by omega) nextSuffix.symm tp first.final_bound next tableT sourceT filledT
   refine ⟨u,?_,up,done,frame.trans frameU,?_⟩
   · rw[cost_cons]
     exact first.executes rest
   · intro q hq
     exact (outU q hq).trans (out q (outside_local g hi q hq))
lemma boot_cursor {W:ℕ} {inverse:Bool} {xs:List BlockState} {g:Geometry W inverse xs} {s:State}
 (h:Header g s):Cursor g 0 (applyBlock boot s):=by
 constructor
 · constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.volume,h.native,h.directory,h.count]
 all_goals simp[boot,applyBlock,Op.apply,writeNat,next]
lemma boot_frame (s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2 h3
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
/-- Complete actual ascending sector cursor. The count is read from real464;
all five-cell records are consumed by the real34. No child, sector list, or
host rearrangement is an instruction in this machine. -/
theorem execution {W n:ℕ} {inverse:Bool} {xs:List BlockState} (g:Geometry W inverse xs)
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State) (h:Header g s) (table:Table g s) (source:Source g v s)
 (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W inverse) n x g.B s (7*W*(xs.map BlockState.width).sum+(12*W+20)*xs.length+5) u ∧
 u.pc=40 ∧Filled g v xs.length u ∧Frame s u ∧
 UniformScalarCopyMachine.Outside (outputBase g) (W*g.volume) s.scalarHeap u:=by
 have safe:readable boot s ∧peak boot s ≤ g.B:=by
  simp[boot,readable,peak,Op.readable,Op.peak];have:=g.code;omega
 have first:=block_runs boot (programFor W inverse) 0 n g.B x s (boot_code W inverse) pc wb
  (by have:=g.code;change 0+3 ≤ g.B;omega) safe.1 safe.2
 let b:=applyBlock boot s
 have bp:b.pc=3:=by rw[applyBlock_pc,pc];rfl
 have tb:Table g b:=table
 have sb:Source g v b:=source
 have empty:Filled g v 0 b:=by intro i hi done;omega
 obtain ⟨u,rest,up,done,frame,out⟩:=loop xs g v x 0 b (by omega) (by simp) bp first.final_bound
  (boot_cursor h) tb sb empty
 refine ⟨u,?_,up,done,(boot_frame s).trans frame,out⟩
 convert first.executes rest using 1
 rw[cost_sum]
 change 7*W*(xs.map BlockState.width).sum+(12*W+20)*xs.length+5=
  3+(7*W*(xs.map BlockState.width).sum+(12*W+20)*xs.length+2)
 omega
/-- Canonical complete sectors have total width L. This is the exact O(WL+WM)
movement budget used on both sides of each common q-child phase. -/
lemma complete_budget {W L:ℕ} {xs:List BlockState} (partition:(xs.map BlockState.width).sum=L):
 7*W*(xs.map BlockState.width).sum+(12*W+20)*xs.length+5=7*W*L+(12*W+20)*xs.length+5:=by rw[partition]
end
end ExactFourierCircuits.UniformAllSectorTransposeMachine
