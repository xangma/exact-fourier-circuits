import UniformSectorPaddingPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllSectorPaddingMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine
open UniformSectorPacking (BlockState)
noncomputable section
/-- Read the actual464 sector count. Nat4472=packed source,4473=produced
five-cell directory. Only the ordinal is initialized; no sector list is supplied
as a machine operation. -/
def boot:List Op:=[.literal 4480 0,.literal 4481 1,.literal 4474 0]
def programFor (W:ℕ):Program:=boot.map Op.code++[.branchLT 4474 464 4 43]++
 (UniformSectorPaddingPreparation.programFor W).map (relocate 4 41)++
 [.natBinary .add 4474 4474 4481,.jump 3,.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=44:=by
 simp only[programFor,List.length_append,List.length_map,
  UniformSectorPaddingPreparation.program_length,List.length_cons,List.length_nil];rfl
lemma boot_code (W:ℕ):BlockAt boot (programFor W) 0:=by
 intro i hi;change i < 3 at hi;interval_cases i <;>rfl
lemma pad_code (W:ℕ):CodeAt (UniformSectorPaddingPreparation.programFor W) (programFor W) 4 41:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 4474 464 4 43])
  [.natBinary .add 4474 4474 4481,.jump 3,.halt] _ 4 41 rfl
lemma branch_at (W:ℕ):(programFor W)[3]?=some (.branchLT 4474 464 4 43):=rfl
lemma advance_at (W:ℕ):(programFor W)[41]?=some (.natBinary .add 4474 4474 4481):=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSectorPaddingPreparation.program_length];change 3+1+37 ≤ 41;omega)]
 simp only[List.length_append,List.length_map,UniformSectorPaddingPreparation.program_length];rfl
lemma jump_at (W:ℕ):(programFor W)[42]?=some (.jump 3):=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSectorPaddingPreparation.program_length];change 3+1+37 ≤ 42;omega)]
 simp only[List.length_append,List.length_map,UniformSectorPaddingPreparation.program_length];rfl
lemma halt_at (W:ℕ):(programFor W)[43]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSectorPaddingPreparation.program_length];change 3+1+37 ≤ 43;omega)]
 simp only[List.length_append,List.length_map,UniformSectorPaddingPreparation.program_length];rfl
structure Cursor (S E M i:ℕ) (s:State):Prop where
 source:s.natReg 4472=S
 directory:s.natReg 4473=E
 count:s.natReg 464=M
 index:s.natReg 4474=i
 one:s.natReg 4481=1
lemma Cursor.withPC {S E M i pc:ℕ} {s:State} (h:Cursor S E M i s):
 Cursor S E M i (setPC s pc):=⟨h.source,h.directory,h.count,h.index,h.one⟩
def Table (W E A:ℕ) (xs:List BlockState) (s:State):Prop:=
 ∀ j,∀ (hj:j < xs.length),UniformSectorBatchDirectoryMachine.BatchCell W E A j (xs[j]'hj) s

def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32 → q≠126 → u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q < 147 ∨154 ≤ q) → (q < 4460 ∨4463 ≤ q) → (q < 4464 ∨4471 ≤ q) →
 q≠4474 → (q < 4476 ∨4482 ≤ q) → u.natReg q=s.natReg q
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,fun _ _ _=>rfl,fun _ _ _ _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq hj=>(k.2.2.2.1 q hq hj).trans (h.2.2.2.1 q hq hj),
 fun q h0 h1 h2 h3 h4=>(k.2.2.2.2 q h0 h1 h2 h3 h4).trans (h.2.2.2.2 q h0 h1 h2 h3 h4)⟩
lemma pad_frame {s u:State} (h:UniformSectorPaddingPreparation.Frame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun q h0 h1 h2 _ h4=>h.2.2.2.2 q h0 h1 h2 (by omega)⟩
def tick (s:State):State:=setPC (writeNat (setPC s 41) 4474 (s.natReg 4474+s.natReg 4481)) 3
lemma tick_frame (s:State):Frame s (tick s):=by
 refine ⟨rfl,rfl,rfl,fun _ _ _=>rfl,?_⟩
 intro q h0 h1 h2 h3 h4
 simp[tick,setPC,writeNat,next,h3]
lemma tick_cursor {S E M i:ℕ} {s:State} (h:Cursor S E M i s):
 Cursor S E M (i+1) (tick s):=by
 constructor <;>simp[tick,setPC,writeNat,next,h.source,h.directory,h.count,h.index,h.one]
lemma cursor_after_pad {S E M i:ℕ} {s u:State} (h:Cursor S E M i s)
 (frame:UniformSectorPaddingPreparation.Frame s u):Cursor S E M i u:=
 ⟨(frame.2.2.2.2 4472 (by omega) (by omega) (by omega) (by omega)).trans h.source,
  (frame.2.2.2.2 4473 (by omega) (by omega) (by omega) (by omega)).trans h.directory,
  (frame.2.2.2.2 464 (by omega) (by omega) (by omega) (by omega)).trans h.count,
  (frame.2.2.2.2 4474 (by omega) (by omega) (by omega) (by omega)).trans h.index,
  (frame.2.2.2.2 4481 (by omega) (by omega) (by omega) (by omega)).trans h.one⟩

lemma iteration {W S E A M i total B n:ℕ} (st:BlockState) (v:Fin total → Scalar)
 (x:Fin n → ℂ) (s:State) (h:Cursor S E M i s)
 (cell:UniformSectorBatchDirectoryMachine.BatchCell W E A i st s)
 (source:UniformSectorPaddingMachine.Source v S s) (hi:i < M)
 (fit:st.start+st.width ≤ total) (positive:0 < W) (roles:W ≤ B)
 (sep:S+total ≤ A) (buffer:A+W*total ≤ B) (entry:E+5*M ≤ B)
 (code:44 ≤ B) (pc:s.pc=3) (wb:WordBound B s):
 ∃u,BoundedRuns (programFor W) n x B s (5*(W*st.width)+2*st.width+30) u ∧u.pc=3 ∧
 UniformSectorPaddingMachine.Prefix
  (fun t:Fin st.width=>v ⟨st.start+t.val,by have tt:=t.isLt;omega⟩)
  (A+W*st.start) (W*st.width) u ∧Cursor S E M (i+1) u ∧Frame s u ∧
 UniformSectorPaddingMachine.Outside (A+W*st.start) (W*st.width) s u:=by
 let entered:=setPC s 4
 have eb:=changePC_bound B s 4 wb (by omega)
 have branch:BoundedRuns (programFor W) n x B s 1 entered:=
  .next wb (by simp[step,pc,branch_at,h.index,h.count,hi,entered,setPC]) (.refl eb)
 let ready:=setPC s 0
 obtain ⟨c,run,cp,padded,padFrame,outside⟩:=UniformSectorPaddingPreparation.execution
  (W:=W) (S:=S) (E:=E) (A:=A) (i:=i) (total:=total) (B:=B) st v x ready
  ⟨h.source,h.directory,h.index⟩ cell source fit positive roles sep buffer (by omega)
  (by omega) rfl (changePC_bound B s 0 wb (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed (pad_code W)
  (by rw[UniformSectorPaddingPreparation.program_length];omega) (by omega) run
 rw[show placed 4 ready=entered by cases s;rfl] at moved
 have cursor:=cursor_after_pad h padFrame
 have mBound:M ≤ B:=by simpa only[h.count] using wb.2.1 464
 have indexB:i+1 ≤ B:=by omega
 let advanced:=writeNat (setPC c 41) 4474 (i+1)
 have ab:=writeNat_bound B (setPC c 41) 4474 (i+1) moved.final_bound (by change 41+1 ≤ B;omega) indexB
 have advance:BoundedRuns (programFor W) n x B (setPC c 41) 1 advanced:=
  .next moved.final_bound (by simp[step,advance_at,setPC,evalNat,cursor.index,cursor.one,advanced]) (.refl ab)
 have endPC:advanced.pc=42:=rfl
 have same:tick c=setPC advanced 3:=by simp[tick,advanced,cursor.index,cursor.one]
 have last:BoundedRuns (programFor W) n x B advanced 1 (tick c):=by
  rw[same]
  exact .next ab (by rw[step,endPC,jump_at];rfl)
   (.refl (changePC_bound B advanced 3 ab (by omega)))
 refine ⟨tick c,?_,rfl,padded,tick_cursor cursor,(pad_frame padFrame).trans (tick_frame c),outside⟩
 convert branch.trans (moved.trans (advance.trans last)) using 1
 omega

def Fits (xs:List BlockState) (total:ℕ):Prop:=
 ∀j,∀ (hj:j < xs.length),(xs[j]'hj).start+(xs[j]'hj).width ≤ total
def Ordered (xs:List BlockState):Prop:=
 ∀j i,∀ (hj:j < xs.length),∀ (hi:i < xs.length),j < i →
 (xs[j]'hj).start+(xs[j]'hj).width ≤ (xs[i]'hi).start
def localValues {total:ℕ} (v:Fin total → Scalar) (st:BlockState)
 (fit:st.start+st.width ≤ total):Fin st.width → Scalar:=
 fun t=>v ⟨st.start+t.val,by have tt:=t.isLt;omega⟩
def Filled {total:ℕ} (W A:ℕ) (xs:List BlockState) (fits:Fits xs total)
 (v:Fin total → Scalar) (done:ℕ) (s:State):Prop:=
 ∀j,∀ (hj:j < xs.length),j < done → UniformSectorPaddingMachine.Prefix
  (localValues v (xs[j]'hj) (fits j hj))
  (A+W*(xs[j]'hj).start) (W*(xs[j]'hj).width) s

def cost (W:ℕ) (xs:List BlockState):ℕ:=
 (xs.map (fun st=>5*(W*st.width)+2*st.width+30)).sum+2
lemma cost_nil (W:ℕ):cost W []=2:=rfl
lemma cost_cons (W:ℕ) (st:BlockState) (xs:List BlockState):
 cost W (st::xs)=(5*(W*st.width)+2*st.width+30)+cost W xs:=by
 simp only[cost,List.map_cons,List.sum_cons];omega
lemma cost_sum (W:ℕ) (xs:List BlockState):
 cost W xs=(5*W+2)*(xs.map BlockState.width).sum+30*xs.length+2:=by
 induction xs with
 | nil=>simp[cost]
 | cons st xs ih=>rw[cost_cons,ih];simp only[List.map_cons,List.sum_cons,List.length_cons];ring

lemma preserve_filled {W A total i:ℕ} {xs:List BlockState} {v:Fin total → Scalar}
 (fits:Fits xs total) (ordered:Ordered xs) (hi:i < xs.length) {s u:State}
 (old:Filled W A xs fits v i s)
 (fresh:UniformSectorPaddingMachine.Prefix (localValues v (xs[i]'hi) (fits i hi))
  (A+W*(xs[i]'hi).start) (W*(xs[i]'hi).width) u)
 (outside:UniformSectorPaddingMachine.Outside
  (A+W*(xs[i]'hi).start) (W*(xs[i]'hi).width) s u):Filled W A xs fits v (i+1) u:=by
 intro j hj done
 by_cases eq:j=i
 · subst j;exact fresh
 · have less:j < i:=by omega
   have before:=ordered j i hj hi less
   have lifted:=Nat.mul_le_mul_left W before
   intro t ht
   have prior:=old j hj less t ht
   exact (outside _ (Or.inl (by nlinarith))).trans prior

lemma loop (remaining:List BlockState) {W S E A total B n:ℕ}
 (xs:List BlockState) (v:Fin total → Scalar) (x:Fin n → ℂ)
 (fits:Fits xs total) (ordered:Ordered xs) (positive:0 < W) (roles:W ≤ B)
 (sep:S+total ≤ A) (buffer:A+W*total ≤ B) (entry:E+5*xs.length ≤ B) (code:44 ≤ B):
 ∀i s,i ≤ xs.length → xs.drop i=remaining → s.pc=3 → WordBound B s →
 Cursor S E xs.length i s → Table W E A xs s → UniformSectorPaddingMachine.Source v S s →
 Filled W A xs fits v i s →
 ∃u,BoundedExecution (programFor W) n x B s (cost W remaining) u ∧u.pc=43 ∧
 Filled W A xs fits v xs.length u ∧Frame s u ∧
 UniformSectorPaddingMachine.Outside A (W*total) s u:=by
 induction remaining with
 | nil=>
   intro i s le suffix pc wb h table source filled
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_nil] at length
   have last:i=xs.length:=by omega
   let u:=setPC s 43
   have ub:=changePC_bound B s 43 wb (by omega)
   have branch:BoundedRuns (programFor W) n x B s 1 u:=
    .next wb (by simp[step,pc,branch_at,h.index,h.count,last,u,setPC]) (.refl ub)
   have stop:BoundedExecution (programFor W) n x B u 1 u:=
    .halt ub (by simp[step,u,setPC,halt_at])
   refine ⟨u,?_,rfl,?_,Frame.refl s,fun _ _=>rfl⟩
   · simpa only[cost_nil] using branch.executes stop
   · simpa only[Filled,UniformSectorPaddingMachine.Prefix,u,setPC,last] using filled
 | cons st remaining ih=>
   intro i s le suffix pc wb h table source filled
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_cons] at length
   have hi:i < xs.length:=by omega
   obtain ⟨equal,nextSuffix⟩:=List.cons.inj (suffix.symm.trans (List.drop_eq_getElem_cons hi))
   subst st
   obtain ⟨t,first,tp,padded,cursor,frame,out⟩:=iteration (xs[i]'hi) v x s h (table i hi) source hi
    (fits i hi) positive roles sep buffer entry code pc wb
   have tableT:Table W E A xs t:=by
    intro j hj
    simpa only[UniformSectorBatchDirectoryMachine.BatchCell,frame.1] using table j hj
   have sourceT:UniformSectorPaddingMachine.Source v S t:=by
    intro j
    exact (out _ (Or.inl (by have jj:=j.isLt;omega))).trans (source j)
   have filledT:Filled W A xs fits v (i+1) t:=preserve_filled fits ordered hi filled padded out
   obtain ⟨u,rest,up,done,frameU,outU⟩:=ih (i+1) t (by omega) nextSuffix.symm tp first.final_bound
    cursor tableT sourceT filledT
   refine ⟨u,?_,up,done,frame.trans frameU,?_⟩
   · rw[cost_cons]
     exact first.executes rest
   · intro q hq
     have endpoint:=Nat.mul_le_mul_left W (fits i hi)
     exact (outU q hq).trans (out q (by
      rcases hq with before|after
      · exact Or.inl (by omega)
      · exact Or.inr (by nlinarith)))

structure Header (S E M:ℕ) (s:State):Prop where
 source:s.natReg 4472=S
 directory:s.natReg 4473=E
 count:s.natReg 464=M
lemma boot_cursor {S E M:ℕ} {s:State} (h:Header S E M s):
 Cursor S E M 0 (applyBlock boot s):=by
 constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.source,h.directory,h.count]
lemma boot_frame (s:State):Frame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,fun _ _ _=>rfl,?_⟩
 intro q h0 h1 h2 h3 h4
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]

/-- Complete literal cursor over the genuine generated sector order. All
widths/starts come from the physical directory; every W-array buffer is written
once. No prepared padding bank, reverse list or child action is supplied. -/
theorem execution {W S E A total B n:ℕ} (axes:List UniformSectorPacking.Axis)
 (v:Fin total → Scalar) (x:Fin n → ℂ) (s:State)
 (volume:(UniformSectorPacking.radices axes).prod=total)
 (h:Header S E (UniformSectorPacking.sectorStates axes).length s)
 (table:Table W E A (UniformSectorPacking.sectorStates axes) s)
 (source:UniformSectorPaddingMachine.Source v S s) (positive:0 < W) (roles:W ≤ B)
 (sep:S+total ≤ A) (buffer:A+W*total ≤ B)
 (entry:E+5*(UniformSectorPacking.sectorStates axes).length ≤ B)
 (code:44 ≤ B) (pc:s.pc=0) (wb:WordBound B s):
 ∃u,BoundedExecution (programFor W) n x B s
  ((5*W+2)*total+30*(UniformSectorPacking.sectorStates axes).length+5) u ∧u.pc=43 ∧
 Filled W A (UniformSectorPacking.sectorStates axes)
  (by simpa only[Fits,volume] using UniformSectorBatchDirectoryMachine.sector_fits axes)
  v (UniformSectorPacking.sectorStates axes).length u ∧Frame s u ∧
 UniformSectorPaddingMachine.Outside A (W*total) s u:=by
 let xs:=UniformSectorPacking.sectorStates axes
 have fits:Fits xs total:=by
  simpa only[Fits,xs,volume] using UniformSectorBatchDirectoryMachine.sector_fits axes
 have ordered:Ordered xs:=UniformSectorBatchDirectoryMachine.sector_before axes
 have safe:readable boot s ∧peak boot s ≤ B:=by
  simp[readable,peak,boot,Op.readable,Op.peak]
  omega
 have first:=block_runs boot (programFor W) 0 n B x s (boot_code W) pc wb
  (by change 0+3 ≤ B;omega) safe.1 safe.2
 let b:=applyBlock boot s
 have bp:b.pc=3:=by rw[applyBlock_pc,pc];rfl
 have start:Filled W A xs fits v 0 b:=by intro j hj less;omega
 obtain ⟨u,rest,up,done,frame,out⟩:=loop xs xs v x fits ordered positive roles sep buffer entry code
  0 b (by omega) (by simp) bp first.final_bound (boot_cursor h) table source start
 refine ⟨u,?_,up,done,(boot_frame s).trans frame,out⟩
 convert first.executes rest using 1
 rw[cost_sum,UniformSectorBatchDirectoryMachine.sector_width_sum,volume]
 simp only[show boot.length=3 from rfl,xs]
 ring
end
end ExactFourierCircuits.UniformAllSectorPaddingMachine
