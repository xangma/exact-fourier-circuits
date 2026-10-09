import UniformMultiAxisSectorMetadataPreparation
import UniformTensorMonomialMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorBatchDirectoryMachine
open UniformMachine UniformTensorMonomialMachine
open UniformSectorPacking (BlockState)
noncomputable section
/-- Consume the genuine124 directory/count headers3215/464. Emit(q,width,
W-role buffer base,original packed start,W*width), in actual sector order.
This is address/header production; buffer padding/child execution follow separately. -/
def boot (W:ℕ):List Op:=[.literal 4444 W,.literal 4445 0,.literal 4446 1,
 .literal 4447 3,.literal 4448 5,.literal 4449 0,.add 4450 464 4445,.add 4440 3215 4445]
def body:List Op:=[.mul 4451 4449 4447,.add 4451 4440 4451,.getNat 4452 4451,
 .add 4451 4451 4446,.getNat 4453 4451,.add 4451 4451 4446,.getNat 4454 4451,
 .mul 4455 4449 4448,.add 4455 4441 4455,.putNat 4455 4454,
 .add 4455 4455 4446,.putNat 4455 4453,.mul 4456 4444 4452,.add 4456 4442 4456,
 .add 4455 4455 4446,.putNat 4455 4456,.add 4455 4455 4446,.putNat 4455 4452,
 .mul 4457 4444 4453,.add 4455 4455 4446,.putNat 4455 4457,.add 4449 4449 4446]
def programFor (W:ℕ):Program:=(boot W).map Op.code++[.branchLT 4449 4450 9 32]++
 body.map Op.code++[.jump 8,.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma boot_length (W:ℕ):(boot W).length=8:=rfl
lemma body_length:body.length=22:=rfl
lemma program_length (W:ℕ):(programFor W).length=33:=rfl
lemma boot_code (W:ℕ):BlockAt (boot W) (programFor W) 0:=by
 intro i hi;change i<8 at hi;interval_cases i <;>rfl
lemma body_code (W:ℕ):BlockAt body (programFor W) 9:=by
 intro i hi;change i<22 at hi;interval_cases i <;>rfl
lemma branch_at (W:ℕ):(programFor W)[8]?=some (.branchLT 4449 4450 9 32):=rfl
lemma jump_at (W:ℕ):(programFor W)[31]?=some (.jump 8):=rfl
lemma halt_at (W:ℕ):(programFor W)[32]?=some .halt:=rfl

def Cell (D i:ℕ) (st:BlockState) (s:State):Prop:=
 s.natHeap (D+3*i)=some st.start ∧s.natHeap (D+3*i+1)=some st.width ∧
 s.natHeap (D+3*i+2)=some st.pairs
def Table (D:ℕ) (xs:List BlockState) (s:State):Prop:=
 ∀i,(hi:i<xs.length)→Cell D i (xs[i]'hi) s
lemma directory_table (L:UniformSectorMetadataMachine.Layout) (xs:List BlockState) (s:State)
 (h:UniformSectorMetadataMachine.Directory L 0 xs s):Table L.directory xs s:=by
 have get:∀count,(UniformSectorMetadataMachine.Directory L count xs s)→
  ∀i,(hi:i<xs.length)→UniformSectorMetadataMachine.Cell L (count+i) (xs[i]'hi) s:=by
  clear h
  induction xs with
  | nil=>simp
  | cons a xs ih=>
    intro count hs i hi
    cases i with
    | zero=>simpa only[Nat.add_zero,List.getElem_cons_zero] using hs.1
    | succ i=>
      have rest:=ih (count+1) hs.2 i (by simp only[List.length_cons] at hi;omega)
      simpa only[List.getElem_cons_succ,show count+(i+1)=(count+1)+i by omega] using rest
 intro i hi
 simpa only[Cell,UniformSectorMetadataMachine.Cell,Nat.zero_add,Nat.mul_comm i 3] using get 0 h i hi

structure Cursor (W D E A M i:ℕ) (s:State):Prop where
 source:s.natReg 4440=D
 target:s.natReg 4441=E
 buffer:s.natReg 4442=A
 roles:s.natReg 4444=W
 zero:s.natReg 4445=0
 one:s.natReg 4446=1
 three:s.natReg 4447=3
 five:s.natReg 4448=5
 index:s.natReg 4449=i
 count:s.natReg 4450=M

lemma Cursor.withPC {W D E A M i pc:ℕ} {s:State} (h:Cursor W D E A M i s):
 Cursor W D E A M i (setPC s pc):=
 ⟨h.source,h.target,h.buffer,h.roles,h.zero,h.one,h.three,h.five,h.index,h.count⟩

def BatchCell (W E A i:ℕ) (st:BlockState) (s:State):Prop:=
 s.natHeap (E+5*i)=some st.pairs ∧s.natHeap (E+5*i+1)=some st.width ∧
 s.natHeap (E+5*i+2)=some (A+W*st.start) ∧
 s.natHeap (E+5*i+3)=some st.start ∧s.natHeap (E+5*i+4)=some (W*st.width)
def Frame (s u:State):Prop:=u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 ∀q,(q<4440 ∨4441≤q)→(q<4444 ∨4458≤q)→u.natReg q=s.natReg q
lemma body_heap {W D E A M i:ℕ} {st:BlockState} {s:State}
 (h:Cursor W D E A M i s) (cell:Cell D i st s):
 (applyBlock body s).natHeap=
 Function.update (Function.update (Function.update (Function.update
 (Function.update s.natHeap (E+5*i) (some st.pairs)) (E+5*i+1) (some st.width))
 (E+5*i+2) (some (A+W*st.start))) (E+5*i+3) (some st.start))
 (E+5*i+4) (some (W*st.width)):=by
 rcases cell with ⟨hs,hw,hq⟩
 simp only[Nat.add_assoc] at hs hw hq
 simp[body,applyBlock,Op.apply,writeNat,next,h.source,h.target,h.buffer,h.roles,h.one,h.three,
  h.five,h.index,hs,hw,hq,Nat.mul_comm i 3,Nat.mul_comm i 5,Nat.add_assoc]
lemma body_cursor {W D E A M i:ℕ} {s:State} (h:Cursor W D E A M i s):
 Cursor W D E A M (i+1) (setPC (applyBlock body (setPC s 9)) 8):=by
 constructor <;> simp[body,applyBlock,Op.apply,writeNat,next,setPC,h.source,h.target,h.buffer,
  h.roles,h.zero,h.one,h.three,h.five,h.index,h.count]
lemma body_cell {W D E A M i:ℕ} {st:BlockState} {s:State}
 (h:Cursor W D E A M i s) (cell:Cell D i st s):
 BatchCell W E A i st (setPC (applyBlock body (setPC s 9)) 8):=by
 have heap:=body_heap (h.withPC (pc:=9)) cell
 unfold BatchCell
 change _ ∧ _ ∧ _ ∧ _ ∧ _
 simp only[show (setPC (applyBlock body (setPC s 9)) 8).natHeap=(applyBlock body (setPC s 9)).natHeap from rfl,heap]
 simp (disch:=omega) [Function.update_of_ne]
lemma body_outside {W D E A M i:ℕ} {st:BlockState} {s:State}
 (h:Cursor W D E A M i s) (cell:Cell D i st s) (q:ℕ) (hq:q<E+5*i ∨E+5*i+5≤q):
 (setPC (applyBlock body (setPC s 9)) 8).natHeap q=s.natHeap q:=by
 have heap:=body_heap (h.withPC (pc:=9)) cell
 change (applyBlock body (setPC s 9)).natHeap q=s.natHeap q
 rw[heap]
 simp (disch:=omega) [Function.update_of_ne,setPC]
lemma body_safe {W D E A M i total B:ℕ} {st:BlockState} {s:State}
 (h:Cursor W D E A M i s) (cell:Cell D i st s) (hi:i<M)
 (fit:st.start+st.width≤total) (entry:E+5*M≤B) (buffer:A+W*total≤B)
 (source:D+3*M≤E) (_code:33≤B) (wb:WordBound B s):
 readable body (setPC s 9) ∧peak body (setPC s 9)≤B:=by
 have hs:st.start≤total:=by omega
 have hw:st.width≤total:=by omega
 have ws:=Nat.mul_le_mul_left W hs
 have ww:=Nat.mul_le_mul_left W hw
 have widthB:st.width≤B:=(wb.2.2.1 _ _ cell.2.1).2
 have startB:st.start≤B:=(wb.2.2.1 _ _ cell.1).2
 have qp:st.pairs≤B:=(wb.2.2.1 _ _ cell.2.2).2
 rcases cell with ⟨hstart,hwidth,hq⟩
 simp only[Nat.add_assoc] at hstart hwidth hq
 constructor
 · simp[readable,body,Op.readable,Op.apply,writeNat,next,setPC,h.source,h.one,h.three,h.index,hstart,hwidth,hq,Nat.mul_comm i 3,Nat.add_assoc]
 · simp[peak,body,Op.peak,Op.apply,writeNat,next,setPC,h.source,h.target,h.buffer,
    h.roles,h.one,h.three,h.five,h.index,hstart,hwidth,hq,Nat.mul_comm i 3,Nat.add_assoc]
   omega


def nextState (s:State):State:=setPC (applyBlock body (setPC s 9)) 8
lemma iteration {W D E A M i total B n:ℕ} {st:BlockState} {s:State}
 (h:Cursor W D E A M i s) (cell:Cell D i st s) (hi:i<M)
 (fit:st.start+st.width≤total) (entry:E+5*M≤B) (buffer:A+W*total≤B)
 (source:D+3*M≤E) (code:33≤B) (x:Fin n→ℂ) (pc:s.pc=8) (wb:WordBound B s):
 BoundedRuns (programFor W) n x B s 24 (nextState s):=by
 let e:=setPC s 9
 have eb:=changePC_bound B s 9 wb (by omega)
 have first:BoundedRuns (programFor W) n x B s 1 e:=.next wb
  (by simp[step,pc,branch_at,h.index,h.count,hi,e,setPC]) (.refl eb)
 have safe:=body_safe h cell hi fit entry buffer source code wb
 have run:=block_runs body (programFor W) 9 n B x e (body_code W) rfl eb
  (by rw[body_length];omega) safe.1 safe.2
 have stop:(applyBlock body e).pc=31:=by rw[applyBlock_pc,body_length];rfl
 have last:BoundedRuns (programFor W) n x B (applyBlock body e) 1 (nextState s):=
  .next run.final_bound (by rw[step,stop,jump_at];rfl)
   (.refl (changePC_bound B _ 8 run.final_bound (by omega)))
 simpa only[body_length] using first.trans (run.trans last)

lemma iteration_frame {W D E A M i:ℕ} {s:State} (_h:Cursor W D E A M i s):
 Frame s (nextState s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro q hq hqq
 simp (disch:=omega) [nextState,body,applyBlock,Op.apply,setPC,writeNat,next]

def Written (W E A i:ℕ) (xs:List BlockState) (s:State):Prop:=
 ∀ j, ∀ (hj : j < xs.length), j < i → BatchCell W E A j (xs[j]'hj) s
lemma table_retained {W D E A M i:ℕ} {xs:List BlockState} {s:State}
 (h:Cursor W D E A M i s) (table:Table D xs s) (len:M=xs.length) (hi:i<M)
 (source:D+3*M≤E):Table D xs (nextState s):=by
 intro j hj
 have cell:=table i (by omega)
 have outside:=body_outside h cell
 unfold Cell
 have old:=table j hj
 have b0:=outside (D+3*j) (Or.inl (by omega))
 have b1:=outside (D+3*j+1) (Or.inl (by omega))
 have b2:=outside (D+3*j+2) (Or.inl (by omega))
 exact ⟨b0.trans old.1,b1.trans old.2.1,b2.trans old.2.2⟩
lemma written_step {W D E A M i:ℕ} {xs:List BlockState} {s:State}
 (h:Cursor W D E A M i s) (table:Table D xs s) (old:Written W E A i xs s)
 (len:M=xs.length) (hi:i<M):Written W E A (i+1) xs (nextState s):=by
 intro j hj hjdone
 have cell:=table i (by omega)
 by_cases eq:j=i
 · subst j;exact body_cell h cell
 · have prior:=old j hj (by omega)
   have outside:=body_outside h cell
   unfold BatchCell at prior ⊢
   rcases prior with ⟨h0,h1,h2,h3,h4⟩
   exact ⟨(outside _ (by omega)).trans h0,(outside _ (by omega)).trans h1,
    (outside _ (by omega)).trans h2,(outside _ (by omega)).trans h3,
    (outside _ (by omega)).trans h4⟩


lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 k.2.2.2.1.trans h.2.2.2.1,fun q hq hqq=>(k.2.2.2.2 q hq hqq).trans (h.2.2.2.2 q hq hqq)⟩
def Outside (E M:ℕ) (s u:State):Prop:=
 ∀ q, (q < E ∨ E+5*M ≤ q) → u.natHeap q=s.natHeap q
lemma loop (fuel:ℕ) {W D E A total B n:ℕ} (xs:List BlockState)
 (x:Fin n→ℂ) (fits:∀ j,∀ (hj:j<xs.length), (xs[j]'hj).start+(xs[j]'hj).width≤total)
 (entry:E+5*xs.length≤B) (buffer:A+W*total≤B) (source:D+3*xs.length≤E) (code:33≤B):
 ∀ i s, i+fuel=xs.length → s.pc=8 → WordBound B s →
 Cursor W D E A xs.length i s → Table D xs s → Written W E A i xs s →
 ∃ u, BoundedExecution (programFor W) n x B s (24*fuel+2) u ∧ u.pc=32 ∧
 Written W E A xs.length xs u ∧ Table D xs u ∧ Frame s u ∧ Outside E xs.length s u:=by
 induction fuel with
 | zero=>
   intro i s len pc wb h table written
   have last:i=xs.length:=by omega
   let u:=setPC s 32
   have ub:=changePC_bound B s 32 wb (by omega)
   have stop:BoundedExecution (programFor W) n x B u 1 u:=
    .halt ub (by simp[step,u,setPC,halt_at])
   have first:BoundedRuns (programFor W) n x B s 1 u:=
    .next wb (by simp[step,pc,branch_at,h.index,h.count,last,u,setPC]) (.refl ub)
   refine ⟨u,?_,rfl,?_,table,Frame.refl s,fun _ _=>rfl⟩
   · simpa only[Nat.mul_zero,Nat.zero_add] using first.executes stop
   · simpa only[Written,BatchCell,u,setPC,last] using written
 | succ fuel ih=>
   intro i s len pc wb h table written
   have hi:i<xs.length:=by omega
   have cell:=table i hi
   have run:=iteration h cell hi (fits i hi) entry buffer source code x pc wb
   have hc:=body_cursor h
   have ht:=table_retained h table rfl hi source
   have hw:=written_step h table written rfl hi
   obtain ⟨u,rest,up,writtenU,tableU,frameU,outU⟩:=
    ih (i+1) (nextState s) (by omega) rfl run.final_bound hc ht hw
   refine ⟨u,?_,up,writtenU,tableU,(iteration_frame h).trans frameU,?_⟩
   · convert run.executes rest using 1
     omega
   · intro q hq
     exact (outU q hq).trans (body_outside h cell q (by rcases hq with hq|hq; all_goals omega))

structure Header (D E A M:ℕ) (s:State):Prop where
 source:s.natReg 3215=D
 count:s.natReg 464=M
 target:s.natReg 4441=E
 buffer:s.natReg 4442=A
lemma boot_cursor {W D E A M:ℕ} {s:State} (h:Header D E A M s):
 Cursor W D E A M 0 (applyBlock (boot W) s):=by
 constructor <;> simp[boot,applyBlock,Op.apply,writeNat,next,h.source,h.count,h.target,h.buffer]
lemma boot_frame (W:ℕ) (s:State):Frame s (applyBlock (boot W) s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro q hq hqq
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_safe {W D E A M B:ℕ} {s:State} (h:Header D E A M s)
 (roles:W≤B) (code:33≤B) (wb:WordBound B s):
 readable (boot W) s ∧ peak (boot W) s≤B:=by
 have ds: D≤B:=by simpa only[h.source] using wb.2.1 3215
 have ms: M≤B:=by simpa only[h.count] using wb.2.1 464
 simp[readable,peak,boot,Op.readable,Op.peak,Op.apply,writeNat,next,h.source,h.count]
 omega

/-- Every address and store is executed. The input is the actual three-cell
sector directory; no batch headers, padding buffers, or child action is supplied. -/
theorem execution {W D E A total B n:ℕ} (xs:List BlockState) (x:Fin n→ℂ) (s:State)
 (h:Header D E A xs.length s) (table:Table D xs s)
 (fits:∀ j,∀ (hj:j<xs.length), (xs[j]'hj).start+(xs[j]'hj).width≤total)
 (entry:E+5*xs.length≤B) (buffer:A+W*total≤B) (source:D+3*xs.length≤E)
 (roles:W≤B) (code:33≤B) (pc:s.pc=0) (wb:WordBound B s):
 ∃ u, BoundedExecution (programFor W) n x B s (24*xs.length+10) u ∧ u.pc=32 ∧
 Written W E A xs.length xs u ∧ Table D xs u ∧ Frame s u ∧ Outside E xs.length s u:=by
 have safe:=boot_safe h roles code wb
 have first:=block_runs (boot W) (programFor W) 0 n B x s (boot_code W) pc wb
  (by rw[boot_length];omega) safe.1 safe.2
 let b:=applyBlock (boot W) s
 have bp:b.pc=8:=by rw[applyBlock_pc,boot_length,pc]
 have bt:Table D xs b:=table
 have bw:Written W E A 0 xs b:=by intro j hj hi;omega
 obtain ⟨u,rest,up,filled,tableU,frameU,outU⟩:=
  loop xs.length xs x fits entry buffer source code 0 b (by omega) bp first.final_bound
   (boot_cursor h) bt bw
 refine ⟨u,?_,up,filled,tableU,(boot_frame W s).trans frameU,outU⟩
 convert first.executes rest using 1
 simp only[boot_length];omega

lemma expected_fit (axes:List UniformSectorPacking.Axis)
 (b:UniformSectorPacking.BlockChoices axes):
 (UniformSectorPacking.expectedBlockState axes b).start+
 (UniformSectorPacking.expectedBlockState axes b).width≤(UniformSectorPacking.radices axes).prod:=by
 have positive:=UniformSectorPacking.sectorProduct_pos axes b
 let last:Fin (UniformSectorPacking.sectorRadices axes b).prod:=⟨_,Nat.sub_lt positive (by decide : 0<1)⟩
 have bound:=(UniformSectorPacking.sectorCoordinate axes b last).isLt
 rw[UniformSectorPacking.sectorCoordinate_value] at bound
 change UniformSectorPacking.sectorStart axes b+(UniformSectorPacking.sectorRadices axes b).prod≤_
 change UniformSectorPacking.sectorStart axes b+((UniformSectorPacking.sectorRadices axes b).prod-1)<_ at bound
 omega
lemma sector_fits (axes:List UniformSectorPacking.Axis):
 ∀ j,∀ (hj:j<(UniformSectorPacking.sectorStates axes).length),
 ((UniformSectorPacking.sectorStates axes)[j]'hj).start+
 ((UniformSectorPacking.sectorStates axes)[j]'hj).width≤(UniformSectorPacking.radices axes).prod:=by
 intro j hj
 simpa only[UniformSectorPacking.sectorStates,List.getElem_ofFn] using
  expected_fit axes ((UniformSectorPacking.sectorIndexEquiv axes).symm ⟨j,by simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using hj⟩)
lemma sector_width (axes:List UniformSectorPacking.Axis):
 ∀ j,∀ (hj:j<(UniformSectorPacking.sectorStates axes).length),
 ((UniformSectorPacking.sectorStates axes)[j]'hj).width=
 2^((UniformSectorPacking.sectorStates axes)[j]'hj).pairs:=by
 intro j hj
 simpa only[UniformSectorPacking.sectorStates,List.getElem_ofFn,UniformSectorPacking.expectedBlockState] using
  UniformSectorPacking.sectorWidth_pow_two axes
  ((UniformSectorPacking.sectorIndexEquiv axes).symm ⟨j,by simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using hj⟩)
lemma sector_count (axes:List UniformSectorPacking.Axis):
 (UniformSectorPacking.sectorStates axes).length=(UniformSectorPacking.blockCounts axes).prod:=by
 simp only[UniformSectorPacking.sectorStates,List.length_ofFn,UniformSectorPacking.sectorWidths_length]

lemma block_before_order (ws:List ℕ) (i j:Fin ws.length) (lt:i.val < j.val):
 UniformTraversal.blockBefore ws i+ws.get i  ≤  UniformTraversal.blockBefore ws j:=by
 induction ws with
 | nil=>exact Fin.elim0 i
 | cons q ws ih=>
   revert i
   refine Fin.cases ?_ (fun j=>?_) j
   · intro i lt
     change i.val < 0 at lt
     omega
   · intro i
     refine Fin.cases ?_ (fun i=>?_) i
     · intro _lt
       simp[UniformTraversal.blockBefore]
     · intro lt
       have h:=ih i j (by change i.val+1 < j.val+1 at lt;omega)
       simpa [UniformTraversal.blockBefore,Nat.add_assoc] using Nat.add_le_add_left h q
lemma sector_start_index (axes:List UniformSectorPacking.Axis) (j:ℕ)
 (hj:j < (UniformSectorPacking.sectorStates axes).length):
 ((UniformSectorPacking.sectorStates axes)[j]'hj).start=
 UniformTraversal.blockBefore (UniformSectorPacking.sectorWidths axes)
  ⟨j,by simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using hj⟩:=by
 simp only[UniformSectorPacking.sectorStates,List.getElem_ofFn,UniformSectorPacking.expectedBlockState]
 exact (UniformSectorPacking.sectorStart_before axes _).symm.trans
  (congrArg (UniformTraversal.blockBefore (UniformSectorPacking.sectorWidths axes))
   ((UniformSectorPacking.sectorIndexEquiv axes).apply_symm_apply _))
lemma sector_width_index (axes:List UniformSectorPacking.Axis) (j:ℕ)
 (hj:j < (UniformSectorPacking.sectorStates axes).length):
 ((UniformSectorPacking.sectorStates axes)[j]'hj).width=
 (UniformSectorPacking.sectorWidths axes).get
  ⟨j,by simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using hj⟩:=by
 simp only[UniformSectorPacking.sectorStates,List.getElem_ofFn,UniformSectorPacking.expectedBlockState]
 rw[←UniformSectorPacking.sectorWidths_get]
 exact congrArg ((UniformSectorPacking.sectorWidths axes).get)
  ((UniformSectorPacking.sectorIndexEquiv axes).apply_symm_apply _)
lemma sector_before (axes:List UniformSectorPacking.Axis) (i j:ℕ)
 (hi:i < (UniformSectorPacking.sectorStates axes).length)
 (hj:j < (UniformSectorPacking.sectorStates axes).length) (lt:i < j):
 ((UniformSectorPacking.sectorStates axes)[i]'hi).start+
 ((UniformSectorPacking.sectorStates axes)[i]'hi).width ≤
 ((UniformSectorPacking.sectorStates axes)[j]'hj).start:=by
 rw[sector_start_index,sector_width_index,sector_start_index]
 exact block_before_order _ _ _ lt
lemma sector_width_sum (axes:List UniformSectorPacking.Axis):
 ((UniformSectorPacking.sectorStates axes).map UniformSectorPacking.BlockState.width).sum=
 (UniformSectorPacking.radices axes).prod:=by
 have eq:((UniformSectorPacking.sectorStates axes).map UniformSectorPacking.BlockState.width)=
  UniformSectorPacking.sectorWidths axes:=by
  apply List.ext_getElem
  · simp only[UniformSectorPacking.sectorStates,List.length_map,List.length_ofFn]
  · intro j h1 h2
    simp only[List.getElem_map]
    exact sector_width_index axes j (by simpa only[List.length_map] using h1)
 rw[eq,UniformSectorPacking.sectorWidths_sum]

end
end ExactFourierCircuits.UniformSectorBatchDirectoryMachine
