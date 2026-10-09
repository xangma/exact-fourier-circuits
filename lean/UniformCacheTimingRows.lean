import UniformCacheTimingControl
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingRows
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformLocalRectangleDescriptors (Row)

def ticks (L:List Row):ℕ:=(L.map (fun q=>4*Nat.clog 2 (2*(q.a+q.e))+28)).sum+1
def amounts (L:List Row):ℕ:=(L.map (fun q=>UniformCacheRowDurationMachine.amount q.a q.e)).sum

def writePrefixes (T ordinal c:ℕ)(L:List Row)(heap:ℕ→Option ℕ):ℕ→Option ℕ:=match L with
 | []=>heap
 | q::qs=>writePrefixes T (ordinal+1) (c+UniformCacheRowDurationMachine.amount q.a q.e) qs
   (Function.update heap (T+ordinal) (some c))

def TableAt (base i:ℕ)(L:List Row)(s:State):Prop:=∀ h : ℕ, (hh:h<L.length)→
 s.natHeap (base+7*(i+h)+2)=some (L[h]'hh).a ∧
 s.natHeap (base+7*(i+h)+3)=some (L[h]'hh).e

structure Cursor (D R U V T N K base count ordinal i c:ℕ)(s:State):Prop extends Header D R U V T N K s where
 base:s.natReg 6522=base
 count:s.natReg 6523=count
 correction:s.natReg 6528=c
 ordinal:s.natReg 6529=ordinal
 index:s.natReg 6530=i

noncomputable section
lemma Cursor.pc {D R U V T N K base count ordinal i c:ℕ}{s:State}
 (h:Cursor D R U V T N K base count ordinal i c s)(p:ℕ):
 Cursor D R U V T N K base count ordinal i c (setPC s p):=
 ⟨h.toHeader.pc p,h.base,h.count,h.correction,h.ordinal,h.index⟩
lemma TableAt.pc {base i:ℕ}{L:List Row}{s:State}(h:TableAt base i L s)(p:ℕ):TableAt base i L (setPC s p):=h
lemma TableAt.head {base i:ℕ}{q:Row}{qs:List Row}{s:State}(h:TableAt base i (q::qs) s):
 s.natHeap (base+7*i+2)=some q.a∧s.natHeap (base+7*i+3)=some q.e:=by
 have hx:=h 0 (by simp)
 change s.natHeap (base+7*(i+0)+2)=some q.a ∧ s.natHeap (base+7*(i+0)+3)=some q.e at hx
 simpa only [Nat.add_zero] using hx
lemma read_cursor {D R U V T N K base count ordinal i c:ℕ}(s:State)
 (h:Cursor D R U V T N K base count ordinal i c s):
 Cursor D R U V T N K base count ordinal i c (applyBlock rowRead s):=by
 constructor
 · constructor <;>simp [rowRead,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
   h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 all_goals simp [rowRead,applyBlock,Op.apply,writeNat,next,h.base,h.count,h.correction,h.ordinal,h.index]
lemma read_inputs {D R U V T N K base count ordinal i c:ℕ}{q:Row}{qs:List Row}(s:State)
 (h:Cursor D R U V T N K base count ordinal i c s)(ht:TableAt base i (q::qs) s):
 (applyBlock rowRead s).natReg 6540=q.a∧(applyBlock rowRead s).natReg 6541=q.e:=by
 have hh:=ht.head
 simp only [Nat.mul_comm,Nat.add_assoc] at hh
 simp [rowRead,applyBlock,Op.apply,writeNat,next,h.base,h.index,h.seven,h.two,h.one,hh.1,hh.2,Nat.add_assoc]
lemma read_heap {D R U V T N K base count ordinal i c:ℕ}(s:State)
 (h:Cursor D R U V T N K base count ordinal i c s):
 (applyBlock rowRead s).natHeap=Function.update s.natHeap (T+ordinal) (some c):=by
 simp [rowRead,applyBlock,Op.apply,writeNat,next,h.base,h.index,h.seven,h.two,h.one,h.requestStarts,h.ordinal,h.correction]
lemma read_regs (s:State)(r:ℕ)(hr:r<6528∨6551<r):
 (applyBlock rowRead s).natReg r=s.natReg r:=by
 simp (disch:=omega) [rowRead,applyBlock,Op.apply,writeNat,next]
lemma helper_cursor {D R U V T N K base count ordinal i c:ℕ}{s u:State}
 (h:Cursor D R U V T N K base count ordinal i c s)(f:UniformCacheRowDurationMachine.Frame s u):
 Cursor D R U V T N K base count ordinal i c u:=by
 constructor
 · constructor
   · exact (f.natReg _ (by omega)).trans h.nodes
   · exact (f.natReg _ (by omega)).trans h.requests
   · exact (f.natReg _ (by omega)).trans h.durations
   · exact (f.natReg _ (by omega)).trans h.starts
   · exact (f.natReg _ (by omega)).trans h.requestStarts
   · exact (f.natReg _ (by omega)).trans h.rootStart
   · exact (f.natReg _ (by omega)).trans h.nodeCount
   · exact (f.natReg _ (by omega)).trans h.requestCount
   · exact (f.natReg _ (by omega)).trans h.zero
   · exact (f.natReg _ (by omega)).trans h.one
   · exact (f.natReg _ (by omega)).trans h.two
   · exact (f.natReg _ (by omega)).trans h.three
   · exact (f.natReg _ (by omega)).trans h.seven
   · exact (f.natReg _ (by omega)).trans h.fourteen
 · exact (f.natReg _ (by omega)).trans h.base
 · exact (f.natReg _ (by omega)).trans h.count
 · exact (f.natReg _ (by omega)).trans h.correction
 · exact (f.natReg _ (by omega)).trans h.ordinal
 · exact (f.natReg _ (by omega)).trans h.index
lemma advance_cursor {D R U V T N K base count ordinal i c amount:ℕ}(s:State)
 (h:Cursor D R U V T N K base count ordinal i c s)(ha:s.natReg 6542=amount):
 Cursor D R U V T N K base count (ordinal+1) (i+1) (c+amount) (applyBlock rowAdvance s):=by
 constructor
 · constructor <;>simp [rowAdvance,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
   h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 all_goals simp [rowAdvance,applyBlock,Op.apply,writeNat,next,h.base,h.count,h.correction,h.ordinal,h.index,h.one,ha]
lemma advance_regs (s:State)(r:ℕ)(hr:r<6528∨6551<r):
 (applyBlock rowAdvance s).natReg r=s.natReg r:=by
 simp (disch:=omega) [rowAdvance,applyBlock,Op.apply,writeNat,next]

/-- Rectangle durations are computed from the actual a/e words by the charged
18-instruction doubling helper. Every stored row prefix is produced here. -/
theorem loop (n D R U V T N K base count ordinal i c B:ℕ)(L:List Row)(x:Fin n→ℂ)(s:State)
 (h:Cursor D R U V T N K base count ordinal i c s)(ht:TableAt base i L s)
 (endIndex:i+L.length=count)(hp:s.pc=41)(hs:WordBound B s)(code:122≤B)
 (source:base+7*count+4≤T)(sourceBound:base+7*count+4≤B)
 (destination:T+ordinal+L.length≤B)(total:c+amounts L≤B)
 (budgets:∀q∈L,UniformCacheRowDurationMachine.budget q.a q.e≤B):∃u,
 BoundedRuns program n x B s (ticks L) u∧u.pc=77∧
 Cursor D R U V T N K base count (ordinal+L.length) count (c+amounts L) u∧
 u.natHeap=writePrefixes T ordinal c L s.natHeap∧
 (∀r,r<6528∨6551<r→u.natReg r=s.natReg r):=by
 induction L generalizing i ordinal c s with
 | nil=>
  have eq:i=count:=by simpa using endIndex
  have step:UniformMachine.step program n x s=.running (setPC s 77):=by
   simp [UniformMachine.step,hp,code_41,h.index,h.count,eq,setPC]
  refine ⟨setPC s 77,control_run program n B 77 x s hs (by omega) step,rfl,?_,rfl,fun _ _=>rfl⟩
  simpa [amounts,eq] using h.pc 77
 | cons q qs ih=>
  have hi:i<count:=by simp only [List.length_cons] at endIndex;omega
  have enterStep:UniformMachine.step program n x s=.running (setPC s 42):=by
   simp [UniformMachine.step,hp,code_41,h.index,h.count,hi,setPC]
  have enter:=control_run program n B 42 x s hs (by omega) enterStep
  let a:=setPC s 42
  have ah:=h.pc 42
  have heads:=ht.head
  simp only [Nat.mul_comm,Nat.add_assoc] at heads
  have qbudget:=budgets q (by simp)
  have qa:q.a≤B∧q.e≤B:=by unfold UniformCacheRowDurationMachine.budget at qbudget;omega
  have read:=block_runs rowRead program 42 n B x a rowRead_code rfl enter.final_bound
   (by change 50≤B;omega) (by
    simp [rowRead,readable,Op.readable,Op.apply,writeNat,next,a,setPC,h.base,h.index,h.seven,h.two,h.one,
     heads.1,heads.2,Nat.add_assoc]) (by
    simp [rowRead,peak,Op.peak,Op.apply,writeNat,next,a,setPC,h.base,h.index,h.seven,h.two,h.one,
     h.requestStarts,h.ordinal,h.correction,heads.1,heads.2,Nat.add_assoc]
    have nonnegative:0≤amounts (q::qs):=Nat.zero_le _
    omega)
  let b:=applyBlock rowRead a
  have bp:b.pc=50:=by rw [applyBlock_pc];rfl
  have inputs:=read_inputs a ah ht
  obtain ⟨z,helper,zp,value,hf⟩:=UniformCacheRowDurationMachine.execution n q.a q.e B x (setPC b 0)
   inputs.1 inputs.2 rfl (changePC_bound B b 0 read.final_bound (by omega)) qbudget
  have placed:=UniformBoundedAssembly.boundedExecution_placed row_code (by simp [UniformCacheRowDurationMachine.program_length];omega)
   (by omega:68≤B) helper
  have placedStart:UniformAssembly.placed 50 (setPC b 0)=b:=by
   change setPC b 50=b
   rw [←bp]
   cases b
   rfl
  rw [placedStart] at placed
  let z':=setPC z 68
  have zh:Cursor D R U V T N K base count ordinal i c z':=
   (helper_cursor ((read_cursor a ah).pc 0) hf).pc 68
  have value' : z'.natReg 6542=UniformCacheRowDurationMachine.amount q.a q.e := value
  have last:=block_runs rowAdvance program 68 n B x z' rowAdvance_code rfl placed.final_bound
   (by change 71≤B;omega) (by simp [rowAdvance,readable,Op.readable]) (by
    simp [rowAdvance,peak,Op.peak,Op.apply,writeNat,next,zh.correction,zh.ordinal,zh.index,zh.one,value']
    simp only [amounts,List.map_cons,List.sum_cons] at total
    simp only [List.length_cons] at destination
    omega)
  let b':=applyBlock rowAdvance z'
  have b'p:b'.pc=71:=by rw [applyBlock_pc];rfl
  have backStep:UniformMachine.step program n x b'=.running (setPC b' 41):=by simp [UniformMachine.step,b'p,code_71,setPC]
  have back:=control_run program n B 41 x b' last.final_bound (by omega) backStep
  have bh:=advance_cursor z' zh value'
  have heap:b'.natHeap=Function.update s.natHeap (T+ordinal) (some c):=by
   change z.natHeap=_
   rw [hf.natHeap]
   exact read_heap a ah
  have tailTable:TableAt base (i+1) qs (setPC b' 41):=by
   intro j hj
   have old:=ht (j+1) (by simp;omega)
   have addr2:base+7*(i+1+j)+2<T+ordinal:=by simp only [List.length_cons] at endIndex;omega
   have addr3:base+7*(i+1+j)+3<T+ordinal:=by simp only [List.length_cons] at endIndex;omega
   constructor
   · change b'.natHeap _=_
     rw [heap,Function.update_of_ne (by omega:base+7*(i+1+j)+2≠T+ordinal)]
     simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using old.1
   · change b'.natHeap _=_
     rw [heap,Function.update_of_ne (by omega:base+7*(i+1+j)+3≠T+ordinal)]
     simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using old.2
  obtain ⟨u,tail,up,out,uh,uf⟩:=ih (ordinal+1) (i+1) (c+UniformCacheRowDurationMachine.amount q.a q.e)
   (setPC b' 41) (bh.pc 41) tailTable (by simp only [List.length_cons] at endIndex;omega) rfl back.final_bound
   (by simp only [List.length_cons] at destination;omega) (by simpa [amounts,Nat.add_assoc] using total)
   (fun r hr=>budgets r (by simp [hr]))
  refine ⟨u,?_,up,?_,?_,?_⟩
  · convert (((enter.trans read).trans placed).trans last).trans (back.trans tail) using 1
    change ticks (q::qs)=1+8+(4*Nat.clog 2 (2*(q.a+q.e))+15)+3+(1+ticks qs)
    simp only [ticks,List.map_cons,List.sum_cons]
    omega
  · simpa [amounts,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using out
  · rw [uh]
    change writePrefixes T (ordinal+1) (c+UniformCacheRowDurationMachine.amount q.a q.e) qs b'.natHeap=_
    rw [heap]
    rfl
  · intro r hr
    rw [uf r hr]
    change b'.natReg r=s.natReg r
    rw [advance_regs z' r hr]
    change z.natReg r=s.natReg r
    rw [hf.natReg r (by omega)]
    change (applyBlock rowRead a).natReg r=s.natReg r
    rw [read_regs a r hr]
    rfl
end
end ExactFourierCircuits.UniformCacheTimingRows
