import UniformCacheTimingForwardRows
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingForwardNode
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformCacheTimingForwardRows (Values writeStarts)

structure Loaded (D R U V T N K k parent base count duration correction : ℕ) (s : State) : Prop
 extends Init D R U V T N K k s where
 parent : s.natReg 6521=parent
 base : s.natReg 6522=base
 count : s.natReg 6523=count
 duration : s.natReg 6526=duration
 correction : s.natReg 6528=correction
 address : s.natReg 6525=V+k
noncomputable section
lemma Loaded.pc {D R U V T N K k parent base count duration correction : ℕ} {s : State}
 (h : Loaded D R U V T N K k parent base count duration correction s) (p : ℕ) :
 Loaded D R U V T N K k parent base count duration correction (setPC s p) :=
 ⟨h.toInit.pc p,h.parent,h.base,h.count,h.duration,h.correction,h.address⟩
lemma load_header {D R U V T N K k parent base count duration correction : ℕ} (s : State)
 (h : Init D R U V T N K k s)
 (p : s.natHeap (D+7*k+3)=some parent) (b : s.natHeap (D+7*k+5)=some base)
 (c : s.natHeap (D+7*k+6)=some count) (d : s.natHeap (U+k)=some duration)
 (a : s.natHeap (V+k)=some correction) :
 Loaded D R U V T N K k parent base count duration correction (applyBlock loadForward s) := by
 simp only [Nat.add_assoc,Nat.mul_comm] at p b c
 constructor
 · constructor
   · constructor <;>simp [loadForward,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [loadForward,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [loadForward,applyBlock,Op.apply,writeNat,next,h.nodes,h.index,h.seven,h.three,h.two,h.one,
   h.durations,h.starts,p,b,c,d,a,Nat.add_assoc]
lemma load_heap (s : State) : (applyBlock loadForward s).natHeap=s.natHeap := by
 rfl
lemma start_header {D R U V T N K k parent base count duration correction : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s) :
 Loaded D R U V T N K k parent base count duration correction (applyBlock parentStart s) := by
 constructor
 · constructor
   · constructor <;>simp [parentStart,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [parentStart,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [parentStart,applyBlock,Op.apply,writeNat,next,h.parent,h.base,h.count,h.duration,h.correction,h.address]
lemma root_header {D R U V T N K k parent base count duration correction : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s) :
 Loaded D R U V T N K k parent base count duration correction (applyBlock rootStart s) := by
 constructor
 · constructor
   · constructor <;>simp [rootStart,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [rootStart,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [rootStart,applyBlock,Op.apply,writeNat,next,h.parent,h.base,h.count,h.duration,h.correction,h.address]

lemma setup_header {D R U V T N K k parent base count duration correction : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s) :
 Loaded D R U V T N K k parent base count duration correction (applyBlock startSetup s) := by
 constructor
 · constructor
   · constructor <;>simp [startSetup,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [startSetup,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [startSetup,applyBlock,Op.apply,writeNat,next,h.parent,h.base,h.count,h.duration,h.correction,h.address]

/-- The genuine branches read an earlier parent's converted start; the root
uses the literal zero installed by startup. -/
theorem select_start (n D R U V T N K k parent base count duration correction B : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Loaded D R U V T N K k parent base count duration correction s)
 (hp : s.pc=100) (hs : WordBound B s) (code : 122≤B)
 (parentBefore : k=0∨parent<k) (index : k<N) (fit : V+N≤B)
 (parents : 0<k→s.natHeap (V+parent)=some 0) : ∃u,
 BoundedRuns program n x B s (if k=0 then 2 else 4) u ∧ u.pc=105 ∧
 Loaded D R U V T N K k parent base count duration correction u ∧
 u.natReg 6533=0 ∧ u.natHeap=s.natHeap := by
 by_cases zero : k=0
 · have step : UniformMachine.step program n x s=.running (setPC s 104) := by
    simp [UniformMachine.step,hp,code_100,h.zero,h.index,zero,setPC]
   have enter:=control_run program n B 104 x s hs (by omega) step
   let a:=setPC s 104
   have body:=block_runs rootStart program 104 n B x a rootStart_code rfl enter.final_bound
    (by change 105≤B;omega) (by simp [rootStart,readable,Op.readable]) (by
     simp [rootStart,peak,Op.peak,a,setPC,h.rootStart,h.zero])
   refine ⟨applyBlock rootStart a,?_,?_,root_header a (h.pc 104),?_,rfl⟩
   · simpa [zero] using (show BoundedRuns program n x B s 2 (applyBlock rootStart a) from enter.trans body)
   · rw [applyBlock_pc];rfl
   · simp [rootStart,applyBlock,Op.apply,writeNat,next,a,setPC,h.rootStart,h.zero]
 · have positive : 0<k := by omega
   have pp : parent<k := by rcases parentBefore with eq|lt;exact False.elim (zero eq);exact lt
   have val:=parents positive
   have step : UniformMachine.step program n x s=.running (setPC s 101) := by
    simp [UniformMachine.step,hp,code_100,h.zero,h.index,positive,setPC]
   have enter:=control_run program n B 101 x s hs (by omega) step
   let a:=setPC s 101
   have body:=block_runs parentStart program 101 n B x a parentStart_code rfl enter.final_bound
    (by change 103≤B;omega) (by
     simp [parentStart,readable,Op.readable,Op.apply,writeNat,next,a,setPC,h.starts,h.parent,val]) (by
     simp [parentStart,peak,Op.peak,Op.apply,writeNat,next,a,setPC,h.starts,h.parent,val]
     omega)
   have bp : (applyBlock parentStart a).pc=103 := by rw [applyBlock_pc];rfl
   have stepBack : UniformMachine.step program n x (applyBlock parentStart a)=
    .running (setPC (applyBlock parentStart a) 105) := by
     simp [UniformMachine.step,bp,code_103,setPC]
   have back:=control_run program n B 105 x (applyBlock parentStart a) body.final_bound (by omega) stepBack
   refine ⟨setPC (applyBlock parentStart a) 105,?_,rfl,(start_header a (h.pc 101)).pc 105,?_,rfl⟩
   · simpa [zero] using (show BoundedRuns program n x B s 4 (setPC (applyBlock parentStart a) 105) from (enter.trans body).trans back)
   · simp [parentStart,applyBlock,Op.apply,writeNat,next,a,setPC,h.starts,h.parent,val]

lemma setup_values {D R U V T N K k parent base count duration correction : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s) (hz : s.natReg 6533=0) :
 (applyBlock startSetup s).natReg 6534=duration-correction ∧
 (applyBlock startSetup s).natReg 6529=base-R ∧
 (applyBlock startSetup s).natReg 6533=0 := by
 simp [startSetup,applyBlock,Op.apply,writeNat,next,h.base,h.requests,h.duration,h.correction,hz]
lemma divide_header {D R U V T N K k parent base count duration correction ordinal : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s) :
 Loaded D R U V T N K k parent base count duration correction (writeNat s 6529 ordinal) := by
 constructor
 · constructor
   · constructor <;>simp [writeNat,next,h.nodes,h.requests,h.durations,h.starts,h.requestStarts,h.rootStart,
     h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [writeNat,next,h.index]
 all_goals simp [writeNat,next,h.parent,h.base,h.count,h.duration,h.correction,h.address]
lemma rowSetup_cursor {D R U V T N K k parent base count duration correction ordinal : ℕ} (s : State)
 (h : Loaded D R U V T N K k parent base count duration correction s)
 (ho : s.natReg 6529=ordinal) (hv : s.natReg 6534=duration-correction) :
 UniformCacheTimingForwardRows.Cursor D R U V T N K k count ordinal 0 (duration-correction)
 (applyBlock startRowSetup s) := by
 constructor
 · constructor
   · constructor <;>simp [startRowSetup,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [startRowSetup,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [startRowSetup,applyBlock,Op.apply,writeNat,next,h.count,ho,hv]
lemma store_header {D R U V T N K k : ℕ} (s : State) (h : Init D R U V T N K k s) :
 Init D R U V T N K (k+1) (applyBlock storeStart s) := by
 constructor
 · constructor <;>simp [storeStart,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 · simp [storeStart,applyBlock,Op.apply,writeNat,next,h.index,h.one]

def ticks (k count : ℕ) : ℕ := (if k=0 then 24 else 26)+8*count

/-- One actual forward node. Duration, correction and prefix values are read
from the existing banks, then converted in place by the literal machine. -/
theorem node (n D R U V T N K k parent base duration correction ordinal B : ℕ)
 (L : List ℕ) (x : Fin n→ℂ) (s : State) (h : Init D R U V T N K k s)
 (hp : s.pc=87) (hs : WordBound B s) (code : 122≤B) (index : k<N)
 (directoryFit : D+7*N≤B) (_durationFit : U+N≤B) (startsFit : V+N≤B)
 (p : s.natHeap (D+7*k+3)=some parent) (b : s.natHeap (D+7*k+5)=some base)
 (c : s.natHeap (D+7*k+6)=some L.length) (d : s.natHeap (U+k)=some duration)
 (a : s.natHeap (V+k)=some correction) (baseEq : base=R+7*ordinal)
 (parentsBefore : k=0∨parent<k) (parents : 0<k→s.natHeap (V+parent)=some 0)
 (values : Values T ordinal L s) (destination : T+ordinal+L.length≤B)
 (total : ∀v∈L,duration-correction+v≤B) : ∃u,
 BoundedRuns program n x B s (ticks k L.length) u ∧ u.pc=87 ∧
 Init D R U V T N K (k+1) u ∧
 u.natHeap=Function.update (writeStarts T ordinal (duration-correction) L s.natHeap) (V+k) (some 0) := by
 have pv:=hs.2.2.1 _ _ p
 have bv:=hs.2.2.1 _ _ b
 have cv:=hs.2.2.1 _ _ c
 have dv:=hs.2.2.1 _ _ d
 have av:=hs.2.2.1 _ _ a
 have step : UniformMachine.step program n x s=.running (setPC s 88) := by
  simp [UniformMachine.step,hp,code_87,h.index,h.nodeCount,index,setPC]
 have enter:=control_run program n B 88 x s hs (by omega) step
 let e:=setPC s 88
 have pp : s.natHeap (D+(k*7+3))=some parent := by simpa only [Nat.mul_comm,Nat.add_assoc] using p
 have bb : s.natHeap (D+(k*7+5))=some base := by simpa only [Nat.mul_comm,Nat.add_assoc] using b
 have cc : s.natHeap (D+(k*7+6))=some L.length := by simpa only [Nat.mul_comm,Nat.add_assoc] using c
 have load:=block_runs loadForward program 88 n B x e loadForward_code rfl enter.final_bound
  (by change 100≤B;omega) (by
   simp [loadForward,readable,Op.readable,Op.apply,writeNat,next,e,setPC,h.nodes,h.index,h.seven,h.three,h.two,h.one,
    h.durations,h.starts,pp,bb,cc,d,a,Nat.add_assoc]) (by
   simp [loadForward,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.nodes,h.index,h.seven,h.three,h.two,h.one,
    h.durations,h.starts,pp,bb,cc,d,a,Nat.add_assoc]
   omega)
 let l:=applyBlock loadForward e
 have lp : l.pc=100 := by rw [applyBlock_pc];rfl
 have lh:=load_header e (h.pc 88) p b c d a
 obtain ⟨r,select,rp,rh,rz,rheap⟩:=select_start n D R U V T N K k parent base L.length duration correction B
  x l lh lp load.final_bound code parentsBefore index startsFit parents
 have setup:=block_runs startSetup program 105 n B x r startSetup_code rp select.final_bound
  (by change 108≤B;omega) (by simp [startSetup,readable,Op.readable]) (by
   simp [startSetup,peak,Op.peak,Op.apply,writeNat,next,rh.duration,rh.correction,rh.base,rh.requests,rz]
   omega)
 let t:=applyBlock startSetup r
 have tp : t.pc=108 := by rw [applyBlock_pc,rp];rfl
 have th:=setup_header r rh
 have tv:=setup_values r rh rz
 have ordinalFit : ordinal≤B := by omega
 have t7 : t.natReg 6514=7 := th.seven
 have tord : t.natReg 6529=base-R := tv.2.1
 have divstep : UniformMachine.step program n x t=.running (writeNat t 6529 ordinal) := by
  simp [UniformMachine.step,tp,code_108,evalNat,t7,tord,baseEq]
 have divbound:=writeNat_bound B t 6529 ordinal setup.final_bound (by omega) ordinalFit
 have divrun : BoundedRuns program n x B t 1 (writeNat t 6529 ordinal) :=
  .next setup.final_bound divstep (.refl divbound)
 let z:=writeNat t 6529 ordinal
 have zp : z.pc=109 := by simp [z,writeNat,next,tp]
 have zh:=divide_header t th (ordinal:=ordinal)
 have zo : z.natReg 6529=ordinal := by simp [z,writeNat]
 have zv : z.natReg 6534=duration-correction := by simpa [z,writeNat] using tv.1
 have zz : z.natReg 6533=0 := by simpa [z,writeNat] using tv.2.2
 have rowsSetup:=block_runs startRowSetup program 109 n B x z startRowSetup_code zp divrun.final_bound
  (by change 110≤B;omega) (by simp [startRowSetup,readable,Op.readable]) (by simp [startRowSetup,peak,Op.peak])
 let q:=applyBlock startRowSetup z
 have qp : q.pc=110 := by rw [applyBlock_pc,zp];rfl
 have qh:=rowSetup_cursor z zh zo zv
 have qheap : q.natHeap=s.natHeap := by exact rheap
 have qzero : q.natReg 6533=0 := by simpa [q,startRowSetup,applyBlock,Op.apply,writeNat,next] using zz
 have qaddress : q.natReg 6525=V+k := by
  simpa [q,startRowSetup,applyBlock,Op.apply,writeNat,next,z,writeNat] using th.address
 obtain ⟨u,rows,up,uh,uheap,regs⟩:=UniformCacheTimingForwardRows.loop n D R U V T N K k L.length ordinal 0
  (duration-correction) B L x q qh (by simpa only [Values,qheap] using values) (by omega) qp
  rowsSetup.final_bound code destination total
 have uzero : u.natReg 6533=0 := (regs 6533 (by omega)).trans qzero
 have uaddress : u.natReg 6525=V+k := (regs 6525 (by omega)).trans qaddress
 have store:=block_runs storeStart program 118 n B x u storeStart_code up rows.final_bound
  (by change 120≤B;omega) (by simp [storeStart,readable,Op.readable]) (by
   simp [storeStart,peak,Op.peak,Op.apply,next,uaddress,uzero,uh.index,uh.one]
   omega)
 let v:=applyBlock storeStart u
 have vp : v.pc=120 := by rw [applyBlock_pc,up];rfl
 have backstep : UniformMachine.step program n x v=.running (setPC v 87) := by
  simp [UniformMachine.step,vp,code_120,setPC]
 have back:=control_run program n B 87 x v store.final_bound (by omega) backstep
 refine ⟨setPC v 87,?_,rfl,(store_header u uh.toInit).pc 87,?_⟩
 · have run:=((((((enter.trans load).trans select).trans setup).trans divrun).trans rowsSetup).trans rows).trans
    (store.trans back)
   change BoundedRuns program n x B s
    (1+12+(if k=0 then 2 else 4)+3+1+1+(8*L.length+1)+(2+1)) (setPC v 87) at run
   convert run using 1
   unfold ticks
   split_ifs <;>omega
 · change v.natHeap=_
   simp only [v,storeStart,applyBlock,Op.apply,writeNat,next,uaddress,uzero]
   rw [uheap,qheap]
end
end ExactFourierCircuits.UniformCacheTimingForwardNode
