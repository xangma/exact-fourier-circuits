import UniformHeapDirectFourier
set_option autoImplicit false
namespace ExactFourierCircuits.UniformHeapDirectBatch
open UniformMachine UniformAssembly UniformPairMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section
open scoped BigOperators

/-- Real contiguous fibers:4950=radix,4951=count,4952=source,
4953=destination,4954=prepared root address. No generated action is an input. -/
def boot : List Op := [.literal 4955 0,.literal 4956 0,.literal 4957 1]
def setup : List Op := [.mul 4958 4955 4950,.add 4801 4952 4958,
  .add 4802 4953 4958,.add 4800 4950 4956,.add 4803 4954 4956]
def post : List Op := [.add 4955 4955 4957]
def head : Program := boot.map Op.code++[.branchLT 4955 4951 4 33]++setup.map Op.code
def program : Program := head++UniformHeapDirectFourier.program.map (relocate 9 31)++
  post.map Op.code++[.jump 3,.halt]
theorem head_length : head.length=9 := rfl
theorem program_length : program.length=34 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem setup_code : BlockAt setup program 4 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem post_code : BlockAt post program 31 := by intro i hi;change i<1 at hi;interval_cases i; rfl
theorem child_code : CodeAt UniformHeapDirectFourier.program program 9 31 := by
  intro i hi
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by rw [head_length];omega)]
  simp only [head_length,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
theorem branch_code : program[3]?=some (.branchLT 4955 4951 4 33) := rfl
theorem jump_code : program[32]?=some (.jump 3) := rfl
theorem halt_code : program[33]?=some .halt := rfl

def arrayBase (A r i : ℕ) := A+i*r
structure Header (r count A D root i : ℕ) (s : State) : Prop where
  width : s.natReg 4950=r
  count : s.natReg 4951=count
  source : s.natReg 4952=A
  destination : s.natReg 4953=D
  root : s.natReg 4954=root
  index : s.natReg 4955=i
  zero : s.natReg 4956=0
  one : s.natReg 4957=1
  pc : s.pc=3
def Source {count : ℕ} (r A : ℕ) (v : Fin count→Fin r→Scalar) (s : State) : Prop :=
  ∀w z,s.scalarHeap (arrayBase A r w.val+z.val)=some (v w z)
def Partial {count r : ℕ} (D i : ℕ) (eta : ℂ) (v : Fin count→Fin r→Scalar) (s : State) : Prop :=
  ∀w:Fin count,w.val < i→∀z:Fin r,∃t,
    s.scalarHeap (arrayBase D r w.val+z.val)=some t ∧
    t.value=∑j:Fin r,eta^(z.val*j.val)*(v w j).value
def Changed (q : ℕ) : Prop := (4800≤q ∧ q≤4807) ∨ (4955≤q ∧ q≤4958)
structure Frame (D volume : ℕ) (s u : State) : Prop where
  natHeap : u.natHeap=s.natHeap
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  natReg : ∀q,¬Changed q→u.natReg q=s.natReg q
  scalarReg : ∀q,q<90 ∨ 95<q→u.scalarReg q=s.scalarReg q
  scalarHeap : ∀a,a<D ∨ D+volume≤a→u.scalarHeap a=s.scalarHeap a
theorem Frame.refl (D volume : ℕ) (s : State) : Frame D volume s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {D volume : ℕ} {s u v : State} (f:Frame D volume s u) (g:Frame D volume u v) :
    Frame D volume s v :=
  ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
    fun q h=>(g.natReg q h).trans (f.natReg q h),fun q h=>(g.scalarReg q h).trans (f.scalarReg q h),
    fun a h=>(g.scalarHeap a h).trans (f.scalarHeap a h)⟩
theorem Frame.pc (D volume : ℕ) (s : State) (pc : ℕ) : Frame D volume s (setPC s pc) :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem array_extent {A r count i : ℕ} (hi:i<count) : arrayBase A r i+r≤A+count*r := by
  have hm:=Nat.mul_le_mul_right r (show i+1≤count by omega)
  unfold arrayBase
  nlinarith
theorem array_outside {A r i w : ℕ} (hi:w≠i) (z : Fin r) :
    arrayBase A r w+z.val<arrayBase A r i ∨ arrayBase A r i+r≤arrayBase A r w+z.val := by
  unfold arrayBase
  have hz:=z.isLt
  rcases lt_or_gt_of_ne hi with h|h
  · left
    have hm:=Nat.mul_le_mul_right r (show w+1 ≤ i by omega)
    nlinarith
  · right
    have hm:=Nat.mul_le_mul_right r (show i+1≤w by omega)
    nlinarith
theorem source_outside {A D r count : ℕ} (sep:A+count*r≤D ∨ D+count*r≤A)
    (w : Fin count) (z : Fin r) :
    arrayBase A r w.val+z.val<D ∨ D+count*r≤arrayBase A r w.val+z.val := by
  have ex:=array_extent (A:=A) (r:=r) w.isLt
  unfold arrayBase at ex ⊢
  have hz:=z.isLt
  omega
theorem Frame.source {A D r count : ℕ} {s u : State} (f:Frame D (count*r) s u)
    (sep:A+count*r≤D ∨ D+count*r≤A) (v : Fin count→Fin r→Scalar)
    (h:Source r A v s) : Source r A v u := by
  intro w z
  rw [f.scalarHeap _ (source_outside sep w z)]
  exact h w z

theorem setup_values {r count A D root i : ℕ} {s : State} (h:Header r count A D root i s) :
    (applyBlock setup (setPC s 4)).natReg 4800=r ∧
    (applyBlock setup (setPC s 4)).natReg 4801=arrayBase A r i ∧
    (applyBlock setup (setPC s 4)).natReg 4802=arrayBase D r i ∧
    (applyBlock setup (setPC s 4)).natReg 4803=root := by
  simp [setup,applyBlock,Op.apply,setPC,writeNat,next,h.width,h.source,h.destination,h.index,h.zero,h.root,arrayBase]
theorem setup_keep (s : State) (q : ℕ) (h:¬Changed q) :
    (applyBlock setup (setPC s 4)).natReg q=s.natReg q := by
  simp (disch:=unfold Changed at h;omega) [setup,applyBlock,Op.apply,setPC,writeNat,next]
theorem setup_frame (D volume : ℕ) (s : State) : Frame D volume s (applyBlock setup (setPC s 4)) :=
  ⟨rfl,rfl,rfl,setup_keep s,fun _ _=>rfl,fun _ _=>rfl⟩
theorem partial_after {r count D i : ℕ} {eta : ℂ} {s u : State} (v : Fin count→Fin r→Scalar)
    (hi:i<count) (h:Partial D i eta v s)
    (result:∀z:Fin r,∃t,u.scalarHeap (arrayBase D r i+z.val)=some t ∧
      t.value=∑j:Fin r,eta^(z.val*j.val)*(v ⟨i,hi⟩ j).value)
    (outside:UniformHeapDirectFourier.Outside (arrayBase D r i) r s u) : Partial D (i+1) eta v u := by
  intro w hw z
  by_cases he:w.val=i
  · have heq:w=⟨i,hi⟩:=Fin.ext he
    subst w
    exact result z
  · obtain ⟨t,ht,hv⟩:=h w (by omega) z
    refine ⟨t,?_,hv⟩
    rw [outside _ (array_outside he z)]
    exact ht
theorem child_frame {D r count i : ℕ} {s u : State} (hi:i<count)
    (f:UniformHeapDirectFourier.Frame s u)
    (outside:UniformHeapDirectFourier.Outside (arrayBase D r i) r s u) : Frame D (count*r) s u := by
  refine ⟨f.1,f.2.1,f.2.2.1,?_,f.2.2.2.2,?_⟩
  · intro q h
    apply f.2.2.2.1
    unfold Changed at h
    omega
  · intro a h
    apply outside
    have ex:=array_extent (A:=D) (r:=r) hi
    have lower:D≤arrayBase D r i:=by unfold arrayBase;omega
    omega
def after (s : State) : State := setPC (applyBlock post s) 3
theorem after_frame (D volume : ℕ) (s : State) : Frame D volume s (after s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro q h
  simp (disch:=unfold Changed at h;omega) [after,post,applyBlock,Op.apply,writeNat,next,setPC]
theorem after_header {r count A D root i : ℕ} {s : State} (h:Header r count A D root i (setPC s 3)) :
    Header r count A D root (i+1) (after s) := by
  constructor <;> simp [after,post,applyBlock,Op.apply,writeNat,next,setPC,
    show s.natReg 4950=r from h.width,show s.natReg 4951=count from h.count,
    show s.natReg 4952=A from h.source,show s.natReg 4953=D from h.destination,
    show s.natReg 4954=root from h.root,show s.natReg 4955=i from h.index,
    show s.natReg 4956=0 from h.zero,show s.natReg 4957=1 from h.one]
theorem post_runs {n r count A D root i B : ℕ} (x : Fin n→ℂ) {s : State}
    (h:Header r count A D root i (setPC s 3)) (hi:i<count) (pc:s.pc=31)
    (code:34≤B) (bound:WordBound B s) : BoundedRuns program n x B s 2 (after s) := by
  have hr:s.natReg 4951=count:=h.count
  have hc:count≤B:=by simpa only [hr] using bound.2.1 4951
  have block:=block_runs post program 31 n B x s post_code pc bound
    (by change 31+1≤B;omega) (by simp [post,readable,Op.readable])
    (by simp [post,peak,Op.peak,show s.natReg 4955=i from h.index,show s.natReg 4957=1 from h.one];omega)
  have pc':(applyBlock post s).pc=32:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
  have jump:BoundedRuns program n x B (applyBlock post s) 1 (after s):=.next block.final_bound
    (by simp [step,jump_code,pc',after,setPC])
    (.refl (changePC_bound B _ 3 block.final_bound (by omega)))
  exact block.trans jump
def arrayCost (r : ℕ) := (8*r+10)*r+14

theorem iteration {n r count A D root i B : ℕ} (x : Fin n→ℂ) (s : State)
    (eta : ℂ) (v : Fin count→Fin r→Scalar) (h:Header r count A D root i s) (hi:i<count)
    (src:Source r A v s) (values:Partial D i eta v s)
    (rootVal:s.scalarHeap root=some (prepared eta)) (rootOut:root<D ∨ D+count*r≤root)
    (sep:A+count*r≤D ∨ D+count*r≤A) (code:34≤B)
    (aBound:A+count*r≤B) (dBound:D+count*r≤B) (bound:WordBound B s) : ∃u,
    BoundedRuns program n x B s (arrayCost r) u ∧ Header r count A D root (i+1) u ∧
    Source r A v u ∧ Partial D (i+1) eta v u ∧ Frame D (count*r) s u ∧
    u.scalarHeap root=some (prepared eta) := by
  let e:=setPC s 4
  have eb:=changePC_bound B s 4 bound (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next bound
    (by simp [step,branch_code,h.pc,h.index,h.count,hi,e,setPC]) (.refl eb)
  have ae:=array_extent (A:=A) (r:=r) hi
  have de:=array_extent (A:=D) (r:=r) hi
  have ar:A+i*r≤B:=by unfold arrayBase at ae;omega
  have dr:D+i*r≤B:=by unfold arrayBase at de;omega
  have rb:r≤B:=by simpa only [h.width] using bound.2.1 4950
  have rootB:root≤B:=by simpa only [h.root] using bound.2.1 4954
  have setupRun:=block_runs setup program 4 n B x e setup_code rfl eb
    (by change 4+5≤B;omega) (by simp [setup,readable,Op.readable])
    (by simp [setup,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.width,h.source,h.destination,
      h.index,h.zero,h.root,ar,dr,rb,rootB])
  let z:=applyBlock setup e
  let entry:=setPC z 0
  have entryB:=changePC_bound B z 0 setupRun.final_bound (by omega)
  obtain ⟨h0,h1,h2,h3⟩:=setup_values h
  have childSrc:UniformHeapDirectFourier.Bank r (arrayBase A r i) (v ⟨i,hi⟩) entry:=src ⟨i,hi⟩
  have childSep:arrayBase A r i+r≤arrayBase D r i ∨ arrayBase D r i+r≤arrayBase A r i:=by
    unfold arrayBase at ae de ⊢
    rcases sep with sep|sep
    · left;nlinarith
    · right;nlinarith
  obtain ⟨child,run,result,_,frame,outside,_⟩:=UniformHeapDirectFourier.execution x
    (arrayBase A r i) (arrayBase D r i) root B eta (v ⟨i,hi⟩) entry rfl h0 h1 h2 h3 rootVal childSrc
    childSep (by omega) (ae.trans aBound) (de.trans dBound) entryB
  have moved:=UniformBoundedAssembly.boundedExecution_placed child_code
    (by rw [UniformHeapDirectFourier.program_length];omega) (by omega :31≤B) run
  have zpc:z.pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have ez:placed 9 entry=z:=by change setPC z 9=z;unfold setPC;rw [←zpc]
  rw [ez] at moved
  let mid:=setPC child 31
  have kept (q : ℕ) (hq:4950≤q) : mid.natReg q=z.natReg q :=frame.2.2.2.1 q (by omega)
  have hh:Header r count A D root i (setPC mid 3):=by
    constructor
    · exact (kept 4950 (by omega)).trans (setup_keep s 4950 (by unfold Changed;omega)) |>.trans h.width
    · exact (kept 4951 (by omega)).trans (setup_keep s 4951 (by unfold Changed;omega)) |>.trans h.count
    · exact (kept 4952 (by omega)).trans (setup_keep s 4952 (by unfold Changed;omega)) |>.trans h.source
    · exact (kept 4953 (by omega)).trans (setup_keep s 4953 (by unfold Changed;omega)) |>.trans h.destination
    · exact (kept 4954 (by omega)).trans (setup_keep s 4954 (by unfold Changed;omega)) |>.trans h.root
    · exact (kept 4955 (by omega)).trans (by simp [z,e,setup,applyBlock,Op.apply,writeNat,next,setPC]) |>.trans h.index
    · exact (kept 4956 (by omega)).trans (by simp [z,e,setup,applyBlock,Op.apply,writeNat,next,setPC]) |>.trans h.zero
    · exact (kept 4957 (by omega)).trans (by simp [z,e,setup,applyBlock,Op.apply,writeNat,next,setPC]) |>.trans h.one
    · rfl
  have finishRun:=post_runs x hh hi rfl code moved.final_bound
  have cf:Frame D (count*r) z mid:=by
    apply child_frame hi
    · exact frame
    · exact outside
  have allFrame:Frame D (count*r) s (after mid):=
    ((setup_frame D (count*r) s).trans cf).trans (after_frame D (count*r) mid)
  have outPartial:Partial D (i+1) eta v mid:=partial_after v hi values result outside
  refine ⟨after mid,?_,after_header hh,allFrame.source sep v src,outPartial,allFrame,?_⟩
  · convert ((branch.trans setupRun).trans moved).trans finishRun using 1
    change (8*r+10)*r+14=1+5+((8*r+10)*r+6)+2
    omega
  · rw [allFrame.scalarHeap root rootOut,rootVal]

theorem loop_execution (n B r count A D root remaining : ℕ) (x : Fin n→ℂ) :
    ∀i s (eta : ℂ) (v : Fin count→Fin r→Scalar),i+remaining=count→Header r count A D root i s→
    Source r A v s→Partial D i eta v s→s.scalarHeap root=some (prepared eta)→
    (root<D ∨ D+count*r≤root)→(A+count*r≤D ∨ D+count*r≤A)→34≤B→
    A+count*r≤B→D+count*r≤B→WordBound B s→∃u,
    BoundedExecution program n x B s (remaining*arrayCost r+2) u ∧
    Source r A v u ∧ Partial D count eta v u ∧ Frame D (count*r) s u ∧
    u.scalarHeap root=some (prepared eta) ∧ u.pc=33 := by
  induction remaining with
  | zero =>
    intro i s eta v eq h src values rootVal rootOut sep code aBound dBound bound
    have he:i=count:=by omega
    let u:=setPC s 33
    have ub:=changePC_bound B s 33 bound (by omega)
    simp only [Nat.zero_mul,Nat.zero_add]
    refine ⟨u,.next bound (u:=u) ?_ (.halt ub ?_),src,?_,Frame.pc D (count*r) s 33,rootVal,rfl⟩
    · simp [step,branch_code,h.pc,h.index,h.count,he,u,setPC]
    · simp [step,halt_code,u,setPC]
    · intro w hw z
      change ∃t,s.scalarHeap (arrayBase D r w.val+z.val)=some t ∧ _
      exact values w (by omega) z
  | succ remaining ih =>
    intro i s eta v eq h src values rootVal rootOut sep code aBound dBound bound
    obtain ⟨mid,first,head,source,result,frame,rm⟩:=iteration x s eta v h (by omega)
      src values rootVal rootOut sep code aBound dBound bound
    obtain ⟨u,last,out,answer,rest,ru,pcu⟩:=ih (i+1) mid eta v (by omega) head source result rm
      rootOut sep code aBound dBound first.final_bound
    refine ⟨u,?_,out,answer,frame.trans rest,ru,pcu⟩
    convert first.executes last using 1
    ring

def bootState (s : State) := applyBlock boot s
theorem boot_header {r count A D root : ℕ} {s : State} (pc:s.pc=0)
    (width:s.natReg 4950=r) (countVal:s.natReg 4951=count) (source:s.natReg 4952=A)
    (dest:s.natReg 4953=D) (rootVal:s.natReg 4954=root) : Header r count A D root 0 (bootState s) := by
  constructor <;> simp [bootState,boot,applyBlock,Op.apply,writeNat,next,pc,width,countVal,source,dest,rootVal]
theorem boot_frame (D volume : ℕ) (s : State) : Frame D volume s (bootState s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro q h
  simp (disch:=unfold Changed at h;omega) [bootState,boot,applyBlock,Op.apply,writeNat,next]
theorem boot_runs {n B : ℕ} (x : Fin n→ℂ) (s : State) (pc:s.pc=0)
    (bound:WordBound B s) (code:34≤B) : BoundedRuns program n x B s 3 (bootState s) :=
  block_runs boot program 0 n B x s boot_code pc bound (by change 0+3≤B;omega)
    (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)

/-- Actual batched small-radix Fourier execution, from dirty destinations,
with raw headers and one prepared root. Sources and unrelated state survive. -/
theorem execution (n B r count A D root : ℕ) (x : Fin n→ℂ) (s : State)
    (eta : ℂ) (v : Fin count→Fin r→Scalar) (pc:s.pc=0)
    (width:s.natReg 4950=r) (arrays:s.natReg 4951=count) (source:s.natReg 4952=A)
    (dest:s.natReg 4953=D) (rootReg:s.natReg 4954=root)
    (rootVal:s.scalarHeap root=some (prepared eta)) (src:Source r A v s)
    (rootOut:root<D ∨ D+count*r≤root) (sep:A+count*r≤D ∨ D+count*r≤A)
    (code:34≤B) (aBound:A+count*r≤B) (dBound:D+count*r≤B) (bound:WordBound B s) : ∃u,
    BoundedExecution program n x B s (count*arrayCost r+5) u ∧
    (∀w:Fin count,∀z:Fin r,∃t,u.scalarHeap (arrayBase D r w.val+z.val)=some t ∧
      t.value=∑j:Fin r,eta^(z.val*j.val)*(v w j).value) ∧
    Source r A v u ∧ Frame D (count*r) s u ∧
    u.scalarHeap root=some (prepared eta) ∧ u.pc=33 := by
  have first:=boot_runs x s pc bound code
  have empty:Partial D 0 eta v (bootState s):=by intro w hw;omega
  obtain ⟨u,last,src',values,frame,ru,pcu⟩:=loop_execution n B r count A D root count x
    0 (bootState s) eta v (by omega) (boot_header pc width arrays source dest rootReg)
    src empty rootVal rootOut sep code aBound dBound first.final_bound
  refine ⟨u,?_,fun w z=>values w w.isLt z,src',(boot_frame D (count*r) s).trans frame,ru,pcu⟩
  convert first.executes last using 1
  omega

theorem small_cost_bound {r threshold : ℕ} (hr:0<r) (hsmall:r<threshold) (count : ℕ) :
    count*arrayCost r+5≤(8*threshold+24)*(count*r)+5 := by
  have hcount:count≤count*r:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left count (show 1≤r by omega)
  have hc:count*((8*r+10)*r)≤(8*threshold+10)*(count*r):=by
    have h:=Nat.mul_le_mul_right (count*r) (show 8*r+10≤8*threshold+10 by omega)
    nlinarith
  unfold arrayCost
  nlinarith

end
end ExactFourierCircuits.UniformHeapDirectBatch
