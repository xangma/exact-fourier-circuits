import UniformBinaryTensorCMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBinaryBatchCMachine
open UniformMachine UniformAssembly UniformBinaryTensorCoordinates
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section

/-- Input headers4900=k,4901=array count,4902=base,4903=2^k. The
fixed42 child is executed on every real array; no child-action premise occurs. -/
def boot : List Op := [.literal 4904 0,.literal 4905 0,.literal 4906 1]
def setup : List Op := [.mul 4907 4904 4903,.add 4907 4902 4907,
  .add 2823 4907 4905,.add 2824 4903 4905,.add 2825 4900 4905]
def post : List Op := [.add 4904 4904 4906]
def head : Program := boot.map Op.code++[.branchLT 4904 4901 4 53]++setup.map Op.code
def program : Program := head++UniformBinaryTensorCMachine.program.map (relocate 9 51)++
  post.map Op.code++[.jump 3,.halt]
theorem head_length : head.length=9 := rfl
theorem program_length : program.length=54 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem setup_code : BlockAt setup program 4 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem post_code : BlockAt post program 51 := by intro i hi;change i<1 at hi;interval_cases i; rfl
theorem child_code : CodeAt UniformBinaryTensorCMachine.program program 9 51 := by
  intro i hi
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by rw [head_length];omega)]
  simp only [head_length,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
theorem branch_code : program[3]?=some (.branchLT 4904 4901 4 53) := rfl
theorem jump_code : program[52]?=some (.jump 3) := rfl
theorem halt_code : program[53]?=some .halt := rfl

def transformed (k : ℕ) (v : Fin (2^k)→Scalar) : Fin (2^k)→Scalar :=
  applyAxes k (List.finRange k) v
def arrayBase (A k i : ℕ) : ℕ := A+i*2^k
structure Header (k count A i : ℕ) (s : State) : Prop where
  bits : s.natReg 4900=k
  count : s.natReg 4901=count
  base : s.natReg 4902=A
  size : s.natReg 4903=2^k
  index : s.natReg 4904=i
  zero : s.natReg 4905=0
  one : s.natReg 4906=1
  pc : s.pc=3
def Partial {count : ℕ} (k A i : ℕ) (v : Fin count→Fin (2^k)→Scalar) (s : State) : Prop :=
  ∀w:Fin count,∀z:Fin (2^k),s.scalarHeap (arrayBase A k w.val+z.val)=
    some (if w.val < i then transformed k (v w) z else v w z)

def Changed (r : ℕ) : Prop := UniformBinaryTensorCMachine.Changed r ∨
  r=2823 ∨ r=2824 ∨ r=2825 ∨ r=4904 ∨ r=4905 ∨ r=4906 ∨ r=4907
structure Frame (A volume : ℕ) (s u : State) : Prop where
  natHeap : u.natHeap=s.natHeap
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  natReg : ∀r,¬Changed r→u.natReg r=s.natReg r
  scalarReg : ∀r,8≤r→u.scalarReg r=s.scalarReg r
  scalarHeap : ∀a,a<A ∨ A+volume≤a→u.scalarHeap a=s.scalarHeap a
theorem Frame.refl (A volume : ℕ) (s : State) : Frame A volume s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {A volume : ℕ} {s u v : State} (h:Frame A volume s u) (h':Frame A volume u v) :
    Frame A volume s v :=
  ⟨h'.natHeap.trans h.natHeap,h'.outputs.trans h.outputs,h'.roots.trans h.roots,
    fun r hr=>(h'.natReg r hr).trans (h.natReg r hr),
    fun r hr=>(h'.scalarReg r hr).trans (h.scalarReg r hr),
    fun a ha=>(h'.scalarHeap a ha).trans (h.scalarHeap a ha)⟩
theorem Frame.pc (A volume : ℕ) (s : State) (pc : ℕ) : Frame A volume s (setPC s pc) :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩

theorem array_extent {A k count i : ℕ} (hi:i<count) : arrayBase A k i+2^k≤A+count*2^k := by
  have h:=Nat.mul_le_mul_right (2^k) (show i+1≤count by omega)
  unfold arrayBase
  nlinarith
theorem array_outside {A k i w : ℕ} (hi:w≠i) (z : Fin (2^k)) :
    arrayBase A k w+z.val<arrayBase A k i ∨
      arrayBase A k i+2^k≤arrayBase A k w+z.val := by
  unfold arrayBase
  have hz:=z.isLt
  have hp:0<2^k:=pow_pos (by omega) _
  rcases lt_or_gt_of_ne hi with h|h
  · left
    have hm:=Nat.mul_le_mul_right (2^k) (show w+1 ≤ i by omega)
    nlinarith
  · right
    have hm:=Nat.mul_le_mul_right (2^k) (show i+1≤w by omega)
    nlinarith

theorem setup_values {k count A i : ℕ} {s : State} (h:Header k count A i s) :
    (applyBlock setup (setPC s 4)).natReg 2823=arrayBase A k i ∧
    (applyBlock setup (setPC s 4)).natReg 2824=2^k ∧
    (applyBlock setup (setPC s 4)).natReg 2825=k := by
  simp [setup,applyBlock,Op.apply,setPC,writeNat,next,h.bits,h.base,h.size,h.index,h.zero,arrayBase]
theorem setup_keep (s : State) (r : ℕ) (hr:r≠4907 ∧ r≠2823 ∧ r≠2824 ∧ r≠2825) :
    (applyBlock setup (setPC s 4)).natReg r=s.natReg r := by
  simp [setup,applyBlock,Op.apply,setPC,writeNat,next,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2]
theorem setup_frame (A volume : ℕ) (s : State) : Frame A volume s (applyBlock setup (setPC s 4)) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  apply setup_keep
  unfold Changed at hr
  omega

theorem partial_current {k count A i : ℕ} {s : State} (v : Fin count→Fin (2^k)→Scalar)
    (hi:i<count) (h:Partial k A i v s) :
    UniformBinaryTensorCMachine.Present (arrayBase A k i) k (v ⟨i,hi⟩) s := by
  intro z
  simpa using h ⟨i,hi⟩ z

theorem partial_after {k count A i : ℕ} {s u : State} (v : Fin count→Fin (2^k)→Scalar)
    (hi:i<count) (h:Partial k A i v s)
    (result:UniformBinaryTensorCMachine.Present (arrayBase A k i) k (transformed k (v ⟨i,hi⟩)) u)
    (frame:UniformBinaryTensorCMachine.Frame (arrayBase A k i) (2^k) s u) :
    Partial k A (i+1) v u := by
  intro w z
  by_cases he:w.val=i
  · have hw:w=⟨i,hi⟩:=Fin.ext he
    subst w
    simpa using result z
  · rw [frame.scalarHeap _ (array_outside he z),h w z]
    congr 1
    have heq:(w.val < i+1)↔(w.val < i):=by omega
    simp [heq]

theorem child_frame {A k count i : ℕ} {s u : State} (hi:i<count)
    (f:UniformBinaryTensorCMachine.Frame (arrayBase A k i) (2^k) s u) :
    Frame A (count*2^k) s u := by
  refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,?_⟩
  · intro r hr
    exact f.natReg r (by unfold Changed at hr;tauto)
  · intro a ha
    apply f.scalarHeap
    have hbase:A≤arrayBase A k i:=by unfold arrayBase;omega
    have hend:=array_extent (A:=A) (k:=k) hi
    omega

def after (s : State) : State := setPC (applyBlock post s) 3
theorem after_frame (A volume : ℕ) (s : State) : Frame A volume s (after s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  have he:r≠4904:=by unfold Changed at hr;tauto
  simp [after,post,applyBlock,Op.apply,writeNat,next,setPC,he]
theorem after_header {k count A i : ℕ} {s : State} (h:Header k count A i (setPC s 3)) :
    Header k count A (i+1) (after s) := by
  constructor <;> simp [after,post,applyBlock,Op.apply,writeNat,next,setPC,
    show s.natReg 4900=k from h.bits,show s.natReg 4901=count from h.count,
    show s.natReg 4902=A from h.base,show s.natReg 4903=2^k from h.size,
    show s.natReg 4904=i from h.index,show s.natReg 4905=0 from h.zero,
    show s.natReg 4906=1 from h.one]

theorem post_runs {n k count A i B : ℕ} (x : Fin n→ℂ) {s : State}
    (h:Header k count A i (setPC s 3)) (hi:i<count) (hp:s.pc=51)
    (hB:54≤B) (hs:WordBound B s) : BoundedRuns program n x B s 2 (after s) := by
  have hreg:s.natReg 4901=count:=h.count
  have hcount:count≤B:=by simpa only [hreg] using hs.2.1 4901
  have block:=block_runs post program 51 n B x s post_code hp hs
    (by change 51+1≤B;omega) (by simp [post,readable,Op.readable])
    (by simp [post,peak,Op.peak,show s.natReg 4904=i from h.index,show s.natReg 4906=1 from h.one];omega)
  have hp':(applyBlock post s).pc=52:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  have bound:=changePC_bound B (applyBlock post s) 3 block.final_bound (by omega)
  have jump:BoundedRuns program n x B (applyBlock post s) 1 (after s):=.next block.final_bound
    (by simp [step,jump_code,hp',after,setPC]) (.refl bound)
  exact block.trans jump

def arrayCost (k : ℕ) : ℕ := k*(25*2^(k-1)+11)+16

theorem iteration {n k count A i B : ℕ} (x : Fin n→ℂ) (s : State)
    (v : Fin count→Fin (2^k)→Scalar) (h:Header k count A i s) (hi:i<count)
    (hv:Partial k A i v s) (ha:3≤A) (con:UniformBinaryCStageMachine.Constants s)
    (hB:54≤B) (extent:A+count*2^k≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (arrayCost k) u ∧ Header k count A (i+1) u ∧
    Partial k A (i+1) v u ∧ Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u := by
  let e:=setPC s 4
  have eb:=changePC_bound B s 4 hs (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [step,branch_code,h.pc,h.index,h.count,hi,e,setPC]) (.refl eb)
  have ex:=array_extent (A:=A) (k:=k) hi
  have curBound:arrayBase A k i+2^k≤B:=ex.trans extent
  have kBound:k≤B:=by simpa only [h.bits] using hs.2.1 4900
  have sizeBound:2^k≤B:=by simpa only [h.size] using hs.2.1 4903
  have addressBound:A+i*2^k≤B:=by
    have hb:arrayBase A k i≤B:= (Nat.le_add_right _ _).trans curBound
    simpa only [arrayBase] using hb
  have setRun:=block_runs setup program 4 n B x e setup_code rfl eb
    (by change 4+5≤B;omega) (by simp [setup,readable,Op.readable])
    (by simp [setup,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.bits,h.base,h.size,h.index,h.zero,
      addressBound,kBound,sizeBound])
  let z:=applyBlock setup e
  let entry:=setPC z 0
  have entryBound:=changePC_bound B z 0 setRun.final_bound (by omega)
  obtain ⟨ha',hsz',hk'⟩:=setup_values h
  obtain ⟨child,run,values,_,frame,cu,_⟩:=UniformBinaryTensorCMachine.execution n B k (arrayBase A k i) x entry
    (v ⟨i,hi⟩) rfl ha' hsz' hk' (by unfold arrayBase;omega)
    (partial_current v hi hv) con entryBound (by omega) curBound
  have moved:=UniformBoundedAssembly.boundedExecution_placed child_code
    (by rw [UniformBinaryTensorCMachine.program_length];omega) (by omega :51≤B) run
  have zpc:z.pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have ez:placed 9 entry=z:=by change setPC z 9=z;unfold setPC;rw [←zpc]
  rw [ez] at moved
  let mid:=setPC child 51
  have kept (r : ℕ) (hr:4900≤r) : mid.natReg r=z.natReg r :=
    frame.natReg r (by unfold UniformBinaryTensorCMachine.Changed;omega)
  have hh:Header k count A i (setPC mid 3):=by
    constructor
    · exact (kept 4900 (by omega)).trans (setup_keep s 4900 (by omega)) |>.trans h.bits
    · exact (kept 4901 (by omega)).trans (setup_keep s 4901 (by omega)) |>.trans h.count
    · exact (kept 4902 (by omega)).trans (setup_keep s 4902 (by omega)) |>.trans h.base
    · exact (kept 4903 (by omega)).trans (setup_keep s 4903 (by omega)) |>.trans h.size
    · exact (kept 4904 (by omega)).trans (setup_keep s 4904 (by omega)) |>.trans h.index
    · exact (kept 4905 (by omega)).trans (setup_keep s 4905 (by omega)) |>.trans h.zero
    · exact (kept 4906 (by omega)).trans (setup_keep s 4906 (by omega)) |>.trans h.one
    · rfl
  have finishRun:=post_runs x hh hi rfl hB moved.final_bound
  have fmid:=frame.trans (UniformBinaryTensorCMachine.Frame.pc (arrayBase A k i) (2^k) child 51)
  have fwhole:UniformBinaryTensorCMachine.Frame (arrayBase A k i) (2^k) z mid:=
    (UniformBinaryTensorCMachine.Frame.pc (arrayBase A k i) (2^k) z 0).trans fmid
  have beforePartial:Partial k A i v entry:=hv
  have outPartial:Partial k A (i+1) v mid:=partial_after v hi beforePartial values fmid
  have f1:Frame A (count*2^k) s z:=setup_frame A (count*2^k) s
  have f2:Frame A (count*2^k) z mid:=child_frame hi fwhole
  refine ⟨after mid,?_,after_header hh,outPartial,(f1.trans f2).trans (after_frame A (count*2^k) mid),cu⟩
  convert ((branch.trans setRun).trans moved).trans finishRun using 1
  change k*(25*2^(k-1)+11)+16=1+5+(k*(25*2^(k-1)+11)+8)+2
  omega

theorem loop_execution (n B k count A remaining : ℕ) (x : Fin n→ℂ) :
    ∀i s (v : Fin count→Fin (2^k)→Scalar),i+remaining=count→Header k count A i s→
    Partial k A i v s→3≤A→UniformBinaryCStageMachine.Constants s→54≤B→
    A+count*2^k≤B→WordBound B s→∃u,
    BoundedExecution program n x B s (remaining*arrayCost k+2) u ∧
    Partial k A count v u ∧ Frame A (count*2^k) s u ∧
    UniformBinaryCStageMachine.Constants u ∧ u.pc=53 := by
  induction remaining with
  | zero =>
    intro i s v eq h values a con code extent bound
    have he:i=count:=by omega
    let u:=setPC s 53
    have ub:=changePC_bound B s 53 bound (by omega)
    simp only [Nat.zero_mul,Nat.zero_add]
    refine ⟨u,.next bound (u:=u) ?_ (.halt ub ?_),?_,Frame.pc A (count*2^k) s 53,con,rfl⟩
    · simp [step,branch_code,h.pc,h.index,h.count,he,u,setPC]
    · simp [step,halt_code,u,setPC]
    · intro w z
      change s.scalarHeap (arrayBase A k w.val+z.val)=_
      simpa only [he] using values w z
  | succ remaining ih =>
    intro i s v eq h values a con code extent bound
    obtain ⟨mid,first,head,result,frame,constants⟩:=iteration x s v h (by omega)
      values a con code extent bound
    obtain ⟨u,last,out,rest,cu,pcu⟩:=ih (i+1) mid v (by omega) head result a constants
      code extent first.final_bound
    refine ⟨u,?_,out,frame.trans rest,cu,pcu⟩
    convert first.executes last using 1
    ring

def bootState (s : State) : State := applyBlock boot s
theorem boot_header {k count A : ℕ} {s : State} (pc:s.pc=0)
    (bits:s.natReg 4900=k) (arrays:s.natReg 4901=count)
    (base:s.natReg 4902=A) (size:s.natReg 4903=2^k) : Header k count A 0 (bootState s) := by
  constructor <;> simp [bootState,boot,applyBlock,Op.apply,writeNat,next,pc,bits,arrays,base,size]
theorem boot_frame (A volume : ℕ) (s : State) : Frame A volume s (bootState s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  have he:r≠4904 ∧ r≠4905 ∧ r≠4906:=by unfold Changed at hr;tauto
  simp [bootState,boot,applyBlock,Op.apply,writeNat,next,he.1,he.2.1,he.2.2]
theorem boot_runs {n B : ℕ} (x : Fin n→ℂ) (s : State) (pc:s.pc=0)
    (bound:WordBound B s) (code:54≤B) : BoundedRuns program n x B s 3 (bootState s) := by
  exact block_runs boot program 0 n B x s boot_code pc bound (by change 0+3≤B;omega)
    (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)

/-- A real loop executes all arrays, including an empty batch, retaining
the complete outside frame and the actual Boolean scalar flags. -/
theorem execution (n B k count A : ℕ) (x : Fin n→ℂ) (s : State)
    (v : Fin count→Fin (2^k)→Scalar) (pc:s.pc=0)
    (bits:s.natReg 4900=k) (arrays:s.natReg 4901=count)
    (base:s.natReg 4902=A) (size:s.natReg 4903=2^k)
    (data:∀w z,s.scalarHeap (arrayBase A k w.val+z.val)=some (v w z))
    (ha:3≤A) (con:UniformBinaryCStageMachine.Constants s)
    (hB:54≤B) (extent:A+count*2^k≤B) (bound:WordBound B s) : ∃u,
    BoundedExecution program n x B s (count*arrayCost k+5) u ∧
    (∀w z,u.scalarHeap (arrayBase A k w.val+z.val)=some (transformed k (v w) z)) ∧
    (∀w z,(u.scalarHeap (arrayBase A k w.val+z.val)).map Scalar.value=
      some ((physicalMatrix k).mulVec (fun y=>(v w y).value) z)) ∧
    Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u ∧ u.pc=53 := by
  have first:=boot_runs x s pc bound hB
  have hv:Partial k A 0 v (bootState s):=by
    intro w z
    change s.scalarHeap (arrayBase A k w.val+z.val)=_
    simpa using data w z
  obtain ⟨u,last,out,frame,cu,pcu⟩:=loop_execution n B k count A count x 0 (bootState s) v
    (by omega) (boot_header pc bits arrays base size) hv ha con hB extent first.final_bound
  have values:∀w z,u.scalarHeap (arrayBase A k w.val+z.val)=some (transformed k (v w) z):=by
    intro w z
    simpa only [ite_eq_left w.isLt] using out w z
  refine ⟨u,?_,values,?_,(boot_frame A (count*2^k) s).trans frame,cu,pcu⟩
  · convert first.executes last using 1
    omega
  · intro w z
    rw [values w z]
    simp only [Option.map_some]
    exact congrArg some (congrFun (applyAxes_tensor k (v w)) z)

theorem arrayCost_bound (k : ℕ) : arrayCost k≤(36*k+16)*2^k := by
  have hp:1≤2^k:=Nat.one_le_pow k 2 (by omega)
  have hs:2^(k-1)≤2^k:=Nat.pow_le_pow_right (by omega) (by omega)
  unfold arrayCost
  have hm:=Nat.mul_le_mul_left k (show 25*2^(k-1)+11≤36*2^k by omega)
  nlinarith
theorem base_cost_bound {k threshold : ℕ} (hk:k<threshold) (count : ℕ) :
    count*arrayCost k+5≤(36*threshold+16)*(count*2^k)+5 := by
  have h:arrayCost k≤(36*threshold+16)*2^k:=
    (arrayCost_bound k).trans (Nat.mul_le_mul_right (2^k) (by omega))
  have hm:=Nat.mul_le_mul_left count h
  nlinarith

end
end ExactFourierCircuits.UniformBinaryBatchCMachine
