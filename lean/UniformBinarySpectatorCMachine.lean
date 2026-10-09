import UniformBinaryBatchCMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBinarySpectatorCMachine
open UniformMachine UniformAssembly UniformBinaryTensorCoordinates
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section

/-- Real k/count/base/size/start headers5200..5204. Compute the stride
by charged doubling and execute the actual binary suffix on every array. -/
def boot : List Op := [.literal 5205 1,.literal 5206 0,.literal 5207 1,
  .literal 5208 2,.literal 5209 0,.literal 5212 0]
def powerStep : List Op := [.mul 5205 5205 5208,.add 5206 5206 5207]
def setup : List Op := [.mul 5210 5209 5203,.add 5210 5202 5210,
  .add 2823 5210 5212,.add 2824 5203 5212,.add 2825 5200 5212,
  .add 2820 5204 5212,.add 2821 5207 5212,.add 2822 5208 5212,
  .add 2800 5205 5212,.add 2801 5210 5212,.mul 5211 5205 5208]
def post : List Op := [.add 5209 5209 5207]
def head : Program := boot.map Op.code++[.branchLT 5206 5204 7 10]++
  powerStep.map Op.code++[.jump 6,.branchLT 5209 5201 11 68]++setup.map Op.code++
  [.natBinary .div 2802 5203 5211,.jump 30]
def program : Program := head++UniformBinaryTensorCMachine.program.map (relocate 24 66)++
  post.map Op.code++[.jump 10,.halt]
theorem head_length : head.length=24 := rfl
theorem program_length : program.length=69 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem powerStep_code : BlockAt powerStep program 7 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem setup_code : BlockAt setup program 11 := by intro i hi;change i<11 at hi;interval_cases i <;> rfl
theorem post_code : BlockAt post program 66 := by intro i hi;change i<1 at hi;interval_cases i; rfl
theorem child_code : CodeAt UniformBinaryTensorCMachine.program program 24 66 := by
  intro i hi
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by rw [head_length];omega)]
  simp only [head_length,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
theorem powerBranch_code : program[6]?=some (.branchLT 5206 5204 7 10) := rfl
theorem powerJump_code : program[9]?=some (.jump 6) := rfl
theorem branch_code : program[10]?=some (.branchLT 5209 5201 11 68) := rfl
theorem divide_code : program[22]?=some (.natBinary .div 2802 5203 5211) := rfl
theorem call_code : program[23]?=some (.jump 30) := rfl
theorem jump_code : program[67]?=some (.jump 10) := rfl
theorem halt_code : program[68]?=some .halt := rfl

def transformed (k b : ℕ) (v : Fin (2^k)→Scalar) : Fin (2^k)→Scalar :=
  applyAxes k ((List.finRange k).drop b) v
def arrayBase (A k i : ℕ) : ℕ := A+i*2^k
structure Header (k b count A i : ℕ) (s : State) : Prop where
  bits : s.natReg 5200=k
  count : s.natReg 5201=count
  base : s.natReg 5202=A
  size : s.natReg 5203=2^k
  start : s.natReg 5204=b
  stride : s.natReg 5205=2^b
  index : s.natReg 5209=i
  zero : s.natReg 5212=0
  one : s.natReg 5207=1
  two : s.natReg 5208=2
  pc : s.pc=10
def Partial {count : ℕ} (k b A i : ℕ) (v : Fin count→Fin (2^k)→Scalar) (s : State) : Prop :=
  ∀w:Fin count,∀z:Fin (2^k),s.scalarHeap (arrayBase A k w.val+z.val)=
    some (if w.val < i then transformed k b (v w) z else v w z)

def Changed (r : ℕ) : Prop := UniformBinaryTensorCMachine.Changed r ∨
  r=2823 ∨ r=2824 ∨ r=2825 ∨ r=5209 ∨ r=5212 ∨ r=5207 ∨ r=5210 ∨ r=5211 ∨ r=5205 ∨ r=5206 ∨ r=5208
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

structure PowerHeader (k b count A j : ℕ) (s : State) : Prop where
  bits : s.natReg 5200=k
  count : s.natReg 5201=count
  base : s.natReg 5202=A
  size : s.natReg 5203=2^k
  start : s.natReg 5204=b
  stride : s.natReg 5205=2^j
  index : s.natReg 5206=j
  batch : s.natReg 5209=0
  zero : s.natReg 5212=0
  one : s.natReg 5207=1
  two : s.natReg 5208=2
  pc : s.pc=6

def powered (s : State) : State := setPC (applyBlock powerStep (setPC s 7)) 6

theorem power_header {k b count A j : ℕ} {s : State} (h:PowerHeader k b count A j s) :
    PowerHeader k b count A (j+1) (powered s) := by
  constructor <;> simp [powered,powerStep,applyBlock,Op.apply,writeNat,next,setPC,
    h.bits,h.count,h.base,h.size,h.start,h.stride,h.index,h.batch,h.zero,h.one,h.two,Nat.pow_succ]
theorem power_frame (A volume : ℕ) (s : State) : Frame A volume s (powered s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  have he:r≠5205 ∧ r≠5206:=by unfold Changed at hr;tauto
  simp [powered,powerStep,applyBlock,Op.apply,writeNat,next,setPC,he.1,he.2]
theorem power_runs {n k b count A j B : ℕ} (x : Fin n→ℂ) {s : State}
    (h:PowerHeader k b count A j s) (hj:j<b) (hb:b≤k) (hB:69≤B)
    (bound:WordBound B s) : BoundedRuns program n x B s 4 (powered s) := by
  have kb:k≤B:=by simpa only [h.bits] using bound.2.1 5200
  have sz:2^k≤B:=by simpa only [h.size] using bound.2.1 5203
  have pv:2^j*2≤B:=by
    rw [←Nat.pow_succ]
    exact (Nat.pow_le_pow_right (by omega) (by omega :j+1≤k)).trans sz
  let e:=setPC s 7
  have eb:=changePC_bound B s 7 bound (by omega)
  have first:BoundedRuns program n x B s 1 e:=.next bound
    (by simp [step,powerBranch_code,h.pc,h.index,h.start,hj,e,setPC]) (.refl eb)
  have body:=block_runs powerStep program 7 n B x e powerStep_code rfl eb
    (by change 7+2≤B;omega) (by simp [powerStep,readable,Op.readable])
    (by simp [powerStep,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.stride,h.index,h.one,h.two,pv];omega)
  have pc:(applyBlock powerStep e).pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have last:BoundedRuns program n x B (applyBlock powerStep e) 1 (powered s):=
    .next body.final_bound (by simp only [step,pc,powerJump_code];rfl)
      (.refl (changePC_bound B _ 6 body.final_bound (by omega)))
  convert (first.trans body).trans last using 1
  rfl

theorem power_loop (n B k b count A remaining : ℕ) (x : Fin n→ℂ) :
    ∀j s,j+remaining=b→PowerHeader k b count A j s→b≤k→69≤B→WordBound B s→∃u,
    BoundedRuns program n x B s (4*remaining+1) u ∧ Header k b count A 0 u ∧
    Frame A (count*2^k) s u ∧ u.scalarHeap=s.scalarHeap := by
  induction remaining with
  | zero=>
    intro j s eq h hb hB bound
    have he:j=b:=by omega
    let u:=setPC s 10
    have ub:=changePC_bound B s 10 bound (by omega)
    refine ⟨u,?_,?_,Frame.pc A (count*2^k) s 10,rfl⟩
    · simp only [Nat.mul_zero,Nat.zero_add]
      exact .next bound (by simp [step,powerBranch_code,h.pc,h.index,h.start,he,u,setPC]) (.refl ub)
    · exact ⟨h.bits,h.count,h.base,h.size,h.start,by change s.natReg 5205=2^b;simpa only [he] using h.stride,
        h.batch,h.zero,h.one,h.two,rfl⟩
  | succ remaining ih=>
    intro j s eq h hb hB bound
    have first:=power_runs x h (by omega) hb hB bound
    obtain ⟨u,last,head,frame,heap⟩:=ih (j+1) (powered s) (by omega) (power_header h) hb hB first.final_bound
    refine ⟨u,?_,head,(power_frame A (count*2^k) s).trans frame,heap⟩
    convert first.trans last using 1
    omega

def bootState (s : State) : State := applyBlock boot s
theorem boot_header {k b count A : ℕ} {s : State} (pc:s.pc=0)
    (bits:s.natReg 5200=k) (arrays:s.natReg 5201=count)
    (base:s.natReg 5202=A) (size:s.natReg 5203=2^k) (start:s.natReg 5204=b) :
    PowerHeader k b count A 0 (bootState s) := by
  constructor <;> simp [bootState,boot,applyBlock,Op.apply,writeNat,next,pc,bits,arrays,base,size,start]
theorem boot_frame (A volume : ℕ) (s : State) : Frame A volume s (bootState s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  have he:r≠5205 ∧ r≠5206 ∧ r≠5207 ∧ r≠5208 ∧ r≠5209 ∧ r≠5212:=by unfold Changed at hr;tauto
  simp [bootState,boot,applyBlock,Op.apply,writeNat,next,he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1,he.2.2.2.2.2]
theorem boot_runs {n B : ℕ} (x : Fin n→ℂ) (s : State) (pc:s.pc=0)
    (bound:WordBound B s) (code:69≤B) : BoundedRuns program n x B s 6 (bootState s) := by
  exact block_runs boot program 0 n B x s boot_code pc bound (by change 0+6≤B;omega)
    (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)

def ready (s : State) : State :=
  let z:=applyBlock setup (setPC s 11)
  writeNat z 2802 (z.natReg 5203/z.natReg 5211)
def entered (s : State) : State := setPC (ready s) 30

theorem ready_header {k b count A i : ℕ} {s : State} (h:Header k b count A i s) :
    UniformBinaryTensorCMachine.Header k (arrayBase A k i) b (setPC (ready s) 6) := by
  constructor <;> simp [ready,setup,applyBlock,Op.apply,writeNat,next,setPC,
    h.bits,h.base,h.size,h.start,h.stride,h.index,h.zero,h.one,h.two,arrayBase]
theorem ready_keep (s : State) (r : ℕ)
    (hr:r≠5210 ∧ r≠2823 ∧ r≠2824 ∧ r≠2825 ∧ r≠2820 ∧ r≠2821 ∧
      r≠2822 ∧ r≠2800 ∧ r≠2801 ∧ r≠5211 ∧ r≠2802) :
    (ready s).natReg r=s.natReg r := by
  rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  simp [ready,setup,applyBlock,Op.apply,writeNat,next,setPC,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
theorem ready_frame (A volume : ℕ) (s : State) : Frame A volume s (entered s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  apply ready_keep
  unfold Changed UniformBinaryTensorCMachine.Changed at hr
  omega

theorem ready_parent {k b count A i : ℕ} {s : State} (h:Header k b count A i s) :
    Header k b count A i (setPC (ready s) 10) := by
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,rfl⟩
  · exact (ready_keep s 5200 (by omega)).trans h.bits
  · exact (ready_keep s 5201 (by omega)).trans h.count
  · exact (ready_keep s 5202 (by omega)).trans h.base
  · exact (ready_keep s 5203 (by omega)).trans h.size
  · exact (ready_keep s 5204 (by omega)).trans h.start
  · exact (ready_keep s 5205 (by omega)).trans h.stride
  · exact (ready_keep s 5209 (by omega)).trans h.index
  · exact (ready_keep s 5212 (by omega)).trans h.zero
  · exact (ready_keep s 5207 (by omega)).trans h.one
  · exact (ready_keep s 5208 (by omega)).trans h.two

theorem setup_runs {n k b count A i B : ℕ} (x : Fin n→ℂ) {s : State}
    (h:Header k b count A i s) (hi:i<count) (hB:69≤B)
    (extent:A+count*2^k≤B) (strideBound:2^b*2≤B) (bound:WordBound B s) :
    BoundedRuns program n x B s 14 (entered s) := by
  let e:=setPC s 11
  have eb:=changePC_bound B s 11 bound (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next bound
    (by simp [step,branch_code,h.pc,h.index,h.count,hi,e,setPC]) (.refl eb)
  have curBound:arrayBase A k i+2^k≤B:=(array_extent (A:=A) (k:=k) hi).trans extent
  have kBound:k≤B:=by simpa only [h.bits] using bound.2.1 5200
  have bBound:b≤B:=by simpa only [h.start] using bound.2.1 5204
  have sizeBound:2^k≤B:=by simpa only [h.size] using bound.2.1 5203
  have addressBound:A+i*2^k≤B:=by
    have he:arrayBase A k i≤B:=(Nat.le_add_right _ _).trans curBound
    exact he
  have strideSmall:2^b≤B:=by omega
  have setRun:=block_runs setup program 11 n B x e setup_code rfl eb
    (by change 11+11≤B;omega) (by simp [setup,readable,Op.readable])
    (by simp [setup,peak,Op.peak,Op.apply,writeNat,next,e,setPC,h.bits,h.base,h.size,
      h.start,h.stride,h.index,h.zero,h.one,h.two,addressBound,kBound,
      bBound,sizeBound,strideSmall,strideBound];omega)
  let z:=applyBlock setup e
  have zpc:z.pc=22:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have den:z.natReg 5211=2^b*2:=by
    simp [z,e,setup,applyBlock,Op.apply,writeNat,next,setPC,h.stride,h.two]
  have sz:z.natReg 5203=2^k:=by
    simp [z,e,setup,applyBlock,Op.apply,writeNat,next,setPC,h.size]
  have divBound:=writeNat_bound B z 2802 (z.natReg 5203/z.natReg 5211) setRun.final_bound
    (by rw [zpc];omega) ((Nat.div_le_self _ _).trans (by rw [sz];exact sizeBound))
  have rp:(ready s).pc=23:=by change z.pc+1=23;rw [zpc]
  have divided:BoundedRuns program n x B z 1 (ready s):=.next setRun.final_bound
    (by
      simp only [step,zpc,divide_code,evalNat]
      have dn:z.natReg 5211≠0:=by rw [den];positivity
      simp only [dn,ite_false]
      rfl)
    (.refl divBound)
  have called:BoundedRuns program n x B (ready s) 1 (entered s):=.next divBound
    (by simp only [step,rp,call_code];rfl) (.refl (changePC_bound B _ 30 divBound (by omega)))
  convert ((branch.trans setRun).trans divided).trans called using 1
  rfl

theorem partial_current {k b count A i : ℕ} {s : State} (v : Fin count→Fin (2^k)→Scalar)
    (hi:i<count) (h:Partial k b A i v s) :
    UniformBinaryTensorCMachine.Present (arrayBase A k i) k (v ⟨i,hi⟩) s := by
  intro z
  simpa using h ⟨i,hi⟩ z

theorem partial_after {k b count A i : ℕ} {s u : State} (v : Fin count→Fin (2^k)→Scalar)
    (hi:i<count) (h:Partial k b A i v s)
    (result:UniformBinaryTensorCMachine.Present (arrayBase A k i) k (transformed k b (v ⟨i,hi⟩)) u)
    (frame:UniformBinaryTensorCMachine.Frame (arrayBase A k i) (2^k) s u) :
    Partial k b A (i+1) v u := by
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

def after (s : State) : State := setPC (applyBlock post s) 10
theorem after_frame (A volume : ℕ) (s : State) : Frame A volume s (after s) := by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
  intro r hr
  have he:r≠5209:=by unfold Changed at hr;tauto
  simp [after,post,applyBlock,Op.apply,writeNat,next,setPC,he]
theorem after_header {k b count A i : ℕ} {s : State} (h:Header k b count A i (setPC s 10)) :
    Header k b count A (i+1) (after s) := by
  constructor <;> simp [after,post,applyBlock,Op.apply,writeNat,next,setPC,
    show s.natReg 5200=k from h.bits,show s.natReg 5201=count from h.count,
    show s.natReg 5202=A from h.base,show s.natReg 5203=2^k from h.size,
    show s.natReg 5204=b from h.start,show s.natReg 5205=2^b from h.stride,
    show s.natReg 5209=i from h.index,show s.natReg 5212=0 from h.zero,
    show s.natReg 5207=1 from h.one,show s.natReg 5208=2 from h.two]

theorem post_runs {n k b count A i B : ℕ} (x : Fin n→ℂ) {s : State}
    (h:Header k b count A i (setPC s 10)) (hi:i<count) (hp:s.pc=66)
    (hB:69≤B) (bound:WordBound B s) : BoundedRuns program n x B s 2 (after s) := by
  have countBound:count≤B:=by simpa only [show s.natReg 5201=count from h.count] using bound.2.1 5201
  have body:=block_runs post program 66 n B x s post_code hp bound
    (by change 66+1≤B;omega) (by simp [post,readable,Op.readable])
    (by simp [post,peak,Op.peak,show s.natReg 5209=i from h.index,show s.natReg 5207=1 from h.one];omega)
  have pc:(applyBlock post s).pc=67:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  have last:BoundedRuns program n x B (applyBlock post s) 1 (after s):=.next body.final_bound
    (by simp only [step,pc,jump_code];rfl) (.refl (changePC_bound B _ 10 body.final_bound (by omega)))
  exact body.trans last

def arrayCost (k b : ℕ) : ℕ := (k-b)*(25*2^(k-1)+11)+18

theorem iteration {n k b count A i B : ℕ} (x : Fin n→ℂ) (s : State)
    (v : Fin count→Fin (2^k)→Scalar) (h:Header k b count A i s) (hi:i<count)
    (hv:Partial k b A i v s) (hb:b≤k) (ha:3≤A) (con:UniformBinaryCStageMachine.Constants s)
    (hB:69≤B) (extent:A+count*2^k≤B) (strideBound:2^b*2≤B) (bound:WordBound B s) : ∃u,
    BoundedRuns program n x B s (arrayCost k b) u ∧ Header k b count A (i+1) u ∧
    Partial k b A (i+1) v u ∧ Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u := by
  have first:=setup_runs x h hi hB extent strideBound bound
  let entry:=setPC (ready s) 6
  have entryBound:WordBound B entry:=changePC_bound B (entered s) 6 first.final_bound (by omega)
  have currentBound:arrayBase A k i+2^k≤B:=(array_extent (A:=A) (k:=k) hi).trans extent
  have beforePartial:Partial k b A i v entry:=hv
  obtain ⟨child,run,values,frame,cu,_⟩:=UniformBinaryTensorCMachine.loop_execution n B k
    (arrayBase A k i) (k-b) x b entry (v ⟨i,hi⟩) (by omega) (ready_header h)
    (by unfold arrayBase;omega) (partial_current v hi beforePartial) con entryBound (by omega) currentBound
  have moved:=UniformBoundedAssembly.boundedExecution_placed child_code
    (by rw [UniformBinaryTensorCMachine.program_length];omega) (by omega :66≤B) run
  have ez:placed 24 entry=entered s:=rfl
  rw [ez] at moved
  let mid:=setPC child 66
  have fmid:=frame.trans (UniformBinaryTensorCMachine.Frame.pc (arrayBase A k i) (2^k) child 66)
  have fwhole:UniformBinaryTensorCMachine.Frame (arrayBase A k i) (2^k) (entered s) mid:=
    (UniformBinaryTensorCMachine.Frame.pc (arrayBase A k i) (2^k) (entered s) 6).trans fmid
  have kept (r : ℕ) (hr:5200≤r) : mid.natReg r=(ready s).natReg r :=
    fmid.natReg r (by unfold UniformBinaryTensorCMachine.Changed;omega)
  have rh:=ready_parent h
  have hh:Header k b count A i (setPC mid 10):=by
    refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,rfl⟩
    · exact (kept 5200 (by omega)).trans rh.bits
    · exact (kept 5201 (by omega)).trans rh.count
    · exact (kept 5202 (by omega)).trans rh.base
    · exact (kept 5203 (by omega)).trans rh.size
    · exact (kept 5204 (by omega)).trans rh.start
    · exact (kept 5205 (by omega)).trans rh.stride
    · exact (kept 5209 (by omega)).trans rh.index
    · exact (kept 5212 (by omega)).trans rh.zero
    · exact (kept 5207 (by omega)).trans rh.one
    · exact (kept 5208 (by omega)).trans rh.two
  have finishRun:=post_runs x hh hi rfl hB moved.final_bound
  have outPartial:Partial k b A (i+1) v mid:=partial_after v hi beforePartial values fmid
  have allFrame:Frame A (count*2^k) s mid:=(ready_frame A (count*2^k) s).trans (child_frame hi fwhole)
  refine ⟨after mid,?_,after_header hh,outPartial,allFrame.trans (after_frame A (count*2^k) mid),cu⟩
  convert (first.trans moved).trans finishRun using 1
  change (k-b)*(25*2^(k-1)+11)+18=14+((k-b)*(25*2^(k-1)+11)+2)+2
  omega

theorem loop_execution (n B k b count A remaining : ℕ) (x : Fin n→ℂ) :
    ∀i s (v : Fin count→Fin (2^k)→Scalar),i+remaining=count→Header k b count A i s→
    Partial k b A i v s→b≤k→3≤A→UniformBinaryCStageMachine.Constants s→69≤B→
    A+count*2^k≤B→2^b*2≤B→WordBound B s→∃u,
    BoundedExecution program n x B s (remaining*arrayCost k b+2) u ∧
    Partial k b A count v u ∧ Frame A (count*2^k) s u ∧
    UniformBinaryCStageMachine.Constants u ∧ u.pc=68 := by
  induction remaining with
  | zero=>
    intro i s v eq h values hb a con code extent strideBound bound
    have he:i=count:=by omega
    let u:=setPC s 68
    have ub:=changePC_bound B s 68 bound (by omega)
    simp only [Nat.zero_mul,Nat.zero_add]
    refine ⟨u,.next bound (u:=u) ?_ (.halt ub ?_),?_,Frame.pc A (count*2^k) s 68,con,rfl⟩
    · simp [step,branch_code,h.pc,h.index,h.count,he,u,setPC]
    · simp [step,halt_code,u,setPC]
    · intro w z
      change s.scalarHeap (arrayBase A k w.val+z.val)=_
      simpa only [he] using values w z
  | succ remaining ih=>
    intro i s v eq h values hb a con code extent strideBound bound
    obtain ⟨mid,first,head,result,frame,constants⟩:=iteration x s v h (by omega)
      values hb a con code extent strideBound bound
    obtain ⟨u,last,out,rest,cu,pcu⟩:=ih (i+1) mid v (by omega) head result hb a constants
      code extent strideBound first.final_bound
    refine ⟨u,?_,out,frame.trans rest,cu,pcu⟩
    convert first.executes last using 1
    ring

/-- All high spectator axes of each real array are executed, with no changes
outside the role-major bank, no recursive child assumption and no extra roots. -/
theorem execution (n B k b count A : ℕ) (x : Fin n→ℂ) (s : State)
    (v : Fin count→Fin (2^k)→Scalar) (pc:s.pc=0)
    (bits:s.natReg 5200=k) (arrays:s.natReg 5201=count)
    (base:s.natReg 5202=A) (size:s.natReg 5203=2^k) (start:s.natReg 5204=b)
    (data:∀w z,s.scalarHeap (arrayBase A k w.val+z.val)=some (v w z))
    (hb:b≤k) (ha:3≤A) (con:UniformBinaryCStageMachine.Constants s)
    (hB:69≤B) (extent:A+count*2^k≤B) (strideBound:2^b*2≤B) (bound:WordBound B s) : ∃u,
    BoundedExecution program n x B s (4*b+count*arrayCost k b+9) u ∧
    (∀w z,u.scalarHeap (arrayBase A k w.val+z.val)=some (transformed k b (v w) z)) ∧
    Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u ∧ u.pc=68 := by
  have bootRun:=boot_runs x s pc bound hB
  obtain ⟨e,powerRun,head,powerFrame,powerHeap⟩:=power_loop n B k b count A b x 0 (bootState s)
    (by omega) (boot_header pc bits arrays base size start) hb hB bootRun.final_bound
  have bf:Frame A (count*2^k) s e:=(boot_frame A (count*2^k) s).trans powerFrame
  have scalarAll:∀a,e.scalarHeap a=s.scalarHeap a:=fun a=>congrFun powerHeap a
  have hv:Partial k b A 0 v e:=by
    intro w z
    rw [scalarAll,data]
    simp
  have ec:UniformBinaryCStageMachine.Constants e:=by
    rcases con with ⟨hc,hd⟩
    exact ⟨by rw [scalarAll];exact hc,by rw [scalarAll];exact hd⟩
  obtain ⟨u,last,out,frame,cu,pcu⟩:=loop_execution n B k b count A count x 0 e v
    (by omega) head hv hb ha ec hB extent strideBound powerRun.final_bound
  have values:∀w z,u.scalarHeap (arrayBase A k w.val+z.val)=some (transformed k b (v w) z):=by
    intro w z
    simpa only [ite_eq_left w.isLt] using out w z
  refine ⟨u,?_,values,bf.trans frame,cu,pcu⟩
  convert (bootRun.trans powerRun).executes last using 1
  omega

theorem arrayCost_bound (k b : ℕ) : arrayCost k b≤(36*(k-b)+18)*2^k := by
  have hp:1≤2^k:=Nat.one_le_pow k 2 (by omega)
  have hs:2^(k-1)≤2^k:=Nat.pow_le_pow_right (by omega) (by omega)
  unfold arrayCost
  have hm:=Nat.mul_le_mul_left (k-b) (show 25*2^(k-1)+11≤36*2^k by omega)
  nlinarith

theorem runtime_bound {k b count : ℕ} (hb:b≤k) (hw:1≤count) :
    4*b+count*arrayCost k b+9≤(36*(k-b)+22)*(count*2^k)+9 := by
  have hp:k≤2^k:=(Nat.lt_pow_self (by omega :1<2)).le
  have volume:2^k≤count*2^k:=by
    simpa using Nat.mul_le_mul_right (2^k) hw
  have hm:=Nat.mul_le_mul_left count (arrayCost_bound k b)
  nlinarith

theorem remainder_runtime_bound {k b count m : ℕ} (hb:b≤k) (hw:1≤count)
    (hr:k-b < m) :
    4*b+count*arrayCost k b+9≤(36*m+22)*(count*2^k)+9 := by
  have h:36*(k-b)+22≤36*m+22:=by omega
  exact (runtime_bound hb hw).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 9)

theorem stride_bound {k b count A B : ℕ} (hb:b≤k) (hw:2≤count)
    (extent:A+count*2^k≤B) : 2^b*2≤B := by
  have hs:2^b≤2^k:=Nat.pow_le_pow_right (by omega) hb
  have hm:=Nat.mul_le_mul_right (2^k) hw
  nlinarith

/-- The high-bit suffix closes the full C tensor once the low-bit prefix
has been executed, with the exact physical binary coordinate order. -/
theorem prefix_suffix (k b : ℕ) (v : Fin (2^k)→Scalar) :
    transformed k b (applyAxes k ((List.finRange k).take b) v)=
      applyAxes k (List.finRange k) v := by
  unfold transformed applyAxes
  rw [←List.foldl_append,List.take_append_drop]

theorem prefix_suffix_values (k b : ℕ) (v : Fin (2^k)→Scalar) :
    (fun z=>(transformed k b (applyAxes k ((List.finRange k).take b) v) z).value)=
      (physicalMatrix k).mulVec (fun z=>(v z).value) := by
  rw [prefix_suffix]
  exact applyAxes_tensor k v

end
end ExactFourierCircuits.UniformBinarySpectatorCMachine
