import UniformResidualAddressToggleMachine
import UniformDFSProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualFiberAddressMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section
/-- Fixed binary DFS. Images are read at k-depth-1, so selected low bits
remain contiguous. The native accumulator is restored from a two-word stack.
There is no callback, bitwise RAM instruction, or per-leaf axis scan. -/
def boot : List Op := [.literal 4020 0,.literal 4021 0,.literal 4022 0,
 .literal 4023 0,.literal 4024 1,.literal 4025 2,.literal 4026 0]
def enter : List Op := [.literal 4022 0]
def save : List Op := [.binary .mul 4027 4020 4025,.binary .add 4027 4010 4027,
 .store 4027 4021,.binary .add 4027 4027 4024,
 .binary .add 4028 4022 4024,.store 4027 4028]
def toggleSetup : List Op := [.binary .sub 4002 4008 4020,
 .binary .sub 4002 4002 4024,.binary .mul 4000 4021 4024,
 .binary .mul 4001 4009 4024,.binary .mul 4003 4014 4024,
 .binary .mul 4004 4015 4024,.binary .mul 4005 4012 4024]
def afterToggle : List Op := [.binary .mul 4021 4000 4024]
def descend : List Op := [.binary .add 4020 4020 4024]
def emit : List Op := [.binary .add 4027 4011 4023,.store 4027 4021,
 .binary .add 4023 4023 4024]
def pop : List Op := [.binary .sub 4020 4020 4024,.binary .mul 4027 4020 4025,
 .binary .add 4027 4010 4027,.load 4021 4027,
 .binary .add 4027 4027 4024,.load 4022 4027]
def program : Program := boot.map Op.code++[.branchLT 4020 4008 8 58]++
 enter.map Op.code++[.branchLT 4022 4025 10 62]++save.map Op.code++
 [.branchLT 4022 4024 56 17]++toggleSetup.map Op.code++
 UniformResidualAddressToggleMachine.program.map (relocate 24 55)++
 afterToggle.map Op.code++descend.map Op.code++[.jump 7]++
 emit.map Op.code++[.jump 62,.branchLT 4026 4020 63 70]++pop.map Op.code++[.jump 9,.halt]
theorem program_length : program.length=71 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
theorem enter_code : BlockAt enter program 8 := by intro i hi;change i<1 at hi;interval_cases i;rfl
theorem save_code : BlockAt save program 10 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem setup_code : BlockAt toggleSetup program 17 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
theorem toggle_code : CodeAt UniformResidualAddressToggleMachine.program program 24 55 := by
 intro i hi;change i<31 at hi;interval_cases i <;> rfl
theorem after_code : BlockAt afterToggle program 55 := by intro i hi;change i<1 at hi;interval_cases i;rfl
theorem descend_code : BlockAt descend program 56 := by intro i hi;change i<1 at hi;interval_cases i;rfl
theorem emit_code : BlockAt emit program 58 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem pop_code : BlockAt pop program 63 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem node_at : program[7]?=some (.branchLT 4020 4008 8 58) := rfl
theorem child_at : program[9]?=some (.branchLT 4022 4025 10 62) := rfl
theorem select_at : program[16]?=some (.branchLT 4022 4024 56 17) := rfl
theorem down_at : program[57]?=some (.jump 7) := rfl
theorem emit_at : program[61]?=some (.jump 62) := rfl
theorem return_at : program[62]?=some (.branchLT 4026 4020 63 70) := rfl
theorem pop_at : program[69]?=some (.jump 9) := rfl
theorem halt_at : program[70]?=some .halt := rfl

structure Header (k q w images stack output table : ℕ) (s : State) : Prop where
 bits : s.natReg 4008=k
 images : s.natReg 4009=images
 stack : s.natReg 4010=stack
 output : s.natReg 4011=output
 table : s.natReg 4012=table
 width : s.natReg 4014=w
 size : s.natReg 4015=2^q
 one : s.natReg 4024=1
 two : s.natReg 4025=2
 zero : s.natReg 4026=0

/-- Mathematical cost of the literal DFS transitions; actual complete
execution is proved separately, so this alone is not a runtime certificate. -/
def treeCost (w : ℕ) : ℕ→ℕ
 | 0=>5
 | k+1=>2*treeCost w k+17*w+62

theorem treeCost_balance (w k : ℕ) :
 treeCost w k+(17*w+62)=(17*w+67)*2^k := by
 induction k with
 | zero=>simp [treeCost];ring
 | succ k ih=>rw [treeCost,Nat.pow_succ];nlinarith

theorem treeCost_linear (w k : ℕ) :
 treeCost w k+9≤(17*w+67)*2^k+9 := by have h:=treeCost_balance w k;omega

/-- One literal leaf emits the native address, preserving all scalar state. -/
theorem leaf_runs (n B k q w images stack output table a c : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Header k q w images stack output table s)
 (pc : s.pc=7) (depth : s.natReg 4020=k) (address : s.natReg 4021=a)
 (count : s.natReg 4023=c) (bound : WordBound B s) (code : 71≤B)
 (extent : output+c≤B) (value : a≤B) (countBound : c+1≤B) :
 ∃u,BoundedRuns program n x B s 5 u ∧ u.pc=62 ∧
 Header k q w images stack output table u ∧ u.natReg 4020=k ∧ u.natReg 4021=a ∧
 u.natReg 4023=c+1 ∧ u.natHeap (output+c)=some a ∧
 (∀z,z≠output+c→u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let entry:State:={s with pc:=58}
 have eb:=changePC_bound B s 58 bound (by omega)
 have branch : BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,pc,node_at,depth,h.bits,entry]) (.refl eb)
 have safe : readable emit entry ∧ peak emit entry≤B := by
  simp [emit,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   entry,h.output,h.one,address,count]
  omega
 have er:=block_runs emit program 58 n B x entry emit_code rfl eb
  (by change 61≤B;omega) safe.1 safe.2
 let written:=applyBlock emit entry
 let u:State:={written with pc:=62}
 have wp : written.pc=61 := by simp [written,emit,applyBlock,Op.apply,writeNat,next,entry]
 have ub:=changePC_bound B written 62 er.final_bound (by omega)
 have jump : BoundedRuns program n x B written 1 u:=.next er.final_bound
  (by simp [step,wp,emit_at,u]) (.refl ub)
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl⟩
 · convert branch.trans (er.trans jump) using 1
   simp [emit]
 · constructor <;> simp [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry,
    h.bits,h.images,h.stack,h.output,h.table,h.width,h.size,h.one,h.two,h.zero]
 · simpa [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry] using depth
 · simpa [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry] using address
 · simp [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry,count,h.one]
 · simp [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry,address,count,h.output,h.one]
 · intro z ne
   simp [u,written,emit,applyBlock,Op.apply,evalNat,writeNat,next,entry,address,count,h.output,h.one,ne]


/-- Return restores both the native parent and its next child from actual
stack cells. No entry stack is assumed for the whole traversal. -/
theorem pop_runs (n B k q w images stack output table d a digit : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Header k q w images stack output table s)
 (pc : s.pc=62) (depth : s.natReg 4020=d+1)
 (left : s.natHeap (stack+2*d)=some a)
 (right : s.natHeap (stack+2*d+1)=some digit)
 (bound : WordBound B s) (code : 71≤B)
 (extent : stack+2*d+1≤B) :
 ∃u,BoundedRuns program n x B s 8 u ∧ u.pc=9 ∧
 Header k q w images stack output table u ∧ u.natReg 4023=s.natReg 4023 ∧
 u.natReg 4020=d ∧ u.natReg 4021=a ∧ u.natReg 4022=digit ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let entry:State:={s with pc:=63}
 have eb:=changePC_bound B s 63 bound (by omega)
 have branch : BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,pc,return_at,depth,h.zero,entry]) (.refl eb)
 have la : a≤B := (bound.2.2.1 _ _ left).2
 have ld : digit≤B := (bound.2.2.1 _ _ right).2
 have sameLeft : s.natHeap (stack+d*2)=some a := by simpa [Nat.mul_comm] using left
 have sameRight : s.natHeap (stack+d*2+1)=some digit := by simpa [Nat.mul_comm] using right
 have safe : readable pop entry ∧ peak pop entry≤B := by
  simp [pop,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   entry,h.stack,h.one,h.two,depth,sameLeft,sameRight]
  omega
 have pr:=block_runs pop program 63 n B x entry pop_code rfl eb
  (by change 69≤B;omega) safe.1 safe.2
 let restored:=applyBlock pop entry
 let u:State:={restored with pc:=9}
 have rp : restored.pc=69 := by simp [restored,pop,applyBlock,Op.apply,writeNat,next,entry]
 have ub:=changePC_bound B restored 9 pr.final_bound (by omega)
 have jump : BoundedRuns program n x B restored 1 u:=.next pr.final_bound
  (by simp [step,rp,pop_at,u]) (.refl ub)
 refine ⟨u,?_,rfl,?_,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
 · convert branch.trans (pr.trans jump) using 1
   simp [pop]
 · constructor <;> simp [u,restored,pop,applyBlock,Op.apply,evalNat,writeNat,next,entry,
    h.bits,h.images,h.stack,h.output,h.table,h.width,h.size,h.one,h.two,h.zero]
 all_goals simp [u,restored,pop,applyBlock,Op.apply,evalNat,writeNat,next,
  entry,h.stack,h.one,h.two,depth,sameLeft,sameRight]


lemma save_runs (n B k q w images stack output table d a j : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Header k q w images stack output table s)
 (pc : s.pc=9) (depth : s.natReg 4020=d) (address : s.natReg 4021=a)
 (digit : s.natReg 4022=j) (jlt : j<2) (bound : WordBound B s) (code : 71≤B)
 (extent : stack+2*d+2≤B) :
 BoundedRuns program n x B s 7 (applyBlock save {s with pc:=10}) := by
 let entry:State:={s with pc:=10}
 have eb:=changePC_bound B s 10 bound (by omega)
 have branch : BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,pc,child_at,digit,h.two,jlt,entry]) (.refl eb)
 have av : a≤B := by have h:=bound.2.1 4021;rw [address] at h;exact h
 have safe : readable save entry ∧ peak save entry≤B := by
  simp [save,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   entry,h.stack,h.one,h.two,depth,address,digit]
  omega
 have sr:=block_runs save program 10 n B x entry save_code rfl eb (by change 16≤B;omega) safe.1 safe.2
 convert branch.trans sr using 1
 simp [save]

theorem zero_child_runs (n B k q w images stack output table d a : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Header k q w images stack output table s)
 (pc : s.pc=9) (depth : s.natReg 4020=d) (address : s.natReg 4021=a)
 (digit : s.natReg 4022=0) (low : d<k) (bound : WordBound B s) (code : 71≤B)
 (extent : stack+2*d+2≤B) : ∃u,
 BoundedRuns program n x B s 10 u ∧ u.pc=7 ∧
 Header k q w images stack output table u ∧ u.natReg 4020=d+1 ∧
 u.natReg 4021=a ∧ u.natReg 4023=s.natReg 4023 ∧
 u.natHeap=Function.update (Function.update s.natHeap (stack+2*d) (some a))
   (stack+2*d+1) (some 1) ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have sr:=save_runs n B k q w images stack output table d a 0 x s h pc depth address digit
  (by omega) bound code extent
 let saved:=applyBlock save {s with pc:=10}
 let selected:State:={saved with pc:=56}
 have sp : saved.pc=16 := by simp [saved,save,applyBlock,Op.apply,writeNat,next]
 have selectRun : BoundedRuns program n x B saved 1 selected:=.next sr.final_bound
  (by simp [step,select_at,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,digit,h.one,selected])
  (.refl (changePC_bound B saved 56 sr.final_bound (by omega)))
 have db : d+1≤B := by have kb:=bound.2.1 4008;rw [h.bits] at kb;omega
 have safe : readable descend selected ∧ peak descend selected≤B := by
  simp [descend,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,
   selected,saved,save,applyBlock,writeNat,next,h.one,depth,db]
 have dr:=block_runs descend program 56 n B x selected descend_code rfl selectRun.final_bound
  (by change 57≤B;omega) safe.1 safe.2
 let descended:=applyBlock descend selected
 let u:State:={descended with pc:=7}
 have dp : descended.pc=57 := by simp [descended,descend,applyBlock,Op.apply,writeNat,next,selected]
 have jump : BoundedRuns program n x B descended 1 u:=.next dr.final_bound
  (by simp [step,dp,down_at,u]) (.refl (changePC_bound B descended 7 dr.final_bound (by omega)))
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl⟩
 · convert sr.trans (selectRun.trans (dr.trans jump)) using 1
   simp [descend]
 · constructor <;> simp [u,descended,descend,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,
   h.bits,h.images,h.stack,h.output,h.table,h.width,h.size,h.one,h.two,h.zero]
 · simp [u,descended,descend,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,depth]
 · simp [u,descended,descend,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,address]
 · rfl
 · simp [u,descended,descend,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,
   h.stack,h.one,h.two,depth,address,digit,Nat.mul_comm]


theorem one_child_runs (n B k q w images stack output table d a image : ℕ)
 (x : Fin n→ℂ) (s : State) (h : Header k q w images stack output table s)
 (pc : s.pc=9) (depth : s.natReg 4020=d) (address : s.natReg 4021=a)
 (digit : s.natReg 4022=1) (low : d<k) (bound : WordBound B s) (code : 71≤B)
 (extent : stack+2*d+2≤B) (imagesBefore : images+k ≤ stack)
 (stackBefore : stack+2*d+2≤table) (tableExtent : table+2^q*2^q≤B)
 (volume : 2^(q*w)≤B) (smallA : a<2^(q*w)) (smallImage : image<2^(q*w))
 (physical : s.natHeap (images+(k-d-1))=some image)
 (entries : UniformXorTableMachine.Entries q table (2^q*2^q) s) : ∃u,
 BoundedRuns program n x B s (17*w+33) u ∧ u.pc=7 ∧
 Header k q w images stack output table u ∧ u.natReg 4020=d+1 ∧
 u.natReg 4021=a^^^image ∧ u.natReg 4023=s.natReg 4023 ∧
 u.natHeap=Function.update (Function.update s.natHeap (stack+2*d) (some a))
   (stack+2*d+1) (some 2) ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have sr:=save_runs n B k q w images stack output table d a 1 x s h pc depth address digit
  (by omega) bound code extent
 let saved:=applyBlock save {s with pc:=10}
 let selected:State:={saved with pc:=17}
 have sp : saved.pc=16 := by simp [saved,save,applyBlock,Op.apply,writeNat,next]
 have selectRun : BoundedRuns program n x B saved 1 selected:=.next sr.final_bound
  (by simp [step,select_at,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,digit,h.one,selected])
  (.refl (changePC_bound B saved 17 sr.final_bound (by omega)))
 have imSmall : k-d-1<k := by omega
 have imageB : images+(k-d-1)≤B := by omega
 have smallIndex : k-d-1≤B := by omega
 have av : a≤B := smallA.le.trans volume
 have wb : w≤B := by have b:=bound.2.1 4014;rw [h.width] at b;exact b
 have nb : 2^q≤B := by have b:=bound.2.1 4015;rw [h.size] at b;exact b
 have tb : table≤B := by omega
 have safe : readable toggleSetup selected ∧ peak toggleSetup selected≤B := by
  simp [toggleSetup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   selected,saved,save,applyBlock,h.bits,h.images,h.width,h.size,h.table,h.one,depth,address]
  omega
 have setupRun:=block_runs toggleSetup program 17 n B x selected setup_code rfl selectRun.final_bound
  (by change 24≤B;omega) safe.1 safe.2
 let ready:=applyBlock toggleSetup selected
 let child:State:={ready with pc:=0}
 have cb:=changePC_bound B ready 0 setupRun.final_bound (by omega)
 have rp : ready.pc=24 := by simp [ready,toggleSetup,applyBlock,Op.apply,writeNat,next,selected]
 have arg0 : child.natReg 4000=a := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,address]
 have arg1 : child.natReg 4001=images := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,h.images]
 have arg2 : child.natReg 4002=k-d-1 := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,h.bits,depth]
 have arg3 : child.natReg 4003=w := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,h.width]
 have arg4 : child.natReg 4004=2^q := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,h.size]
 have arg5 : child.natReg 4005=table := by
  simp [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,h.one,h.table]
 have below : images+(k-d-1)<stack := by omega
 have actual : child.natHeap (images+(k-d-1))=some image := by
  simpa (disch:=omega) [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,
   h.stack,h.one,h.two,depth,address,digit,Nat.mul_comm] using physical
 have tableNow : UniformXorTableMachine.Entries q table (2^q*2^q) child := by
  intro j hj
  have value:=entries j hj
  simpa (disch:=omega) [child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next,
   h.stack,h.one,h.two,depth,address,digit,Nat.mul_comm] using value
 obtain ⟨v,tr,pcv,val,tf⟩:=UniformResidualAddressToggleMachine.execution n B q w a images (k-d-1) image table
  x child rfl arg0 arg1 arg2 arg3 arg4 arg5 actual tableNow smallA smallImage cb (by omega) imageB tableExtent volume
 have call:=UniformBoundedAssembly.boundedExecution_placed toggle_code
  (by change 55≤B;omega) (by omega) tr
 have start : UniformAssembly.placed 24 child=ready := by
  change {ready with pc:=24}=ready
  rw [←rp]
 rw [start] at call
 let ret:State:={v with pc:=55}
 have keep (r:ℕ) (hr:4008≤r ∧ r<4027) : ret.natReg r=s.natReg r := by
  have k:=tf.natReg r (by
   unfold UniformResidualAddressToggleMachine.Changed UniformBlockXorMachine.Changed
   omega)
  simpa (disch:=omega) [ret,child,ready,toggleSetup,selected,saved,save,applyBlock,Op.apply,evalNat,writeNat,next] using k
 have one : ret.natReg 4024=1 := (keep 4024 (by omega)).trans h.one
 have dep : ret.natReg 4020=d := (keep 4020 (by omega)).trans depth
 have header : Header k q w images stack output table ret :=
  ⟨(keep 4008 (by omega)).trans h.bits,(keep 4009 (by omega)).trans h.images,
   (keep 4010 (by omega)).trans h.stack,(keep 4011 (by omega)).trans h.output,
   (keep 4012 (by omega)).trans h.table,(keep 4014 (by omega)).trans h.width,
   (keep 4015 (by omega)).trans h.size,one,(keep 4025 (by omega)).trans h.two,
   (keep 4026 (by omega)).trans h.zero⟩
 have result : ret.natReg 4000=a^^^image := val
 have xb : a^^^image≤B := (Nat.xor_lt_two_pow smallA smallImage).le.trans volume
 have safeAfter : readable afterToggle ret ∧ peak afterToggle ret≤B := by
  simp [afterToggle,readable,peak,Op.readable,Op.peak,evalNat,one,result,xb]
 have ar:=block_runs afterToggle program 55 n B x ret after_code rfl call.final_bound
  (by change 56≤B;omega) safeAfter.1 safeAfter.2
 let copied:=applyBlock afterToggle ret
 have dp : copied.pc=56 := by simp [copied,afterToggle,applyBlock,Op.apply,writeNat,next,ret]
 have db : d+1≤B := by have b:=bound.2.1 4008;rw [h.bits] at b;omega
 have safeDescend : readable descend copied ∧ peak descend copied≤B := by
  simp [descend,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,copied,afterToggle,
   applyBlock,writeNat,next,one,dep,db]
 have dr:=block_runs descend program 56 n B x copied descend_code dp ar.final_bound
  (by change 57≤B;omega) safeDescend.1 safeDescend.2
 let descended:=applyBlock descend copied
 let u:State:={descended with pc:=7}
 have up : descended.pc=57 := by simp [descended,descend,applyBlock,Op.apply,writeNat,next,dp]
 have jump : BoundedRuns program n x B descended 1 u:=.next dr.final_bound
  (by simp [step,up,down_at,u]) (.refl (changePC_bound B descended 7 dr.final_bound (by omega)))
 refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · convert sr.trans (selectRun.trans (setupRun.trans (call.trans (ar.trans (dr.trans jump))))) using 1
   simp [toggleSetup,afterToggle,descend]
   omega
 · constructor <;> simp [u,descended,descend,copied,afterToggle,applyBlock,Op.apply,evalNat,writeNat,next,
   header.bits,header.images,header.stack,header.output,header.table,header.width,header.size,
   header.one,header.two,header.zero]
 · simp [u,descended,descend,copied,afterToggle,applyBlock,Op.apply,evalNat,writeNat,next,one,dep]
 · simp [u,descended,descend,copied,afterToggle,applyBlock,Op.apply,evalNat,writeNat,next,one,result]
 · simpa [u,descended,descend,copied,afterToggle,applyBlock,Op.apply,evalNat,writeNat,next] using keep 4023 (by omega)
 · simpa [u,descended,descend,copied,afterToggle,ret,child,ready,toggleSetup,selected,saved,save,applyBlock,
   Op.apply,evalNat,writeNat,next,h.stack,h.one,h.two,depth,address,digit,Nat.mul_comm] using tf.natHeap
 · exact tf.scalarHeap
 · exact tf.scalarReg
 · exact tf.outputs
 · exact tf.roots

end
end ExactFourierCircuits.UniformResidualFiberAddressMachine
