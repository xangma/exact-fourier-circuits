import UniformBinaryTensorCoordinates

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBinaryTensorCMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformBinaryTensorCoordinates

/- One fixed all-axis ordinary C tensor loop. Nat2823=A,2824=2^k,
2825=k are input headers. Nat2820 is the actual axis counter;2821/2
are local one/two. Every call, header update and return is charged. -/
def boot : List Op := [.literal 2820 0,.literal 2821 1,.literal 2822 2,
 .literal 2800 1,.mul 2801 2823 2821]
def updates : List Op := [.mul 2800 2800 2822,.add 2820 2820 2821]
def program : Program := boot.map Op.code ++
 [.natBinary .div 2802 2824 2822,.branchLT 2820 2825 7 41] ++
 UniformBinaryCStageMachine.program.map (relocate 7 37) ++ updates.map Op.code ++
 [.natBinary .div 2802 2802 2822,.jump 6,.halt]
theorem program_length : program.length=42 := rfl
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem updates_code : BlockAt updates program 37 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem stage_code : CodeAt UniformBinaryCStageMachine.program program 7 37 := by
 intro i hi;change i<30 at hi;interval_cases i <;> rfl
theorem branch_at : program[6]?=some (.branchLT 2820 2825 7 41) := rfl
theorem jump_at : program[40]?=some (.jump 6) := rfl
theorem halt_at : program[41]?=some .halt := rfl
theorem boot_div_at : program[5]?=some (.natBinary .div 2802 2824 2822) := rfl
theorem update_div_at : program[39]?=some (.natBinary .div 2802 2802 2822) := rfl

noncomputable section

structure Header (k A i : ℕ) (s : State) : Prop where
 pc : s.pc=6
 axis : s.natReg 2820=i
 one : s.natReg 2821=1
 two : s.natReg 2822=2
 base : s.natReg 2823=A
 size : s.natReg 2824=2^k
 bits : s.natReg 2825=k
 stride : s.natReg 2800=2^i
 upper : s.natReg 2802=2^k/(2^i*2)
 dataBase : s.natReg 2801=A

theorem binary_upper (k i : ℕ) (hi : i<k) :
 2^k/(2^i*2)=2^(k-(i+1)) := by
 have vol:=axis_volume k (⟨i,hi⟩:Fin k)
 change 2^i*2*2^(k-(i+1))=2^k at vol
 rw [←vol]
 simp

def bootState (s : State) : State :=
 writeNat (applyBlock boot s) 2802 (s.natReg 2824/2)

theorem boot_header (k A : ℕ) (s : State) (pc : s.pc=0)
 (a : s.natReg 2823=A) (size : s.natReg 2824=2^k) (bits : s.natReg 2825=k) :
 Header k A 0 (bootState s) := by
 constructor <;> simp [bootState,boot,applyBlock,Op.apply,writeNat,next,pc,a,size,bits]

def divided (s : State) : State :=
 writeNat (applyBlock updates s) 2802 (s.natReg 2802/2)
def advance (s : State) : State := setPC (divided s) 6

theorem advance_header (k A i : ℕ) (s : State) (h : Header k A i (setPC s 6))
 (pc : s.pc=37) : Header k A (i+1) (advance s) := by
 have quotient : (2^k/(2^i*2))/2=2^k/(2^(i+1)*2) := by
  rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
 rcases h with ⟨_,axis,one,two,base,size,bits,stride,upper,dataBase⟩
 dsimp only [setPC] at axis one two base size bits stride upper dataBase
 constructor <;> simp [advance,divided,updates,applyBlock,Op.apply,setPC,writeNat,next,
  axis,one,two,base,size,bits,stride,upper,dataBase,quotient,pc]
 all_goals rw [Nat.pow_succ]

def Present (A k : ℕ) (v : Fin (2^k)→Scalar) (s : State) : Prop :=
 ∀z,s.scalarHeap (A+z.val)=some (v z)

def Changed (r : ℕ) : Prop :=
 r=0 ∨ r=1 ∨ r=2 ∨ r=2800 ∨ r=2801 ∨ r=2802 ∨ r=2803 ∨ r=2804 ∨
 r=2805 ∨ r=2806 ∨ r=2810 ∨ r=2811 ∨ r=2820 ∨ r=2821 ∨ r=2822
structure Frame (A L : ℕ) (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg : ∀r,8≤r→u.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,z<A∨A+L≤z→u.scalarHeap z=s.scalarHeap z

theorem Frame.refl (A L : ℕ) (s : State) : Frame A L s s :=
 ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.pc (A L : ℕ) (s : State) (pc : ℕ) : Frame A L s (setPC s pc) :=
 ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {A L : ℕ} {s u v : State} (f : Frame A L s u) (g : Frame A L u v) :
 Frame A L s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
  fun r h=>(g.natReg r h).trans (f.natReg r h),
  fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
  fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
theorem Frame.of_stage {A L : ℕ} {s u : State} (f : UniformBinaryCStageMachine.Frame A L s u) :
 Frame A L s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,f.scalarHeap⟩
 intro r hr
 apply f.natReg
 unfold Changed at hr
 unfold UniformBinaryCStageMachine.Kept
 omega

theorem frame_boot (A L : ℕ) (s : State) : Frame A L s (bootState s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r hr
 simp only [Changed,not_or] at hr
 simp [bootState,boot,applyBlock,Op.apply,writeNat,next,hr]

theorem frame_advance (A L : ℕ) (s : State) : Frame A L s (advance s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r hr
 simp only [Changed,not_or] at hr
 simp [advance,divided,updates,applyBlock,Op.apply,setPC,writeNat,next,hr]

theorem boot_runs (n B k A : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (a : s.natReg 2823=A) (size : s.natReg 2824=2^k)
 (bound : WordBound B s) (code : 42≤B) (extent : A+2^k≤B) :
 BoundedRuns program n x B s 6 (bootState s) := by
 have cap : peak boot s≤B := by
  simp [boot,peak,Op.peak,Op.apply,writeNat,next,a,show A≤B by omega,
   show 2≤B by omega,show 1≤B by omega]
 have run:=block_runs boot program 0 n B x s boot_code pc bound
  (by simp [boot];omega) (by simp [boot,readable,Op.readable]) cap
 have b : WordBound B (bootState s) := writeNat_bound B (applyBlock boot s) 2802
  (s.natReg 2824/2) run.final_bound
  (by simp [boot,applyBlock,Op.apply,writeNat,next,pc];omega)
  ((Nat.div_le_self _ _).trans (by rw [size];omega))
 have last : BoundedRuns program n x B (applyBlock boot s) 1 (bootState s) := by
  refine .next run.final_bound ?_ (.refl b)
  simp [step,boot_div_at,bootState,boot,applyBlock,Op.apply,writeNat,next,evalNat,pc]
 exact run.trans last

theorem header_transport (k A i : ℕ) {s u : State} (h : Header k A i s)
 (f : UniformBinaryCStageMachine.Frame A (2^k) s u) : Header k A i (setPC u 6) := by
 refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals
  dsimp only [setPC]
  rw [f.natReg _ (by unfold UniformBinaryCStageMachine.Kept;omega)]
  first | exact h.axis | exact h.one | exact h.two | exact h.base | exact h.size
        | exact h.bits | exact h.stride | exact h.upper | exact h.dataBase

theorem advance_runs (n B k A i : ℕ) (x : Fin n→ℂ) (s : State)
 (h : Header k A i (setPC s 6)) (pc : s.pc=37) (hi : i<k)
 (bound : WordBound B s) (code : 42≤B) (extent : A+2^k≤B) :
 BoundedRuns program n x B s 4 (advance s) := by
 have strideBound : 2^i*2≤B := by
  rw [←Nat.pow_succ]
  exact (Nat.pow_le_pow_right (by omega) (by omega : i+1≤k)).trans (by omega)
 have indexBound : i+1≤B := by
  have hb:=bound.2.1 2825
  have bits:=h.bits
  dsimp only [setPC] at bits
  rw [bits] at hb
  omega
 have cap : peak updates s≤B := by
  rcases h with ⟨_,axis,one,two,base,size,bits,stride,upper,dataBase⟩
  dsimp only [setPC] at axis one two stride
  simp [updates,peak,Op.peak,Op.apply,writeNat,next,stride,two,axis,one,strideBound,indexBound]
 have run:=block_runs updates program 37 n B x s updates_code pc bound
  (by simp [updates];omega) (by simp [updates,readable,Op.readable]) cap
 have d : WordBound B (divided s) := writeNat_bound B (applyBlock updates s) 2802
  (s.natReg 2802/2) run.final_bound
  (by simp [updates,applyBlock,Op.apply,writeNat,next,pc];omega)
  ((Nat.div_le_self _ _).trans (bound.2.1 _))
 have endBound : WordBound B (advance s):=changePC_bound B _ 6 d (by omega)
 have last : BoundedRuns program n x B (applyBlock updates s) 2 (advance s) := by
  refine .next run.final_bound (u:=divided s) ?_ (.next d ?_ (.refl endBound))
  · simp [step,update_div_at,divided,updates,applyBlock,Op.apply,writeNat,next,evalNat,pc,
     show s.natReg 2822=2 from h.two]
  · simp [step,jump_at,divided,advance,updates,applyBlock,Op.apply,setPC,writeNat,next,pc]
 exact run.trans last

theorem pair_count (k i : ℕ) (hi : i<k) :
 2^i*2^(k-(i+1))=2^(k-1) := by
 rw [←Nat.pow_add]
 congr 1
 omega

theorem round_runs (n B k A i : ℕ) (x : Fin n→ℂ) (s : State)
 (h : Header k A i s) (hi : i<k) (a : 3≤A)
 (v : Fin (2^k)→Scalar) (data : Present A k v s)
 (constants : UniformBinaryCStageMachine.Constants s)
 (bound : WordBound B s) (code : 42≤B) (extent : A+2^k≤B) :
 ∃u,BoundedRuns program n x B s (25*2^(k-1)+11) u ∧
 Header k A (i+1) u ∧ Present A k (axisAction k ⟨i,hi⟩ v) u ∧
 Frame A (2^k) s u ∧ UniformBinaryCStageMachine.Constants u := by
 let entry:=setPC s 0
 have entryBound:WordBound B entry:=changePC_bound B s 0 bound (by omega)
 obtain ⟨u,run,result,frame,con⟩:=axis_execution n B k A x ⟨i,hi⟩ v entry rfl
  h.stride h.dataBase (h.upper.trans (binary_upper k i hi)) a constants data entryBound (by omega) extent
 have moved:=UniformBoundedAssembly.boundedExecution_placed stage_code
  (by rw [UniformBinaryCStageMachine.program_length];omega) (by omega) run
 have entered : placed 7 entry=setPC s 7 := by cases s;rfl
 rw [entered] at moved
 have branch : BoundedRuns program n x B s 1 (setPC s 7) := by
  refine .next bound ?_ (.refl (changePC_bound B s 7 bound (by omega)))
  simp [step,branch_at,h.pc,h.axis,h.bits,hi,setPC]
 let mid:=setPC u 37
 have f : UniformBinaryCStageMachine.Frame A (2^k) s mid :=
  ((UniformBinaryCStageMachine.Frame.pc A (2^k) s 0).trans frame).trans
   (UniformBinaryCStageMachine.Frame.pc A (2^k) u 37)
 have head:=header_transport k A i h f
 have rest:=advance_runs n B k A i x mid head rfl hi moved.final_bound code extent
 have joined:BoundedRuns program n x B s (25*2^(k-1)+11) (advance mid) := by
  have full:=(branch.trans moved).trans rest
  convert full using 1
  dsimp only [Fin.val_mk]
  rw [pair_count k i hi]
  omega
 refine ⟨advance mid,joined,advance_header k A i mid head rfl,?_,
  (Frame.of_stage f).trans (frame_advance A (2^k) mid),con⟩
 intro z
 exact result z

theorem suffix_cons (k i : ℕ) (hi : i<k) :
 (List.finRange k).drop i=(⟨i,hi⟩:Fin k)::(List.finRange k).drop (i+1) := by
 rw [List.drop_eq_getElem_cons (by simpa using hi)]
 simp

theorem loop_execution (n B k A count : ℕ) (x : Fin n→ℂ) :
 ∀i s (v : Fin (2^k)→Scalar),i+count=k→Header k A i s→3≤A→
 Present A k v s→UniformBinaryCStageMachine.Constants s→WordBound B s→42≤B→A+2^k≤B→
 ∃u,BoundedExecution program n x B s (count*(25*2^(k-1)+11)+2) u ∧
 Present A k (applyAxes k ((List.finRange k).drop i) v) u ∧
 Frame A (2^k) s u ∧ UniformBinaryCStageMachine.Constants u ∧ u.pc=41 := by
 induction count with
 | zero =>
  intro i s v eq h a data con bound code extent
  have ik:i=k:=by omega
  let u:=setPC s 41
  have ub:WordBound B u:=changePC_bound B s 41 bound (by omega)
  simp only [Nat.zero_mul,Nat.zero_add]
  refine ⟨u,.next bound (u:=u) ?_ (.halt ub ?_),?_,Frame.pc A (2^k) s 41,con,rfl⟩
  · simp [step,branch_at,h.pc,h.axis,h.bits,ik,u,setPC]
  · simp [step,halt_at,u,setPC]
  · have empty:(List.finRange k).drop k=[]:=by
     calc
      _=(List.finRange k).drop (List.finRange k).length:=by simp
      _=[]:=List.drop_length
    simpa [Present,ik,applyAxes,empty,u,setPC] using data
 | succ count ih =>
  intro i s v eq h a data con bound code extent
  have hi:i<k:=by omega
  obtain ⟨mid,first,head,values,frame,constants⟩:=round_runs n B k A i x s h hi a v data con bound code extent
  obtain ⟨u,last,result,rest,cu,pcu⟩:=ih (i+1) mid (axisAction k ⟨i,hi⟩ v)
   (by omega) head a values constants first.final_bound code extent
  refine ⟨u,?_,?_,frame.trans rest,cu,pcu⟩
  · convert first.executes last using 1
    ring
  · rw [suffix_cons k i hi]
    exact result

/-- One actual fixed program realizes every ordinary binary C tensor base
case, with an exact runtime and full physical frame in the same word bound. -/
theorem execution (n B k A : ℕ) (x : Fin n→ℂ) (s : State)
 (v : Fin (2^k)→Scalar) (pc : s.pc=0) (a : s.natReg 2823=A)
 (size : s.natReg 2824=2^k) (bits : s.natReg 2825=k) (ha : 3≤A)
 (data : Present A k v s) (con : UniformBinaryCStageMachine.Constants s)
 (bound : WordBound B s) (code : 42≤B) (extent : A+2^k≤B) :
 ∃u,BoundedExecution program n x B s (k*(25*2^(k-1)+11)+8) u ∧
 Present A k (applyAxes k (List.finRange k) v) u ∧
 (∀z,(u.scalarHeap (A+z.val)).map Scalar.value=
   some ((physicalMatrix k).mulVec (fun y=>(v y).value) z)) ∧
 Frame A (2^k) s u ∧ UniformBinaryCStageMachine.Constants u ∧ u.pc=41 := by
 have bootRun:=boot_runs n B k A x s pc a size bound code extent
 obtain ⟨u,rest,result,frame,cu,pcu⟩:=loop_execution n B k A k x 0 (bootState s) v
  (by omega) (boot_header k A s pc a size bits) ha data con bootRun.final_bound code extent
 have output:Present A k (applyAxes k (List.finRange k) v) u:=by simpa using result
 refine ⟨u,?_,output,?_,(frame_boot A (2^k) s).trans frame,cu,pcu⟩
 · convert bootRun.executes rest using 1
   omega
 · intro z
   rw [output z]
   simp only [Option.map_some]
   exact congrArg some (congrFun (applyAxes_tensor k v) z)

theorem canonical_execution (n k A : ℕ) (hn : 0<n) (x : Fin n→ℂ) (s : State)
 (v : Fin (2^k)→Scalar) (pc : s.pc=0) (a : s.natReg 2823=A)
 (size : s.natReg 2824=2^k) (bits : s.natReg 2825=k) (ha : 3≤A)
 (data : Present A k v s) (con : UniformBinaryCStageMachine.Constants s)
 (bound : WordBound ((n+2)^19) s) (extent : A+2^k≤(n+2)^19) :
 ∃u,BoundedExecution program n x ((n+2)^19) s (k*(25*2^(k-1)+11)+8) u ∧
 Present A k (applyAxes k (List.finRange k) v) u ∧
 (∀z,(u.scalarHeap (A+z.val)).map Scalar.value=
   some ((physicalMatrix k).mulVec (fun y=>(v y).value) z)) ∧
 Frame A (2^k) s u ∧ UniformBinaryCStageMachine.Constants u ∧ u.pc=41 := by
 have small:42≤3^19:=by norm_num
 exact execution n _ k A x s v pc a size bits ha data con bound
  (small.trans (Nat.pow_le_pow_left (by omega) 19)) extent

end
end ExactFourierCircuits.UniformBinaryTensorCMachine
