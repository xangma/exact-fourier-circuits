import UniformFixedNetworkChildDispatchMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkPaddingChildMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkShearChildMachine (Present roleBase role_bound role_outside)
open UniformBinaryTensorCoordinates (applyAxes)
/-- A real padding range loops through every role. The all-axis helper is one
fixed42 program and every caller/header/return operation is charged. -/
def boot : List Op := [.add 3307 2854 2866,.add 3308 2854 2855]
def setup : List Op := [.mul 2823 3307 3304,.add 2823 3300 2823,
 .add 2824 3304 2866,.add 2825 3302 2866]
def program : Program := boot.map Op.code++[.branchLT 3307 3308 3 51]++setup.map Op.code++
 UniformBinaryTensorCMachine.program.map (relocate 7 49)++
 [.natBinary .add 3307 3307 3305,.jump 2,.halt]
lemma program_length : program.length=52 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma setup_code : BlockAt setup program 3 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma tensor_code : CodeAt UniformBinaryTensorCMachine.program program 7 49 := by intro i hi;change i<42 at hi;interval_cases i <;> rfl
lemma branch_at : program[2]?=some (.branchLT 3307 3308 3 51) := rfl
lemma increment_at : program[49]?=some (.natBinary .add 3307 3307 3305) := rfl
lemma jump_at : program[50]?=some (.jump 2) := rfl
lemma halt_at : program[51]?=some .halt := rfl
noncomputable section
structure Header (k A d count i:ℕ) (s:State) : Prop where
 pc:s.pc=2
 base:s.natReg 3300=A
 bits:s.natReg 3302=k
 volume:s.natReg 3304=2^k
 one:s.natReg 3305=1
 index:s.natReg 3307=d+i
 stop:s.natReg 3308=d+count
 zero:s.natReg 2866=0

def values {R:ℕ} (k d count:ℕ) (f:Fin R→Fin (2^k)→Scalar) : Fin R→Fin (2^k)→Scalar :=
 fun r=>if d≤r.val∧r.val<d+count then applyAxes k (List.finRange k) (f r) else f r
lemma values_zero {R:ℕ} (k d:ℕ) (f:Fin R→Fin (2^k)→Scalar) : values k d 0 f=f := by
 funext r;simp [values,show ¬(d≤r.val∧r.val<d) by omega]
lemma values_current {R:ℕ} (k d i:ℕ) (r:Fin R) (hr:r.val=d+i) (f:Fin R→Fin (2^k)→Scalar) : values k d i f r=f r := by
 simp [values,hr]
lemma values_next_other {R:ℕ} (k d i:ℕ) (r:Fin R) (hr:r.val≠d+i) (f:Fin R→Fin (2^k)→Scalar) :
 values k d (i+1) f r=values k d i f r := by
 have h:(d≤r.val∧r.val<d+(i+1))↔(d≤r.val∧r.val<d+i):=by omega
 simp only [values,h]

def Changed (r:ℕ) : Prop := UniformBinaryTensorCMachine.Changed r∨r=2823∨r=2824∨r=2825∨r=3307∨r=3308
structure Frame (D V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg:∀r,8≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<D∨D+V≤z→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (D V:ℕ) (s:State) : Frame D V s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.pc {D V:ℕ} {s u:State} (f:Frame D V s u) (p:ℕ) : Frame D V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {D V:ℕ} {s u t:State} (f:Frame D V s u) (g:Frame D V u t) : Frame D V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
 fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma Frame.tensor {D V a b:ℕ} {s u:State} (ha:D≤a) (hb:a+b≤D+V)
 (f:UniformBinaryTensorCMachine.Frame a b s u) : Frame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro z hz;apply f.scalarHeap;omega
lemma frame_boot (D V:ℕ) (s:State) : Frame D V s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma frame_setup (D V:ℕ) (s:State) : Frame D V s (applyBlock setup s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
def advance (s:State) : State := setPC (writeNat s 3307 (s.natReg 3307+1)) 2
lemma frame_advance (D V:ℕ) (s:State) : Frame D V s (advance s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [advance,setPC,writeNat,next]
lemma role_bounds (A V d count i:ℕ) (hi:i<count) :
 A+d*V≤A+(d+i)*V ∧ A+(d+i)*V+V≤A+d*V+count*V := by
 have h:=Nat.mul_le_mul_right V (show i+1≤count by omega)
 simp only [Nat.add_mul,Nat.one_mul] at h
 simp only [Nat.add_mul];omega
lemma setup_header (k A d count i:ℕ) (s:State) (h:Header k A d count i s) :
 (applyBlock setup (setPC s 3)).natReg 2823=roleBase A (2^k) (d+i) ∧
 (applyBlock setup (setPC s 3)).natReg 2824=2^k ∧
 (applyBlock setup (setPC s 3)).natReg 2825=k ∧
 (applyBlock setup (setPC s 3)).pc=7 := by
 rcases h with ⟨pc,base,bits,volume,one,index,stop,zero⟩
 simp [setup,applyBlock,Op.apply,setPC,writeNat,next,base,bits,volume,index,zero,roleBase]
lemma setup_safe (k A d count i B:ℕ) (s:State) (h:Header k A d count i s)
 (endpoint:roleBase A (2^k) (d+i)≤B) (vol:2^k≤B) (bits:k≤B) :
 readable setup (setPC s 3) ∧ peak setup (setPC s 3)≤B := by
 rcases h with ⟨pc,base,hbits,volume,one,index,stop,zero⟩
 unfold roleBase at endpoint
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,setPC,writeNat,next,base,hbits,volume,index,zero]
 omega

/-- The physical tensor helper's stored output advances the whole role-bank
invariant; the other role blocks remain unchanged. -/
lemma present_next {R:ℕ} (k A d i:ℕ) (r:Fin R) (hr:r.val=d+i)
 (f:Fin R→Fin (2^k)→Scalar) (s u:State)
 (before:Present A R (2^k) (values k d i f) s)
 (after:UniformBinaryTensorCMachine.Present (roleBase A (2^k) r.val) k
   (applyAxes k (List.finRange k) (f r)) u)
 (frame:UniformBinaryTensorCMachine.Frame (roleBase A (2^k) r.val) (2^k) s u) :
 Present A R (2^k) (values k d (i+1) f) u := by
 intro t j
 by_cases eq:t=r
 · subst t
   simpa [roleBase,values,hr] using after j
 · rw [frame.scalarHeap _ (role_outside A r t eq j)]
   rw [values_next_other k d i t (by intro h;apply eq;apply Fin.ext;omega) f]
   exact before t j

lemma round_execution {R:ℕ} (k A d count i n B:ℕ) (x:Fin n→ℂ)
 (f:Fin R→Fin (2^k)→Scalar) (s:State) (hi:i<count) (capacity:d+count≤R) (ha:3≤A)
 (h:Header k A d count i s) (data:Present A R (2^k) (values k d i f) s)
 (con:UniformBinaryCStageMachine.Constants s) (hs:WordBound B s) (code:52≤B)
 (extent:A+R*2^k≤B) : ∃u,
 BoundedRuns program n x B s (k*(25*2^(k-1)+11)+15) u ∧ Header k A d count (i+1) u ∧
 Present A R (2^k) (values k d (i+1) f) u ∧ Frame (A+d*2^k) (count*2^k) s u ∧
 UniformBinaryCStageMachine.Constants u := by
 let r:Fin R:=⟨d+i,by omega⟩
 let entry:=setPC s 3
 have be:=changePC_bound B s 3 hs (by omega)
 have first:BoundedRuns program n x B s 1 entry:=.next hs
   (by simp [step,h.pc,branch_at,h.index,h.stop,show d+i<d+count by omega,entry,setPC]) (.refl be)
 have endbound:roleBase A (2^k) r.val+2^k≤B:=(role_bound A (2^k) r).trans extent
 have vol:2^k≤B:=by have h:=h.volume;rw [←h];exact hs.2.1 3304
 have bits:k≤B:=(show k<2^k from Nat.lt_two_pow_self).le.trans vol
 have endpoint:roleBase A (2^k) r.val≤B := (Nat.le_add_right _ _).trans endbound
 have safe:=setup_safe k A d count i B s h (by simpa [r] using endpoint) vol bits
 have caller:=block_runs setup program 3 n B x entry setup_code rfl be (by change 7≤B;omega) safe.1 safe.2
 let ready:=applyBlock setup entry
 let ce:=setPC ready 0
 have cb:=changePC_bound B ready 0 caller.final_bound (by omega)
 obtain ⟨ab,sz,bt,cp⟩:=setup_header k A d count i s h
 have current:UniformBinaryTensorCMachine.Present (roleBase A (2^k) r.val) k (f r) ce:=by
   intro j;change s.scalarHeap (A+r.val*2^k+j.val)=_
   rw [data r j,values_current k d i r rfl f]
 have constants:UniformBinaryCStageMachine.Constants ce:=con
 obtain ⟨child,run,result,numeric,cf,cc,childpc⟩:=UniformBinaryTensorCMachine.execution n B k
   (roleBase A (2^k) r.val) x ce (f r) rfl ab sz bt (by unfold roleBase;omega) current constants cb (by omega) endbound
 have placed:=UniformBoundedAssembly.boundedExecution_placed tensor_code (by change 49≤B;omega) (by omega) run
 have actual:UniformAssembly.placed 7 ce=ready:=by simp [UniformAssembly.placed,ce,ready,entry,setup,applyBlock,Op.apply,setPC,writeNat,next]
 rw [actual] at placed
 let ret:=setPC child 49
 have keep:∀j,3300≤j→ ret.natReg j=s.natReg j:=by
   intro j hj
   change child.natReg j=s.natReg j
   rw [cf.natReg j (by unfold UniformBinaryTensorCMachine.Changed;omega)]
   change (applyBlock setup entry).natReg j=s.natReg j
   simp (disch:=omega) [setup,applyBlock,Op.apply,entry,setPC,writeNat,next]
 have index:ret.natReg 3307=d+i:=(keep _ (by decide)).trans h.index
 have one:ret.natReg 3305=1:=(keep _ (by decide)).trans h.one
 have rb:WordBound B (writeNat ret 3307 (ret.natReg 3307+1)):=writeNat_bound B _ _ _ placed.final_bound
   (by change 50≤B;omega) (by have hb:=hs.2.1 3308;rw [h.stop] at hb;rw [index];omega)
 have ub:=changePC_bound B _ 2 rb (by omega)
 let u:=advance ret
 have inc:step program n x ret=.running (writeNat ret 3307 (ret.natReg 3307+1)):=by
   simp only [step,show ret.pc=49 from rfl,increment_at,evalNat]
   rw [one]
 have jump:step program n x (writeNat ret 3307 (ret.natReg 3307+1))=.running u:=by
   simp [step,ret,setPC,writeNat,next,jump_at,u,advance]
 have tail:BoundedRuns program n x B ret 2 u:=.next placed.final_bound inc (.next rb jump (.refl ub))
 have all:=first.trans (caller.trans (placed.trans tail))
 have lh:=role_bounds A (2^k) d count i hi
 have full:Frame (A+d*2^k) (count*2^k) s u:=
   ((Frame.refl _ _ s).pc 3 |>.trans (frame_setup _ _ entry) |>.pc 0)
   |>.trans (Frame.tensor (by simp [r,roleBase,Nat.add_mul]) (by simpa [r,roleBase] using lh.2) cf)
   |>.pc 49 |>.trans (frame_advance _ _ ret)
 have dh:Header k A d count (i+1) u:=by
   constructor
   · rfl
   · change ret.natReg 3300=A;rw [keep _ (by decide)];exact h.base
   · change ret.natReg 3302=k;rw [keep _ (by decide)];exact h.bits
   · change ret.natReg 3304=2^k;rw [keep _ (by decide)];exact h.volume
   · change ret.natReg 3305=1;exact one
   · simp [u,advance,setPC,writeNat,next,index];omega
   · change ret.natReg 3308=d+count;rw [keep _ (by decide)];exact h.stop
   · change child.natReg 2866=0
     rw [cf.natReg _ (by unfold UniformBinaryTensorCMachine.Changed;omega)]
     exact h.zero
 refine ⟨u,?_,dh,?_,full,cc⟩
 · convert all using 1;change k*(25*2^(k-1)+11)+15=1+(4+((k*(25*2^(k-1)+11)+8)+2));omega
 · have inputs:Present A R (2^k) (values k d i f) ce:=data
   have updated:=present_next k A d i r rfl f ce child inputs result cf
   exact updated

lemma loop_execution {R:ℕ} (k A d count remaining n B:ℕ) (x:Fin n→ℂ)
 (f:Fin R→Fin (2^k)→Scalar) (capacity:d+count≤R) (ha:3≤A) (code:52≤B)
 (extent:A+R*2^k≤B) : ∀i s,i+remaining=count→Header k A d count i s→
 Present A R (2^k) (values k d i f) s→UniformBinaryCStageMachine.Constants s→WordBound B s→∃u,
 BoundedExecution program n x B s (remaining*(k*(25*2^(k-1)+11)+15)+2) u ∧
 Present A R (2^k) (values k d count f) u ∧ Frame (A+d*2^k) (count*2^k) s u ∧
 UniformBinaryCStageMachine.Constants u := by
 induction remaining with
 | zero=>
   intro i s eq h data con hs
   have ic:i=count:=by omega
   subst i
   simp only [Nat.zero_mul,Nat.zero_add]
   let u:=setPC s 51
   have ub:=changePC_bound B s 51 hs (by omega)
   refine ⟨u,.next hs ?_ (.halt ub ?_),data,(Frame.refl _ _ s).pc 51,con⟩
   · simp [step,h.pc,branch_at,h.index,h.stop,u,setPC]
   · simp [step,u,setPC,halt_at]
 | succ remaining ih=>
   intro i s eq h data con hs
   obtain ⟨mid,round,head,out,frame,constants⟩:=round_execution k A d count i n B x f s
     (by omega) capacity ha h data con hs code extent
   obtain ⟨u,last,output,rest,cu⟩:=ih (i+1) mid (by omega) head out constants round.final_bound
   refine ⟨u,?_,output,frame.trans rest,cu⟩
   convert round.executes last using 1;ring

/-- Real role-range child with no supplied per-role action or ready42 headers. -/
theorem execution {R:ℕ} (k A d count n B:ℕ) (x:Fin n→ℂ) (f:Fin R→Fin (2^k)→Scalar) (s:State)
 (pc:s.pc=0) (base:s.natReg 3300=A) (bits:s.natReg 3302=k) (vol:s.natReg 3304=2^k)
 (one:s.natReg 3305=1) (zero:s.natReg 2866=0) (dst:s.natReg 2854=d) (sz:s.natReg 2855=count)
 (capacity:d+count≤R) (ha:3≤A) (data:Present A R (2^k) f s)
 (con:UniformBinaryCStageMachine.Constants s) (hs:WordBound B s) (code:52≤B)
 (extent:A+R*2^k≤B) : ∃u,
 BoundedExecution program n x B s (count*(k*(25*2^(k-1)+11)+15)+4) u ∧
 Present A R (2^k) (values k d count f) u ∧ Frame (A+d*2^k) (count*2^k) s u ∧
 UniformBinaryCStageMachine.Constants u := by
 have rp:R≤R*2^k:=by simpa using Nat.mul_le_mul_left R (show 1≤(2:ℕ)^k from Nat.one_le_two_pow)
 have safe:readable boot s ∧ peak boot s≤B:=by
   simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,dst,sz,zero];omega
 have run:=block_runs boot program 0 n B x s boot_code pc hs (by change 2≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have h:Header k A d count 0 ready:=by
   constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc,base,bits,vol,one,zero,dst,sz]
 have pd:Present A R (2^k) (values k d 0 f) ready:=by rw [values_zero];exact data
 obtain ⟨u,last,out,frame,cu⟩:=loop_execution k A d count count n B x f capacity ha code extent
   0 ready (by omega) h pd con run.final_bound
 refine ⟨u,?_,out,(frame_boot _ _ s).trans frame,cu⟩
 convert run.executes last using 1
 change count*(k*(25*2^(k-1)+11)+15)+4=2+(count*(k*(25*2^(k-1)+11)+15)+2);omega


open UniformFixedNetworkScheduleMachine (Record Printed)
open UniformFixedNetworkChildDispatchMachine (volumeProgram VolumeFrame volume_execution)
def record (q w d count:ℕ) : Record := ⟨5,q,w,d,count,0,0,0,[]⟩
lemma record_good (q w d count:ℕ) : UniformFixedNetworkOpcodeMachine.WellFormed (record q w d count) := by
 norm_num [record,UniformFixedNetworkOpcodeMachine.WellFormed,UniformFixedNetworkOpcodeMachine.bodyLength]
lemma record_length (q w d count:ℕ) : (record q w d count).data.length=8 := rfl

def returnOps : List Op := [.add 2850 2865 2866]
def dispatchProgram : Program := UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++
 volumeProgram.map (relocate 52 62)++program.map (relocate 62 114)++returnOps.map Op.code++[.halt]
lemma dispatchProgram_length : dispatchProgram.length=116 := rfl
lemma reader_code : CodeAt UniformFixedNetworkOpcodeMachine.headProgram dispatchProgram 0 52 := by
 intro i hi;change i<52 at hi;interval_cases i <;> rfl
lemma volume_code : CodeAt volumeProgram dispatchProgram 52 62 := by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma child_code : CodeAt program dispatchProgram 62 114 := by
 intro i hi;change i<52 at hi;interval_cases i <;> rfl
lemma return_code : BlockAt returnOps dispatchProgram 114 := by
 intro i hi;change i<1 at hi;interval_cases i;rfl
lemma dispatch_halt : dispatchProgram[115]?=some .halt := rfl

def FullChanged (r:ℕ) : Prop := Changed r∨(2850≤r∧r<2877)∨(3302≤r∧r<3307)
structure FullFrame (D V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬FullChanged r→u.natReg r=s.natReg r
 scalarReg:∀r,8≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<D∨D+V≤z→u.scalarHeap z=s.scalarHeap z
lemma FullFrame.trans {D V:ℕ} {s u t:State} (f:FullFrame D V s u) (g:FullFrame D V u t) : FullFrame D V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
 fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma FullFrame.pc {D V:ℕ} {s u:State} (f:FullFrame D V s u) (p:ℕ) : FullFrame D V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma FullFrame.reader (D V:ℕ) {s u:State} (f:UniformFixedNetworkOpcodeMachine.Frame s u) : FullFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun _ _=>congrFun f.scalarReg _,fun _ _=>congrFun f.scalarHeap _⟩
 intro r h;apply f.natReg;unfold FullChanged at h;omega
lemma FullFrame.volume (D V:ℕ) {s u:State} (f:VolumeFrame s u) : FullFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,fun _ _=>congrFun f.scalarReg _,fun _ _=>congrFun f.scalarHeap _⟩
 intro r h;apply f.natReg;unfold FullChanged at h;omega
lemma FullFrame.child {D V:ℕ} {s u:State} (f:Frame D V s u) : FullFrame D V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg,f.scalarHeap⟩
 intro r h;apply f.natReg;unfold FullChanged at h;tauto
lemma return_frame (D V:ℕ) (s:State) : FullFrame D V s (applyBlock returnOps s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold FullChanged at h;simp (disch:=omega) [returnOps,applyBlock,Op.apply,writeNat,next]

/-- Continuous actual opcode5 record → charged width computation → every
padding-role tensor → cursor return. No Fields, precomputed width or tensor
results are supplied. Constants are the earlier physical C-constant bank. -/
theorem dispatch_execution {R:ℕ} (q w A T d count B n:ℕ) (x:Fin n→ℂ)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (pc:s.pc=0) (ptr:s.natReg 2850=T) (base:s.natReg 3300=A)
 (bank:Printed T (record q w d count).data s) (data:Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (capacity:d+count≤R) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:116≤B) (tableEnd:T+8≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedExecution dispatchProgram n x B s
   (count*((q*w)*(25*2^(q*w-1)+11)+15)+4*(q*w)+50) u ∧
 Present A R (2^(q*w)) (values (q*w) d count f) u ∧ u.natReg 2850=T+8 ∧
 FullFrame (A+d*2^(q*w)) (count*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 let k:=q*w
 let V:=2^k
 let D:=A+d*V
 have vb:V≤B:=by
   have h:=Nat.mul_le_mul_right V (show 1≤R by omega)
   simp only [Nat.one_mul] at h;change A+R*V≤B at extent;omega
 obtain ⟨read,rr,fields,body,nextptr,rf⟩:=UniformFixedNetworkOpcodeMachine.head_execution T B n
   (record q w d count) x s ptr pc hs bank (record_good q w d count)
   (by simpa [record_length] using tableEnd) width (by omega)
 have reader:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 52≤B;omega) (by omega) rr
 rw [UniformFixedNetworkLiteralDecoderMachine.placed_zero] at reader
 let ve:=setPC read 0
 have vbe:=changePC_bound B read 0 rr.final_bound (by omega)
 obtain ⟨vol,vr,bits,volume,vf,one⟩:=volume_execution q w B n x ve rfl
   (by simpa [ve,setPC,record] using fields.columns) (by simpa [ve,setPC,record] using fields.width) vbe vb (by omega)
 have vrun:=UniformBoundedAssembly.boundedExecution_placed volume_code (by change 62≤B;omega) (by omega) vr
 have ventry:placed 52 ve=setPC read 52:=rfl
 rw [ventry] at vrun
 let ce:=setPC vol 0
 have cb:=changePC_bound B vol 0 vr.final_bound (by omega)
 have ca:ce.natReg 3300=A:=by
   change vol.natReg 3300=A;rw [vf.natReg _ (by omega)]
   change read.natReg 3300=A;rw [rf.natReg _ (by omega)];exact base
 have cz:ce.natReg 2866=0:=by
   change vol.natReg 2866=0;rw [vf.natReg _ (by omega)]
   exact fields.zero
 have cd:ce.natReg 2854=d:=by
   change vol.natReg 2854=d;rw [vf.natReg _ (by omega)]
   simpa [ve,setPC,record] using fields.dest
 have cs:ce.natReg 2855=count:=by
   change vol.natReg 2855=count;rw [vf.natReg _ (by omega)]
   simpa [ve,setPC,record] using fields.source
 have pd:Present A R V f ce:=by
   intro r j;change vol.scalarHeap (A+r.val*V+j.val)=_
   rw [vf.scalarHeap];change read.scalarHeap (A+r.val*V+j.val)=_
   rw [rf.scalarHeap];exact data r j
 have constants:UniformBinaryCStageMachine.Constants ce:=by
   change vol.scalarHeap 1=_ ∧ vol.scalarHeap 2=_
   rw [vf.scalarHeap];change read.scalarHeap 1=_ ∧ read.scalarHeap 2=_
   rw [rf.scalarHeap];exact con
 obtain ⟨child,cr,output,cf,cc⟩:=execution k A d count n B x f ce rfl ca bits volume one cz cd cs capacity ha pd constants cb (by omega) extent
 have childrun:=UniformBoundedAssembly.boundedExecution_placed child_code (by change 114≤B;omega) (by omega) cr
 have actual:placed 62 ce=setPC vol 62:=rfl
 rw [actual] at childrun
 let ret:=setPC child 114
 have rn:ret.natReg 2865=T+8:=by
   change child.natReg 2865=T+8
   rw [cf.natReg 2865 (by norm_num [Changed,UniformBinaryTensorCMachine.Changed])]
   change vol.natReg 2865=T+8;rw [vf.natReg _ (by omega)]
   simpa [ve,setPC,record_length] using nextptr
 have rz:ret.natReg 2866=0:=by
   change child.natReg 2866=0
   rw [cf.natReg 2866 (by norm_num [Changed,UniformBinaryTensorCMachine.Changed])]
   exact cz
 have safe:readable returnOps ret ∧ peak returnOps ret≤B:=by
   simp [returnOps,readable,peak,Op.readable,Op.peak,rn,rz];omega
 have back:=block_runs returnOps dispatchProgram 114 n B x ret return_code rfl childrun.final_bound
   (by change 115≤B;omega) safe.1 safe.2
 let u:=applyBlock returnOps ret
 have up:u.pc=115:=rfl
 have last:BoundedExecution dispatchProgram n x B u 1 u:=.halt back.final_bound (by simp [step,up,dispatch_halt])
 have frame:FullFrame D (count*V) s u:=
   ((FullFrame.reader _ _ rf).pc 0 |>.trans (FullFrame.volume _ _ vf) |>.pc 0)
   |>.trans (FullFrame.child cf) |>.pc 114 |>.trans (return_frame _ _ ret)
 refine ⟨u,?_,output,?_,frame,cc⟩
 · have all:=reader.executes (vrun.executes (childrun.executes (back.executes last)))
   convert all using 1
   norm_num [UniformFixedNetworkOpcodeMachine.headCost,record,returnOps,k]
   omega
 · simp [u,returnOps,applyBlock,Op.apply,writeNat,next,rn,rz]

end
end ExactFourierCircuits.UniformFixedNetworkPaddingChildMachine
