import UniformRootExtractionMachine
import UniformGlobalLocalPreparation
import UniformMasterRootSeedDAG

set_option autoImplicit false

/-! Literal sizing and dyadic-root production from the existing master heap0.
No root request, count oracle, or complex test appears in the bytecode. -/
namespace ExactFourierCircuits.UniformDyadicRootBankMachine
open UniformMachine UniformAssembly OAI.ExactFourier
open UniformReciprocalMachine (Op applyBlock BlockAt block_runs peak readable)
noncomputable section

/-- Nat160=N,161=destination base; private loop workspace162..167. -/
def boot : List Op := [.literal 162 1,.literal 163 2,.literal 164 3,.literal 165 0,.literal 166 1]
def sizeBody : List Op := [.mul 166 166 163,.add 165 165 162]
def ready : List Op := [.add 165 165 164,.literal 167 0,.literal 141 1]
def destination : List Op := [.add 140 161 167]
def advance : List Op := [.mul 141 141 163,.add 167 167 162]
def head : Program := boot.map Op.code ++ [.branchLT 166 160 6 9] ++ sizeBody.map Op.code ++
  [.jump 5] ++ ready.map Op.code ++ [.branchLT 167 165 13 34] ++ destination.map Op.code
def suffix : Program := advance.map Op.code ++ [.jump 12,.halt]
def program : Program := embed head UniformRootExtractionMachine.program suffix 31

theorem head_length : head.length=14 := rfl
theorem program_length : program.length=35 := rfl
theorem extraction_code : CodeAt UniformRootExtractionMachine.program program 14 31 :=
  embed_code head _ suffix 31

theorem boot_at : BlockAt boot program 0 := by
  intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem size_at : BlockAt sizeBody program 6 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem ready_at : BlockAt ready program 9 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem destination_at : BlockAt destination program 13 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl
theorem advance_at : BlockAt advance program 31 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem size_branch : program[5]?=some (.branchLT 166 160 6 9) := rfl
theorem size_jump : program[8]?=some (.jump 5) := rfl
theorem bank_branch : program[12]?=some (.branchLT 167 165 13 34) := rfl
theorem bank_jump : program[33]?=some (.jump 12) := rfl
theorem halt_at : program[34]?=some .halt := rfl

def count (N : ℕ) : ℕ := Nat.clog 2 N+3

def Persistent (r : ℕ) : Prop := 5≤r ∧ r≠140 ∧ r≠141 ∧ r≠146 ∧ (r<162 ∨ 168≤r)

instance persistentDecidable (r : ℕ) : Decidable (Persistent r) := by unfold Persistent;infer_instance

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,r ≠ 0 → r ≠ 1 →u.scalarReg r=s.scalarReg r) ∧
  ∀r,Persistent r→u.natReg r=s.natReg r

def PureFrame (s u : State) : Prop := Frame s u ∧ u.scalarHeap=s.scalarHeap

theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ _=>rfl,fun _ _=>rfl⟩
theorem pureFrame_refl (s : State) : PureFrame s s := ⟨frame_refl s,rfl⟩
theorem Frame.trans {s u v : State} (h:Frame s u) (g:Frame u v) : Frame s v :=
  ⟨g.1.trans h.1,g.2.1.trans h.2.1,g.2.2.1.trans h.2.2.1,
    fun r h0 h1=>(g.2.2.2.1 r h0 h1).trans (h.2.2.2.1 r h0 h1),
    fun r hr=>(g.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
theorem PureFrame.trans {s u v : State} (h:PureFrame s u) (g:PureFrame u v) : PureFrame s v :=
  ⟨h.1.trans g.1,g.2.trans h.2⟩
theorem frame_pc (s : State) (p : ℕ) : PureFrame s {s with pc:=p} := by
  exact ⟨⟨rfl,rfl,rfl,fun _ _ _=>rfl,fun _ _=>rfl⟩,rfl⟩

theorem block_frames (s : State) : PureFrame s (applyBlock boot s) ∧
    PureFrame s (applyBlock sizeBody s) ∧ PureFrame s (applyBlock ready s) ∧
    PureFrame s (applyBlock destination s) ∧ PureFrame s (applyBlock advance s) := by
  unfold PureFrame Frame
  repeat' constructor
  all_goals first
    | (intro r h0 h1;rfl)
    | (intro r hr;unfold Persistent at hr;simp (disch:=omega)
        [applyBlock,boot,sizeBody,ready,destination,advance,Op.apply,writeNat,next])

structure Sizing (N e : ℕ) (s : State) : Prop where
  pc : s.pc=5
  input : s.natReg 160=N
  exponent : s.natReg 165=e
  power : s.natReg 166=2^e
  one : s.natReg 162=1
  two : s.natReg 163=2
  three : s.natReg 164=3

def initialized (s : State) : State := applyBlock boot s
def sizeRound (s : State) : State := {applyBlock sizeBody {s with pc:=6} with pc:=5}

theorem initializes (n N B : ℕ) (x : Fin n→ℂ) (s : State) (hp:s.pc=0) (hN:s.natReg 160=N)
    (hcode:35≤B) (hb:WordBound B s) :
    BoundedRuns program n x B s 5 (initialized s) ∧ Sizing N 0 (initialized s) ∧ PureFrame s (initialized s) := by
  have he := block_runs boot program 0 n B x s boot_at hp hb (by change 5≤B;omega)
    (by trivial) (by simp [peak,boot,Op.peak];omega)
  refine ⟨he,?_,(block_frames s).1⟩
  constructor <;> simp [initialized,applyBlock,boot,Op.apply,writeNat,next,hp,hN]

theorem sizing_round (N e : ℕ) (s : State) (hs:Sizing N e s) :
    Sizing N (e+1) (sizeRound s) ∧ PureFrame s (sizeRound s) := by
  refine ⟨?_,(frame_pc s 6).trans ((block_frames {s with pc:=6}).2.1.trans (frame_pc _ 5))⟩
  rcases hs with ⟨hp,hN,he,hpwr,h1,h2,h3⟩
  constructor <;> simp [sizeRound,applyBlock,sizeBody,Op.apply,writeNat,next,hN,he,hpwr,h1,h2,h3,pow_succ]

theorem size_round_execution (n N e B : ℕ) (x : Fin n→ℂ) (s : State)
    (hs:Sizing N e s) (he:e<Nat.clog 2 N) (hcode:35≤B)
    (hpower:2^(count N)≤B) (hb:WordBound B s) :
    BoundedRuns program n x B s 4 (sizeRound s) := by
  have hgo : s.natReg 166<s.natReg 160 := by rw [hs.power,hs.input];exact Nat.pow_lt_of_lt_clog he
  have hpc := changePC_bound B s 6 hb (by omega)
  have hbound : 2^(e+1)≤B :=
    (Nat.pow_le_pow_right (by decide : 1≤2) (by unfold count;omega)).trans hpower
  have he' : e+1≤B := (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1<2))).trans hbound
  have hr:=block_runs sizeBody program 6 n B x {s with pc:=6} size_at rfl hpc
    (by change 8≤B;omega) (by trivial) (by
      simp [peak,sizeBody,Op.peak,Op.apply,writeNat,next,hs.power,hs.one,hs.two]
      constructor
      · simpa [pow_succ] using hbound
      · simpa [hs.exponent] using he')
  have hj:step program n x (applyBlock sizeBody {s with pc:=6})=.running (sizeRound s) := by
    have hp:(applyBlock sizeBody {s with pc:=6}).pc=8:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
    simp only [step,hp,size_jump];rfl
  exact .next hb (by simp [step,hs.pc,size_branch,hgo])
    (hr.trans (.next hr.final_bound hj (.refl (changePC_bound B _ 5 hr.final_bound (by omega)))))

/-- The proof fuel is not a bytecode register or an execution assumption. -/
theorem sizing_execution (n N e fuel B : ℕ) (x : Fin n→ℂ) (s : State)
    (hs:Sizing N e s) (he:e≤Nat.clog 2 N) (hf:Nat.clog 2 N-e+1≤fuel)
    (hcode:35≤B) (hpower:2^(count N)≤B) (hb:WordBound B s) : ∃u,
    BoundedRuns program n x B s (4*(Nat.clog 2 N-e)+1) u ∧
    u.pc=9 ∧ u.natReg 165=Nat.clog 2 N ∧ u.natReg 160=N ∧
    u.natReg 162=1 ∧ u.natReg 163=2 ∧ u.natReg 164=3 ∧ PureFrame s u := by
  induction fuel generalizing e s with
  | zero => omega
  | succ fuel ih =>
    by_cases hend:e=Nat.clog 2 N
    · let u:State:={s with pc:=9}
      have hstop : ¬s.natReg 166<s.natReg 160 := by
        rw [hs.power,hs.input,hend];exact Nat.not_lt.mpr (Nat.le_pow_clog (by decide) N)
      refine ⟨u,?_,rfl,hs.exponent.trans hend,hs.input,hs.one,hs.two,hs.three,frame_pc s 9⟩
      rw [hend,Nat.sub_self]
      exact .next hb (by simp [step,hs.pc,size_branch,hstop,u])
        (.refl (changePC_bound B s 9 hb (by omega)))
    · have hlt:e<Nat.clog 2 N:=by omega
      have hr:=size_round_execution n N e B x s hs hlt hcode hpower hb
      obtain ⟨u,hu,hpc,hk,hN,h1,h2,h3,hframe⟩:=ih (e+1) (sizeRound s)
        (sizing_round N e s hs).1 (by omega) (by omega) hr.final_bound
      refine ⟨u,?_,hpc,hk,hN,h1,h2,h3,(sizing_round N e s hs).2.trans hframe⟩
      convert hr.trans hu using 1;omega


structure Constants (N A D : ℕ) (s : State) : Prop where
  input : s.natReg 160=N
  base : s.natReg 161=A
  master : s.natReg 104=D
  size : s.natReg 165=count N
  one : s.natReg 162=1
  two : s.natReg 163=2

structure Loop (N A D j : ℕ) (s : State) : Prop where
  constants : Constants N A D s
  pc : s.pc=12
  index : s.natReg 167=j
  order : s.natReg 141=2^j

def Partial (A j : ℕ) (s : State) : Prop :=
  ∀i,i<j→s.scalarHeap (A+i)=some ⟨zeta (2^i),false⟩

/-- The ready block computes count and initial order rather than accepting them. -/
theorem ready_execution (n N A D B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=9) (hN:s.natReg 160=N) (hA:s.natReg 161=A) (hD:s.natReg 104=D)
    (hk:s.natReg 165=Nat.clog 2 N) (h1:s.natReg 162=1) (h2:s.natReg 163=2) (h3:s.natReg 164=3)
    (hcode:35≤B) (hpower:2^(count N)≤B) (hb:WordBound B s) :
    BoundedRuns program n x B s 3 (applyBlock ready s) ∧ Loop N A D 0 (applyBlock ready s) ∧
    PureFrame s (applyBlock ready s) := by
  have hc : count N≤B := (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1<2))).trans hpower
  unfold count at hc
  have hr:=block_runs ready program 9 n B x s ready_at hp hb (by change 12≤B;omega)
    (by trivial) (by simp [peak,ready,Op.peak,hk,h3];omega)
  refine ⟨hr,?_,(block_frames s).2.2.1⟩
  constructor
  · constructor <;> simp [applyBlock,ready,Op.apply,writeNat,next,hN,hA,hD,hk,h1,h2,h3,count]
  · rw [UniformReciprocalMachine.applyBlock_pc,hp];rfl
  · simp [applyBlock,ready,Op.apply,writeNat,next]
  · simp [applyBlock,ready,Op.apply,writeNat,next]

theorem root_frame {s u : State} (hf:UniformRootExtractionMachine.Frame s u) : Frame s u :=
  ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,fun r hr=>hf.2.2.2.2 r hr.1 hr.2.2.2.1⟩

/-- One literal bank iteration: branch,address,extraction,advance,jump. -/
theorem bank_round (n N A D j B : ℕ) (x : Fin n→ℂ) (s : State)
    (hs:Loop N A D j s) (hj:j<count N) (hD:0<D) (hdiv:2^j∣D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hcode:35≤B)
    (hpower:2^(count N)≤B) (hspace:A+count N≤B) (hb:WordBound B s) : ∃u,
    BoundedRuns program n x B s (14+UniformPowerMachine.loopCost (D/2^j)) u ∧
    Loop N A D (j+1) u ∧ u.scalarHeap (A+j)=some ⟨zeta (2^j),false⟩ ∧
    (∀b,b≠A+j→u.scalarHeap b=s.scalarHeap b) ∧ Frame s u := by
  have h13:=changePC_bound B s 13 hb (by omega)
  have hdest:=block_runs destination program 13 n B x {s with pc:=13} destination_at rfl h13
    (by change 14≤B;omega) (by trivial) (by simp [peak,destination,Op.peak,hs.constants.base,hs.index];omega)
  let e:State:={applyBlock destination {s with pc:=13} with pc:=0}
  have he:WordBound B e:=changePC_bound B _ 0 hdest.final_bound (by omega)
  have h104:e.natReg 104=D:=by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.constants.master]
  have h141:e.natReg 141=2^j:=by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.order]
  have h140:e.natReg 140=A+j:=by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.constants.base,hs.index]
  obtain ⟨v,hv,hvalue,houtside,hframe,hpc⟩:=UniformRootExtractionMachine.execution n D (2^j) (A+j) B x e
    rfl h104 h141 h140 hD (by positivity) hdiv hroot (by omega) he
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed extraction_code
    (by rw [UniformRootExtractionMachine.program_length];omega) (by omega) hv
  have hentry:placed 14 e=applyBlock destination {s with pc:=13}:=rfl
  rw [hentry] at hplaced
  let w:State:={v with pc:=31}
  have h162:w.natReg 162=1 := (hframe.2.2.2.2 162 (by decide) (by decide)).trans
    (by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.constants.one])
  have h163:w.natReg 163=2 := (hframe.2.2.2.2 163 (by decide) (by decide)).trans
    (by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.constants.two])
  have h167:w.natReg 167=j := (hframe.2.2.2.2 167 (by decide) (by decide)).trans
    (by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.index])
  have h141':w.natReg 141=2^j := (hframe.2.2.2.2 141 (by decide) (by decide)).trans h141
  have hnext : 2^(j+1)≤B := (Nat.pow_le_pow_right (by decide : 1≤2) (by omega)).trans hpower
  have hindex : j+1≤B := by
    have hc : count N≤B := (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1<2))).trans hpower
    omega
  have ht:=block_runs advance program 31 n B x w advance_at rfl hplaced.final_bound
    (by change 33≤B;omega) (by trivial) (by
      simp [peak,advance,Op.peak,Op.apply,writeNat,next,h162,h163,h167,h141']
      constructor
      · simpa [pow_succ] using hnext
      · exact hindex)
  let u:State:={applyBlock advance w with pc:=12}
  have hu:WordBound B u:=changePC_bound B _ 12 ht.final_bound (by omega)
  have hjump:step program n x (applyBlock advance w)=.running u:=by
    have hc:(applyBlock advance w).pc=33:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
    simp only [step,hc,bank_jump];rfl
  have hfpre:PureFrame s e:=(frame_pc s 13).trans ((block_frames {s with pc:=13}).2.2.2.1.trans (frame_pc _ 0))
  have hfpost:PureFrame w u:=(block_frames w).2.2.2.2.trans (frame_pc _ 12)
  have hf:Frame s u:=hfpre.1.trans ((root_frame hframe).trans ((frame_pc v 31).1.trans hfpost.1))
  have hconst:Constants N A D u:=by
    constructor
    · exact hf.2.2.2.2 160 (by decide) |>.trans hs.constants.input
    · exact hf.2.2.2.2 161 (by decide) |>.trans hs.constants.base
    · exact hf.2.2.2.2 104 (by decide) |>.trans hs.constants.master
    · have h165:w.natReg 165=count N := (hframe.2.2.2.2 165 (by decide) (by decide)).trans
        (by simp [e,applyBlock,destination,Op.apply,writeNat,next,hs.constants.size])
      simpa [u,applyBlock,advance,Op.apply,writeNat,next] using h165
    · simpa [u,applyBlock,advance,Op.apply,writeNat,next] using h162
    · simpa [u,applyBlock,advance,Op.apply,writeNat,next] using h163
  refine ⟨u,?_,?_,?_,?_,hf⟩
  · have hstart:BoundedRuns program n x B s 1 {s with pc:=13}:=
      .next hb (by simp [step,hs.pc,bank_branch,hs.index,hs.constants.size,hj]) (.refl h13)
    have hall:=(hstart.trans hdest).trans (hplaced.trans (ht.trans (.next ht.final_bound hjump (.refl hu))))
    simp only [show destination.length=1 from rfl,show advance.length=2 from rfl] at hall
    convert hall using 1;omega
  · refine ⟨hconst,rfl,?_,?_⟩
    · simp [u,applyBlock,advance,Op.apply,writeNat,next,h167,h162]
    · simp [u,applyBlock,advance,Op.apply,writeNat,next,h141',h163,pow_succ]
  · exact hfpost.2 ▸ hvalue
  · intro b hne
    exact (congrFun hfpost.2 b).trans ((houtside b hne).trans (congrFun hfpre.2 b))


/-- Exact charged cost includes each relocated helper halt/continuation jump. -/
def bankCost (D j : ℕ) : ℕ→ℕ
  | 0 => 2
  | remaining+1 => 14+UniformPowerMachine.loopCost (D/2^j)+bankCost D (j+1) remaining

def runtime (D N : ℕ) : ℕ := 9+4*Nat.clog 2 N+bankCost D 0 (count N)

theorem bankCost_bound (D j remaining : ℕ) :
    bankCost D j remaining≤remaining*(7*(Nat.log2 (D+1)+1)+16)+2 := by
  induction remaining generalizing j with
  | zero => simp [bankCost]
  | succ remaining ih =>
    have hc := UniformRootExtractionMachine.runtime_log_bound D (2^j)
    have ht := ih (j+1)
    rw [bankCost];nlinarith

theorem runtime_log_bound (D N : ℕ) : runtime D N≤32*count N*(Nat.log2 (D+1)+1) := by
  have hc := bankCost_bound D 0 (count N)
  unfold runtime
  have hcount : Nat.clog 2 N+3=count N:=rfl
  nlinarith

/-- No precomputed count, order table, or root-bank action is assumed. -/
theorem bank_execution (n N A D j remaining B : ℕ) (x : Fin n→ℂ) (s : State)
    (hs:Loop N A D j s) (hremain:j+remaining=count N) (hA:0<A) (hD:0<D)
    (hdiv:∀i:Fin (count N),2^i.val∣D) (hpart:Partial A j s)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hcode:35≤B)
    (hpower:2^(count N)≤B) (hspace:A+count N≤B) (hb:WordBound B s) : ∃u,
    BoundedExecution program n x B s (bankCost D j remaining) u ∧ Partial A (count N) u ∧
    (∀b,b<A ∨ A+count N≤b→u.scalarHeap b=s.scalarHeap b) ∧ Frame s u ∧
    u.pc=34 ∧ u.natReg 165=count N ∧ u.natReg 167=count N ∧ u.natReg 141=2^(count N) := by
  induction remaining generalizing j s with
  | zero =>
    have hj:j=count N:=by omega
    let u:State:={s with pc:=34}
    have hu:WordBound B u:=changePC_bound B s 34 hb (by omega)
    have hstop:¬s.natReg 167<s.natReg 165:=by rw [hs.index,hs.constants.size,hj];omega
    refine ⟨u,?_,?_,fun _ _=>rfl,(frame_pc s 34).1,rfl,hs.constants.size,
      hs.index.trans hj,?_⟩
    · exact .next hb (by simp [step,hs.pc,bank_branch,hstop,u]) (.halt hu (by simp [step,u,halt_at]))
    · simpa only [hj,u,Partial] using hpart
    · simpa only [hj] using hs.order
  | succ remaining ih =>
    have hj:j<count N:=by omega
    obtain ⟨v,hv,hloop,hvalue,houtside,hframe⟩:=bank_round n N A D j B x s hs hj hD
      (hdiv ⟨j,hj⟩) hroot hcode hpower hspace hb
    have hp:Partial A (j+1) v:=by
      intro i hi
      by_cases he:i=j
      · subst i;exact hvalue
      · have hil:i<j:=by omega
        exact (houtside (A+i) (by omega)).trans (hpart i hil)
    have hr:v.scalarHeap 0=some ⟨zeta D,false⟩:=(houtside 0 (by omega)).trans hroot
    obtain ⟨u,hu,hbank,hother,hf,hpc,hcount,hindex,horder⟩:=ih (j+1) v hloop
      (by omega) hp hr hv.final_bound
    refine ⟨u,?_,hbank,?_,hframe.trans hf,hpc,hcount,hindex,horder⟩
    · exact hv.executes hu
    · intro b houtsideBank
      exact (hother b houtsideBank).trans (houtside b (by omega))

/-- The single exported fixed program computes sizing and every table entry. -/
theorem execution (n N A D B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hN:s.natReg 160=N) (hbase:s.natReg 161=A) (hmaster:s.natReg 104=D)
    (hA:0<A) (hD:0<D) (hdiv:∀i:Fin (count N),2^i.val∣D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hcode:35≤B)
    (hpower:2^(count N)≤B) (hspace:A+count N≤B) (hb:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime D N) u ∧ Partial A (count N) u ∧
    (∀b,b<A ∨ A+count N≤b→u.scalarHeap b=s.scalarHeap b) ∧ Frame s u ∧
    u.pc=34 ∧ u.natReg 165=count N ∧ u.natReg 167=count N ∧ u.natReg 141=2^(count N) := by
  obtain ⟨hboot,hsize,hbootFrame⟩:=initializes n N B x s hp hN hcode hb
  obtain ⟨v,hv,hpc,hk,hNv,h1,h2,h3,hf⟩:=sizing_execution n N 0 (Nat.clog 2 N+1) B x
    (initialized s) hsize (by omega) (by omega) hcode hpower hboot.final_bound
  have hfv:PureFrame s v:=hbootFrame.trans hf
  have hAv:v.natReg 161=A:=(hfv.1.2.2.2.2 161 (by decide)).trans hbase
  have hDv:v.natReg 104=D:=(hfv.1.2.2.2.2 104 (by decide)).trans hmaster
  obtain ⟨hr,hloop,hfr⟩:=ready_execution n N A D B x v hpc hNv hAv hDv hk h1 h2 h3 hcode hpower hv.final_bound
  have hfullpre:PureFrame s (applyBlock ready v):=hfv.trans hfr
  have hrr:(applyBlock ready v).scalarHeap 0=some ⟨zeta D,false⟩:=
    (congrFun hfullpre.2 0).trans hroot
  obtain ⟨u,hu,hbank,hother,hframe,hend,hcount,hindex,horder⟩:=bank_execution n N A D 0 (count N) B x
    (applyBlock ready v) hloop (by omega) hA hD hdiv (by intro i hi;omega) hrr hcode hpower hspace hr.final_bound
  refine ⟨u,?_,hbank,?_,hfullpre.1.trans hframe,hend,hcount,hindex,horder⟩
  · have h:=((hboot.trans hv).trans hr).executes hu
    change BoundedExecution program n x B s (5+(4*(Nat.clog 2 N-0)+1)+3+bankCost D 0 (count N)) u at h
    convert h using 1;unfold runtime;omega
  · intro b hbt
    exact (hother b hbt).trans (congrFun hfullpre.2 b)


theorem Frame.saved {s u : State} {p n ell L D : ℕ} (h:Frame s u)
    (hs:UniformGlobalNatPreparation.SavedHeaders p n ell L D s) :
    UniformGlobalNatPreparation.SavedHeaders p n ell L D u := by
  refine ⟨(h.2.2.2.2 100 (by decide)).trans hs.nextPrime,
    (h.2.2.2.2 101 (by decide)).trans hs.inputLength,
    (h.2.2.2.2 102 (by decide)).trans hs.count,
    (h.2.2.2.2 103 (by decide)).trans hs.workingLength,
    (h.2.2.2.2 104 (by decide)).trans hs.masterRoot,
    (h.2.2.2.2 105 (by decide)).trans hs.copyAddress,
    (h.2.2.2.2 106 (by decide)).trans hs.copyLength⟩

theorem Frame.metadata {n : ℕ} {s u : State} (h:Frame s u)
    (hm:UniformPermutationInversePreparation.Metadata n s) :
    UniformPermutationInversePreparation.Metadata n u :=
  hm.transport_saved (h.saved hm.saved) (fun _ _=>congrFun h.1 _)

theorem zeta_one : zeta 1=1 := IsPrimitiveRoot.one_right_iff.mp
  (UniformLocalPreparationReferences.canonicalRoot (by decide))

theorem Partial.root_zero {A N : ℕ} {s : State} (h:Partial A (count N) s) :
    s.scalarHeap A=some ⟨1,false⟩ := by
  have h0:=h 0 (by unfold count;omega)
  simpa only [Nat.add_zero,pow_zero,zeta_one] using h0

theorem Partial.root_two {A N : ℕ} {s : State} (h:Partial A (count N) s) :
    s.scalarHeap (A+2)=some ⟨Complex.I,false⟩ := by
  have h2:=h 2 (by unfold count;omega)
  simpa only [show (2:ℕ)^2=4 from rfl,UniformMasterRootSeedDAG.zeta_four] using h2

theorem selected_order_bound {n N : ℕ} (hn:0<n) (hN:0<N)
    (hNL:N≤UniformWorkingLength.workingLength n) : 2^(count N)≤(n+2)^19 := by
  have h:=UniformMasterRootSeedDAG.dyadic_width_bound hN ⟨Nat.clog 2 N+2,by omega⟩
  have he : 2^(count N)=2^(Nat.clog 2 N+2)*2:=by rw [←pow_succ];rfl
  rw [he]
  have hL:=UniformWorkingLength.workingLength_upper hn
  have hp : 64≤(n+2)^18 :=
    (by norm_num : 64≤3^18).trans (Nat.pow_le_pow_left (by omega : 3≤n+2) 18)
  have hp19:(n+2)^19=(n+2)^18*(n+2):=by rw [pow_succ]
  rw [hp19]
  nlinarith

/-- Actual global metadata and operand tables supply the master cell. All bank
size/order/table conditions are computed by the exported literal program. -/
theorem selected_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (N A : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s)
    (hN:0<N) (hNL:N≤UniformWorkingLength.workingLength n)
    (hp:s.pc=0) (haxis:s.natReg 160=N) (hbase:s.natReg 161=A)
    (hA:UniformGlobalLocalPreparation.globalEnd n≤A)
    (hspace:A+count N+35≤(n+2)^19) (hb:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s (runtime (UniformMasterRootMachine.order n) N) u ∧
    Partial A (count N) u ∧
    (∀b,b<A ∨ A+count N≤b→u.scalarHeap b=s.scalarHeap b) ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    Frame s u ∧ u.pc=34 ∧ u.natReg 165=count N ∧ u.natReg 167=count N ∧ u.natReg 141=2^(count N) := by
  have hroot:s.scalarHeap 0=some ⟨zeta (UniformMasterRootMachine.order n),false⟩:=by
    simpa [UniformCConstantsMachine.bank,UniformPairMachine.prepared] using ho.constants 0
  have hAp:0<A:=by
    have hE:=UniformGlobalLocalPreparation.globalEnd_formula n
    omega
  have hdiv (i:Fin (count N)) : 2^i.val∣UniformMasterRootMachine.order n :=
    UniformMasterRootMachine.localPowerOrder_dvd hNL
      (UniformMasterRootSeedDAG.dyadic_width_bound hN i)
  obtain ⟨u,hu,hbank,houtside,hframe,hpc,hcount,hindex,horder⟩:=execution n N A
    (UniformMasterRootMachine.order n) ((n+2)^19) x s hp haxis hbase hm.saved.masterRoot hAp
    (UniformMasterRootMachine.order_bounds hn).1 hdiv hroot (by omega)
    (selected_order_bound hn hN hNL) (by omega) hb
  have hou:UniformInitialPreparation.Operands n x u:=UniformGlobalLocalPreparation.operands_transport_below ho
    (fun i hi=>houtside i (Or.inl (by omega)))
  exact ⟨u,hu,hbank,houtside,hframe.metadata hm,hou,hframe,hpc,hcount,hindex,horder⟩

end
end ExactFourierCircuits.UniformDyadicRootBankMachine
