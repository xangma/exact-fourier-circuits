import UniformTensorMonomialMachine
import UniformRadixInstructionMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReplayCoefficientMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
open UniformRadixTwoDAG (width)

/-- Nat760=height,761=original positive bank,762=negative bank,763=constants.
Only Nat765..772 and Scalar80..88 are scratch. The width and reciprocal are
computed physically; no scalar is inspected to choose an instruction. -/
def boot : List Op := [.literal 765 0,.literal 766 1,.literal 767 2,
  .literal 768 0,.literal 769 1,.literalScalar 80 1,.literalScalar 81 2,
  .literalScalar 82 1,.literalScalar 83 (-1)]
def sizeBody : List Op := [.mul 769 769 767,.scalarMul 82 82 81,.add 768 768 766]
def constantsBody : List Op := [.scalarMul 85 83 84,
  .add 772 763 765,.putScalar 772 80,
  .add 772 772 766,.putScalar 772 83,
  .add 772 772 766,.putScalar 772 84,
  .add 772 772 766,.putScalar 772 85,
  .literalScalar 86 (5/4),.add 772 772 766,.putScalar 772 86,
  .literalScalar 87 (4/5),.add 772 772 766,.putScalar 772 87,
  .literal 771 7,.mul 770 769 771,.literal 768 0]
def negativeBody : List Op := [.add 772 761 768,.getScalar 88 772,
  .scalarMul 88 88 83,.add 772 762 768,.putScalar 772 88,.add 768 768 766]
def program : Program := boot.map Op.code ++ [.branchLT 768 760 10 14] ++
  sizeBody.map Op.code ++ [.jump 9,.fieldBinary .div 84 80 82] ++
  constantsBody.map Op.code ++ [.branchLT 768 770 34 41] ++
  negativeBody.map Op.code ++ [.jump 33,.halt]
theorem program_length : program.length=42 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i<9 at hi;interval_cases i <;> rfl
theorem size_code : BlockAt sizeBody program 10 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem constants_code : BlockAt constantsBody program 15 := by
  intro i hi;change i<18 at hi;interval_cases i <;> rfl
theorem negative_code : BlockAt negativeBody program 34 := by
  intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem size_branch : program[9]?=some (.branchLT 768 760 10 14) := rfl
theorem size_jump : program[13]?=some (.jump 9) := rfl
theorem divide_at : program[14]?=some (.fieldBinary .div 84 80 82) := rfl
theorem negative_branch : program[33]?=some (.branchLT 768 770 34 41) := rfl
theorem negative_jump : program[40]?=some (.jump 33) := rfl
theorem halt_at : program[41]?=some .halt := rfl
def runtime (K : ℕ) := 5*K+56*width K+31

noncomputable section
def constant (K j : ℕ) : ℂ :=
  if j=0 then 1 else if j=1 then -1 else if j=2 then ((2:ℂ)^K)⁻¹
  else if j=3 then -((2:ℂ)^K)⁻¹ else if j=4 then 5/4 else 4/5
structure Header (K C T P : ℕ) (s : State) : Prop where
  height : s.natReg 760=K
  source : s.natReg 761=C
  target : s.natReg 762=T
  constants : s.natReg 763=P
structure SizeCursor (K C T P i : ℕ) (s : State) : Prop where
  header : Header K C T P s
  pc : s.pc=9
  zero : s.natReg 765=0
  one : s.natReg 766=1
  two : s.natReg 767=2
  index : s.natReg 768=i
  width : s.natReg 769=width i
  oneScalar : s.scalarReg 80=prepared 1
  twoScalar : s.scalarReg 81=prepared 2
  sizeScalar : s.scalarReg 82=prepared ((2:ℂ)^i)
  minusScalar : s.scalarReg 83=prepared (-1)
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,(r<765 ∨ 773≤r)→u.natReg r=s.natReg r) ∧
  (∀r,(r<80 ∨ 89≤r)→u.scalarReg r=s.scalarReg r)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
def sizeStep (s : State) := setPC (applyBlock sizeBody (setPC s 10)) 9
theorem sizeStep_heap (s : State) : (sizeStep s).scalarHeap=s.scalarHeap := rfl
theorem sizeStep_frame (s : State) : Frame s (sizeStep s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [sizeStep,sizeBody,applyBlock,Op.apply,setPC,writeNat,writeScalar,next]
theorem sizeStep_cursor {K C T P i : ℕ} {s : State} (h:SizeCursor K C T P i s) :
    SizeCursor K C T P (i+1) (sizeStep s) := by
  refine ⟨⟨?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [sizeStep,sizeBody,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,
    h.header.height,h.header.source,h.header.target,h.header.constants,h.zero,h.one,h.two,
    h.index,h.width,h.oneScalar,h.twoScalar,h.sizeScalar,h.minusScalar,
    prepared,evalField,width,pow_succ]
  all_goals ring

theorem sizeStep_bounded {K C T P i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:SizeCursor K C T P i s) (hi:i<K)
    (hB:42≤B) (hN:width K≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (sizeStep s) := by
  let v:=setPC s 10
  have hb:WordBound B v:=changePC_bound B s 10 hs (by omega)
  have hr:readable sizeBody v:=by
    simp [readable,sizeBody,Op.readable,Op.apply,setPC,v,writeNat,next,
      h.sizeScalar,h.twoScalar,prepared,evalField]
  have grow:width i*2≤B:=by
    have hw:=UniformRadixInstructionMachine.width_mono (show i+1≤K by omega)
    simp only [width] at hw
    omega
  have kB:K≤B:=by rw [←h.header.height];exact hs.2.1 760
  have pk:peak sizeBody v≤B:=by
    simp [peak,sizeBody,Op.peak,Op.apply,setPC,v,writeNat,writeScalar,next,
      h.width,h.two,h.index,h.one];omega
  have enter:BoundedRuns program n x B s 1 v:=.next hs
    (by simp [step,h.pc,size_branch,h.index,h.header.height,hi,v,setPC]) (.refl hb)
  have run:=block_runs sizeBody program 10 n B x v size_code rfl hb
    (by change 10+3≤B;omega) hr pk
  have ipc:(applyBlock sizeBody v).pc=13:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock sizeBody v) 1 (sizeStep s):=
    .next run.final_bound (by rw [step,ipc,size_jump];rfl)
      (.refl (changePC_bound B _ 9 run.final_bound (by omega)))
  simpa [sizeBody] using enter.trans (run.trans jump)

theorem size_loop {K C T P i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:SizeCursor K C T P i s) (hi:i+remaining=K)
    (hB:42≤B) (hN:width K≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*remaining) u ∧ SizeCursor K C T P K u ∧
    u.scalarHeap=s.scalarHeap ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i=K:=by omega
    subst i
    exact ⟨s,.refl hs,h,rfl,frame_refl s⟩
  | succ r ih =>
    have run:=sizeStep_bounded B n x s h (by omega) hB hN hs
    obtain ⟨u,ru,uc,uh,uf⟩:=ih (i:=i+1) (sizeStep s) (sizeStep_cursor h)
      (by omega) run.final_bound
    refine ⟨u,?_,uc,uh.trans (sizeStep_heap s),frame_trans (sizeStep_frame s) uf⟩
    convert run.trans ru using 1;omega

theorem startup (K C T P B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Header K C T P s) (hp:s.pc=0) (hB:42≤B) (hN:width K≤B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*K+9) u ∧ SizeCursor K C T P K u ∧
    u.scalarHeap=s.scalarHeap ∧ Frame s u := by
  have hr:readable boot s:=by simp [readable,boot,Op.readable]
  have pk:peak boot s≤B:=by simp [peak,boot,Op.peak];omega
  have run:=block_runs boot program 0 n B x s boot_code hp hs
    (by change 0+9≤B;omega) hr pk
  let v:=applyBlock boot s
  have cur:SizeCursor K C T P 0 v:=by
    refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp [v,boot,applyBlock,Op.apply,writeNat,writeScalar,next,hp,
      h.height,h.source,h.target,h.constants,width,prepared]
  have vf:Frame s v:=by
    refine ⟨rfl,rfl,rfl,?_,?_⟩
    all_goals intro r hr
    all_goals simp (disch:=omega) [v,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
  obtain ⟨u,ru,uc,uh,uf⟩:=size_loop K B n x v cur (by omega) hB hN run.final_bound
  refine ⟨u,?_,uc,uh,frame_trans vf uf⟩
  convert run.trans ru using 1;simp only [boot,List.length_cons,List.length_nil];omega

def divided (K : ℕ) (s : State) :=
  writeScalar (setPC s 14) 84 (prepared (((2:ℂ)^K)⁻¹))
theorem divided_cursor {K C T P : ℕ} {s : State} (h:SizeCursor K C T P K s) :
    SizeCursor K C T P K (setPC (divided K s) 9) := by
  refine ⟨⟨?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [divided,setPC,writeScalar,next,h.header.height,h.header.source,
    h.header.target,h.header.constants,h.zero,h.one,h.two,h.index,h.width,
    h.oneScalar,h.twoScalar,h.sizeScalar,h.minusScalar]
theorem divided_heap (K : ℕ) (s : State) : (divided K s).scalarHeap=s.scalarHeap := rfl
theorem divided_frame (K : ℕ) (s : State) : Frame s (divided K s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr;simp (disch:=omega) [divided,setPC,writeScalar,next]
theorem divided_bounded {K C T P : ℕ} (B n : ℕ) (x : Fin n→ℂ) (s : State)
    (h:SizeCursor K C T P K s) (hB:42≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 2 (divided K s) := by
  let v:=setPC s 14
  have hb:WordBound B v:=changePC_bound B s 14 hs (by omega)
  have enter:BoundedRuns program n x B s 1 v:=.next hs
    (by simp [step,h.pc,size_branch,h.index,h.header.height,v,setPC]) (.refl hb)
  have nz:(2:ℂ)^K≠0:=pow_ne_zero K (by norm_num)
  have run:BoundedRuns program n x B v 1 (divided K s):=.next hb
    (by simp [step,divide_at,v,setPC,divided,h.oneScalar,h.sizeScalar,evalField,
      prepared,nz,one_div])
    (.refl (writeScalar_bound B v 84 _ hb (by change 14+1≤B;omega)))
  exact enter.trans run

structure NegativeCursor (K C T P i : ℕ) (s : State) : Prop where
  header : Header K C T P s
  pc : s.pc=33
  zero : s.natReg 765=0
  one : s.natReg 766=1
  index : s.natReg 768=i
  width : s.natReg 769=width K
  count : s.natReg 770=7*UniformRadixTwoDAG.width K
  minusScalar : s.scalarReg 83=prepared (-1)
def constantsState (K : ℕ) (s : State) := applyBlock constantsBody (divided K s)
theorem constants_cursor {K C T P : ℕ} {s : State} (h:SizeCursor K C T P K s) :
    NegativeCursor K C T P 0 (constantsState K s) := by
  refine ⟨⟨?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [constantsState,constantsBody,divided,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next,h.header.height,h.header.source,h.header.target,
    h.header.constants,h.zero,h.one,h.width,h.minusScalar]
  all_goals omega
theorem constants_bank {K C T P : ℕ} {s : State} (h:SizeCursor K C T P K s) :
    ∀j,j<6→(constantsState K s).scalarHeap (P+j)=some (prepared (constant K j)) := by
  intro j hj;interval_cases j
  all_goals norm_num [constantsState,constantsBody,divided,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next,h.header.constants,h.zero,h.one,h.oneScalar,h.minusScalar,
    prepared,evalField,constant]
  all_goals simp (disch:=omega)
theorem constants_frame (K : ℕ) (s : State) : Frame s (constantsState K s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [constantsState,constantsBody,divided,applyBlock,Op.apply,
    setPC,writeNat,writeScalar,next]
theorem constants_outside {K C T P : ℕ} {s : State} (h:SizeCursor K C T P K s)
    (j : ℕ) (hj:j<P ∨ P+6≤j) : (constantsState K s).scalarHeap j=s.scalarHeap j := by
  simp (disch:=omega) [constantsState,constantsBody,divided,applyBlock,Op.apply,
    setPC,writeNat,writeScalar,next,h.header.constants,h.zero,h.one]

/-- The eighteen writes/arithmetic operations are charged after division. -/
theorem constantsBody_bounded {K C T P : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:SizeCursor K C T P K s) (hB:42≤B)
    (hP:P+6≤B) (hM:7*width K≤B) (hs:WordBound B (divided K s)) :
    BoundedRuns program n x B (divided K s) 18 (constantsState K s) := by
  have hr:readable constantsBody (divided K s):=by
    simp [readable,constantsBody,Op.readable,divided,setPC,
      writeScalar,next,h.minusScalar,prepared,evalField]
  have pk:peak constantsBody (divided K s)≤B:=by
    simp [peak,constantsBody,Op.peak,Op.apply,divided,setPC,writeScalar,
      writeNat,next,h.header.constants,h.zero,h.one,h.width]
    omega
  exact block_runs constantsBody program 15 n B x (divided K s)
    constants_code rfl hs (by change 15+18≤B;omega) hr pk

theorem constants_bounded {K C T P : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:SizeCursor K C T P K s) (hB:42≤B)
    (hP:P+6≤B) (hM:7*width K≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 20 (constantsState K s) := by
  have run:=divided_bounded B n x s h hB hs
  exact run.trans (constantsBody_bounded B n x s h hB hP hM run.final_bound)

/-- Physical prepared source, not a certificate for the later writes. -/
def Source (C m : ℕ) (bank : ℕ→ℂ) (s : State) : Prop :=
  ∀ j, j < m →s.scalarHeap (C+j)=some (prepared (bank j))
def NegativeBank (T m : ℕ) (bank : ℕ→ℂ) (s : State) : Prop :=
  ∀ j, j < m →s.scalarHeap (T+j)=some (prepared (-bank j))
def Constants (K P : ℕ) (s : State) : Prop :=
  ∀j,j<6→s.scalarHeap (P+j)=some (prepared (constant K j))
def Outside (a m : ℕ) (s u : State) : Prop :=
  ∀j,j<a ∨ a+m≤j→u.scalarHeap j=s.scalarHeap j

def negativeStep (s : State) := setPC (applyBlock negativeBody (setPC s 34)) 33

theorem negativeStep_cursor {K C T P i : ℕ} {s : State}
    (h:NegativeCursor K C T P i s) :
    NegativeCursor K C T P (i+1) (negativeStep s) := by
  refine ⟨⟨?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [negativeStep,negativeBody,applyBlock,Op.apply,setPC,writeNat,
    writeScalar,next,h.header.height,h.header.source,h.header.target,
    h.header.constants,h.zero,h.one,h.index,h.width,h.count,h.minusScalar]

theorem negativeStep_frame (s : State) : Frame s (negativeStep s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [negativeStep,negativeBody,applyBlock,Op.apply,
    setPC,writeNat,writeScalar,next]

theorem negativeStep_heap {K C T P i : ℕ} {s : State} (bank : ℕ→ℂ)
    (h:NegativeCursor K C T P i s)
    (hr:s.scalarHeap (C+i)=some (prepared (bank i))) :
    (negativeStep s).scalarHeap=
      Function.update s.scalarHeap (T+i) (some (prepared (-bank i))) := by
  simp [negativeStep,negativeBody,applyBlock,Op.apply,setPC,writeNat,writeScalar,
    next,h.header.source,h.header.target,h.index,h.one,hr,h.minusScalar,
    prepared,evalField]

theorem negativeStep_bounded {K C T P i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (bank : ℕ→ℂ) (h:NegativeCursor K C T P i s)
    (hi:i<7*width K) (hr:s.scalarHeap (C+i)=some (prepared (bank i)))
    (hB:42≤B) (hC:C+7*width K≤T) (hT:T+7*width K≤P) (hP:P+6≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 8 (negativeStep s) := by
  let v:=setPC s 34
  have hb:WordBound B v:=changePC_bound B s 34 hs (by omega)
  have hRead:readable negativeBody v:=by
    simp [readable,negativeBody,Op.readable,Op.apply,v,setPC,writeNat,writeScalar,
      next,h.header.source,h.index,hr,h.minusScalar,prepared,evalField]
  have hPeak:peak negativeBody v≤B:=by
    simp [peak,negativeBody,Op.peak,Op.apply,v,setPC,writeNat,writeScalar,
      next,h.header.source,h.header.target,h.index,h.one]
    omega
  have enter:BoundedRuns program n x B s 1 v:=.next hs
    (by simp [step,h.pc,negative_branch,h.index,h.count,hi,v,setPC]) (.refl hb)
  have run:=block_runs negativeBody program 34 n B x v negative_code rfl hb
    (by change 34+6≤B;omega) hRead hPeak
  have ipc:(applyBlock negativeBody v).pc=40:=by
    rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock negativeBody v) 1 (negativeStep s):=
    .next run.final_bound (by rw [step,ipc,negative_jump];rfl)
      (.refl (changePC_bound B _ 33 run.final_bound (by omega)))
  exact enter.trans (run.trans jump)

theorem negativeStep_source {K C T P i : ℕ} {s : State} (bank : ℕ→ℂ)
    (h:NegativeCursor K C T P i s) (hi:i<7*width K)
    (src:Source C (7*width K) bank s) (hC:C+7*width K≤T) :
    Source C (7*width K) bank (negativeStep s) := by
  intro j hj
  rw [negativeStep_heap bank h (src i hi)]
  simp (disch:=omega) [src j hj]

theorem negativeStep_constants {K C T P i : ℕ} {s : State} (bank : ℕ→ℂ)
    (h:NegativeCursor K C T P i s) (hi:i<7*width K)
    (src:Source C (7*width K) bank s) (hc:Constants K P s)
    (hT:T+7*width K≤P) : Constants K P (negativeStep s) := by
  intro j hj
  rw [negativeStep_heap bank h (src i hi)]
  simp (disch:=omega) [hc j hj]

/-- The induction carries the written prefix; each store is beyond it. -/
theorem negative_loop {K C T P i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (s : State) (bank : ℕ→ℂ) (h:NegativeCursor K C T P i s)
    (hi:i+remaining=7*width K) (src:Source C (7*width K) bank s)
    (neg:NegativeBank T i bank s) (hc:Constants K P s)
    (hB:42≤B) (hC:C+7*width K≤T) (hT:T+7*width K≤P) (hP:P+6≤B)
    (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (8*remaining) u ∧
    NegativeCursor K C T P (7*width K) u ∧ Source C (7*width K) bank u ∧
    NegativeBank T (7*width K) bank u ∧ Constants K P u ∧
    Outside (T+i) remaining s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i=7*width K:=by omega
    subst i
    exact ⟨s,.refl hs,h,src,neg,hc,fun _ _=>rfl,frame_refl s⟩
  | succ r ih =>
    have ilt:i<7*width K:=by omega
    have hh:=negativeStep_heap bank h (src i ilt)
    have run:=negativeStep_bounded B n x s bank h ilt (src i ilt) hB hC hT hP hs
    have nextNeg:NegativeBank T (i+1) bank (negativeStep s):=by
      intro j hj
      rw [hh]
      by_cases he:j=i
      · subst j;simp
      · have jl : j < i := by omega
        simp (disch:=omega) [neg j jl]
    obtain ⟨u,ru,uc,us,un,uk,uo,uf⟩:=ih (i:=i+1) (negativeStep s)
      (negativeStep_cursor h) (by omega) (negativeStep_source bank h ilt src hC)
      nextNeg (negativeStep_constants bank h ilt src hc hT) run.final_bound
    refine ⟨u,?_,uc,us,un,uk,?_,frame_trans (negativeStep_frame s) uf⟩
    · convert run.trans ru using 1;omega
    · intro j hj
      rw [uo j (by omega),hh]
      simp (disch:=omega)

/-- Actual whole-program preparation, including the final branch and halt. -/
theorem execution (K C T P B n : ℕ) (x : Fin n→ℂ) (s : State) (bank : ℕ→ℂ)
    (h:Header K C T P s) (hp:s.pc=0) (src:Source C (7*width K) bank s)
    (hB:42≤B) (hC:C+7*width K≤T) (hT:T+7*width K≤P) (hP:P+6≤B)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime K) u ∧ u.pc=41 ∧ Header K C T P u ∧
    Source C (7*width K) bank u ∧ NegativeBank T (7*width K) bank u ∧
    Constants K P u ∧ (∀j,(j<T ∨ T+7*width K≤j)→(j<P ∨ P+6≤j)→
      u.scalarHeap j=s.scalarHeap j) ∧ Frame s u := by
  have hM:7*width K≤B:=by omega
  have hN:width K≤B:=by omega
  obtain ⟨v,rv,vc,vh,vf⟩:=startup K C T P B n x s h hp hB hN hs
  have rc:=constants_bounded B n x v vc hB hP hM rv.final_bound
  have cs:Source C (7*width K) bank (constantsState K v):=by
    intro j hj
    rw [constants_outside vc (C+j) (by omega),vh]
    exact src j hj
  have cn:NegativeBank T 0 bank (constantsState K v):=by intro j hj;omega
  obtain ⟨w,rw,wc,ws,wn,wk,wo,wf⟩:=negative_loop (7*width K) B n x
    (constantsState K v) bank (constants_cursor vc) (by omega) cs cn
    (constants_bank vc) hB hC hT hP rc.final_bound
  let u:=setPC w 41
  have hb:WordBound B u:=changePC_bound B w 41 rw.final_bound (by omega)
  have last:BoundedRuns program n x B w 1 u:=.next rw.final_bound
    (by simp [step,wc.pc,negative_branch,wc.index,wc.count,u,setPC]) (.refl hb)
  have halted:step program n x u=.halted u:=by simp [step,u,setPC,halt_at]
  have run:BoundedRuns program n x B s (5*K+56*width K+30) u:=by
    convert rv.trans (rc.trans (rw.trans last)) using 1;omega
  refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_⟩
  · simpa [runtime] using run.executes (BoundedExecution.halt hb halted)
  · exact ⟨wc.header.height,wc.header.source,wc.header.target,wc.header.constants⟩
  · simpa [Source,u,setPC] using ws
  · simpa [NegativeBank,u,setPC] using wn
  · simpa [Constants,u,setPC] using wk
  · intro j hj hjP
    change w.scalarHeap j=s.scalarHeap j
    rw [wo j (by omega),constants_outside vc j hjP,vh]
  · exact frame_trans vf (frame_trans (constants_frame K v)
      (frame_trans wf ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩))

/-- The reciprocal is the normalization for the physically computed width. -/
theorem constant_normalization (K : ℕ) : constant K 2=(width K:ℂ)⁻¹ := by
  simp [constant,UniformRadixTwoDAG.width_eq]

theorem constant_negative_normalization (K : ℕ) : constant K 3=-(width K:ℂ)⁻¹ := by
  simp [constant,UniformRadixTwoDAG.width_eq]

theorem normalization_nonzero (K : ℕ) : (width K:ℂ)≠0 := by
  simp [UniformRadixTwoDAG.width_eq]

theorem constants_values {K P : ℕ} {s : State} (h:Constants K P s) :
    s.scalarHeap P=some (prepared 1) ∧
    s.scalarHeap (P+1)=some (prepared (-1)) ∧
    s.scalarHeap (P+2)=some (prepared ((width K:ℂ)⁻¹)) ∧
    s.scalarHeap (P+3)=some (prepared (-(width K:ℂ)⁻¹)) ∧
    s.scalarHeap (P+4)=some (prepared (5/4)) ∧
    s.scalarHeap (P+5)=some (prepared (4/5)) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [constant] using h 0 (by omega)
  · simpa [constant] using h 1 (by omega)
  · simpa [constant_normalization] using h 2 (by omega)
  · simpa [constant_negative_normalization] using h 3 (by omega)
  · simpa [constant] using h 4 (by omega)
  · simpa [constant] using h 5 (by omega)

/-- A signed reference reads one of the two produced physical banks. -/
def signedAddress (C T : ℕ) (negative : Bool) (j : ℕ) :=
  (if negative then T else C)+j
def signedValue (negative : Bool) (z : ℂ) := if negative then -z else z

theorem signed_ready {C T m : ℕ} {bank : ℕ→ℂ} {s : State}
    (positive:Source C m bank s) (negative:NegativeBank T m bank s)
    (sign : Bool) (j : ℕ) (hj : j < m) :
    s.scalarHeap (signedAddress C T sign j)=some (prepared (signedValue sign (bank j))) := by
  cases sign with
  | false => exact positive j hj
  | true => exact negative j hj

theorem frame_saved {s u : State} (h:Frame s u) (r : ℕ) (hr:100≤r ∧ r≤106) :
    u.natReg r=s.natReg r := h.2.2.2.1 r (by omega)

/-- The positive source may begin at zero. All computed writes still lie
    strictly above zero, so even that original master scalar survives. -/
theorem execution_preserving_master (K C T P B n : ℕ) (x : Fin n→ℂ)
    (s : State) (bank : ℕ→ℂ) (h:Header K C T P s) (hp:s.pc=0)
    (src:Source C (7*width K) bank s) (hB:42≤B)
    (hC:C+7*width K≤T) (hT:T+7*width K≤P) (hP:P+6≤B)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime K) u ∧ u.pc=41 ∧ Header K C T P u ∧
    Source C (7*width K) bank u ∧ NegativeBank T (7*width K) bank u ∧
    Constants K P u ∧ u.scalarHeap 0=s.scalarHeap 0 ∧ Frame s u := by
  obtain ⟨u,run,pc,header,pos,neg,cs,outside,frame⟩:=
    execution K C T P B n x s bank h hp src hB hC hT hP hs
  have hN:0<width K:=UniformRadixTwoDAG.width_pos K
  exact ⟨u,run,pc,header,pos,neg,cs,outside 0 (by omega) (by omega),frame⟩

theorem runtime_zero : runtime 0=87 := rfl
theorem runtime_one : runtime 1=148 := rfl
theorem runtime_two : runtime 2=265 := rfl

end
end ExactFourierCircuits.UniformReplayCoefficientMachine
