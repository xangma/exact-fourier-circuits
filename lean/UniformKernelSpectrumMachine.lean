import UniformFFTInputMachine
import UniformScalarCopyMachine
import UniformContiguousPowerBankMachine
import UniformToeplitzCrossDAG

set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelSpectrumMachine
open UniformMachine UniformAssembly UniformRadixTwoDAG OAI.ExactFourier
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)

/-- Nat525=height,526=six original kernels,527=FFT arena,528=Nat rows,
529=shared-bank destination. The master order is the existing Nat104.
Caller registers are retained; driver scratch is Nat530..539. -/
def sizeBoot : List Op := [.literal 531 0,.literal 532 1,.literal 533 2,
  .add 530 532 531,.add 534 531 531]
def grow : List Op := [.mul 530 530 533,.add 534 534 532]
def countHead : List Op := [.literal 539 3,.mul 538 525 530,.mul 538 538 539]
def loopBoot : List Op := [.literal 535 0,.literal 536 6]
def fftSetup : List Op := [.mul 537 535 530,.add 175 526 537,.add 70 525 531,
  .add 174 530 531,.add 176 532 531,.add 122 527 531,.add 107 528 531]
def copySetup : List Op := [.add 147 530 531,.add 148 527 538,
  .add 149 529 530,.add 149 149 537]
def finish : List Op := [.add 535 535 532]
def rootSetup : List Op := [.literal 539 7,.mul 537 530 539,.add 537 529 537,
  .add 140 537 531,.add 141 530 531]
def powerSetup : List Op := [.add 550 530 531,.add 551 537 531,.add 552 529 531]

def controllerHead : Program := sizeBoot.map Op.code ++ [.branchLT 534 525 6 9] ++
  grow.map Op.code ++ [.jump 5] ++ countHead.map Op.code ++
  [.natBinary .div 538 538 533] ++ loopBoot.map Op.code ++
  [.branchLT 535 536 16 260] ++ fftSetup.map Op.code
def suffix : Program := copySetup.map Op.code ++
  UniformScalarCopyMachine.program.map (relocate 248 258) ++ finish.map Op.code ++
  [.jump 15] ++ rootSetup.map Op.code ++
  UniformRootExtractionMachine.program.map (relocate 265 282) ++ powerSetup.map Op.code ++
  UniformContiguousPowerBankMachine.program.map (relocate 285 296) ++ [.halt]
def program : Program := embed controllerHead UniformFFTInputMachine.combinedProgram suffix 244

theorem controllerHead_length : controllerHead.length=23 := rfl
theorem suffix_length : suffix.length=53 := by
  simp [suffix,copySetup,finish,rootSetup,powerSetup,
    UniformScalarCopyMachine.program_length,UniformRootExtractionMachine.program_length,
    UniformContiguousPowerBankMachine.program_length]
theorem program_length : program.length=297 := by
  rw [program,embed_length,controllerHead_length,UniformFFTInputMachine.combinedProgram_length,suffix_length]
theorem size_branch : program[5]?=some (.branchLT 534 525 6 9) := rfl
theorem size_jump : program[8]?=some (.jump 5) := rfl
theorem loop_branch : program[15]?=some (.branchLT 535 536 16 260) := rfl
theorem loop_jump : program[259]?=some (.jump 15) := by
  unfold program embed
  rw [List.getElem?_append_right (by
    simp only [List.length_append,List.length_map,controllerHead_length,
      UniformFFTInputMachine.combinedProgram_length];omega)]
  simp only [List.length_append,List.length_map,controllerHead_length,
    UniformFFTInputMachine.combinedProgram_length]
  rfl
theorem final_halt : program[296]?=some .halt := by
  unfold program embed
  rw [List.getElem?_append_right (by
    simp only [List.length_append,List.length_map,controllerHead_length,
      UniformFFTInputMachine.combinedProgram_length];omega)]
  simp only [List.length_append,List.length_map,controllerHead_length,
    UniformFFTInputMachine.combinedProgram_length]
  rfl
theorem fft_code : CodeAt UniformFFTInputMachine.combinedProgram program 23 244 :=
  embed_code controllerHead UniformFFTInputMachine.combinedProgram suffix 244

theorem segment_code (before after p : Program) (base returnPC : ℕ)
    (hb:before.length=base) :
    CodeAt p (before ++ p.map (relocate base returnPC) ++ after) base returnPC := by
  intro i hi
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,hb];omega)]
  rw [List.getElem?_append_right (by omega)]
  simp only [hb,show base+i-base=i by omega,List.getElem?_map]

theorem copy_code : CodeAt UniformScalarCopyMachine.program program 248 258 := by
  let before:=controllerHead ++ UniformFFTInputMachine.combinedProgram.map (relocate 23 244) ++ copySetup.map Op.code
  let after:=finish.map Op.code ++ [.jump 15] ++ rootSetup.map Op.code ++
    UniformRootExtractionMachine.program.map (relocate 265 282) ++ powerSetup.map Op.code ++
    UniformContiguousPowerBankMachine.program.map (relocate 285 296) ++ [.halt]
  have hb:before.length=248:=by
    simp [before,controllerHead_length,copySetup,UniformFFTInputMachine.combinedProgram_length]
  have hp:program=before ++ UniformScalarCopyMachine.program.map (relocate 248 258) ++ after:=by
    simp only [program,embed,suffix,before,after,controllerHead_length,List.append_assoc]
  rw [hp]
  exact segment_code before after _ 248 258 hb

theorem root_code : CodeAt UniformRootExtractionMachine.program program 265 282 := by
  let before:=controllerHead ++ UniformFFTInputMachine.combinedProgram.map (relocate 23 244) ++
    copySetup.map Op.code ++ UniformScalarCopyMachine.program.map (relocate 248 258) ++
    finish.map Op.code ++ [.jump 15] ++ rootSetup.map Op.code
  let after:=powerSetup.map Op.code ++
    UniformContiguousPowerBankMachine.program.map (relocate 285 296) ++ [.halt]
  have hb:before.length=265:=by
    simp [before,controllerHead_length,copySetup,finish,rootSetup,
      UniformFFTInputMachine.combinedProgram_length,UniformScalarCopyMachine.program_length]
  have hp:program=before ++ UniformRootExtractionMachine.program.map (relocate 265 282) ++ after:=by
    simp only [program,embed,suffix,before,after,controllerHead_length,List.append_assoc]
  rw [hp]
  exact segment_code before after _ 265 282 hb

theorem power_code : CodeAt UniformContiguousPowerBankMachine.program program 285 296 := by
  let before:=controllerHead ++ UniformFFTInputMachine.combinedProgram.map (relocate 23 244) ++
    copySetup.map Op.code ++ UniformScalarCopyMachine.program.map (relocate 248 258) ++
    finish.map Op.code ++ [.jump 15] ++ rootSetup.map Op.code ++
    UniformRootExtractionMachine.program.map (relocate 265 282) ++ powerSetup.map Op.code
  have hb:before.length=285:=by
    simp [before,controllerHead_length,copySetup,finish,rootSetup,powerSetup,
      UniformFFTInputMachine.combinedProgram_length,UniformScalarCopyMachine.program_length,
      UniformRootExtractionMachine.program_length]
  have hp:program=before ++ UniformContiguousPowerBankMachine.program.map (relocate 285 296) ++ [.halt]:=by
    simp only [program,embed,suffix,before,controllerHead_length,List.append_assoc]
  rw [hp]
  exact segment_code before [.halt] _ 285 296 hb

noncomputable section
structure Header (K S A d C D : ℕ) (s : State) : Prop where
  height : s.natReg 525=K
  kernels : s.natReg 526=S
  arena : s.natReg 527=A
  rows : s.natReg 528=d
  bank : s.natReg 529=C
  order : s.natReg 104=D

def Kernels (K S : ℕ) (values : Fin 6→Fin (width K)→ℂ) (s : State) : Prop :=
  ∀slot j,s.scalarHeap (S+slot.val*width K+j.val)=some (prepared (values slot j))

def Result (K C : ℕ) (values : Fin 6→Fin (width K)→ℂ) (s : State) : Prop :=
  ∀j:Fin (UniformToeplitzCrossDAG.bankSize K),s.scalarHeap (C+j.val)=
    some (prepared (UniformToeplitzCrossDAG.sharedBank K values j))

def wordBudget (K S A d C : ℕ) : ℕ :=
  UniformPreparedFFTMachine.wordBudget K A d+S+C+7*width K+600

def runtimeBudget (D K : ℕ) : ℕ := 4*K+12+
  6*(7+(4*K+10*width K+9+UniformPreparedFFTMachine.runtime D K)+4+(7*width K+4)+3)+
  1+5+(9+UniformPowerMachine.loopCost (D/width K))+3+(6*width K+6)+1

theorem sizeBoot_code : BlockAt sizeBoot program 0 := by
  intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem grow_code : BlockAt grow program 6 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem countHead_code : BlockAt countHead program 9 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem loopBoot_code : BlockAt loopBoot program 13 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem count_div_at : program[12]?=some (.natBinary .div 538 538 533) := rfl

structure Sizing (K t : ℕ) (s : State) : Prop where
  height : s.natReg 525=K
  width : s.natReg 530=width t
  index : s.natReg 534=t
  zero : s.natReg 531=0
  one : s.natReg 532=1
  two : s.natReg 533=2

theorem Sizing.withPC {K t pc : ℕ} {s : State} (h:Sizing K t s) :
    Sizing K t (setPC s pc) := by cases h;constructor <;> assumption

def SetupFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧
  u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ ∀r,(r<530 ∨ 540≤r)→u.natReg r=s.natReg r
theorem setupFrame_refl (s : State) : SetupFrame s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem SetupFrame.trans {s u v : State} (h:SetupFrame s u) (h':SetupFrame u v) :
    SetupFrame s v := ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.1.trans h.2.2.2.2.1,
    fun r hr=>(h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩
theorem SetupFrame.withPC {pc : ℕ} {s u : State} (h:SetupFrame s u) :
    SetupFrame s (setPC u pc) := h

theorem boot_sizing {K : ℕ} {s : State} (h:s.natReg 525=K) :
    Sizing K 0 (applyBlock sizeBoot s) := by
  constructor <;> simp [sizeBoot,applyBlock,Op.apply,writeNat,next,h,width]
theorem boot_frame (s : State) : SetupFrame s (applyBlock sizeBoot s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr;simp (disch:=omega) [sizeBoot,applyBlock,Op.apply,writeNat,next]

theorem grow_sizing {K t : ℕ} {s : State} (h:Sizing K t s) :
    Sizing K (t+1) (applyBlock grow s) := by
  constructor <;> simp [grow,applyBlock,Op.apply,writeNat,next,
    h.height,h.width,h.index,h.zero,h.one,h.two,width]
  all_goals omega
theorem grow_frame (s : State) : SetupFrame s (applyBlock grow s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr;simp (disch:=omega) [grow,applyBlock,Op.apply,writeNat,next]

/-- Every doubling, comparison and jump is charged; the final size is derived
from the physical height header. -/
theorem sizing_loop (n K t remaining B : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Sizing K t s) (ht:t+remaining=K) (hp:s.pc=5)
    (hc:297≤B) (hN:width K≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (4*remaining+1) u ∧ Sizing K K u ∧
    u.pc=9 ∧ SetupFrame s u := by
  induction remaining generalizing t s with
  | zero =>
    have he:t=K:=by omega
    have run:=UniformRadixInstructionMachine.branch_runs program n B 534 525 6 9 x s hs
      (by omega) (by omega) (by rw [hp];exact size_branch)
    have hn:¬s.natReg 534<s.natReg 525:=by rw [h.index,h.height,he];omega
    simp only [hn,ite_false] at run
    exact ⟨setPC s 9,by simpa [setPC] using run,by simpa [he] using h.withPC,
      rfl,(setupFrame_refl s).withPC⟩
  | succ remaining ih =>
    have htK:t<K:=by omega
    have enter:=UniformRadixInstructionMachine.branch_runs program n B 534 525 6 9 x s hs
      (by omega) (by omega) (by rw [hp];exact size_branch)
    have hn:s.natReg 534<s.natReg 525:=by rw [h.index,h.height];exact htK
    simp only [hn,ite_true] at enter
    let v:=setPC s 6
    have hv:WordBound B v:=by simpa [v,setPC] using enter.final_bound
    have hr:readable grow v:=by simp [readable,grow,Op.readable]
    have hw:=UniformRadixInstructionMachine.width_mono (show t+1≤K by omega)
    have hw':width t*2≤B:=by simpa [width,Nat.mul_two] using hw.trans hN
    have hK:K≤B:=by simpa [h.height] using hs.2.1 525
    have hb:peak grow v≤B:=by
      simp [peak,grow,Op.peak,Op.apply,writeNat,next,v,setPC,h.width,h.two,h.index,h.one]
      omega
    have run:=block_runs grow program 6 n B x v grow_code rfl hv (by change 6+2≤B;omega) hr hb
    have hpc:(applyBlock grow v).pc=8:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have jump:=UniformRadixInstructionMachine.jump_runs program n B 5 x (applyBlock grow v)
      run.final_bound (by omega) (by rw [hpc];exact size_jump)
    let w:=setPC (applyBlock grow v) 5
    have hwi:Sizing K (t+1) w:=(grow_sizing h.withPC).withPC
    have hwb:WordBound B w:=by simpa [w,setPC] using jump.final_bound
    obtain ⟨u,hu,hui,hup,hframe⟩:=ih (t+1) w hwi (by omega) rfl hwb
    refine ⟨u,?_,hui,hup,?_⟩
    · convert enter.trans (run.trans (jump.trans hu)) using 1
      simp only [show grow.length=2 from rfl];omega
    · exact (grow_frame v).withPC.trans hframe

structure LoopCursor (K S A d C D i : ℕ) (s : State) : Prop where
  header : Header K S A d C D s
  pc : s.pc=15
  width : s.natReg 530=width K
  count : s.natReg 538=count K
  index : s.natReg 535=i
  slots : s.natReg 536=6
  zero : s.natReg 531=0
  one : s.natReg 532=1
  two : s.natReg 533=2

theorem initialize_driver (n K S A d C D B : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Header K S A d C D s) (hp:s.pc=0) (hs:WordBound B s)
    (hc:297≤B) (hN:width K≤B) (hG:3*K*width K≤B) : ∃u,
    BoundedRuns program n x B s (4*K+12) u ∧ LoopCursor K S A d C D 0 u ∧ SetupFrame s u := by
  have br:readable sizeBoot s:=by simp [readable,sizeBoot,Op.readable]
  have bp:peak sizeBoot s≤B:=by simp [peak,sizeBoot,Op.peak,Op.apply,writeNat,next];omega
  have boot:=block_runs sizeBoot program 0 n B x s sizeBoot_code hp hs (by change 0+5≤B;omega) br bp
  have bpc:(applyBlock sizeBoot s).pc=5:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  obtain ⟨v,hv,hvi,hvp,hvf⟩:=sizing_loop n K 0 K B x (applyBlock sizeBoot s)
    (boot_sizing h.height) (by omega) bpc hc hN boot.final_bound
  have cr:readable countHead v:=by simp [readable,countHead,Op.readable]
  have cp:peak countHead v≤B:=by
    simp [peak,countHead,Op.peak,Op.apply,writeNat,next,hvi.height,hvi.width]
    have ht:K*width K≤3*K*width K:=by nlinarith
    exact ⟨by omega,ht.trans hG,by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hG⟩
  have counts:=block_runs countHead program 9 n B x v countHead_code hvp hv.final_bound
    (by change 9+3≤B;omega) cr cp
  let w:=applyBlock countHead v
  have wpc:w.pc=12:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hvp];rfl
  have wtwo:w.natReg 533=2:=by simpa [w,countHead,applyBlock,Op.apply,writeNat,next] using hvi.two
  let z:=writeNat w 538 (w.natReg 538/w.natReg 533)
  have bz:WordBound B z:=writeNat_bound B w 538 _ counts.final_bound (by omega)
    ((Nat.div_le_self _ _).trans (counts.final_bound.2.1 538))
  have division:BoundedRuns program n x B w 1 z:=.next counts.final_bound
    (by simp [step,wpc,count_div_at,evalNat,wtwo,z]) (.refl bz)
  have zpc:z.pc=13:=by simp [z,writeNat,next,wpc]
  have lr:readable loopBoot z:=by simp [readable,loopBoot,Op.readable]
  have lp:peak loopBoot z≤B:=by simp [peak,loopBoot,Op.peak];omega
  have loops:=block_runs loopBoot program 13 n B x z loopBoot_code zpc bz (by change 13+2≤B;omega) lr lp
  let u:=applyBlock loopBoot z
  have post:SetupFrame v u:=by
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro r hr;simp (disch:=omega) [u,z,w,loopBoot,countHead,applyBlock,Op.apply,writeNat,next]
  have frame:SetupFrame s u:=(boot_frame s).trans (hvf.trans post)
  have nr:=frame.2.2.2.2.2
  have cursor:LoopCursor K S A d C D 0 u:=by
    refine ⟨⟨(nr 525 (by omega)).trans h.height,(nr 526 (by omega)).trans h.kernels,
      (nr 527 (by omega)).trans h.arena,(nr 528 (by omega)).trans h.rows,
      (nr 529 (by omega)).trans h.bank,(nr 104 (by omega)).trans h.order⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [UniformTensorMonomialMachine.applyBlock_pc,zpc];rfl
    all_goals simp [u,z,w,loopBoot,countHead,applyBlock,Op.apply,writeNat,next,
      hvi.width,hvi.height,hvi.zero,hvi.one,hvi.two]
    all_goals simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using UniformRadixInstructionMachine.count_div K
  refine ⟨u,?_,cursor,frame⟩
  convert boot.trans (hv.trans (counts.trans (division.trans loops))) using 1
  simp only [show sizeBoot.length=5 from rfl,show countHead.length=3 from rfl,show loopBoot.length=2 from rfl];omega


/-- The caller supplies only physical original kernels and ordinary disjoint
regions. Neither spectra nor a prepared power bank is supplied. -/
structure Layout (K S A d C D B : ℕ) : Prop where
  sourceEnd : S+6*width K ≤ A
  arenaPositive : 0 < A
  bankAfter : UniformPreparedFFTMachine.rootAddress K A+1 ≤ C
  orderPositive : 0 < D
  divisor : width K ∣ D
  envelope : wordBudget K S A d C ≤ B

theorem Layout.bounds {K S A d C D B : ℕ} (h:Layout K S A d C D B) :
    297 ≤ B ∧ width K ≤ B ∧ 3*K*width K ≤ B ∧
    UniformPreparedFFTMachine.wordBudget K A d ≤ B ∧ C+7*width K+1 ≤ B := by
  have hb:UniformPreparedFFTMachine.wordBudget K A d ≤ B:=by have :=h.envelope;unfold wordBudget at this;omega
  have capB:UniformRadixInstructionMachine.cap (width K) (count K) K ≤ B:=by
    have :=(UniformPreparedFFTMachine.wordBudget_bounds K A d B hb).2.1;omega
  have hc:=UniformRadixInstructionMachine.cap_linear (width K) (count K) K
  have hm:=Nat.mul_le_mul (show K ≤ width K+count K+K+1 by omega)
    (show width K ≤ width K+count K+K+1 by omega)
  have hthree:3*K*width K ≤ UniformRadixInstructionMachine.cap (width K) (count K) K:=by
    unfold UniformRadixInstructionMachine.cap;simp only [pow_two];nlinarith
  have hen:=h.envelope;unfold wordBudget at hen
  exact ⟨by omega,by omega,hthree.trans capB,hb,by omega⟩

/-- Global saved metadata, the rank producer headers, caller headers, and
unrelated high registers survive. FFT/input/copy/root scratch is excluded. -/
def Persistent (r : ℕ) : Prop := (100 ≤ r ∧ r ≤ 106) ∨ (184 ≤ r ∧ r < 530) ∨ 556 ≤ r

def Frame (K A d C : ℕ) (s t : State) : Prop :=
  UniformRadixRowTableMachine.Outside d (3*count K) s.natHeap t ∧
  (∀q,(q < A ∨ UniformPreparedFFTMachine.rootAddress K A+1 ≤ q) →
    (q < C ∨ C+7*width K+1 ≤ q) →t.scalarHeap q=s.scalarHeap q) ∧
  t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
  (∀r,Persistent r →t.natReg r=s.natReg r)

theorem Frame.refl (K A d C : ℕ) (s : State) : Frame K A d C s s :=
  ⟨fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {K A d C : ℕ} {s t u : State} (f:Frame K A d C s t) (g:Frame K A d C t u) :
    Frame K A d C s u :=
  ⟨fun q hq=>(g.1 q hq).trans (f.1 q hq),fun q hq hr=>(g.2.1 q hq hr).trans (f.2.1 q hq hr),
    g.2.2.1.trans f.2.2.1,g.2.2.2.1.trans f.2.2.2.1,
    fun r hr=>(g.2.2.2.2 r hr).trans (f.2.2.2.2 r hr)⟩
theorem Frame.withPC {K A d C pc : ℕ} {s t : State} (f:Frame K A d C s t) :
    Frame K A d C s (setPC t pc) := f

theorem SetupFrame.frame {K A d C : ℕ} {s t : State} (f:SetupFrame s t) : Frame K A d C s t :=
  ⟨fun q _=>congrFun f.1 q,fun q _ _=>congrFun f.2.1 q,f.2.2.2.1,f.2.2.2.2.1,
    fun r hr=>f.2.2.2.2.2 r (by simp only [Persistent] at hr;omega)⟩

def ControlRegs (s t : State) : Prop :=
  ∀r,r ∈ ([104,525,526,527,528,529,530,531,532,533,535,536,538] : List ℕ) →t.natReg r=s.natReg r

structure Context (K S A d C D i : ℕ) (s : State) : Prop where
  header : Header K S A d C D s
  width : s.natReg 530=width K
  count : s.natReg 538=count K
  index : s.natReg 535=i
  slots : s.natReg 536=6
  zero : s.natReg 531=0
  one : s.natReg 532=1
  two : s.natReg 533=2

theorem Header.withPC {K S A d C D pc : ℕ} {s : State} (h:Header K S A d C D s) :
    Header K S A d C D (setPC s pc) := by cases h;constructor <;> assumption

theorem LoopCursor.context {K S A d C D i : ℕ} {s : State} (h:LoopCursor K S A d C D i s) :
    Context K S A d C D i s := ⟨h.header,h.width,h.count,h.index,h.slots,h.zero,h.one,h.two⟩
theorem Context.cursor {K S A d C D i : ℕ} {s : State} (h:Context K S A d C D i s) (hp:s.pc=15) :
    LoopCursor K S A d C D i s := ⟨h.header,hp,h.width,h.count,h.index,h.slots,h.zero,h.one,h.two⟩
theorem Context.withPC {K S A d C D i pc : ℕ} {s : State} (h:Context K S A d C D i s) :
    Context K S A d C D i (setPC s pc) :=
  ⟨h.header.withPC,h.width,h.count,h.index,h.slots,h.zero,h.one,h.two⟩

theorem Context.transport {K S A d C D i : ℕ} {s t : State} (h:Context K S A d C D i s) (f:ControlRegs s t) :
    Context K S A d C D i t := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (f _ (by decide)).trans h.header.height
    | exact (f _ (by decide)).trans h.header.kernels
    | exact (f _ (by decide)).trans h.header.arena
    | exact (f _ (by decide)).trans h.header.rows
    | exact (f _ (by decide)).trans h.header.bank
    | exact (f _ (by decide)).trans h.header.order
    | exact (f _ (by decide)).trans h.width
    | exact (f _ (by decide)).trans h.count
    | exact (f _ (by decide)).trans h.index
    | exact (f _ (by decide)).trans h.slots
    | exact (f _ (by decide)).trans h.zero
    | exact (f _ (by decide)).trans h.one
    | exact (f _ (by decide)).trans h.two

/-- Actual scratch-setting blocks have no heap, root or output effects. -/
theorem pure_frame (K A d C : ℕ) (b : List Op) (s : State)
    (hb:b=fftSetup ∨ b=copySetup ∨ b=finish ∨ b=rootSetup ∨ b=powerSetup) : Frame K A d C s (applyBlock b s) := by
  rcases hb with rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,?_⟩
  all_goals intro r hr
  all_goals simp only [Persistent] at hr
  all_goals simp (disch:=omega) [fftSetup,copySetup,finish,rootSetup,powerSetup,applyBlock,Op.apply,writeNat,next]

theorem pure_controls (b : List Op) (s : State) (hb:b=fftSetup ∨ b=copySetup ∨ b=rootSetup ∨ b=powerSetup) :
    ControlRegs s (applyBlock b s) := by
  rcases hb with rfl|rfl|rfl|rfl
  all_goals intro r hr
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  all_goals simp (disch:=omega) [fftSetup,copySetup,rootSetup,powerSetup,applyBlock,Op.apply,writeNat,next]

theorem suffix_get (i : ℕ) : program[244+i]?=suffix[i]? := by
  unfold program embed
  rw [List.getElem?_append_right (by
    simp only [List.length_append,List.length_map,controllerHead_length,UniformFFTInputMachine.combinedProgram_length];omega)]
  simp only [List.length_append,List.length_map,controllerHead_length,UniformFFTInputMachine.combinedProgram_length]
  rw [show 244+i-(23+221)=i by omega]

theorem fftSetup_at : BlockAt fftSetup program 16 := by
  intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem copySetup_at : BlockAt copySetup program 244 := by
  intro i hi;rw [suffix_get];change i < 4 at hi;interval_cases i <;> rfl
theorem finish_at : BlockAt finish program 258 := by
  intro i hi;rw [show 258+i=244+(14+i) by omega,suffix_get]
  change i < 1 at hi;interval_cases i;rfl
theorem rootSetup_at : BlockAt rootSetup program 260 := by
  intro i hi;rw [show 260+i=244+(16+i) by omega,suffix_get]
  change i < 5 at hi;interval_cases i <;> rfl
theorem powerSetup_at : BlockAt powerSetup program 282 := by
  intro i hi;rw [show 282+i=244+(38+i) by omega,suffix_get]
  change i < 3 at hi;interval_cases i <;> rfl

theorem source_address_bound (K S A : ℕ) (he:S+6*width K ≤ A) (b : Fin 6) (j : Fin (width K)) :
    S+b.val*width K+j.val < A := by
  have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt b.isLt)
  rw [Nat.succ_mul] at hm;have :=j.isLt;omega

theorem padded_self (K : ℕ) (values : Fin (width K)→ℂ) (j : Fin (width K)) :
    UniformFFTInputMachine.padded K (width K) (fun i=>prepared (values i)) j=prepared (values j) := by
  simp [UniformFFTInputMachine.padded,UniformFFTInputMachine.paddedAt,j.isLt]

/-- No scalar expression or prepared spectrum is supplied to the FFT call. -/
def SpectraPrefix (K C i : ℕ) (values : Fin 6→Fin (width K)→ℂ) (s : State) : Prop :=
  ∀b : Fin 6,b.val < i →∀j : Fin (width K),s.scalarHeap (C+width K+b.val*width K+j.val)=
    some (prepared ((fourierMatrix (width K)).mulVec (values b) j))

theorem fftSetup_spec {K S A d C D i : ℕ} (s : State) (h:Context K S A d C D i s) :
    Context K S A d C D i (applyBlock fftSetup s) ∧
    (applyBlock fftSetup s).natReg 175=S+i*width K ∧
    (applyBlock fftSetup s).natReg 70=K ∧ (applyBlock fftSetup s).natReg 174=width K ∧
    (applyBlock fftSetup s).natReg 176=1 ∧ (applyBlock fftSetup s).natReg 122=A ∧
    (applyBlock fftSetup s).natReg 107=d ∧ (applyBlock fftSetup s).natReg 537=i*width K := by
  refine ⟨h.transport (pure_controls fftSetup s (Or.inl rfl)),?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [fftSetup,applyBlock,Op.apply,writeNat,next,h.header.height,h.header.kernels,
    h.header.arena,h.header.rows,h.width,h.index,h.zero,h.one]

theorem fftSetup_safe {K S A d C D i B : ℕ} (s : State) (h:Context K S A d C D i s)
    (hi:i < 6) (layout:Layout K S A d C D B) (hs:WordBound B s) :
    readable fftSetup s ∧ peak fftSetup s ≤ B := by
  have bounds:=layout.bounds
  have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  have hend:=layout.sourceEnd
  have hb: A ≤ B:=by have :=(UniformPreparedFFTMachine.wordBudget_bounds K A d B bounds.2.2.2.1).2.1;omega
  have hd: d ≤ B:=by have :=(UniformPreparedFFTMachine.wordBudget_bounds K A d B bounds.2.2.2.1).2.2.1;omega
  have hk:K ≤ B:=by simpa [h.header.height] using hs.2.1 525
  simp [fftSetup,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    h.header.height,h.header.kernels,h.header.arena,h.header.rows,h.width,h.index,h.zero,h.one]
  omega


theorem fft_controls {s t : State}
    (f:∀r,UniformFFTInputMachine.CombinedPersistent r →t.natReg r=s.natReg r) : ControlRegs s t := by
  intro r hr
  apply f
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [UniformFFTInputMachine.CombinedPersistent,UniformPreparedFFTMachine.Persistent]
  omega

theorem fft_persistent {s t : State}
    (f:∀r,UniformFFTInputMachine.CombinedPersistent r →t.natReg r=s.natReg r)
    (r : ℕ) (hr:Persistent r) : t.natReg r=s.natReg r := by
  apply f
  simp only [UniformFFTInputMachine.CombinedPersistent,UniformPreparedFFTMachine.Persistent]
  simp only [Persistent] at hr
  omega

theorem copy_controls {s t : State} (f:UniformScalarCopyMachine.NatFrame s t) : ControlRegs s t := by
  intro r hr;apply f
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  omega

theorem copy_persistent {s t : State} (f:UniformScalarCopyMachine.NatFrame s t) (r : ℕ) (hr:Persistent r) :
    t.natReg r=s.natReg r := by apply f;simp only [Persistent] at hr;omega

theorem Header.frame {K S A d C D : ℕ} {s t : State} (h:Header K S A d C D s) (f:Frame K A d C s t) :
    Header K S A d C D t := by
  constructor
  all_goals first
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.height
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.kernels
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.arena
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.rows
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.bank
    | exact (f.2.2.2.2 _ (by simp [Persistent])).trans h.order

theorem Layout.arena_le_bank {K S A d C D B : ℕ} (h:Layout K S A d C D B) : A ≤ C := by
  have :=h.bankAfter
  unfold UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at this
  omega

theorem Kernels.frame {K S A d C D B : ℕ} {values : Fin 6→Fin (width K)→ℂ} {s t : State}
    (h:Kernels K S values s) (frame:Frame K A d C s t) (layout:Layout K S A d C D B) : Kernels K S values t := by
  intro b j
  have bound:=source_address_bound K S A layout.sourceEnd b j
  exact (frame.2.1 _ (Or.inl bound) (Or.inl (bound.trans_le layout.arena_le_bank))).trans (h b j)

/-- Actual gathered, prepared-input FFT: both original kernels and previously
copied spectra lie outside the physical FFT arena. -/
theorem fft_call (n K S A d C D B i : ℕ) (values : Fin 6→Fin (width K)→ℂ) (x : Fin n→ℂ) (s : State)
    (ctx:Context K S A d C D i s) (hi:i < 6) (layout:Layout K S A d C D B) (kernels:Kernels K S values s)
    (root:s.scalarHeap 0=some (prepared (zeta D)))
    (h175:s.natReg 175=S+i*width K) (h70:s.natReg 70=K) (h174:s.natReg 174=width K)
    (h176:s.natReg 176=1) (h122:s.natReg 122=A) (h107:s.natReg 107=d)
    (pc:s.pc=23) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 4*K+10*width K+9+UniformPreparedFFTMachine.runtime D K ∧
    Context K S A d C D i u ∧
    (∀j : Fin (width K),u.scalarHeap (A+count K+j.val)=some
      (prepared ((fourierMatrix (width K)).mulVec (values ⟨i,hi⟩) j))) ∧
    (∀q,q < A ∨ UniformPreparedFFTMachine.rootAddress K A+1 ≤ q →u.scalarHeap q=s.scalarHeap q) ∧
    Frame K A d C s u ∧ Kernels K S values u ∧ u.natReg 537=s.natReg 537 ∧ u.pc=244 := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by omega)
  have source:UniformFFTInputMachine.Source (width K) (S+i*width K) 1 (fun j=>prepared (values ⟨i,hi⟩ j)) e:=by
    intro j;simpa only [Nat.one_mul,e,setPC] using kernels ⟨i,hi⟩ j
  have sourceEnd:S+i*width K+1*width K ≤ A:=by
    have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hm;have :=layout.sourceEnd;omega
  have bounds:=layout.bounds
  obtain ⟨v,t,run,ht,out,_,natFrame,scalarFrame,outputs,roots,regs,_⟩:=
    UniformFFTInputMachine.combined_execution n K (width K) (S+i*width K) 1 A d D B x
      (fun j=>prepared (values ⟨i,hi⟩ j)) e source le_rfl sourceEnd layout.arenaPositive (by omega)
      rfl h70 h174 h175 h176 h122 h107 ctx.header.order root layout.orderPositive layout.divisor bounds.2.2.2.1 eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed fft_code
    (by rw [UniformFFTInputMachine.combinedProgram_length];omega) (by omega) run
  have pe:placed 23 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 244
  have newCtx:Context K S A d C D i u:=
    (ctx.withPC.transport (fft_controls regs)).withPC
  have outPrepared:=UniformFFTInputMachine.combined_output_prepared K (width K) A
    (fun j=>prepared (values ⟨i,hi⟩ j)) v (fun _=>rfl) out
  have fr:Frame K A d C s u:=
    ⟨natFrame,fun q hq _=>scalarFrame q hq,outputs,roots,fun r hr=>fft_persistent regs r hr⟩
  refine ⟨u,t,placedRun,by omega,newCtx,?_,scalarFrame,fr,kernels.frame fr layout,
    regs 537 (by simp [UniformFFTInputMachine.CombinedPersistent,UniformPreparedFFTMachine.Persistent]),rfl⟩
  have ps:UniformFFTInputMachine.padded K (width K) (fun j=>prepared (values ⟨i,hi⟩ j))=
      (fun j=>prepared (values ⟨i,hi⟩ j)):=funext (padded_self K (values ⟨i,hi⟩))
  rw [ps] at outPrepared
  intro j
  exact outPrepared j


theorem copySetup_spec {K S A d C D i : ℕ} (s : State) (ctx:Context K S A d C D i s)
    (offset:s.natReg 537=i*width K) :
    Context K S A d C D i (applyBlock copySetup s) ∧
    (applyBlock copySetup s).natReg 147=width K ∧
    (applyBlock copySetup s).natReg 148=A+count K ∧
    (applyBlock copySetup s).natReg 149=C+width K+i*width K := by
  refine ⟨ctx.transport (pure_controls copySetup s (Or.inr (Or.inl rfl))),?_,?_,?_⟩
  all_goals simp [copySetup,applyBlock,Op.apply,writeNat,next,ctx.width,ctx.count,
    ctx.header.arena,ctx.header.bank,ctx.zero,offset]

theorem copySetup_safe {K S A d C D i B : ℕ} (s : State) (ctx:Context K S A d C D i s)
    (offset:s.natReg 537=i*width K) (hi:i < 6) (layout:Layout K S A d C D B) :
    readable copySetup s ∧ peak copySetup s ≤ B := by
  have bounds:=layout.bounds;have rootAfter:=layout.bankAfter
  unfold UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at rootAfter
  have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  simp [copySetup,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    ctx.width,ctx.count,ctx.header.arena,ctx.header.bank,ctx.zero,offset]
  omega

/-- The source premise here is an actual physical FFT output, discharged by
fft_call in the whole driver; it is not an original caller spectrum bank. -/
theorem copy_call (n K S A d C D B i : ℕ) (values : Fin 6→Fin (width K)→ℂ) (x : Fin n→ℂ) (s : State)
    (ctx:Context K S A d C D i s) (hi:i < 6) (layout:Layout K S A d C D B)
    (out:∀j : Fin (width K),s.scalarHeap (A+count K+j.val)=some
      (prepared ((fourierMatrix (width K)).mulVec (values ⟨i,hi⟩) j)))
    (h147:s.natReg 147=width K) (h148:s.natReg 148=A+count K)
    (h149:s.natReg 149=C+width K+i*width K) (pc:s.pc=248) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (7*width K+4) u ∧ Context K S A d C D i u ∧
    (∀j : Fin (width K),u.scalarHeap (C+width K+i*width K+j.val)=some
      (prepared ((fourierMatrix (width K)).mulVec (values ⟨i,hi⟩) j))) ∧
    UniformScalarCopyMachine.Outside (C+width K+i*width K) (width K) s.scalarHeap u ∧
    Frame K A d C s u ∧ u.pc=258 := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by omega)
  have bounds:=layout.bounds
  have present:UniformScalarCopyMachine.Source (width K) (A+count K) e.scalarHeap:=by
    intro j hj;exact ⟨prepared ((fourierMatrix (width K)).mulVec (values ⟨i,hi⟩) ⟨j,hj⟩),out ⟨j,hj⟩⟩
  have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  have after:=layout.bankAfter
  unfold UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at after
  have disjoint:A+count K+width K ≤ C+width K+i*width K:=by omega
  have endBound:C+width K+i*width K+width K ≤ B:=by omega
  obtain ⟨v,run,copied,_,outside,frame,natFrame⟩:=UniformScalarCopyMachine.execution n x
    (width K) (A+count K) (C+width K+i*width K) B e present disjoint endBound (by omega)
    rfl h147 h148 h149 eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed copy_code
    (by rw [UniformScalarCopyMachine.program_length];omega) (by omega) run
  have pe:placed 248 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 258
  have newCtx:Context K S A d C D i u:=
    (ctx.withPC.transport (copy_controls natFrame)).withPC
  have fr:Frame K A d C s u:=by
    refine ⟨fun q _=>congrFun frame.1 q,?_,frame.2.1,frame.2.2.1,
      fun r hr=>copy_persistent natFrame r hr⟩
    intro q _ hq
    exact outside q (by rcases hq with hq|hq <;> omega)
  refine ⟨u,placedRun,newCtx,?_,outside,fr,rfl⟩
  intro j
  exact (copied j.val j.isLt).trans (out j)

theorem finish_spec {K S A d C D i : ℕ} (s : State) (ctx:Context K S A d C D i s) :
    Context K S A d C D (i+1) (applyBlock finish s) := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [finish,applyBlock,Op.apply,writeNat,next,ctx.header.height,ctx.header.kernels,
    ctx.header.arena,ctx.header.rows,ctx.header.bank,ctx.header.order,
    ctx.width,ctx.count,ctx.index,ctx.slots,ctx.zero,ctx.one,ctx.two]


def iterationBudget (D K : ℕ) :=
  7+(4*K+10*width K+9+UniformPreparedFFTMachine.runtime D K)+4+(7*width K+4)+3

theorem SpectraPrefix.transport {K C i : ℕ} {values : Fin 6→Fin (width K)→ℂ}
    {s u : State} (h:SpectraPrefix K C i values s)
    (f:∀b : Fin 6,b.val < i →∀j : Fin (width K),
      u.scalarHeap (C+width K+b.val*width K+j.val)=s.scalarHeap (C+width K+b.val*width K+j.val)) :
    SpectraPrefix K C i values u := by
  intro b hb j;exact (f b hb j).trans (h b hb j)

theorem spectrum_after_arena {K S A d C D B : ℕ} (layout:Layout K S A d C D B)
    (b : Fin 6) (j : Fin (width K)) :
    UniformPreparedFFTMachine.rootAddress K A+1 ≤ C+width K+b.val*width K+j.val := by
  have :=layout.bankAfter;omega

theorem Frame.master {K A d C : ℕ} {s u : State} (f:Frame K A d C s u)
    (hA:0 < A) (hC:0 < C) : u.scalarHeap 0=s.scalarHeap 0 :=
  f.2.1 0 (Or.inl hA) (Or.inl hC)

/-- One actual FFT and copy iteration. The spectrum source is generated inside
this execution, and every branch, setup and continuation is charged. -/
theorem loop_iteration (n K S A d C D B i : ℕ) (values : Fin 6→Fin (width K)→ℂ)
    (x : Fin n→ℂ) (s : State) (cur:LoopCursor K S A d C D i s)
    (hi:i < 6) (layout:Layout K S A d C D B) (kernels:Kernels K S values s)
    (master:s.scalarHeap 0=some (prepared (zeta D)))
    (pfx:SpectraPrefix K C i values s) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ iterationBudget D K ∧
    LoopCursor K S A d C D (i+1) u ∧ Kernels K S values u ∧
    SpectraPrefix K C (i+1) values u ∧ Frame K A d C s u := by
  have bounds:=layout.bounds
  let e:=setPC s 16
  have enter:=UniformRadixInstructionMachine.branch_runs program n B 535 536 16 260 x s hs
    (by omega) (by omega) (by rw [cur.pc];exact loop_branch)
  have cmp:s.natReg 535 < s.natReg 536:=by rw [cur.index,cur.slots];exact hi
  simp only [cmp,ite_true] at enter
  have eb:WordBound B e:=enter.final_bound
  have ec:=cur.context.withPC (pc:=16)
  have safe:=fftSetup_safe e ec hi layout eb
  have setup:=block_runs fftSetup program 16 n B x e fftSetup_at rfl eb
    (by change 16+7 ≤ B;omega) safe.1 safe.2
  let v:=applyBlock fftSetup e
  have vc:=fftSetup_spec e ec
  have vf:Frame K A d C s v:=(pure_frame K A d C fftSetup e (Or.inl rfl))
  have vk:=kernels.frame vf layout
  have Cpos:0 < C:=lt_of_lt_of_le layout.arenaPositive layout.arena_le_bank
  have vm:v.scalarHeap 0=some (prepared (zeta D)):=(vf.master layout.arenaPositive Cpos).trans master
  have vp:v.pc=23:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  obtain ⟨w,t,fft,tc,wc,wout,woutside,wf,wk,woff,wp⟩:=fft_call n K S A d C D B i values x v
    vc.1 hi layout vk vm vc.2.1 vc.2.2.1 vc.2.2.2.1 vc.2.2.2.2.1
    vc.2.2.2.2.2.1 vc.2.2.2.2.2.2.1 vp setup.final_bound
  have offset:w.natReg 537=i*width K:=woff.trans vc.2.2.2.2.2.2.2
  have wprefix:SpectraPrefix K C i values w:=pfx.transport (by
    intro b hb j
    exact (woutside _ (Or.inr (spectrum_after_arena layout b j))).trans rfl)
  have csafe:=copySetup_safe w wc offset hi layout
  have copyStart:=block_runs copySetup program 244 n B x w copySetup_at wp fft.final_bound
    (by change 244+4 ≤ B;omega) csafe.1 csafe.2
  let z:=applyBlock copySetup w
  have zc:=copySetup_spec w wc offset
  have zp:z.pc=248:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
  have zout:∀j : Fin (width K),z.scalarHeap (A+count K+j.val)=some
      (prepared ((fourierMatrix (width K)).mulVec (values ⟨i,hi⟩) j)):=wout
  obtain ⟨q,copy,qc,qout,qoutside,qf,qp⟩:=copy_call n K S A d C D B i values x z zc.1 hi layout
    zout zc.2.1 zc.2.2.1 zc.2.2.2 zp copyStart.final_bound
  have qpfx:SpectraPrefix K C (i+1) values q:=by
    intro b hb j
    by_cases eq:b.val=i
    · have beq:b=⟨i,hi⟩:=Fin.ext eq
      simpa only [beq,eq] using qout j
    · have old:b.val < i:=by omega
      have mul:=Nat.mul_le_mul_right (width K) (show b.val+1 ≤ i by omega)
      rw [Nat.add_mul,Nat.one_mul] at mul
      have outside:C+width K+b.val*width K+j.val < C+width K+i*width K:=by have :=j.isLt;omega
      exact (qoutside _ (Or.inl outside)).trans (wprefix b old j)
  have fsafe:readable finish q ∧ peak finish q ≤ B:=by
    simp [readable,finish,Op.readable,peak,Op.peak,qc.index,qc.one]
    omega
  have done:=block_runs finish program 258 n B x q finish_at qp copy.final_bound
    (by change 258+1 ≤ B;omega) fsafe.1 fsafe.2
  let r:=applyBlock finish q
  have rp:r.pc=259:=by rw [UniformTensorMonomialMachine.applyBlock_pc,qp];rfl
  have jump:=UniformRadixInstructionMachine.jump_runs program n B 15 x r done.final_bound
    (by omega) (by rw [rp];exact loop_jump)
  let u:=setPC r 15
  have uc:LoopCursor K S A d C D (i+1) u:=(finish_spec q qc).withPC.cursor rfl
  have fr:Frame K A d C s u:=vf.trans (wf.trans ((pure_frame K A d C copySetup w (Or.inr (Or.inl rfl))).trans
    (qf.trans (pure_frame K A d C finish q (Or.inr (Or.inr (Or.inl rfl))))))).withPC
  refine ⟨u,1+7+t+4+(7*width K+4)+1+1,?_,?_,uc,kernels.frame fr layout,qpfx,fr⟩
  · convert enter.trans (setup.trans (fft.trans (copyStart.trans (copy.trans (done.trans jump))))) using 1
    simp only [show fftSetup.length=7 from rfl,show copySetup.length=4 from rfl,show finish.length=1 from rfl]
    all_goals first | omega | rfl
  · unfold iterationBudget;omega



/-- The six spectra are obtained by the fixed loop, rather than supplied in its
postcondition or in the original input contract. -/
theorem spectra_loop (n K S A d C D B i remaining : ℕ)
    (values : Fin 6→Fin (width K)→ℂ) (x : Fin n→ℂ) (s : State)
    (cur:LoopCursor K S A d C D i s) (hremain:i+remaining=6)
    (layout:Layout K S A d C D B) (kernels:Kernels K S values s)
    (master:s.scalarHeap 0=some (prepared (zeta D)))
    (pfx:SpectraPrefix K C i values s) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ remaining*iterationBudget D K+1 ∧
    Context K S A d C D 6 u ∧ u.pc=260 ∧ Kernels K S values u ∧
    SpectraPrefix K C 6 values u ∧ Frame K A d C s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i=6:=by omega
    subst i
    have bounds:=layout.bounds
    have branch:=UniformRadixInstructionMachine.branch_runs program n B 535 536 16 260 x s hs
      (by omega) (by omega) (by rw [cur.pc];exact loop_branch)
    have cmp:¬s.natReg 535 < s.natReg 536:=by rw [cur.index,cur.slots];omega
    simp only [cmp,ite_false] at branch
    exact ⟨setPC s 260,1,branch,by omega,cur.context.withPC,rfl,kernels,pfx,(Frame.refl K A d C s).withPC⟩
  | succ remaining ih =>
    obtain ⟨v,t,run,tc,vc,vk,vp,vf⟩:=loop_iteration n K S A d C D B i values x s cur
      (by omega) layout kernels master pfx hs
    have cp:0 < C:=lt_of_lt_of_le layout.arenaPositive layout.arena_le_bank
    have vm:v.scalarHeap 0=some (prepared (zeta D)):=(vf.master layout.arenaPositive cp).trans master
    obtain ⟨u,t',run',tc',uc,up,uk,ux,uf⟩:=ih (i+1) v vc (by omega) vk vm vp run.final_bound
    refine ⟨u,t+t',run.trans run',?_,uc,up,uk,ux,vf.trans uf⟩
    rw [Nat.succ_mul]
    omega

theorem rootSetup_spec {K S A d C D i : ℕ} (s : State) (ctx:Context K S A d C D i s) :
    Context K S A d C D i (applyBlock rootSetup s) ∧
    (applyBlock rootSetup s).natReg 140=C+7*width K ∧
    (applyBlock rootSetup s).natReg 141=width K ∧
    (applyBlock rootSetup s).natReg 537=C+7*width K := by
  refine ⟨ctx.transport (pure_controls rootSetup s (Or.inr (Or.inr (Or.inl rfl)))),?_,?_,?_⟩
  all_goals simp [rootSetup,applyBlock,Op.apply,writeNat,next,ctx.width,ctx.header.bank,ctx.zero]
  all_goals omega

theorem rootSetup_safe {K S A d C D i B : ℕ} (s : State) (ctx:Context K S A d C D i s)
    (layout:Layout K S A d C D B) : readable rootSetup s ∧ peak rootSetup s ≤ B := by
  have bounds:=layout.bounds
  simp [readable,rootSetup,Op.readable,peak,Op.peak,Op.apply,writeNat,next,ctx.width,ctx.header.bank,ctx.zero]
  omega

theorem root_controls {s u : State} (f:UniformRootExtractionMachine.Frame s u) : ControlRegs s u := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  exact f.2.2.2.2 r (by omega) (by omega)

theorem root_persistent {s u : State} (f:UniformRootExtractionMachine.Frame s u) :
    ∀r,Persistent r→u.natReg r=s.natReg r := by
  intro r hr;simp only [Persistent] at hr
  exact f.2.2.2.2 r (by omega) (by omega)

/-- The canonical dyadic root is extracted from the retained master cell;
this call issues no root request. -/
theorem root_call (n K S A d C D B : ℕ) (x : Fin n→ℂ) (s : State)
    (ctx:Context K S A d C D 6 s) (layout:Layout K S A d C D B)
    (master:s.scalarHeap 0=some (prepared (zeta D)))
    (h140:s.natReg 140=C+7*width K) (h141:s.natReg 141=width K)
    (hp:s.pc=265) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (9+UniformPowerMachine.loopCost (D/width K)) u ∧
    Context K S A d C D 6 u ∧ u.pc=282 ∧
    u.scalarHeap (C+7*width K)=some (prepared (zeta (width K))) ∧
    (∀q,q≠C+7*width K→u.scalarHeap q=s.scalarHeap q) ∧
    Frame K A d C s u ∧ u.natReg 537=s.natReg 537 := by
  let e:=setPC s 0
  have bounds:=layout.bounds
  have eb:=changePC_bound B s 0 hs (by omega)
  have Npos:0 < width K:=width_pos K
  obtain ⟨v,run,root,outside,fr,vp⟩:=UniformRootExtractionMachine.execution n D (width K)
    (C+7*width K) B x e rfl ctx.header.order h141 h140 layout.orderPositive Npos layout.divisor
    master (by omega) eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed root_code
    (by rw [UniformRootExtractionMachine.program_length];omega) (by omega) run
  have pe:placed 265 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 282
  have newCtx:Context K S A d C D 6 u:=(ctx.withPC.transport (root_controls fr)).withPC
  have frame:Frame K A d C s u:=by
    refine ⟨fun q _=>congrFun fr.1 q,?_,fr.2.1,fr.2.2.1,fun r hr=>root_persistent fr r hr⟩
    intro q _ hq
    exact outside q (by rcases hq with hq|hq <;> omega)
  exact ⟨u,placedRun,newCtx,rfl,root,outside,frame,fr.2.2.2.2 537 (by omega) (by omega)⟩

theorem powerSetup_spec {K S A d C D i : ℕ} (s : State) (ctx:Context K S A d C D i s)
    (offset:s.natReg 537=C+7*width K) :
    Context K S A d C D i (applyBlock powerSetup s) ∧
    UniformContiguousPowerBankMachine.Header (width K) (C+7*width K) C (applyBlock powerSetup s) := by
  refine ⟨ctx.transport (pure_controls powerSetup s (Or.inr (Or.inr (Or.inr rfl)))),?_,?_,?_⟩
  all_goals simp [powerSetup,applyBlock,Op.apply,writeNat,next,ctx.width,ctx.zero,ctx.header.bank,offset]

theorem powerSetup_safe {K S A d C D i B : ℕ} (s : State) (ctx:Context K S A d C D i s)
    (offset:s.natReg 537=C+7*width K) (layout:Layout K S A d C D B) :
    readable powerSetup s ∧ peak powerSetup s ≤ B := by
  have bounds:=layout.bounds
  simp [readable,powerSetup,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    ctx.width,ctx.zero,ctx.header.bank,offset]
  omega

theorem power_controls {s u : State} (f:UniformContiguousPowerBankMachine.Frame s u) : ControlRegs s u := by
  intro r hr;simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  exact f.2.2.2.1 r (by omega)

theorem power_persistent {s u : State} (f:UniformContiguousPowerBankMachine.Frame s u) :
    ∀r,Persistent r→u.natReg r=s.natReg r := by
  intro r hr;simp only [Persistent] at hr
  exact f.2.2.2.1 r (by omega)

theorem power_call (n K S A d C D B : ℕ) (x : Fin n→ℂ) (s : State)
    (ctx:Context K S A d C D 6 s) (layout:Layout K S A d C D B)
    (hh:UniformContiguousPowerBankMachine.Header (width K) (C+7*width K) C s)
    (root:s.scalarHeap (C+7*width K)=some (prepared (zeta (width K))))
    (hp:s.pc=285) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (6*width K+6) u ∧ Context K S A d C D 6 u ∧ u.pc=296 ∧
    (∀j : Fin (width K),u.scalarHeap (C+j.val)=some (prepared (zeta (width K)^j.val))) ∧
    UniformContiguousPowerBankMachine.Outside C (width K) s u ∧ Frame K A d C s u := by
  let e:=setPC s 0
  have bounds:=layout.bounds
  have eb:=changePC_bound B s 0 hs (by omega)
  obtain ⟨v,run,powers,outside,fr,_,vp⟩:=UniformContiguousPowerBankMachine.execution
    (width K) (C+7*width K) C B n x (zeta (width K)) e
    ⟨hh.length,hh.source,hh.target⟩ rfl root (by omega) (by omega) eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed power_code
    (by rw [UniformContiguousPowerBankMachine.program_length];omega) (by omega) run
  have pe:placed 285 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 296
  have newCtx:Context K S A d C D 6 u:=(ctx.withPC.transport (power_controls fr)).withPC
  have frame:Frame K A d C s u:=by
    refine ⟨fun q _=>congrFun fr.1 q,?_,fr.2.1,fr.2.2.1,fun r hr=>power_persistent fr r hr⟩
    intro q _ hq
    exact outside q (by rcases hq with hq|hq <;> omega)
  exact ⟨u,placedRun,newCtx,rfl,fun j=>powers j.val j.isLt,outside,frame⟩



theorem spectrum_address_end (K C : ℕ) (b : Fin 6) (j : Fin (width K)) :
    C+width K+b.val*width K+j.val < C+7*width K := by
  have hm:=Nat.mul_le_mul_right (width K) (Nat.succ_le_of_lt b.isLt)
  rw [Nat.succ_mul] at hm;have :=j.isLt;omega

theorem Result.of_parts {K C : ℕ} {values : Fin 6→Fin (width K)→ℂ} {s : State}
    (powers:∀j : Fin (width K),s.scalarHeap (C+j.val)=some (prepared (zeta (width K)^j.val)))
    (spectra:SpectraPrefix K C 6 values s) : Result K C values s := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [UniformToeplitzCrossDAG.sharedBank,Fin.addCases_left,Fin.val_castAdd] using powers i
  · intro i
    let bj:=finProdFinEquiv.symm i
    have hv:bj.1.val*width K+bj.2.val=i.val:=by
      have h:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
      change bj.2.val+width K*bj.1.val=i.val at h
      simpa only [Nat.mul_comm,Nat.add_comm] using h
    have out:=spectra bj.1 bj.1.isLt bj.2
    simpa only [UniformToeplitzCrossDAG.sharedBank,Fin.addCases_right,Fin.val_natAdd,
      Nat.add_assoc,hv] using out

/-- One literal 297-instruction program computes all seven banks from the six
physical original kernels and the existing canonical master root. There is no
spectrum, power-table, root-request or helper-postcondition input premise. -/
theorem execution (n K S A d C D B : ℕ) (values : Fin 6→Fin (width K)→ℂ)
    (x : Fin n→ℂ) (s : State) (header:Header K S A d C D s)
    (layout:Layout K S A d C D B) (kernels:Kernels K S values s)
    (master:s.scalarHeap 0=some (prepared (zeta D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget D K ∧
    Result K C values u ∧ Kernels K S values u ∧ Header K S A d C D u ∧
    Frame K A d C s u ∧ u.scalarHeap 0=s.scalarHeap 0 ∧ u.pc=296 := by
  have bounds:=layout.bounds
  have Cpos:0<C:=lt_of_lt_of_le layout.arenaPositive layout.arena_le_bank
  obtain ⟨v,init,vc,vf⟩:=initialize_driver n K S A d C D B x s header hp hs
    bounds.1 bounds.2.1 bounds.2.2.1
  have initialFrame:Frame K A d C s v:=vf.frame
  have vk:=kernels.frame initialFrame layout
  have vm:v.scalarHeap 0=some (prepared (zeta D)):=(initialFrame.master layout.arenaPositive Cpos).trans master
  have pfx:SpectraPrefix K C 0 values v:=by intro b hb;omega
  obtain ⟨w,t,loop,tc,wc,wp,wk,ws,wf⟩:=spectra_loop n K S A d C D B 0 6 values x v vc
    (by omega) layout vk vm pfx init.final_bound
  have safe:=rootSetup_safe w wc layout
  have startRoot:=block_runs rootSetup program 260 n B x w rootSetup_at wp loop.final_bound
    (by change 260+5≤B;omega) safe.1 safe.2
  let z:=applyBlock rootSetup w
  have zc:=rootSetup_spec w wc
  have zp:z.pc=265:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
  have zf:Frame K A d C s z:=initialFrame.trans (wf.trans
    (pure_frame K A d C rootSetup w (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have zm:z.scalarHeap 0=some (prepared (zeta D)):=(zf.master layout.arenaPositive Cpos).trans master
  obtain ⟨q,root,qc,qp,qr,qoutside,qf,qoff⟩:=root_call n K S A d C D B x z zc.1 layout
    zm zc.2.1 zc.2.2.1 zp startRoot.final_bound
  have qo:q.natReg 537=C+7*width K:=qoff.trans zc.2.2.2
  have qs:SpectraPrefix K C 6 values q:=ws.transport (by
    intro b hb j
    exact qoutside _ (ne_of_lt (spectrum_address_end K C b j)))
  have psafe:=powerSetup_safe q qc qo layout
  have startPower:=block_runs powerSetup program 282 n B x q powerSetup_at qp root.final_bound
    (by change 282+3≤B;omega) psafe.1 psafe.2
  let r:=applyBlock powerSetup q
  have rc:=powerSetup_spec q qc qo
  have rp:r.pc=285:=by rw [UniformTensorMonomialMachine.applyBlock_pc,qp];rfl
  obtain ⟨u,power,uc,up,upowers,uoutside,uf⟩:=power_call n K S A d C D B x r rc.1 layout
    rc.2 qr rp startPower.final_bound
  have us:SpectraPrefix K C 6 values u:=qs.transport (by
    intro b hb j
    exact uoutside _ (Or.inr (by omega)))
  have frame:Frame K A d C s u:=zf.trans (qf.trans
    ((pure_frame K A d C powerSetup q (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans uf))
  have stop:BoundedExecution program n x B u 1 u:=.halt power.final_bound
    (by simp only [step,up,final_halt])
  refine ⟨u,4*K+12+t+5+(9+UniformPowerMachine.loopCost (D/width K))+3+(6*width K+6)+1,
    ?_,?_,Result.of_parts upowers us,kernels.frame frame layout,uc.header,frame,
    frame.master layout.arenaPositive Cpos,up⟩
  · convert init.executes (loop.executes (startRoot.executes (root.executes (startPower.executes (power.executes stop))))) using 1
    simp only [show rootSetup.length=5 from rfl,show powerSetup.length=3 from rfl]
    omega
  · unfold runtimeBudget iterationBudget at *
    omega



theorem runtime_log_bound (D K : ℕ) : runtimeBudget D K ≤
    6*(19*K+85)*count K+52*K+156*width K+49*(Nat.log2 (D+1)+1)+519 := by
  have fft:=UniformPreparedFFTMachine.runtime_log_bound D K
  have root:=UniformRootExtractionMachine.runtime_log_bound D (width K)
  unfold runtimeBudget
  nlinarith


end
end ExactFourierCircuits.UniformKernelSpectrumMachine
