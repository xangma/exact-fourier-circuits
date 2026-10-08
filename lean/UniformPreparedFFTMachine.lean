import UniformOffsetLinearMachine
import UniformRootExtractionMachine
import UniformContext
import UniformGlobalLocalPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedFFTMachine
open UniformMachine UniformAssembly UniformRadixTwoDAG OAI.ExactFourier

/- The table printer's actual construction also certifies retained width/count
registers. This proof uses its literal sizing loop, not an assumed ready table. -/
section
open UniformRadixRowTableMachine
open UniformRadixInstructionMachine (cap block block_runs block_pc AOp peakBlock cap_linear count_div)
theorem row_execution_context (n K d a B:ℕ) (x:Fin n→ℂ) (s:State)
    (hp:s.pc=0) (hk:s.natReg 70=K) (hd:s.natReg 107=d) (ha:s.natReg 122=a)
    (hs:WordBound B s) (hscalar:a+cap (width K) (count K) K≤B) (htable:d+3*count K≤B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤(19*K+63)*count K+4*K+16 ∧
    Printed K d a (count K) u ∧ Outside d (3*count K) s.natHeap u ∧ Preserved s u ∧
    Context K d a (count K) u := by
  have hcap:cap (width K) (count K) K≤B:=by omega
  have hc:114≤B:=(code_bound K).trans hcap
  have hsetup:=block_runs setup program 0 n B x s setup_at hp hs (by change 0+7≤B;omega)
    (setup_valid s) (by rw [setup_peak];omega)
  have hsi:=setup_spec K d a s hk hd ha
  have hsp:(block setup s).pc=7:=by rw [block_pc,hp];rfl
  obtain ⟨v,hv,hvi,hvp,hvheap⟩:=initialize_loop n K d a 0 K B x (block setup s) hsi (by omega) hsetup.final_bound hcap hsp
  have hwidth:width K≤cap (width K) (count K) K:=by have:=cap_linear (width K) (count K) K;omega
  have hsizePeak:peakBlock sizes v≤B:=by
    have he:3*K*width K=2*count K:=by have:=count_exact K;omega
    have hl:=cap_linear (width K) (count K) K
    simp [peakBlock,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,hvi.height,hvi.base,hvi.Nreg,hvi.zero,hvi.two,hvi.three,count_div]
    all_goals omega
  have hsize:=block_runs sizes program 11 n B x v sizes_at hvp hv.final_bound
    (by change 11+6≤B;omega) (sizes_valid v hvi.two) hsizePeak
  have hsizei:=sizes_spec K d a v hvi
  have hsizep:(block sizes v).pc=17:=by rw [block_pc,hvp];rfl
  have hsizeheap:(block sizes v).natHeap=s.natHeap:=
    (block_heap sizes v).trans (hvheap.trans (block_heap setup s))
  obtain ⟨u,t,hu,ht,hui,hup,huo⟩:=rows_loop n K d a 0 (count K) B x (block sizes v) s.natHeap hsizei (by omega)
    hsize.final_bound hscalar htable hsizep (by intro q hq;omega)
    (by intro i hi;rw [hsizeheap])
  have hAll:BoundedExecution program n x B s (7+(4*K+1)+(6+t)) u:=by
    convert hsetup.executes (hv.executes (hsize.executes hu)) using 1
    norm_num [setup,sizes];omega
  exact ⟨u,_,hAll,by omega,hup,huo,execution_preserved hAll.executes,hui⟩

end

open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)

/-- Stash exact sizes in high registers, and place the extracted root beyond
all input, FFT gate and sparse power-bank cells. -/
def rootSetup : List Op := [.literal 153 0,.add 154 109 153,.add 155 108 153,
  .add 156 122 117,.literal 158 5,.mul 157 155 158,.add 157 156 157,
  .literal 159 4,.add 157 157 159,.add 141 155 153,.add 140 157 153]
def powerSetup : List Op := [.add 130 155 153,.add 131 156 153,.getScalar 30 157]
def fftSetup : List Op := [.add 0 154 153,.add 9 122 155,.add 137 107 153]

def program : Program :=
  (UniformRadixRowTableMachine.program.map (relocate 0 114)) ++ rootSetup.map Op.code ++
  (UniformRootExtractionMachine.program.map (relocate 125 142)) ++ powerSetup.map Op.code ++
  (UniformRadixPowerBankMachine.program.map (relocate 145 163)) ++ fftSetup.map Op.code ++
  (UniformOffsetLinearMachine.program.map (relocate 166 198)) ++ [.halt]

theorem rootSetup_length : rootSetup.length=11 := rfl
theorem powerSetup_length : powerSetup.length=3 := rfl
theorem fftSetup_length : fftSetup.length=3 := rfl
theorem program_length : program.length=199 := by simp [program,rootSetup_length,powerSetup_length,fftSetup_length,UniformRadixRowTableMachine.program_length,UniformRootExtractionMachine.program_length,UniformRadixPowerBankMachine.program_length,UniformOffsetLinearMachine.program_length]

theorem segment_code (a b p : Program) (ret : ℕ) :
    CodeAt p (a++p.map (relocate a.length ret)++b) a.length ret := by
  intro i hi
  rw [List.getElem?_append_left (by simp;omega),List.getElem?_append_right (by omega)]
  simp [List.getElem?_map]

theorem row_code : CodeAt UniformRadixRowTableMachine.program program 0 114 := by
  intro i hi
  have hb:i<114:=by simpa only [UniformRadixRowTableMachine.program_length] using hi
  simp only [program,List.getElem?_append,List.length_append,List.length_map,List.getElem?_map,UniformRadixRowTableMachine.program_length,UniformRootExtractionMachine.program_length,UniformRadixPowerBankMachine.program_length,UniformOffsetLinearMachine.program_length,rootSetup_length,powerSetup_length,fftSetup_length]
  split_ifs <;> first | omega | (congr 1;congr 1;omega)

theorem root_code : CodeAt UniformRootExtractionMachine.program program 125 142 := by
  intro i hi
  have hb:i<17:=by simpa only [UniformRootExtractionMachine.program_length] using hi
  simp only [program,List.getElem?_append,List.length_append,List.length_map,List.getElem?_map,UniformRadixRowTableMachine.program_length,UniformRootExtractionMachine.program_length,UniformRadixPowerBankMachine.program_length,UniformOffsetLinearMachine.program_length,rootSetup_length,powerSetup_length,fftSetup_length]
  split_ifs <;> try omega
  all_goals simp only [show 125+i-(114+11)=i by omega]

theorem power_code : CodeAt UniformRadixPowerBankMachine.program program 145 163 := by
  intro i hi
  have hb:i<18:=by simpa only [UniformRadixPowerBankMachine.program_length] using hi
  simp only [program,List.getElem?_append,List.length_append,List.length_map,List.getElem?_map,UniformRadixRowTableMachine.program_length,UniformRootExtractionMachine.program_length,UniformRadixPowerBankMachine.program_length,UniformOffsetLinearMachine.program_length,rootSetup_length,powerSetup_length,fftSetup_length]
  split_ifs <;> try omega
  all_goals simp only [show 145+i-(114+11+17+3)=i by omega]

theorem fft_code : CodeAt UniformOffsetLinearMachine.program program 166 198 := by
  intro i hi
  have hb:i<32:=by simpa only [UniformOffsetLinearMachine.program_length] using hi
  simp only [program,List.getElem?_append,List.length_append,List.length_map,List.getElem?_map,UniformRadixRowTableMachine.program_length,UniformRootExtractionMachine.program_length,UniformRadixPowerBankMachine.program_length,UniformOffsetLinearMachine.program_length,rootSetup_length,powerSetup_length,fftSetup_length]
  split_ifs <;> try omega
  all_goals simp only [show 166+i-(114+11+17+3+18+3)=i by omega]

theorem rootSetup_at : BlockAt rootSetup program 114 := by intro i hi;change i<11 at hi;interval_cases i <;> rfl
theorem powerSetup_at : BlockAt powerSetup program 142 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem fftSetup_at : BlockAt fftSetup program 163 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem halt_at : program[198]?=some .halt := rfl

def powerBase (K A : ℕ) : ℕ := A+width K+count K
def rootAddress (K A : ℕ) : ℕ := powerBase K A+5*width K+4

def runtime (D K : ℕ) : ℕ := (19*K+63)*count K+4*K+16+
  (9+UniformPowerMachine.loopCost (D/width K))+(8*width K+3)+(22*count K+5)+18

noncomputable section

theorem reset_placed (s : State) (base : ℕ) (hp:s.pc=base) : placed base {s with pc:=0}=s := by
  cases s;simp_all [placed]

/-- The only persistent entry parameters are height70, scalar base122,
natural-table base107, master order104 and actual master root heap0. -/
structure Entry (K A d D : ℕ) (input : Fin (width K)→Scalar) (s : State) : Prop where
  pc : s.pc=0
  height : s.natReg 70=K
  base : s.natReg 122=A
  tableBase : s.natReg 107=d
  order : s.natReg 104=D
  root : s.scalarHeap 0=some ⟨zeta D,false⟩
  data : ∀i,s.scalarHeap (A+i.val)=some (input i)

structure Sizes (K A d D : ℕ) (s : State) : Prop where
  zero : s.natReg 153=0
  count : s.natReg 154=count K
  width : s.natReg 155=width K
  powerBase : s.natReg 156=powerBase K A
  rootAddress : s.natReg 157=rootAddress K A
  base : s.natReg 122=A
  tableBase : s.natReg 107=d
  order : s.natReg 104=D

theorem rootSetup_spec (K A d D : ℕ) (s : State) (h:UniformRadixRowTableMachine.Context K d A (count K) s)
    (hD:s.natReg 104=D) : Sizes K A d D (applyBlock rootSetup s) ∧
    (applyBlock rootSetup s).natReg 141=width K ∧
    (applyBlock rootSetup s).natReg 140=rootAddress K A := by
  constructor
  · constructor <;> simp [applyBlock,rootSetup,Op.apply,writeNat,next,h.Greg,h.Nreg,h.prep,h.scalarBase,h.base,hD,powerBase,rootAddress,Nat.add_assoc,Nat.mul_comm]
  · constructor <;> simp [applyBlock,rootSetup,Op.apply,writeNat,next,h.Greg,h.Nreg,h.prep,h.scalarBase,powerBase,rootAddress,Nat.add_assoc,Nat.mul_comm]

theorem rootSetup_readable (s : State) : readable rootSetup s := by simp [readable,rootSetup,Op.readable]

theorem rootSetup_peak (K A d : ℕ) (s : State) (h:UniformRadixRowTableMachine.Context K d A (count K) s) :
    peak rootSetup s≤rootAddress K A+5 := by
  have hn:=width_pos K
  simp [peak,rootSetup,Op.apply,Op.peak,writeNat,next,h.Greg,h.Nreg,h.prep,h.scalarBase,powerBase,rootAddress,Nat.add_assoc,Nat.mul_comm]
  all_goals omega

theorem Sizes.withPC {K A d D pc : ℕ} {s : State} (h:Sizes K A d D s) : Sizes K A d D {s with pc:=pc} := by cases h;constructor <;> assumption

theorem sizes_root {K A d D : ℕ} {s u : State} (h:Sizes K A d D s) (f:UniformRootExtractionMachine.Frame s u) : Sizes K A d D u := by
  constructor
  all_goals first | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.zero | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.count | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.width | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.powerBase | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.rootAddress | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.base | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.tableBase | exact (f.2.2.2.2 _ (by decide) (by decide)).trans h.order


theorem powerSetup_spec (K A d D : ℕ) (s : State) (h:Sizes K A d D s)
    (hr:s.scalarHeap (rootAddress K A)=some ⟨zeta (width K),false⟩) :
    Sizes K A d D (applyBlock powerSetup s) ∧
    (applyBlock powerSetup s).natReg 130=width K ∧
    (applyBlock powerSetup s).natReg 131=powerBase K A ∧
    (applyBlock powerSetup s).scalarReg 30=UniformRadixPowerBankMachine.prepared (zeta (width K)) := by
  refine ⟨?_,?_,?_,?_⟩
  · constructor <;> simp [applyBlock,powerSetup,Op.apply,writeNat,writeScalar,next,h.zero,h.count,h.width,h.powerBase,h.rootAddress,h.base,h.tableBase,h.order]
  · simp [applyBlock,powerSetup,Op.apply,writeNat,writeScalar,next,h.zero,h.width]
  · simp [applyBlock,powerSetup,Op.apply,writeNat,writeScalar,next,h.zero,h.powerBase]
  · simp [applyBlock,powerSetup,Op.apply,writeNat,writeScalar,next,h.rootAddress,hr,UniformRadixPowerBankMachine.prepared]

theorem powerSetup_readable (K A d D : ℕ) (s : State) (h:Sizes K A d D s)
    (hr:s.scalarHeap (rootAddress K A)=some ⟨zeta (width K),false⟩) : readable powerSetup s := by
  simp [readable,powerSetup,Op.readable,Op.apply,writeNat,next,h.rootAddress,hr]

theorem powerSetup_peak (K A d D : ℕ) (s : State) (h:Sizes K A d D s) :
    peak powerSetup s≤powerBase K A+width K := by
  simp [peak,powerSetup,Op.peak,Op.apply,writeNat,next,h.zero,h.width,h.powerBase]
  try omega

theorem sizes_power {K A d D : ℕ} {s u : State} (h:Sizes K A d D s)
    (f:UniformRadixPowerBankMachine.Frame s u) : Sizes K A d D u := by
  constructor
  all_goals first | exact (f.2.2.2.2 _ (by omega)).trans h.zero | exact (f.2.2.2.2 _ (by omega)).trans h.count | exact (f.2.2.2.2 _ (by omega)).trans h.width | exact (f.2.2.2.2 _ (by omega)).trans h.powerBase | exact (f.2.2.2.2 _ (by omega)).trans h.rootAddress | exact (f.2.2.2.2 _ (by omega)).trans h.base | exact (f.2.2.2.2 _ (by omega)).trans h.tableBase | exact (f.2.2.2.2 _ (by omega)).trans h.order

theorem fftSetup_spec (K A d D : ℕ) (s : State) (h:Sizes K A d D s) :
    (applyBlock fftSetup s).natReg 0=count K ∧
    (applyBlock fftSetup s).natReg 9=A+width K ∧
    (applyBlock fftSetup s).natReg 137=d := by
  simp [applyBlock,fftSetup,Op.apply,writeNat,next,h.zero,h.count,h.width,h.base,h.tableBase]

theorem fftSetup_readable (s : State) : readable fftSetup s := by simp [readable,fftSetup,Op.readable]

theorem fftSetup_peak (K A d D : ℕ) (s : State) (h:Sizes K A d D s) :
    peak fftSetup s≤d+A+width K+count K := by
  simp [peak,fftSetup,Op.peak,Op.apply,writeNat,next,h.zero,h.count,h.width,h.base,h.tableBase]
  omega

/-- High global header registers and caller's argument registers survive. -/
def Persistent (r : ℕ) : Prop := r=70 ∨ r=107 ∨ r=122 ∨ (100≤r ∧ r≤106) ∨ 160≤r

def SetupFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,Persistent r→u.natReg r=s.natReg r)

theorem setup_frame (b : List Op) (hb:b=rootSetup ∨ b=powerSetup ∨ b=fftSetup) (s : State) :
    SetupFrame s (applyBlock b s) := by
  rcases hb with rfl|rfl|rfl
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro r hr;simp only [Persistent] at hr
  all_goals simp (disch:=omega) [applyBlock,rootSetup,powerSetup,fftSetup,Op.apply,writeNat,writeScalar,next]

theorem row_persistent {s u : State} (h:UniformRadixRowTableMachine.Preserved s u)
    (r : ℕ) (hr:Persistent r) : u.natReg r=s.natReg r :=
  h.2.2.2.2 r (by simp only [Persistent] at hr;omega) (by simp only [Persistent] at hr;omega)

theorem root_persistent {s u : State} (h:UniformRootExtractionMachine.Frame s u)
    (r : ℕ) (hr:Persistent r) : u.natReg r=s.natReg r :=
  h.2.2.2.2 r (by simp only [Persistent] at hr;omega) (by simp only [Persistent] at hr;omega)

theorem power_persistent {s u : State} (h:UniformRadixPowerBankMachine.Frame s u)
    (r : ℕ) (hr:Persistent r) : u.natReg r=s.natReg r :=
  h.2.2.2.2 r (by simp only [Persistent] at hr;omega)

theorem fft_persistent {s u : State} (h:UniformOffsetLinearMachine.Frame s u)
    (r : ℕ) (hr:Persistent r) : u.natReg r=s.natReg r :=
  h.2.2.2.1 r (Or.inr (by simp only [Persistent] at hr;omega))

theorem fft_contextFree : UniformContext.ContextFree UniformOffsetLinearMachine.program := by
  simp [UniformContext.ContextFree,UniformOffsetLinearMachine.program,UniformContext.instructionFree]

/-- Actual complete table, root extraction, sparse prepared powers and tagged
FFT interpretation execute as one fixed program. No ready table/power/root or
whole-action certificate is accepted at entry. The input cells already exist. -/
theorem execution (n K A d D B : ℕ) (x : Fin n→ℂ)
    (input : Fin (width K)→Scalar) (s : State) (h:Entry K A d D input s)
    (hD:0<D) (hdiv:width K∣D) (hcode:199≤B)
    (hrow:A+UniformRadixInstructionMachine.cap (width K) (count K) K≤B)
    (htable:d+3*count K≤B) (hmem:rootAddress K A+5≤B)
    (hfft:d+4*count K+(A+width K)+42≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤runtime D K ∧
    (∀i,u.scalarHeap (A+count K+i.val)=some
      ⟨(fourierMatrix (width K)).mulVec (fun i=>(input i).value) i,
        UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun i=>(input i).dependent) (count K+i.val)⟩) ∧
    UniformRadixRowTableMachine.Outside d (3*count K) s.natHeap u ∧
    (∀i,(i < A + width K ∨ rootAddress K A + 1 ≤ i) →u.scalarHeap i=s.scalarHeap i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,Persistent r→u.natReg r=s.natReg r) ∧ u.pc=198 := by
  have hN:=width_pos K
  obtain ⟨v,tv,hv,htv,hprinted,hout,hvf,hctx⟩:=row_execution_context n K d A B x s h.pc h.height h.tableBase h.base hs hrow htable
  have hplacedv:=UniformBoundedAssembly.boundedExecution_placed row_code (by simpa only [UniformRadixRowTableMachine.program_length,Nat.zero_add] using (show 114≤B by omega)) (by omega) hv
  have hentryv:placed 0 s=s:=by cases s;simp [placed]
  rw [hentryv] at hplacedv
  let vs:State:={v with pc:=114}
  have hvs:WordBound B vs:=hplacedv.final_bound
  have hvctx:UniformRadixRowTableMachine.Context K d A (count K) vs:=hctx.withPC
  have hvD:vs.natReg 104=D:=(row_persistent hvf 104 (by simp [Persistent])).trans h.order
  have hrb:=block_runs rootSetup program 114 n B x vs rootSetup_at rfl hvs (by simpa only [rootSetup_length] using (show 125≤B by omega))
    (rootSetup_readable vs) ((rootSetup_peak K A d vs hvctx).trans hmem)
  let rs:=applyBlock rootSetup vs
  have hrs:=rootSetup_spec K A d D vs hvctx hvD
  have hrpc:rs.pc=125:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have hrsf:=setup_frame rootSetup (Or.inl rfl) vs
  have hroot:rs.scalarHeap 0=some ⟨zeta D,false⟩:=by rw [hrsf.2.1,hvf.1];exact h.root
  let re:State:={rs with pc:=0}
  have hreb:WordBound B re:=changePC_bound B rs 0 hrb.final_bound (by omega)
  obtain ⟨w,hw,hwroot,hwoutside,hwf,hwpc⟩:=UniformRootExtractionMachine.execution n D (width K) (rootAddress K A) B x re rfl hrs.1.order hrs.2.1 hrs.2.2 hD (width_pos K) hdiv hroot (by omega) hreb
  have hplacedw:=UniformBoundedAssembly.boundedExecution_placed root_code (by simpa only [UniformRootExtractionMachine.program_length] using (show 142≤B by omega)) (by omega) hw
  have hew:placed 125 re=rs:=reset_placed rs 125 hrpc
  rw [hew] at hplacedw
  let ws:State:={w with pc:=142}
  have hwsz:Sizes K A d D ws:=(sizes_root hrs.1 hwf).withPC
  have hpb:=block_runs powerSetup program 142 n B x ws powerSetup_at rfl hplacedw.final_bound (by simpa only [powerSetup_length] using (show 145≤B by omega))
    (powerSetup_readable K A d D ws hwsz hwroot) ((powerSetup_peak K A d D ws hwsz).trans (by unfold rootAddress at hmem;omega))
  let ps:=applyBlock powerSetup ws
  have hpctx:=powerSetup_spec K A d D ws hwsz hwroot
  have hppc:ps.pc=145:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have hpsf:=setup_frame powerSetup (Or.inr (Or.inl rfl)) ws
  let pe:State:={ps with pc:=0}
  have hpeb:WordBound B pe:=changePC_bound B ps 0 hpb.final_bound (by omega)
  obtain ⟨q,hq,hbank,hqoutside,hqf,hqpc⟩:=UniformRadixPowerBankMachine.execution n x (width K) (powerBase K A) B (zeta (width K)) pe rfl (width_pos K) hpctx.2.1 hpctx.2.2.1 hpctx.2.2.2 (by omega) (by unfold rootAddress at hmem;omega) hpeb
  have hplacedq:=UniformBoundedAssembly.boundedExecution_placed power_code (by simpa only [UniformRadixPowerBankMachine.program_length] using (show 163≤B by omega)) (by omega) hq
  have heq:placed 145 pe=ps:=reset_placed ps 145 hppc
  rw [heq] at hplacedq
  let qs:State:={q with pc:=163}
  have hqsz:Sizes K A d D qs:=(sizes_power hpctx.1 hqf).withPC
  have hfb:=block_runs fftSetup program 163 n B x qs fftSetup_at rfl hplacedq.final_bound (by simpa only [fftSetup_length] using (show 166≤B by omega))
    (fftSetup_readable qs) ((fftSetup_peak K A d D qs hqsz).trans (by omega))
  let fs:=applyBlock fftSetup qs
  have hfctx:=fftSetup_spec K A d D qs hqsz
  have hfpc:fs.pc=166:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have hfsf:=setup_frame fftSetup (Or.inr (Or.inr rfl)) qs
  let fe:State:={fs with pc:=0}
  have hfeb:WordBound B fe:=changePC_bound B fs 0 hfb.final_bound (by omega)
  have htablefe:UniformRadixRowTableMachine.Printed K d A (count K) fe:=hprinted.congr
    (hfsf.1.trans (hqf.1.trans (hpsf.1.trans (hwf.1.trans hrsf.1))))
  have hinputfe:∀i:Fin (width K),fe.scalarHeap (A+i.val)=some (input i):=by
    intro i
    have hi:=i.isLt
    have hiP:A+i.val<powerBase K A:=by unfold powerBase;omega
    have hiR:A+i.val≠rootAddress K A:=by unfold rootAddress;omega
    rw [hfsf.2.1,hqoutside _ (Or.inl hiP),hpsf.2.1,hwoutside _ hiR,hrsf.2.1,hvf.1]
    exact h.data i
  have hbankfe:UniformRadixPowerBankMachine.Bank (width K) (A+UniformRadixTwoMachine.prepBase K) (zeta (width K)) fe:=by
    intro j hj
    rw [hfsf.2.1]
    simpa only [UniformRadixTwoMachine.prepBase,powerBase,Nat.add_assoc] using hbank j hj
  have hfe:=UniformOffsetLinearMachine.TaggedFFT.entry_of_producers K A d (zeta (width K)) input fe rfl hfctx.1 hfctx.2.1 hfctx.2.2 htablefe hinputfe hbankfe
  obtain ⟨u,tu,hu,htu,huf,huoutside,huspec⟩:=UniformOffsetLinearMachine.TaggedFFT.specified_execution K A d input fe B hfe hfft hfeb
  have hglobal:=UniformContext.bounded_execution fft_contextFree x hu
  have hplacedu:=UniformBoundedAssembly.boundedExecution_placed fft_code (by simpa only [UniformOffsetLinearMachine.program_length] using (show 198≤B by omega)) (by omega) hglobal
  have heu:placed 166 fe=fs:=reset_placed fs 166 hfpc
  rw [heu] at hplacedu
  let z:State:={u with pc:=198}
  have hhalt:BoundedExecution program n x B z 1 z:=.halt hplacedu.final_bound (by simp only [step];rfl)
  have hall:=hplacedv.executes (hrb.executes (hplacedw.executes (hpb.executes (hplacedq.executes (hfb.executes (hplacedu.executes hhalt))))))
  refine ⟨z,_,hall,?_,huspec,?_,?_,?_,?_,?_,rfl⟩
  · simp only [rootSetup_length,powerSetup_length,fftSetup_length] at *
    unfold runtime;omega
  · apply hout.congr
    exact huf.1.trans (hfsf.1.trans (hqf.1.trans (hpsf.1.trans (hwf.1.trans hrsf.1))))
  · intro i hi
    have hiF : i < A + width K ∨ A + width K + count K ≤ i :=by unfold rootAddress powerBase at hi;omega
    have hiP : i < powerBase K A ∨ powerBase K A + 5 * width K + 3 ≤ i :=by dsimp only [rootAddress,powerBase] at hi ⊢;omega
    have hiR:i≠rootAddress K A:=by dsimp only [rootAddress,powerBase] at hi ⊢;omega
    rw [huoutside i hiF,hfsf.2.1,hqoutside i hiP,hpsf.2.1,hwoutside i hiR,hrsf.2.1,hvf.1]
  · exact huf.2.1.trans (hfsf.2.2.1.trans (hqf.2.1.trans (hpsf.2.2.1.trans (hwf.2.1.trans (hrsf.2.2.1.trans hvf.2.2.1)))))
  · exact huf.2.2.1.trans (hfsf.2.2.2.1.trans (hqf.2.2.1.trans (hpsf.2.2.2.1.trans (hwf.2.2.1.trans (hrsf.2.2.2.1.trans hvf.2.2.2.1)))))
  · intro r hr
    exact (fft_persistent huf r hr).trans ((hfsf.2.2.2.2 r hr).trans ((power_persistent hqf r hr).trans
      ((hpsf.2.2.2.2 r hr).trans ((root_persistent hwf r hr).trans ((hrsf.2.2.2.2 r hr).trans (row_persistent hvf r hr))))))


/-- Explicit coarse local address envelope; existing unrelated state still has
to satisfy the same ambient WordBound. This is polynomial local preparation. -/
def wordBudget (K A d : ℕ) : ℕ :=
  A+UniformRadixInstructionMachine.cap (width K) (count K) K+
  (d+3*count K)+(rootAddress K A+5)+(d+4*count K+(A+width K)+42)+199

theorem wordBudget_bounds (K A d B : ℕ) (h:wordBudget K A d≤B) :
    199≤B ∧ A+UniformRadixInstructionMachine.cap (width K) (count K) K≤B ∧
    d+3*count K≤B ∧ rootAddress K A+5≤B ∧ d+4*count K+(A+width K)+42≤B := by
  unfold wordBudget at h;omega

theorem wordBudget_power (K A d : ℕ) : wordBudget K A d≤3*A+2*d+2^(4*K+15) := by
  have hl:=UniformRadixInstructionMachine.cap_linear (width K) (count K) K
  have hp:=UniformRadixInstructionMachine.cap_power K
  have hc:200≤UniformRadixInstructionMachine.cap (width K) (count K) K:=by unfold UniformRadixInstructionMachine.cap;omega
  have he:2^(4*K+15)=8*2^(4*K+12):=by rw [show 4*K+15=(4*K+12)+3 by omega,pow_add];norm_num;ring
  rw [he]
  unfold wordBudget rootAddress powerBase
  omega

theorem runtime_log_bound (D K : ℕ) : runtime D K≤
    (19*K+85)*count K+4*K+8*width K+7*(Nat.log2 (D+1)+1)+53 := by
  have h:=UniformRootExtractionMachine.runtime_log_bound D (width K)
  unfold runtime
  nlinarith

/-- Saved global startup metadata and operands suffice to extract the canonical
local root. The full selected protected prefix, including beta inverse, survives.
Neither roots, powers, table rows nor the FFT action are extra premises. -/
theorem selected_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (r K A d : ℕ)
    (input : Fin (width K)→Scalar) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s)
    (hr:r≤UniformWorkingLength.workingLength n) (hk:2^K≤8*r)
    (hp:s.pc=0) (hK:s.natReg 70=K) (hA:s.natReg 122=A) (hd:s.natReg 107=d)
    (hi:∀i,s.scalarHeap (A+i.val)=some (input i))
    (hAglobal:UniformGlobalLocalPreparation.globalEnd n≤A)
    (hdglobal:UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n≤d)
    (hbudget:wordBudget K A d≤(n+2)^19) (hs:WordBound ((n+2)^19) s) : ∃u t,
    BoundedExecution program n x ((n+2)^19) s t u ∧
    t≤runtime (UniformMasterRootMachine.order n) K ∧
    (∀i,u.scalarHeap (A+count K+i.val)=some
      ⟨(fourierMatrix (width K)).mulVec (fun i=>(input i).value) i,
        UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun i=>(input i).dependent) (count K+i.val)⟩) ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    (∀i,i<UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n→u.natHeap i=s.natHeap i) ∧
    (∀i,(i < A + width K ∨ rootAddress K A + 1 ≤ i) →u.scalarHeap i=s.scalarHeap i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,Persistent r→u.natReg r=s.natReg r) ∧ u.pc=198 := by
  have hroot:s.scalarHeap 0=some ⟨zeta (UniformMasterRootMachine.order n),false⟩:=by
    simpa [UniformCConstantsMachine.bank,UniformPairMachine.prepared] using ho.constants 0
  have hentry:Entry K A d (UniformMasterRootMachine.order n) input s:=
    ⟨hp,hK,hA,hd,hm.saved.masterRoot,hroot,hi⟩
  have hb:=wordBudget_bounds K A d ((n+2)^19) hbudget
  have hdiv:width K∣UniformMasterRootMachine.order n:=by
    simpa only [width_eq] using UniformMasterRootMachine.localPowerOrder_dvd hr hk
  obtain ⟨u,t,he,ht,hout,hNat,hScalar,hOutputs,hRoots,hRegs,hpc⟩:=execution n K A d (UniformMasterRootMachine.order n) ((n+2)^19) x input s hentry
    (UniformMasterRootMachine.order_bounds hn).1 hdiv hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hs
  have hprefix:∀i,i<UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n→u.natHeap i=s.natHeap i:=by
    intro i hi;exact hNat i (Or.inl (by omega))
  have hsaved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
      (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) u:=by
    constructor
    · exact (hRegs 100 (by simp [Persistent])).trans hm.saved.nextPrime
    · exact (hRegs 101 (by simp [Persistent])).trans hm.saved.inputLength
    · exact (hRegs 102 (by simp [Persistent])).trans hm.saved.count
    · exact (hRegs 103 (by simp [Persistent])).trans hm.saved.workingLength
    · exact (hRegs 104 (by simp [Persistent])).trans hm.saved.masterRoot
    · exact (hRegs 105 (by simp [Persistent])).trans hm.saved.copyAddress
    · exact (hRegs 106 (by simp [Persistent])).trans hm.saved.copyLength
  have hmu:UniformPermutationInversePreparation.Metadata n u:=hm.transport_saved hsaved (by
    intro a ha
    apply hprefix
    unfold UniformPermutationInversePreparation.inverseBase;omega)
  have hou:UniformInitialPreparation.Operands n x u:=UniformGlobalLocalPreparation.operands_transport_below ho (by
    intro i hi;exact hScalar i (Or.inl (by omega)))
  exact ⟨u,t,he,ht,hout,hmu,hou,hprefix,hScalar,hOutputs,hRoots,hRegs,hpc⟩

/-- A protected permutation bank retains its specified permutation pointwise.
This introduces no producer or table-readiness premise. -/
theorem permutation_transport {N base d m : ℕ} {s u : State} {p : Equiv.Perm (Fin N)}
    (h:UniformGlobalNatPreparation.PermutationBank N base s.natHeap p)
    (ho:UniformRadixRowTableMachine.Outside d m s.natHeap u) (hb:base+N≤d) :
    UniformGlobalNatPreparation.PermutationBank N base u.natHeap p := by
  intro j
  have hj:=j.isLt
  exact (ho (base+j.val) (Or.inl (by omega))).trans (h j)

/-- The fully assembled program retains prepared flags when the local input
array contains only prepared coefficients, including any padded zeros. -/
theorem prepared_execution (n K A d D B : ℕ) (x : Fin n→ℂ)
    (input : Fin (width K)→Scalar) (s : State) (h:Entry K A d D input s)
    (hprepared:∀i,(input i).dependent=false)
    (hD:0<D) (hdiv:width K∣D) (hcode:199≤B)
    (hrow:A+UniformRadixInstructionMachine.cap (width K) (count K) K≤B)
    (htable:d+3*count K≤B) (hmem:rootAddress K A+5≤B)
    (hfft:d+4*count K+(A+width K)+42≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤runtime D K ∧
    (∀i,u.scalarHeap (A+count K+i.val)=some (UniformRadixTwoMachine.preparedScalar
      ((fourierMatrix (width K)).mulVec (fun i=>(input i).value) i))) ∧
    UniformRadixRowTableMachine.Outside d (3*count K) s.natHeap u ∧
    (∀i,(i < A + width K ∨ rootAddress K A + 1 ≤ i) →u.scalarHeap i=s.scalarHeap i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,Persistent r→u.natReg r=s.natReg r) ∧ u.pc=198 := by
  obtain ⟨u,t,he,ht,hout,hNat,hScalar,hOutputs,hRoots,hRegs,hpc⟩:=execution n K A d D B x input s h hD hdiv hcode hrow htable hmem hfft hs
  refine ⟨u,t,he,ht,?_,hNat,hScalar,hOutputs,hRoots,hRegs,hpc⟩
  intro i
  rw [hout i,UniformOffsetLinearMachine.TaggedFFT.dependencyValue_prepared K (fun i=>(input i).dependent) hprepared]
  rfl

end
end ExactFourierCircuits.UniformPreparedFFTMachine
