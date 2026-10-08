import UniformRankKernelMachine
import UniformKernelSpectrumMachine
import UniformToeplitzCrossTopologyMachine
import UniformDAGDepthMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRankCrossPreparationMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Only the height and original parameter/layout headers enter. Width489,
kernel-source526, cross arguments and all depth arguments are installed by
actual instructions. Nat670..674 are scratch; Nat675 is the depth-bank base. -/
def sizing : Program := [
 .natLiteral 670 0,.natLiteral 671 1,.natLiteral 672 2,
 .natLiteral 673 1,.natLiteral 674 0,.branchLT 674 525 6 9,
 .natBinary .mul 673 673 672,.natBinary .add 674 674 671,.jump 5,
 .natBinary .add 489 673 670,.natBinary .add 526 490 670,.halt]
def crossSetup : List Op := [.add 560 525 670,.add 561 484 670,.add 562 485 670]
def depthSetup : List Op := [.add 650 485 670,.literal 671 3,
 .mul 651 525 489,.mul 651 651 671,.literal 672 2,.mul 673 489 672,
 .add 651 651 673,.literal 671 6,.mul 651 651 671,.mul 673 484 672,
 .add 651 651 673,.add 652 564 670,.add 653 675 670]
def program : Program := sizing.map (relocate 0 12) ++
 UniformRankKernelMachine.program.map (relocate 12 102) ++
 UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++
 UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++
 UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
theorem sizing_length : sizing.length=12 := rfl
theorem crossSetup_length : crossSetup.length=3 := rfl
theorem depthSetup_length : depthSetup.length=13 := rfl
theorem program_length : program.length=722 := by
 simp only [program,List.length_append,List.length_map,sizing_length,
  UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length,
  crossSetup_length,UniformToeplitzCrossTopologyMachine.program_length,
  depthSetup_length,UniformDAGDepthMachine.program_length,List.length_singleton]

theorem segment_code (before after p : Program) (base returnPC : ℕ)
    (hb : before.length=base) :
    CodeAt p (before ++ p.map (relocate base returnPC) ++ after) base returnPC := by
 intro i hi
 rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,hb];omega)]
 rw [List.getElem?_append_right (by omega)]
 simp only [hb,show base+i-base=i by omega,List.getElem?_map]

theorem sizing_code : CodeAt sizing program 0 12 := by
  let after:=UniformRankKernelMachine.program.map (relocate 12 102) ++
    UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++
    UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++
    UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have he:program=[] ++ sizing.map (relocate 0 12) ++ after:=by
    simp only [program,after,List.nil_append,List.append_assoc]
  rw [he]
  exact segment_code [] after sizing 0 12 rfl

open UniformRadixTwoDAG OAI.ExactFourier
open UniformPairMachine (prepared)

structure Parameters where
  K : ℕ
  H : ℕ
  G : ℕ
  hSize : ℕ
  gSize : ℕ
  a : ℕ
  e : ℕ
  i0 : ℕ
  j0 : ℕ
  split : ℕ
  S : ℕ
  A : ℕ
  d : ℕ
  C : ℕ
  D : ℕ
  conv : ℕ
  tape : ℕ
  depth : ℕ

def Parameters.rank (p : Parameters) : UniformRankKernelMachine.Parameters :=
  ⟨p.H,p.G,p.hSize,p.gSize,p.a,p.e,p.i0,p.j0,p.split,width p.K,p.S⟩

def Parameters.register (p : Parameters) : ℕ → ℕ
  | 104=>p.D | 480=>p.H | 481=>p.hSize | 482=>p.G | 483=>p.gSize
  | 484=>p.a | 485=>p.e | 486=>p.i0 | 487=>p.j0 | 488=>p.split
  | 490=>p.S | 525=>p.K | 527=>p.A | 528=>p.d | 529=>p.C
  | 563=>p.conv | 564=>p.tape | 675=>p.depth
  | _=>0

def headerRegisters : List ℕ := [104,480,481,482,483,484,485,486,487,488,490,525,527,528,529,563,564,675]

def Header (p : Parameters) (s : State) : Prop :=
  ∀r,r ∈ headerRegisters → s.natReg r=p.register r

/-- Width489 and kernelSource526 are deliberately absent from the entry header. -/
def Preserved (r : ℕ) : Prop := (100 ≤ r ∧ r ≤ 106) ∨ r ∈ headerRegisters ∨ 676 ≤ r

noncomputable section

theorem header_preserved (r : ℕ) (hr:r ∈ headerRegisters) : Preserved r := Or.inr (Or.inl hr)

theorem Header.transport {p : Parameters} {s t : State} (h:Header p s)
    (f:∀r,Preserved r → t.natReg r=s.natReg r) : Header p t := by
  intro r hr;exact (f r (header_preserved r hr)).trans (h r hr)

theorem Header.withPC {p : Parameters} {s : State} (h:Header p s) (pc : ℕ) :
    Header p (setPC s pc) := h

def Shape (p : Parameters) := 6*(3*p.K*width p.K+2*width p.K)+2*p.a

def Layout (p : Parameters) (B : ℕ) : Prop :=
  UniformRankKernelMachine.Geometry p.rank B ∧
  UniformKernelSpectrumMachine.Layout p.K p.S p.A p.d p.C p.D B ∧
  p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ p.tape ∧
  UniformToeplitzCrossTopologyMachine.budget p.K p.a p.e p.conv p.tape ≤ B ∧
  p.tape+5*Shape p ≤ p.depth ∧ p.depth+p.e+1+Shape p ≤ B ∧ 722 ≤ B

/-- Outside all four actually written Nat regions and three scalar regions. -/
def Frame (p : Parameters) (s u : State) : Prop :=
  (∀q,(q < p.d ∨ p.d+3*count p.K ≤ q) →
    (q < p.conv ∨ p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ q) →
    (q < p.tape ∨ p.tape+5*Shape p ≤ q) →
    (q < p.depth ∨ p.depth+p.e+1+Shape p ≤ q) → u.natHeap q=s.natHeap q) ∧
  (∀q,(q < p.S ∨ p.S+6*width p.K ≤ q) →
    (q < p.A ∨ UniformPreparedFFTMachine.rootAddress p.K p.A+1 ≤ q) →
    (q < p.C ∨ p.C+7*width p.K+1 ≤ q) → u.scalarHeap q=s.scalarHeap q) ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,Preserved r → u.natReg r=s.natReg r)

theorem Frame.refl (p : Parameters) (s : State) : Frame p s s :=
  ⟨fun _ _ _ _ _=>rfl,fun _ _ _ _=>rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {p : Parameters} {s t u : State} (h:Frame p s t) (h':Frame p t u) : Frame p s u :=
  ⟨fun q a b c d=>(h'.1 q a b c d).trans (h.1 q a b c d),
    fun q a b c=>(h'.2.1 q a b c).trans (h.2.1 q a b c),
    h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
theorem Frame.withPC {p : Parameters} {s t : State} (h:Frame p s t) (pc : ℕ) :
    Frame p s (setPC t pc) := h

/-- Actual sizing is a separate literal12 subprogram, charged before rank. -/
def sizingBoot : List Op := [.literal 670 0,.literal 671 1,.literal 672 2,.literal 673 1,.literal 674 0]
def sizingGrow : List Op := [.mul 673 673 672,.add 674 674 671]
def sizingFinish : List Op := [.add 489 673 670,.add 526 490 670]
theorem sizingBoot_at : BlockAt sizingBoot sizing 0 := by intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem sizingGrow_at : BlockAt sizingGrow sizing 6 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem sizingFinish_at : BlockAt sizingFinish sizing 9 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem sizing_branch : sizing[5]?=some (.branchLT 674 525 6 9) := rfl
theorem sizing_jump : sizing[8]?=some (.jump 5) := rfl
theorem sizing_halt : sizing[11]?=some .halt := rfl

structure Sizing (K t : ℕ) (s : State) : Prop where
 height:s.natReg 525=K
 width:s.natReg 673=width t
 index:s.natReg 674=t
 zero:s.natReg 670=0
 one:s.natReg 671=1
 two:s.natReg 672=2

theorem Sizing.withPC {K t : ℕ} {s : State} (h:Sizing K t s) (pc : ℕ) :
    Sizing K t (setPC s pc) := ⟨h.height,h.width,h.index,h.zero,h.one,h.two⟩

def SizingFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀r,(r < 670 ∨ 674 < r) → r ≠ 489 → r ≠ 526 → u.natReg r=s.natReg r

theorem SizingFrame.refl (s : State) : SizingFrame s s := ⟨rfl,rfl,rfl,rfl,fun _ _ _ _=>rfl⟩
theorem SizingFrame.trans {s t u : State} (f:SizingFrame s t) (g:SizingFrame t u) : SizingFrame s u :=
  ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,g.2.2.2.1.trans f.2.2.2.1,
    fun r a b c=>(g.2.2.2.2 r a b c).trans (f.2.2.2.2 r a b c)⟩
theorem SizingFrame.withPC {s t : State} (f:SizingFrame s t) (pc : ℕ) : SizingFrame s (setPC t pc) := f

theorem preserved_ranges {r : ℕ} (hr:Preserved r) :
    (r < 670 ∨ 674 < r) ∧ r ≠ 489 ∧ r ≠ 526 := by
  simp only [Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  omega

theorem SizingFrame.frame {p : Parameters} {s t : State} (f:SizingFrame s t) : Frame p s t :=
  ⟨fun q _ _ _ _=>congrFun f.1 q,fun q _ _ _=>congrFun f.2.1 q,f.2.2.1,f.2.2.2.1,
    fun r hr=>f.2.2.2.2 r (preserved_ranges hr).1 (preserved_ranges hr).2.1 (preserved_ranges hr).2.2⟩

theorem sizing_blocks_frame (b : List Op) (s : State)
    (h:b=sizingBoot ∨ b=sizingGrow ∨ b=sizingFinish) : SizingFrame s (applyBlock b s) := by
  rcases h with rfl|rfl|rfl
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro r hr h489 h526
  all_goals simp (disch:=omega) [sizingBoot,sizingGrow,sizingFinish,applyBlock,Op.apply,writeNat,next]

theorem sizingGrow_spec {K t : ℕ} {s : State} (h:Sizing K t s) : Sizing K (t+1) (applyBlock sizingGrow s) := by
  constructor
  all_goals simp [sizingGrow,applyBlock,Op.apply,writeNat,next,h.height,h.width,h.index,h.zero,h.one,h.two,width]
  all_goals omega

theorem sizing_loop (n K t remaining B : ℕ) (x : Fin n → ℂ) (s : State)
    (cur:Sizing K t s) (hr:t+remaining=K) (hp:s.pc=5)
    (hcode:722 ≤ B) (hN:width K ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns sizing n x B s (4*remaining+1) u ∧ Sizing K K u ∧ u.pc=9 ∧ SizingFrame s u := by
  induction remaining generalizing t s with
  | zero=>
    have he:t=K:=by omega
    subst t
    have branch:=UniformRadixInstructionMachine.branch_runs sizing n B 674 525 6 9 x s hs
      (by omega) (by omega) (by rw [hp];exact sizing_branch)
    have cmp:¬s.natReg 674 < s.natReg 525:=by rw [cur.index,cur.height];omega
    simp only [cmp,ite_false] at branch
    exact ⟨setPC s 9,branch,cur.withPC 9,rfl,(SizingFrame.refl s).withPC 9⟩
  | succ remaining ih=>
    have cmp:s.natReg 674 < s.natReg 525:=by rw [cur.index,cur.height];omega
    have branch:=UniformRadixInstructionMachine.branch_runs sizing n B 674 525 6 9 x s hs
      (by omega) (by omega) (by rw [hp];exact sizing_branch)
    simp only [cmp,ite_true] at branch
    let e:=setPC s 6
    have eb:WordBound B e:=branch.final_bound
    have hwidth:=UniformRadixInstructionMachine.width_mono (show t+1 ≤ K by omega)
    have hm:width t*2 ≤ B:=by simpa [width,Nat.mul_two] using hwidth.trans hN
    have kB:K ≤ B:=by simpa only [cur.height] using hs.2.1 525
    have ready:readable sizingGrow e:=by simp [readable,sizingGrow,Op.readable]
    have pk:peak sizingGrow e ≤ B:=by
      simp [peak,sizingGrow,Op.peak,Op.apply,writeNat,next,e,setPC,cur.width,cur.two,cur.index,cur.one]
      omega
    have run:=block_runs sizingGrow sizing 6 n B x e sizingGrow_at rfl eb (by change 6+2 ≤ B;omega) ready pk
    have ep:(applyBlock sizingGrow e).pc=8:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
    have jump:=UniformRadixInstructionMachine.jump_runs sizing n B 5 x (applyBlock sizingGrow e)
      run.final_bound (by omega) (by rw [ep];exact sizing_jump)
    let w:=setPC (applyBlock sizingGrow e) 5
    have wc:Sizing K (t+1) w:=(sizingGrow_spec (cur.withPC 6)).withPC 5
    obtain ⟨u,tail,uc,up,uf⟩:=ih (t+1) w wc (by omega) rfl jump.final_bound
    refine ⟨u,?_,uc,up,(show SizingFrame s w from (sizing_blocks_frame sizingGrow e (Or.inr (Or.inl rfl))).withPC 5).trans uf⟩
    convert branch.trans (run.trans (jump.trans tail)) using 1
    simp only [show sizingGrow.length=2 from rfl]
    omega



/-- The physical width and kernel-source headers are installed by literal
instructions; neither header enters the caller contract. -/
theorem sizing_execution (p : Parameters) (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (header:Header p s) (hp:s.pc=0) (hs:WordBound B s)
    (hc:722 ≤ B) (hN:width p.K ≤ B) : ∃u,
    BoundedExecution sizing n x B s (4*p.K+9) u ∧ u.pc=11 ∧
    Header p u ∧ u.natReg 489=width p.K ∧ u.natReg 526=p.S ∧ u.natReg 670=0 ∧ SizingFrame s u := by
  have height:s.natReg 525=p.K:=header 525 (by decide)
  have source:s.natReg 490=p.S:=header 490 (by decide)
  have ready:readable sizingBoot s:=by simp [readable,sizingBoot,Op.readable]
  have pk:peak sizingBoot s ≤ B:=by simp [peak,sizingBoot,Op.peak];omega
  have boot:=block_runs sizingBoot sizing 0 n B x s sizingBoot_at hp hs (by change 0+5 ≤ B;omega) ready pk
  let v:=applyBlock sizingBoot s
  have cur:Sizing p.K 0 v:=by
    constructor <;> simp [v,sizingBoot,applyBlock,Op.apply,writeNat,next,height,width]
  have vp:v.pc=5:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  obtain ⟨w,loop,wc,wp,wf⟩:=sizing_loop n p.K 0 p.K B x v cur (by omega) vp hc hN boot.final_bound
  have sf:SizingFrame s w:=(sizing_blocks_frame sizingBoot s (Or.inl rfl)).trans wf
  have src:w.natReg 490=p.S:=(sf.2.2.2.2 490 (Or.inl (by omega)) (by omega) (by omega)).trans source
  have readableFinish:readable sizingFinish w:=by simp [readable,sizingFinish,Op.readable]
  have sB:p.S ≤ B:=by simpa only [src] using loop.final_bound.2.1 490
  have finishPeak:peak sizingFinish w ≤ B:=by
    simp [peak,sizingFinish,Op.peak,Op.apply,writeNat,next,wc.width,wc.zero,src]
    exact ⟨hN,sB⟩
  have finish:=block_runs sizingFinish sizing 9 n B x w sizingFinish_at wp loop.final_bound
    (by change 9+2 ≤ B;omega) readableFinish finishPeak
  let u:=applyBlock sizingFinish w
  have up:u.pc=11:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
  have uf:SizingFrame s u:=sf.trans (sizing_blocks_frame sizingFinish w (Or.inr (Or.inr rfl)))
  have stop:BoundedExecution sizing n x B u 1 u:=.halt finish.final_bound (by simp only [step,up,sizing_halt])
  refine ⟨u,?_,up,header.transport (uf.frame (p:=p)).2.2.2.2,?_,?_,?_,uf⟩
  · convert boot.executes (loop.executes (finish.executes stop)) using 1
    simp only [show sizingBoot.length=5 from rfl,show sizingFinish.length=2 from rfl]
    omega
  all_goals simp [u,sizingFinish,applyBlock,Op.apply,writeNat,next,wc.width,wc.zero,src]

/-- Internal zero survives every helper and is used by the later caller blocks. -/
def ReadyHeader (p : Parameters) (s : State) : Prop :=
  Header p s ∧ s.natReg 489=width p.K ∧ s.natReg 526=p.S ∧ s.natReg 670=0

theorem ReadyHeader.rank {p : Parameters} {s : State} (h:ReadyHeader p s) :
    UniformRankKernelMachine.Headers p.rank s := by
  constructor
  all_goals first
    | exact h.2.1
    | exact h.1 _ (by decide)

theorem ReadyHeader.spectrum {p : Parameters} {s : State} (h:ReadyHeader p s) :
    UniformKernelSpectrumMachine.Header p.K p.S p.A p.d p.C p.D s := by
  constructor
  all_goals first | exact h.2.2.1 | exact h.1 _ (by decide)

theorem ReadyHeader.withPC {p : Parameters} {s : State} (h:ReadyHeader p s) (pc : ℕ) :
    ReadyHeader p (setPC s pc) := ⟨h.1.withPC pc,h.2.1,h.2.2.1,h.2.2.2⟩

/-- The zero is not an original input value; it is produced by sizing12. -/
theorem sizing_call (p : Parameters) (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (header:Header p s) (hp:s.pc=0) (hs:WordBound B s) (layout:Layout p B) : ∃u,
    BoundedRuns program n x B s (4*p.K+9) u ∧ u.pc=12 ∧ ReadyHeader p u ∧ Frame p s u := by
  have hc:=layout.2.2.2.2.2.2
  have hN:=layout.2.1.bounds.2.1
  obtain ⟨v,run,vp,vh,vN,vS,v0,vf⟩:=sizing_execution p B n x s header hp hs hc hN
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed sizing_code
    (by rw [sizing_length];omega) (by omega) run
  have pe:placed 0 s=s:=by cases s;simp [placed]
  rw [pe] at placedRun
  exact ⟨setPC v 12,placedRun,rfl,⟨vh.withPC 12,vN,vS,v0⟩,vf.frame.withPC 12⟩


theorem rank_code : CodeAt UniformRankKernelMachine.program program 12 102 := by
  let before:Program:=sizing.map (relocate 0 12)
  let after:Program:=UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++ UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++ UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have hb:before.length=12:=by simp only [before,List.length_map,sizing_length]
  have he:program=before ++ UniformRankKernelMachine.program.map (relocate 12 102) ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact segment_code before after _ 12 102 hb

theorem spectrum_code : CodeAt UniformKernelSpectrumMachine.program program 102 399 := by
  let before:Program:=sizing.map (relocate 0 12) ++ UniformRankKernelMachine.program.map (relocate 12 102)
  let after:Program:=crossSetup.map Op.code ++ UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++ UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have hb:before.length=102:=by simp only [before,List.length_append,List.length_map,sizing_length,UniformRankKernelMachine.program_length]
  have he:program=before ++ UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact segment_code before after _ 102 399 hb

theorem cross_code : CodeAt UniformToeplitzCrossTopologyMachine.program program 402 673 := by
  let before:Program:=sizing.map (relocate 0 12) ++ UniformRankKernelMachine.program.map (relocate 12 102) ++ UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code
  let after:Program:=depthSetup.map Op.code ++ UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have hb:before.length=402:=by simp only [before,List.length_append,List.length_map,sizing_length,UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length,crossSetup_length]
  have he:program=before ++ UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact segment_code before after _ 402 673 hb

theorem depth_code : CodeAt UniformDAGDepthMachine.program program 686 721 := by
  let before:Program:=sizing.map (relocate 0 12) ++ UniformRankKernelMachine.program.map (relocate 12 102) ++ UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++ UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code
  let after:Program:=[.halt]
  have hb:before.length=686:=by simp only [before,List.length_append,List.length_map,sizing_length,UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length,crossSetup_length,UniformToeplitzCrossTopologyMachine.program_length,depthSetup_length]
  have he:program=before ++ UniformDAGDepthMachine.program.map (relocate 686 721) ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact segment_code before after _ 686 721 hb

theorem block_of_segment (b : List Op) (before after : Program) (base : ℕ) (hb:before.length=base) :
    BlockAt b (before ++ b.map Op.code ++ after) base := by
  intro i hi
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,hb];omega)]
  rw [List.getElem?_append_right (by omega)]
  simp only [hb,show base+i-base=i by omega,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]

theorem crossSetup_at : BlockAt crossSetup program 399 := by
  let before:Program:=sizing.map (relocate 0 12) ++ UniformRankKernelMachine.program.map (relocate 12 102) ++ UniformKernelSpectrumMachine.program.map (relocate 102 399)
  let after:Program:=UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++ UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have hb:before.length=399:=by simp only [before,List.length_append,List.length_map,sizing_length,UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length]
  have he:program=before ++ crossSetup.map Op.code ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact block_of_segment crossSetup before after 399 hb

theorem depthSetup_at : BlockAt depthSetup program 673 := by
  let before:Program:=sizing.map (relocate 0 12) ++ UniformRankKernelMachine.program.map (relocate 12 102) ++ UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++ UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673)
  let after:Program:=UniformDAGDepthMachine.program.map (relocate 686 721) ++ [.halt]
  have hb:before.length=673:=by simp only [before,List.length_append,List.length_map,sizing_length,UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length,crossSetup_length,UniformToeplitzCrossTopologyMachine.program_length]
  have he:program=before ++ depthSetup.map Op.code ++ after:=by
    simp only [program,before,after,List.append_assoc]
  rw [he]
  exact block_of_segment depthSetup before after 673 hb



def Working (r : ℕ) : Prop := Preserved r ∨ r=489 ∨ r=526 ∨ r=670

theorem ReadyHeader.transport {p : Parameters} {s t : State} (h:ReadyHeader p s)
    (f:∀r,Working r → t.natReg r=s.natReg r) : ReadyHeader p t :=
  ⟨h.1.transport (fun r hr=>f r (Or.inl hr)),
    (f 489 (Or.inr (Or.inl rfl))).trans h.2.1,
    (f 526 (Or.inr (Or.inr (Or.inl rfl)))).trans h.2.2.1,
    (f 670 (Or.inr (Or.inr (Or.inr rfl)))).trans h.2.2.2⟩

theorem working_rank_range {r : ℕ} (hr:Working r) : r < 491 ∨ 524 < r := by
  simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  omega

theorem working_spectrum_range {r : ℕ} (hr:Working r) : UniformKernelSpectrumMachine.Persistent r := by
  simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  unfold UniformKernelSpectrumMachine.Persistent
  omega

theorem working_cross_range {r : ℕ} (hr:Working r) :
    ((r < 70 ∨ 96 < r) ∧ (r < 400 ∨ 419 < r) ∧ (r < 565 ∨ 599 < r)) := by
  simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  omega

theorem working_depth_range {r : ℕ} (hr:Working r) : r < 654 ∨ 666 ≤ r := by
  simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  omega

theorem rank_working {p : Parameters} {s t : State} (h:UniformRankKernelMachine.Frame p.rank s t) :
    ∀r,Working r → t.natReg r=s.natReg r := fun r hr=>h.2.2.2.1 r (working_rank_range hr)

theorem spectrum_working {p : Parameters} {s t : State}
    (h:UniformKernelSpectrumMachine.Frame p.K p.A p.d p.C s t) :
    ∀r,Working r → t.natReg r=s.natReg r := fun r hr=>h.2.2.2.2 r (working_spectrum_range hr)

theorem cross_working {s t : State} (h:UniformToeplitzCrossTopologyMachine.Frame s t) :
    ∀r,Working r → t.natReg r=s.natReg r := fun r hr=>h.2.2.2.2 r (working_cross_range hr)

theorem depth_working {s t : State} (h:UniformDAGDepthMachine.Frame s t) :
    ∀r,Working r → t.natReg r=s.natReg r := fun r hr=>h.2.2.2.2 r (working_depth_range hr)

theorem rank_frame {p : Parameters} {s t : State} (h:UniformRankKernelMachine.Frame p.rank s t) : Frame p s t :=
  ⟨fun q _ _ _ _=>congrFun h.1 q,fun q hq _ _=>h.2.2.2.2.2 q hq,
    h.2.1,h.2.2.1,fun r hr=>rank_working h r (Or.inl hr)⟩

theorem spectrum_frame {p : Parameters} {s t : State}
    (h:UniformKernelSpectrumMachine.Frame p.K p.A p.d p.C s t) : Frame p s t :=
  ⟨fun q hq _ _ _=>h.1 q hq,fun q _ hq hc=>h.2.1 q hq hc,
    h.2.2.1,h.2.2.2.1,fun r hr=>spectrum_working h r (Or.inl hr)⟩

theorem cross_frame {p : Parameters} {s t : State}
    (h:UniformToeplitzCrossTopologyMachine.Frame s t)
    (outside:∀q,(q < p.conv ∨ p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ q) →
      (q < p.tape ∨ p.tape+5*Shape p ≤ q) → t.natHeap q=s.natHeap q) : Frame p s t :=
  ⟨fun q _ a b _=>outside q a b,fun q _ _ _=>congrFun h.1 q,
    h.2.2.1,h.2.2.2.1,fun r hr=>cross_working h r (Or.inl hr)⟩

theorem depth_frame {p : Parameters} {s t : State} (h:UniformDAGDepthMachine.Frame s t)
    (outside:UniformDAGDepthMachine.Outside p.depth (p.e+1+Shape p) s t) : Frame p s t :=
  ⟨fun q _ _ _ hq=>outside q (by simpa only [Nat.add_assoc] using hq),fun q _ _ _=>congrFun h.1 q,
    h.2.2.1,h.2.2.2.1,fun r hr=>depth_working h r (Or.inl hr)⟩

/-- No header or heap reset is performed by the host between phases. -/
theorem rank_call (p : Parameters) (B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (header:ReadyHeader p s) (layout:Layout p B)
    (bh:UniformRankKernelMachine.Bank p.H p.hSize h s)
    (bg:UniformRankKernelMachine.Bank p.G p.gSize g s)
    (hp:s.pc=12) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (UniformRankKernelMachine.runtime p.rank) u ∧ u.pc=102 ∧
    ReadyHeader p u ∧ UniformRankKernelMachine.KernelBank p.rank p.K h g u ∧
    UniformRankKernelMachine.Bank p.H p.hSize h u ∧ UniformRankKernelMachine.Bank p.G p.gSize g u ∧
    Frame p s u := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by have :=layout.2.2.2.2.2.2;omega)
  obtain ⟨v,run,kernels,_,hbank,gbank,fr,vp⟩:=UniformRankKernelMachine.rank_kernel_execution
    p.rank B p.K n h g x e (header.withPC 0).rank layout.1 rfl bh bg rfl eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed rank_code
    (by rw [UniformRankKernelMachine.program_length];have :=layout.2.2.2.2.2.2;omega)
    (by have :=layout.2.2.2.2.2.2;omega) run
  have pe:placed 12 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 102
  have wh:ReadyHeader p u:=((header.withPC 0).transport (rank_working fr)).withPC 102
  exact ⟨u,placedRun,rfl,wh,kernels,hbank,gbank,(rank_frame fr).withPC 102⟩

def kernelValues (p : Parameters) (h g : ℕ → ℂ) := UniformToeplitzCrossDAG.rankKernels p.K p.a p.e
  (UniformRankKernelMachine.matrixValue p.rank h g) (UniformRankKernelMachine.vValue p.rank h)
  (UniformRankKernelMachine.wValue p.rank g)

theorem kernel_bank_spectrum {p : Parameters} {h g : ℕ → ℂ} {s : State}
    (bank:UniformRankKernelMachine.KernelBank p.rank p.K h g s) :
    UniformKernelSpectrumMachine.Kernels p.K p.S (kernelValues p h g) s := bank

theorem Frame.master {p : Parameters} {B : ℕ} {s t : State} (f:Frame p s t) (layout:Layout p B) :
    t.scalarHeap 0=s.scalarHeap 0 := by
  have Spos:=layout.1.masterFresh
  have Apos:=layout.2.1.arenaPositive
  have Cpos:=lt_of_lt_of_le Apos layout.2.1.arena_le_bank
  exact f.2.1 0 (Or.inl Spos) (Or.inl Apos) (Or.inl Cpos)


/-- Enriches the frozen spectrum API with the actually retained extracted root.
The proof reuses its literal loop/root/power executions, without frozen edits. -/
theorem spectrum_execution_root (n K S A d C D B : ℕ) (values : Fin 6 → Fin (width K) → ℂ)
    (x : Fin n → ℂ) (s : State) (header:UniformKernelSpectrumMachine.Header K S A d C D s)
    (layout:UniformKernelSpectrumMachine.Layout K S A d C D B) (kernels:UniformKernelSpectrumMachine.Kernels K S values s)
    (master:s.scalarHeap 0=some (prepared (zeta D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution UniformKernelSpectrumMachine.program n x B s t u ∧ t ≤ UniformKernelSpectrumMachine.runtimeBudget D K ∧
    UniformKernelSpectrumMachine.Result K C values u ∧ UniformKernelSpectrumMachine.Kernels K S values u ∧ UniformKernelSpectrumMachine.Header K S A d C D u ∧
    UniformKernelSpectrumMachine.Frame K A d C s u ∧ u.scalarHeap 0=s.scalarHeap 0 ∧ u.pc=296 ∧ u.scalarHeap (C+7*width K)=some (prepared (zeta (width K))) := by
  have bounds:=layout.bounds
  have Cpos:0 < C:=lt_of_lt_of_le layout.arenaPositive layout.arena_le_bank
  obtain ⟨v,init,vc,vf⟩:=UniformKernelSpectrumMachine.initialize_driver n K S A d C D B x s header hp hs
    bounds.1 bounds.2.1 bounds.2.2.1
  have initialFrame:UniformKernelSpectrumMachine.Frame K A d C s v:=vf.frame
  have vk:=kernels.frame initialFrame layout
  have vm:v.scalarHeap 0=some (prepared (zeta D)):=(initialFrame.master layout.arenaPositive Cpos).trans master
  have pfx:UniformKernelSpectrumMachine.SpectraPrefix K C 0 values v:=by intro b hb;omega
  obtain ⟨w,t,loop,tc,wc,wp,wk,ws,wf⟩:=UniformKernelSpectrumMachine.spectra_loop n K S A d C D B 0 6 values x v vc
    (by omega) layout vk vm pfx init.final_bound
  have safe:=UniformKernelSpectrumMachine.rootSetup_safe w wc layout
  have startRoot:=block_runs UniformKernelSpectrumMachine.rootSetup UniformKernelSpectrumMachine.program 260 n B x w UniformKernelSpectrumMachine.rootSetup_at wp loop.final_bound
    (by change 260+5 ≤ B;omega) safe.1 safe.2
  let z:=applyBlock UniformKernelSpectrumMachine.rootSetup w
  have zc:=UniformKernelSpectrumMachine.rootSetup_spec w wc
  have zp:z.pc=265:=by rw [UniformTensorMonomialMachine.applyBlock_pc,wp];rfl
  have zf:UniformKernelSpectrumMachine.Frame K A d C s z:=initialFrame.trans (wf.trans
    (UniformKernelSpectrumMachine.pure_frame K A d C UniformKernelSpectrumMachine.rootSetup w (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have zm:z.scalarHeap 0=some (prepared (zeta D)):=(zf.master layout.arenaPositive Cpos).trans master
  obtain ⟨q,root,qc,qp,qr,qoutside,qf,qoff⟩:=UniformKernelSpectrumMachine.root_call n K S A d C D B x z zc.1 layout
    zm zc.2.1 zc.2.2.1 zp startRoot.final_bound
  have qo:q.natReg 537=C+7*width K:=qoff.trans zc.2.2.2
  have qs:UniformKernelSpectrumMachine.SpectraPrefix K C 6 values q:=ws.transport (by
    intro b hb j
    exact qoutside _ (ne_of_lt (UniformKernelSpectrumMachine.spectrum_address_end K C b j)))
  have psafe:=UniformKernelSpectrumMachine.powerSetup_safe q qc qo layout
  have startPower:=block_runs UniformKernelSpectrumMachine.powerSetup UniformKernelSpectrumMachine.program 282 n B x q UniformKernelSpectrumMachine.powerSetup_at qp root.final_bound
    (by change 282+3 ≤ B;omega) psafe.1 psafe.2
  let r:=applyBlock UniformKernelSpectrumMachine.powerSetup q
  have rc:=UniformKernelSpectrumMachine.powerSetup_spec q qc qo
  have rp:r.pc=285:=by rw [UniformTensorMonomialMachine.applyBlock_pc,qp];rfl
  obtain ⟨u,power,uc,up,upowers,uoutside,uf⟩:=UniformKernelSpectrumMachine.power_call n K S A d C D B x r rc.1 layout
    rc.2 qr rp startPower.final_bound
  have us:UniformKernelSpectrumMachine.SpectraPrefix K C 6 values u:=qs.transport (by
    intro b hb j
    exact uoutside _ (Or.inr (by omega)))
  have frame:UniformKernelSpectrumMachine.Frame K A d C s u:=zf.trans (qf.trans
    ((UniformKernelSpectrumMachine.pure_frame K A d C UniformKernelSpectrumMachine.powerSetup q (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans uf))
  have stop:BoundedExecution UniformKernelSpectrumMachine.program n x B u 1 u:=.halt power.final_bound
    (by simp only [step,up,UniformKernelSpectrumMachine.final_halt])
  refine ⟨u,4*K+12+t+5+(9+UniformPowerMachine.loopCost (D/width K))+3+(6*width K+6)+1,
    ?_,?_,UniformKernelSpectrumMachine.Result.of_parts upowers us,kernels.frame frame layout,uc.header,frame,
    frame.master layout.arenaPositive Cpos,up,?_⟩
  · convert init.executes (loop.executes (startRoot.executes (root.executes (startPower.executes (power.executes stop))))) using 1
    simp only [show UniformKernelSpectrumMachine.rootSetup.length=5 from rfl,show UniformKernelSpectrumMachine.powerSetup.length=3 from rfl]
    omega
  · unfold UniformKernelSpectrumMachine.runtimeBudget UniformKernelSpectrumMachine.iterationBudget at *
    omega
  · exact (uoutside _ (Or.inr (by omega))).trans qr



theorem Frame.source {p : Parameters} {B a size : ℕ} {s u : State} {f : ℕ → ℂ}
    (frame:Frame p s u) (layout:Layout p B)
    (source:UniformRankKernelMachine.Bank a size f s) (fresh:a+size ≤ p.S) :
    UniformRankKernelMachine.Bank a size f u := by
  intro i hi
  have hS:a+i < p.S:=by omega
  have hA:a+i < p.A:=by have :=layout.2.1.sourceEnd;omega
  have hC:a+i < p.C:=lt_of_lt_of_le hA layout.2.1.arena_le_bank
  exact (frame.2.1 (a+i) (Or.inl hS) (Or.inl hA) (Or.inl hC)).trans (source i hi)

theorem spectrum_call (p : Parameters) (B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (header:ReadyHeader p s) (layout:Layout p B)
    (kernels:UniformRankKernelMachine.KernelBank p.rank p.K h g s)
    (master:s.scalarHeap 0=some (prepared (zeta p.D))) (hp:s.pc=102) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ UniformKernelSpectrumMachine.runtimeBudget p.D p.K ∧
    u.pc=399 ∧ ReadyHeader p u ∧
    UniformKernelSpectrumMachine.Result p.K p.C (kernelValues p h g) u ∧
    u.scalarHeap (p.C+7*width p.K)=some (prepared (zeta (width p.K))) ∧ Frame p s u := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by have :=layout.2.2.2.2.2.2;omega)
  obtain ⟨v,t,run,tc,bank,_,_,fr,_,vp,root⟩:=spectrum_execution_root n p.K p.S p.A p.d p.C p.D B
    (kernelValues p h g) x e (header.withPC 0).spectrum layout.2.1 (kernel_bank_spectrum kernels) master rfl eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed spectrum_code
    (by rw [UniformKernelSpectrumMachine.program_length];have :=layout.2.2.2.2.2.2;omega)
    (by have :=layout.2.2.2.2.2.2;omega) run
  have pe:placed 102 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 399
  have wh:ReadyHeader p u:=((header.withPC 0).transport (spectrum_working fr)).withPC 399
  exact ⟨u,t,placedRun,tc,rfl,wh,bank,root,(spectrum_frame fr).withPC 399⟩

/-- Only charged additions install the actual cross arguments. -/
theorem crossSetup_spec {p : Parameters} {s : State} (h:ReadyHeader p s) :
    ReadyHeader p (applyBlock crossSetup s) ∧
    UniformToeplitzCrossTopologyMachine.Params p.K p.a p.e p.conv p.tape (applyBlock crossSetup s) := by
  have working:∀r,Working r → (applyBlock crossSetup s).natReg r=s.natReg r:=by
    intro r hr
    simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
    simp (disch:=omega) [crossSetup,applyBlock,Op.apply,writeNat,next]
  have hk:s.natReg 525=p.K:=h.1 _ (by decide)
  have ha:s.natReg 484=p.a:=h.1 _ (by decide)
  have he:s.natReg 485=p.e:=h.1 _ (by decide)
  have hc:s.natReg 563=p.conv:=h.1 _ (by decide)
  have hd:s.natReg 564=p.tape:=h.1 _ (by decide)
  refine ⟨h.transport working,?_,?_,?_,?_,?_⟩
  all_goals simp [crossSetup,applyBlock,Op.apply,writeNat,next,h.2.2.2,hk,ha,he,hc,hd]

theorem crossSetup_safe {p : Parameters} {s : State} (h:ReadyHeader p s) {B : ℕ} (hs:WordBound B s) :
    readable crossSetup s ∧ peak crossSetup s ≤ B := by
  have h525:=hs.2.1 525;have h484:=hs.2.1 484;have h485:=hs.2.1 485
  simpa [readable,crossSetup,Op.readable,peak,Op.peak,Op.apply,writeNat,next,h.2.2.2] using
    And.intro h525 (And.intro h484 h485)

theorem caller_frame (p : Parameters) (b : List Op) (s : State) (hb:b=crossSetup ∨ b=depthSetup) :
    Frame p s (applyBlock b s) := by
  rcases hb with rfl|rfl
  all_goals refine ⟨fun _ _ _ _ _=>rfl,fun _ _ _ _=>rfl,rfl,rfl,?_⟩
  all_goals intro r hr
  all_goals simp only [Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
  all_goals simp (disch:=omega) [crossSetup,depthSetup,applyBlock,Op.apply,writeNat,next]

theorem conv_size (p : Parameters) : UniformToeplitzCrossTopologyMachine.G p.K=
    3*p.K*width p.K+2*width p.K := by
  unfold UniformToeplitzCrossTopologyMachine.G
  rw [←UniformConvolutionDAG.records_length,UniformConvolutionDAG.gate_count,←width_eq]

theorem cross_size (p : Parameters) (ha:p.a ≤ width p.K) (he:p.e ≤ width p.K) :
    (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e ha he).size=Shape p := by
  rw [UniformToeplitzCrossDAG.crossDAG_size,←width_eq]
  rfl

/-- The physical typed tape is generated here from the integer arguments. -/
theorem cross_call (p : Parameters) (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (header:ReadyHeader p s) (layout:Layout p B)
    (args:UniformToeplitzCrossTopologyMachine.Params p.K p.a p.e p.conv p.tape s)
    (hp:s.pc=402) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧
    t ≤ 4*p.K+113+(19*p.K+344)*UniformToeplitzCrossTopologyMachine.G p.K+40*p.a ∧
    u.pc=673 ∧ ReadyHeader p u ∧
    UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape u ∧ Frame p s u ∧ u.scalarHeap=s.scalarHeap := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by have :=layout.2.2.2.2.2.2;omega)
  obtain ⟨v,t,run,tc,tape,fr,_,_,vp,outside⟩:=UniformToeplitzCrossTopologyMachine.typed_execution
    n p.K p.a p.e p.conv p.tape B x e layout.1.widthA layout.1.widthE args rfl layout.2.2.1 eb layout.2.2.2.1
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed cross_code
    (by rw [UniformToeplitzCrossTopologyMachine.program_length];have :=layout.2.2.2.2.2.2;omega)
    (by have :=layout.2.2.2.2.2.2;omega) run
  have pe:placed 402 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 673
  have wh:ReadyHeader p u:=((header.withPC 0).transport (cross_working fr)).withPC 673
  have outside':∀q,(q < p.conv ∨ p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ q) →
    (q < p.tape ∨ p.tape+5*Shape p ≤ q) → u.natHeap q=s.natHeap q:=by
    intro q a b
    have eqn:6*UniformToeplitzCrossTopologyMachine.G p.K+2*p.a=Shape p:=by rw [conv_size];rfl
    exact outside q a (by simpa only [eqn] using b)
  exact ⟨u,t,placedRun,tc,rfl,wh,tape,(cross_frame fr outside'),fr.1⟩



/-- The depth gate count is computed from K, physical N489 and a484. -/
theorem depthSetup_spec {p : Parameters} {s : State} (h:ReadyHeader p s) :
    ReadyHeader p (applyBlock depthSetup s) ∧
    UniformDAGDepthMachine.Header p.e (Shape p) p.tape p.depth (applyBlock depthSetup s) := by
  have working:∀r,Working r → (applyBlock depthSetup s).natReg r=s.natReg r:=by
    intro r hr
    simp only [Working,Preserved,headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
    simp (disch:=omega) [depthSetup,applyBlock,Op.apply,writeNat,next]
  have hk:s.natReg 525=p.K:=h.1 _ (by decide)
  have ha:s.natReg 484=p.a:=h.1 _ (by decide)
  have he:s.natReg 485=p.e:=h.1 _ (by decide)
  have ht:s.natReg 564=p.tape:=h.1 _ (by decide)
  have hd:s.natReg 675=p.depth:=h.1 _ (by decide)
  refine ⟨h.transport working,?_,?_,?_,?_⟩
  all_goals simp [depthSetup,applyBlock,Op.apply,writeNat,next,h.2.1,h.2.2.2,hk,ha,he,ht,hd,Shape]
  ring

theorem depthSetup_safe {p : Parameters} {s : State} (h:ReadyHeader p s) {B : ℕ} (layout:Layout p B) :
    readable depthSetup s ∧ peak depthSetup s ≤ B := by
  have shapeB:Shape p ≤ B:=by have :=layout.2.2.2.2.2.1;omega
  have eB:p.e ≤ B:=by have :=layout.2.2.2.2.2.1;omega
  have depthB:p.depth ≤ B:=by have :=layout.2.2.2.2.2.1;omega
  have tapeB:p.tape ≤ B:=by have :=layout.2.2.2.2.1;omega
  have codeB:=layout.2.2.2.2.2.2
  have hk:s.natReg 525=p.K:=h.1 _ (by decide)
  have ha:s.natReg 484=p.a:=h.1 _ (by decide)
  have he:s.natReg 485=p.e:=h.1 _ (by decide)
  have ht:s.natReg 564=p.tape:=h.1 _ (by decide)
  have hd:s.natReg 675=p.depth:=h.1 _ (by decide)
  simp [readable,depthSetup,Op.readable,peak,Op.peak,Op.apply,writeNat,next,h.2.1,h.2.2.2,hk,ha,he,ht,hd]
  unfold Shape at shapeB
  repeat' constructor
  all_goals nlinarith

/-- The generated encoded tape is the only tape read by literalDepth35. -/
theorem depth_call (p : Parameters) (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (header:ReadyHeader p s) (layout:Layout p B)
    (args:UniformDAGDepthMachine.Header p.e (Shape p) p.tape p.depth s)
    (tape:UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape s)
    (hp:s.pc=686) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ UniformDAGDepthMachine.runtimeBudget p.e (Shape p) ∧
    u.pc=721 ∧ ReadyHeader p u ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),u.natHeap (p.depth+i.val)=some
      (UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i)) ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),UniformToeplitzCrossDAG.runDepth
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i ≤ 8*p.K+6) ∧
    UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape u ∧ Frame p s u ∧ u.scalarHeap=s.scalarHeap := by
  let e:=setPC s 0
  have eb:=changePC_bound B s 0 hs (by have :=layout.2.2.2.2.2.2;omega)
  have size:=cross_size p layout.1.widthA layout.1.widthE
  have typedArgs:UniformDAGDepthMachine.Header p.e
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size p.tape p.depth e:=by
    refine ⟨args.inputs,?_,args.tape,args.bank⟩
    simpa only [size,e,setPC] using args.gates
  obtain ⟨v,t,run,tc,vp,_,bank,height,vtape,outside,fr⟩:=UniformDAGDepthMachine.cross_execution
    p.K p.a p.e layout.1.widthA layout.1.widthE p.tape p.depth B n x e typedArgs rfl tape
    (by simpa only [size] using layout.2.2.2.2.1)
    (by simpa only [size,Nat.add_assoc] using layout.2.2.2.2.2.1)
    (by have :=layout.2.2.2.2.2.2;omega) eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed depth_code
    (by rw [UniformDAGDepthMachine.program_length];have :=layout.2.2.2.2.2.2;omega)
    (by have :=layout.2.2.2.2.2.2;omega) run
  have pe:placed 686 e=s:=by cases s;simp_all [placed,e,setPC]
  rw [pe] at placedRun
  let u:=setPC v 721
  have wh:ReadyHeader p u:=((header.withPC 0).transport (depth_working fr)).withPC 721
  refine ⟨u,t,placedRun,?_,rfl,wh,?_,?_,vtape,?_,fr.1⟩
  · simpa only [size] using tc
  · exact bank
  · exact height
  · apply depth_frame (p:=p) fr
    intro q hq
    exact outside q (by simpa only [size] using hq)



theorem final_halt : program[721]?=some .halt := by
  let before:=sizing.map (relocate 0 12) ++
    UniformRankKernelMachine.program.map (relocate 12 102) ++
    UniformKernelSpectrumMachine.program.map (relocate 102 399) ++ crossSetup.map Op.code ++
    UniformToeplitzCrossTopologyMachine.program.map (relocate 402 673) ++ depthSetup.map Op.code ++
    UniformDAGDepthMachine.program.map (relocate 686 721)
  have hb:before.length=721:=by
    simp only [before,List.length_append,List.length_map,sizing_length,
      UniformRankKernelMachine.program_length,UniformKernelSpectrumMachine.program_length,
      crossSetup_length,UniformToeplitzCrossTopologyMachine.program_length,depthSetup_length,
      UniformDAGDepthMachine.program_length]
  have he:program=before ++ [.halt]:=by simp only [program,before,List.append_assoc]
  rw [he,List.getElem?_append_right (by omega),hb]
  rfl

def runtimeBudget (p : Parameters) := 4*p.K+9+UniformRankKernelMachine.runtime p.rank+
  UniformKernelSpectrumMachine.runtimeBudget p.D p.K+3+
  (4*p.K+113+(19*p.K+344)*UniformToeplitzCrossTopologyMachine.G p.K+40*p.a)+13+
  UniformDAGDepthMachine.runtimeBudget p.e (Shape p)+1

/-- Actual whole literal722 execution from original prepared H/G/master banks.
Every intermediate bank, typed tape and depth label is produced by the code. -/
theorem execution (p : Parameters) (B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (header:Header p s) (layout:Layout p B)
    (bh:UniformRankKernelMachine.Bank p.H p.hSize h s)
    (bg:UniformRankKernelMachine.Bank p.G p.gSize g s)
    (master:s.scalarHeap 0=some (prepared (zeta p.D))) (hp:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget p ∧ u.pc=721 ∧ ReadyHeader p u ∧
    UniformKernelSpectrumMachine.Result p.K p.C (kernelValues p h g) u ∧
    u.scalarHeap (p.C+7*width p.K)=some (prepared (zeta (width p.K))) ∧
    UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape u ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),
      u.natHeap (p.depth+i.val)=some (UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i)) ∧
    (∀i : Fin (p.e+1+(UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).size),
      UniformToeplitzCrossDAG.runDepth
        (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program (fun _=>0) i ≤ 8*p.K+6) ∧
    UniformRankKernelMachine.Bank p.H p.hSize h u ∧ UniformRankKernelMachine.Bank p.G p.gSize g u ∧
    Frame p s u ∧ u.scalarHeap 0=s.scalarHeap 0 := by
  have codeB:=layout.2.2.2.2.2.2
  obtain ⟨v,start,vp,vh,vf⟩:=sizing_call p B n x s header hp hs layout
  have hgv:UniformRankKernelMachine.Bank p.H p.hSize h v:=by
    exact vf.source layout bh layout.1.hFresh
  have ggv:UniformRankKernelMachine.Bank p.G p.gSize g v:=by
    exact vf.source layout bg layout.1.gFresh
  obtain ⟨w,rank,wp,wh,kernels,_,_,wf⟩:=rank_call p B n h g x v vh layout hgv ggv vp start.final_bound
  have beforeSpec:Frame p s w:=vf.trans wf
  have wm:w.scalarHeap 0=some (prepared (zeta p.D)):=(beforeSpec.master layout).trans master
  obtain ⟨z,ts,spectrum,tsB,zp,zh,bank,root,zf⟩:=spectrum_call p B n h g x w wh layout kernels wm wp rank.final_bound
  have safe:=crossSetup_safe zh spectrum.final_bound
  have crossStart:=block_runs crossSetup program 399 n B x z crossSetup_at zp spectrum.final_bound
    (by rw [crossSetup_length];omega) safe.1 safe.2
  let q:=applyBlock crossSetup z
  have qc:=crossSetup_spec zh
  have qp:q.pc=402:=by rw [UniformTensorMonomialMachine.applyBlock_pc,zp,crossSetup_length]
  obtain ⟨r,tc,cross,tcB,rp,rh,tape,rf,rs⟩:=cross_call p B n x q qc.1 layout qc.2 qp crossStart.final_bound
  have dsafe:=depthSetup_safe rh layout
  have depthStart:=block_runs depthSetup program 673 n B x r depthSetup_at rp cross.final_bound
    (by rw [depthSetup_length];omega) dsafe.1 dsafe.2
  let a:=applyBlock depthSetup r
  have ac:=depthSetup_spec rh
  have ap:a.pc=686:=by rw [UniformTensorMonomialMachine.applyBlock_pc,rp,depthSetup_length]
  have atape:UniformDAGDepthMachine.EncodedTape
      (UniformToeplitzCrossDAG.crossDAG p.K p.a p.e layout.1.widthA layout.1.widthE).program p.tape a:=tape
  obtain ⟨u,td,depth,tdB,up,uh,labels,height,utape,uf,us⟩:=depth_call p B n x a ac.1 layout ac.2 atape ap depthStart.final_bound
  have fullFrame:Frame p s u:=beforeSpec.trans (zf.trans ((caller_frame p crossSetup z (Or.inl rfl)).trans
    (rf.trans ((caller_frame p depthSetup r (Or.inr rfl)).trans uf))))
  have scalarEq:u.scalarHeap=z.scalarHeap:=us.trans rs
  have ubank:UniformKernelSpectrumMachine.Result p.K p.C (kernelValues p h g) u:=by
    intro j;rw [scalarEq];exact bank j
  have uroot:u.scalarHeap (p.C+7*width p.K)=some (prepared (zeta (width p.K))):=by rw [scalarEq];exact root
  have stop:BoundedExecution program n x B u 1 u:=.halt depth.final_bound (by simp only [step,up,final_halt])
  refine ⟨u,4*p.K+9+UniformRankKernelMachine.runtime p.rank+ts+3+tc+13+td+1,?_,?_,up,uh,ubank,uroot,
    utape,labels,height,fullFrame.source layout bh layout.1.hFresh,fullFrame.source layout bg layout.1.gFresh,
    fullFrame,fullFrame.master layout⟩
  · convert start.executes (rank.executes (spectrum.executes (crossStart.executes
      (cross.executes (depthStart.executes (depth.executes stop)))))) using 1
    simp only [crossSetup_length,depthSetup_length]
    omega
  · unfold runtimeBudget
    omega


end

end ExactFourierCircuits.UniformRankCrossPreparationMachine
