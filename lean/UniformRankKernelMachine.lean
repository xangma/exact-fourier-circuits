import UniformRankKernelPreparation
import UniformReciprocalMachine
import UniformBoundedAssembly
import UniformPairMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformRankKernelMachine
open UniformMachine UniformAssembly
open UniformPairMachine (prepared)
open UniformReciprocalMachine (Op applyBlock readable peak BlockAt block_runs)
open scoped BigOperators
noncomputable section

/-- Physical source banks are prepared scalar cells, not an expression tape
or supplied output/action certificate. -/
def Bank (a size : ℕ) (f : ℕ → ℂ) (s : State) : Prop :=
  ∀i,i < size → s.scalarHeap (a+i)=some (prepared (f i))

/-- Actual finite border sum, evaluated from the physical H/G arrays. -/
def crossSum (h g : ℕ → ℂ) (I J k : ℕ) : ℂ :=
  ∑u∈Finset.range k,h (I-J-u)*g u

theorem crossSum_zero (h g : ℕ → ℂ) (I J : ℕ) : crossSum h g I J 0=0 := by
  simp [crossSum]
theorem crossSum_succ (h g : ℕ → ℂ) (I J k : ℕ) :
    crossSum h g I J (k+1)=crossSum h g I J k+h (I-J-k)*g k :=
  Finset.sum_range_succ _ _

def crossBoot : List Op := [.literal 494 0,.sub 499 488 498,.literalScalar 54 0]
def crossTerm : List Op := [.sub 500 497 498,.sub 500 500 494,.add 500 480 500,
  .getScalar 55 500,.add 501 482 494,.getScalar 56 501,.field .mul 57 55 56,
  .field .add 54 54 57,.add 494 494 492]
def crossProgram : Program := crossBoot.map Op.code++[.branchLT 494 499 4 14]++
  crossTerm.map Op.code++[.jump 3,.halt]

theorem crossBoot_length : crossBoot.length=3 := rfl
theorem crossTerm_length : crossTerm.length=9 := rfl
theorem crossProgram_length : crossProgram.length=15 := rfl
theorem cross_boot_code : BlockAt crossBoot crossProgram 0 := by
  intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem cross_term_code : BlockAt crossTerm crossProgram 4 := by
  intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem cross_branch : crossProgram[3]?=some (.branchLT 494 499 4 14) := rfl
theorem cross_jump : crossProgram[13]?=some (.jump 3) := rfl
theorem cross_halt : crossProgram[14]?=some .halt := rfl

structure CrossHeaders (H G split I J : ℕ) (s : State) : Prop where
  hBase : s.natReg 480=H
  gBase : s.natReg 482=G
  split : s.natReg 488=split
  one : s.natReg 492=1
  row : s.natReg 497=I
  column : s.natReg 498=J

structure CrossTerm (split I J k : ℕ) (h g : ℕ → ℂ) (s : State) : Prop where
  index : s.natReg 494=k
  stop : s.natReg 499=split-J
  accumulator : s.scalarReg 54=prepared (crossSum h g I J k)

structure CrossBounds (H G hSize gSize split I J B : ℕ) : Prop where
  code : 15 ≤ B
  hEnd : H+hSize ≤ B
  gEnd : G+gSize ≤ B
  splitBound : split < gSize
  rowBound : I < hSize
  interior : split ≤ I
  columnBound : J ≤ split

def CrossFrame (s t : State) : Prop :=
  t.natHeap=s.natHeap ∧ t.scalarHeap=s.scalarHeap ∧ t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
  (∀r,r ≠ 494 → r ≠ 499 → r ≠ 500 → r ≠ 501 → t.natReg r=s.natReg r) ∧
  (∀r,(r < 54 ∨ 57 < r) → t.scalarReg r=s.scalarReg r)

theorem CrossFrame.refl (s : State) : CrossFrame s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ _ _=>rfl,fun _ _=>rfl⟩
theorem CrossFrame.trans {s t u : State} (h:CrossFrame s t) (h':CrossFrame t u) : CrossFrame s u :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun r h1 h2 h3 h4=>(h'.2.2.2.2.1 r h1 h2 h3 h4).trans (h.2.2.2.2.1 r h1 h2 h3 h4),
    fun r hr=>(h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩

theorem cross_blocks_frame (s : State) :
    CrossFrame s (applyBlock crossBoot s) ∧ CrossFrame s (applyBlock crossTerm s) := by
  constructor
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals first
    | (intro r h1 h2 h3 h4;simp (disch:=omega) [crossBoot,crossTerm,applyBlock,Op.apply,writeNat,writeScalar,next])
    | (intro r hr;simp (disch:=omega) [crossBoot,crossTerm,applyBlock,Op.apply,writeNat,writeScalar,next])

theorem CrossHeaders.withPC {H G split I J pc : ℕ} {s : State}
    (h:CrossHeaders H G split I J s) : CrossHeaders H G split I J {s with pc:=pc} :=
  ⟨h.hBase,h.gBase,h.split,h.one,h.row,h.column⟩
theorem CrossTerm.withPC {split I J k pc : ℕ} {h g : ℕ → ℂ} {s : State}
    (p:CrossTerm split I J k h g s) : CrossTerm split I J k h g {s with pc:=pc} :=
  ⟨p.index,p.stop,p.accumulator⟩
theorem CrossHeaders.frame {H G split I J : ℕ} {s t : State}
    (h:CrossHeaders H G split I J s) (f:CrossFrame s t) : CrossHeaders H G split I J t := by
  constructor
  · exact (f.2.2.2.2.1 480 (by decide) (by decide) (by decide) (by decide)).trans h.hBase
  · exact (f.2.2.2.2.1 482 (by decide) (by decide) (by decide) (by decide)).trans h.gBase
  · exact (f.2.2.2.2.1 488 (by decide) (by decide) (by decide) (by decide)).trans h.split
  · exact (f.2.2.2.2.1 492 (by decide) (by decide) (by decide) (by decide)).trans h.one
  · exact (f.2.2.2.2.1 497 (by decide) (by decide) (by decide) (by decide)).trans h.row
  · exact (f.2.2.2.2.1 498 (by decide) (by decide) (by decide) (by decide)).trans h.column

theorem cross_boot_values (H G split I J : ℕ) (h g : ℕ → ℂ) (s : State)
    (p:CrossHeaders H G split I J s) :
    CrossHeaders H G split I J (applyBlock crossBoot s) ∧
    CrossTerm split I J 0 h g (applyBlock crossBoot s) := by
  refine ⟨p.frame (cross_blocks_frame s).1,?_⟩
  constructor <;> simp [crossBoot,applyBlock,Op.apply,writeNat,writeScalar,next,p.split,p.column,prepared,crossSum_zero]

theorem cross_term_values (H G hSize gSize split I J k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (p:CrossHeaders H G split I J s) (t:CrossTerm split I J k h g s)
    (bh:Bank H hSize h s) (bg:Bank G gSize g s)
    (bounds:CrossBounds H G hSize gSize split I J B) (hk:k < split-J) :
    CrossHeaders H G split I J (applyBlock crossTerm s) ∧
    CrossTerm split I J (k+1) h g (applyBlock crossTerm s) := by
  have hhi:I-J-k < hSize:=by have h:=bounds.rowBound;omega
  have hgi:k < gSize:=by have h:=bounds.splitBound;omega
  have hh:=bh _ hhi;have hg:=bg _ hgi
  refine ⟨p.frame (cross_blocks_frame s).2,?_⟩
  constructor <;> simp [crossTerm,applyBlock,Op.apply,writeNat,writeScalar,next,
    p.hBase,p.gBase,p.row,p.column,p.one,t.index,t.stop,t.accumulator,
    hh,hg,prepared,evalField,crossSum_succ]

theorem Bank.withPC {a size pc : ℕ} {f : ℕ → ℂ} {s : State} (h:Bank a size f s) :
    Bank a size f {s with pc:=pc} := h

theorem Bank.frame {a size : ℕ} {f : ℕ → ℂ} {s t : State} (h:Bank a size f s) (hf:CrossFrame s t) :
    Bank a size f t := by intro i hi;exact (congrFun hf.2.1 _).trans (h i hi)

theorem CrossFrame.withPC {s t : State} (h:CrossFrame s t) (pc : ℕ) : CrossFrame s {t with pc:=pc} :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

theorem cross_boot_safe (H G hSize gSize split I J B : ℕ) (s : State)
    (p:CrossHeaders H G split I J s) (bounds:CrossBounds H G hSize gSize split I J B) :
    readable crossBoot s ∧ peak crossBoot s ≤ B := by
  have hb:=bounds.gEnd;have hs:=bounds.splitBound
  simp [crossBoot,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,p.split,p.column]
  omega

theorem cross_term_safe (H G hSize gSize split I J k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (p:CrossHeaders H G split I J s) (t:CrossTerm split I J k h g s)
    (bh:Bank H hSize h s) (bg:Bank G gSize g s)
    (bounds:CrossBounds H G hSize gSize split I J B) (hk:k < split-J) :
    readable crossTerm s ∧ peak crossTerm s ≤ B := by
  have hhi:I-J-k < hSize:=by have h:=bounds.rowBound;omega
  have hgi:k < gSize:=by have h:=bounds.splitBound;omega
  have hh:=bh _ hhi;have hg:=bg _ hgi
  have hhB:=bounds.hEnd;have hgB:=bounds.gEnd;have hiB:=bounds.rowBound
  simp [crossTerm,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,writeScalar,next,
    p.hBase,p.gBase,p.row,p.column,p.one,t.index,t.accumulator,hh,hg,prepared,evalField]
  omega

theorem cross_iteration (H G hSize gSize split I J k B n : ℕ) (h g : ℕ → ℂ)
    (x : Fin n → ℂ) (s : State) (p:CrossHeaders H G split I J s) (t:CrossTerm split I J k h g s)
    (bh:Bank H hSize h s) (bg:Bank G gSize g s) (bounds:CrossBounds H G hSize gSize split I J B)
    (hk:k < split-J) (hp:s.pc=3) (hs:WordBound B s) : ∃u,
    BoundedRuns crossProgram n x B s 11 u ∧ CrossHeaders H G split I J u ∧
    CrossTerm split I J (k+1) h g u ∧ CrossFrame s u ∧ u.pc=3 := by
  have hcode:=bounds.code
  let a:State:={s with pc:=4}
  have ab:=changePC_bound B s 4 hs (by omega)
  have hd:BoundedRuns crossProgram n x B s 1 a:=
    .next hs (by simp [step,hp,cross_branch,t.index,t.stop,hk,a]) (.refl ab)
  have p':CrossHeaders H G split I J a:=p.withPC
  have t':CrossTerm split I J k h g a:=t.withPC
  have safe:=cross_term_safe H G hSize gSize split I J k B h g a p' t' bh.withPC bg.withPC bounds hk
  have body:=block_runs crossTerm crossProgram 4 n B x a cross_term_code rfl ab
    (by rw [crossTerm_length];omega) safe.1 safe.2
  have bt:=(cross_term_values H G hSize gSize split I J k B h g a p' t' bh.withPC bg.withPC bounds hk)
  let u:State:={applyBlock crossTerm a with pc:=3}
  have ub:=changePC_bound B (applyBlock crossTerm a) 3 body.final_bound (by omega)
  have bp:(applyBlock crossTerm a).pc=13:=by
    rw [UniformReciprocalMachine.applyBlock_pc,crossTerm_length]
  have jump:BoundedRuns crossProgram n x B (applyBlock crossTerm a) 1 u:=
    .next body.final_bound (by simp [step,bp,cross_jump,u]) (.refl ub)
  refine ⟨u,?_,bt.1.withPC,bt.2.withPC,?_,rfl⟩
  · convert hd.trans (body.trans jump) using 1;rfl
  · exact ((cross_blocks_frame a).2).withPC 3

theorem cross_loop (H G hSize gSize split I J k f B n : ℕ) (h g : ℕ → ℂ)
    (x : Fin n → ℂ) (s : State) (p:CrossHeaders H G split I J s) (t:CrossTerm split I J k h g s)
    (bh:Bank H hSize h s) (bg:Bank G gSize g s) (bounds:CrossBounds H G hSize gSize split I J B)
    (hf:k+f=split-J) (hp:s.pc=3) (hs:WordBound B s) : ∃u,
    BoundedRuns crossProgram n x B s (11*f+1) u ∧ CrossHeaders H G split I J u ∧
    CrossTerm split I J (split-J) h g u ∧ CrossFrame s u ∧ u.pc=14 := by
  induction f generalizing k s with
  | zero =>
    have he:k=split-J:=by omega
    subst k
    let u:State:={s with pc:=14}
    have hcode:=bounds.code
    have ub:=changePC_bound B s 14 hs (by omega)
    refine ⟨u,?_,p.withPC,t.withPC,(CrossFrame.refl s).withPC 14,rfl⟩
    exact .next hs (by simp [step,hp,cross_branch,t.index,t.stop,u]) (.refl ub)
  | succ f ih =>
    obtain ⟨v,run,vp,vt,vf,vpc⟩:=cross_iteration H G hSize gSize split I J k B n h g x s p t bh bg bounds
      (by omega) hp hs
    obtain ⟨u,tail,up,ut,uf,upc⟩:=ih (k+1) v vp vt (bh.frame vf) (bg.frame vf) (by omega) vpc run.final_bound
    refine ⟨u,?_,up,ut,vf.trans uf,upc⟩
    convert run.trans tail using 1
    omega

/-- Literal15-instruction helper, exact finite convolution charge, no output
bank/action premise, no root instruction or data-dependent scalar branch. -/
theorem cross_execution (H G hSize gSize split I J B n : ℕ) (h g : ℕ → ℂ)
    (x : Fin n → ℂ) (s : State) (p:CrossHeaders H G split I J s)
    (bh:Bank H hSize h s) (bg:Bank G gSize g s) (bounds:CrossBounds H G hSize gSize split I J B)
    (hp:s.pc=0) (hs:WordBound B s) : ∃u,
    BoundedExecution crossProgram n x B s (11*(split-J)+5) u ∧
    CrossFrame s u ∧ CrossHeaders H G split I J u ∧ u.pc=14 ∧
    u.scalarReg 54=prepared (OAI.ExactFourier.ToeplitzLayers.cross split h g I J) := by
  have hc:=bounds.code
  have safe:=cross_boot_safe H G hSize gSize split I J B s p bounds
  have boot:=block_runs crossBoot crossProgram 0 n B x s cross_boot_code hp hs
    (by rw [crossBoot_length];omega) safe.1 safe.2
  let a:=applyBlock crossBoot s
  have av:=cross_boot_values H G split I J h g s p
  have af:CrossFrame s a:=(cross_blocks_frame s).1
  have ap:a.pc=3:=by rw [UniformReciprocalMachine.applyBlock_pc,crossBoot_length,hp]
  obtain ⟨u,loop,up,ut,uf,upc⟩:=cross_loop H G hSize gSize split I J 0 (split-J) B n h g x a av.1 av.2
    (bh.frame af) (bg.frame af) bounds (by omega) ap boot.final_bound
  have last:BoundedExecution crossProgram n x B u 1 u:=.halt loop.final_bound
    (by simp [step,upc,cross_halt])
  refine ⟨u,?_,af.trans uf,up,upc,ut.accumulator⟩
  convert boot.executes (loop.executes last) using 1
  rw [crossBoot_length]
  omega


/-- Caller header values. The only source premise is an actual prepared H/G
bank; every output value is computed by the literal code below. -/
structure Parameters where
  H : ℕ
  G : ℕ
  hSize : ℕ
  gSize : ℕ
  a : ℕ
  e : ℕ
  i0 : ℕ
  j0 : ℕ
  split : ℕ
  N : ℕ
  S : ℕ

structure Geometry (p : Parameters) (B : ℕ) : Prop where
  positiveA : 0 < p.a
  positiveE : 0 < p.e
  hRows : p.i0+p.a ≤ p.hSize
  gSplit : p.split < p.gSize
  interior : p.split ≤ p.i0
  columns : p.j0+p.e ≤ p.split
  widthA : p.a ≤ p.N
  widthE : p.e ≤ p.N
  hFresh : p.H+p.hSize ≤ p.S
  gFresh : p.G+p.gSize ≤ p.S
  masterFresh : 0 < p.S
  outputBound : p.S+6*p.N ≤ B
  codeBound : 90 ≤ B

structure Headers (p : Parameters) (s : State) : Prop where
  hBase : s.natReg 480=p.H
  hSize : s.natReg 481=p.hSize
  gBase : s.natReg 482=p.G
  gSize : s.natReg 483=p.gSize
  height : s.natReg 484=p.a
  width : s.natReg 485=p.e
  row : s.natReg 486=p.i0
  column : s.natReg 487=p.j0
  split : s.natReg 488=p.split
  fftSize : s.natReg 489=p.N
  target : s.natReg 490=p.S

def boot : List Op := [.literal 492 1,.literal 510 6,.mul 524 489 510,
  .literalScalar 50 0,.literalScalar 51 1,.literal 493 0,.literal 517 0,
  .add 511 490 517,.add 512 511 489,.add 513 512 489,
  .add 514 513 489,.add 515 514 489,.add 516 515 489]
def zeroBody : List Op := [.add 501 490 493,.putScalar 501 50,.add 493 493 492]
def cache : List Op := [.sub 500 486 488,.add 500 480 500,.getScalar 55 500,
  .field .sub 52 50 55,.sub 501 488 487,.add 501 482 501,
  .getScalar 53 501,.literal 491 0]
def rowPre : List Op := [.add 498 487 491,.sub 501 488 498,.add 501 482 501,
  .getScalar 59 501,.add 497 486 517]
def rowFinish : List Op := [.field .mul 57 52 59,.field .sub 54 54 57,
  .add 501 511 491,.putScalar 501 59,.add 501 513 491,.putScalar 501 54,
  .add 491 491 492]
def vStart : List Op := [.literal 491 0]
def vPre : List Op := [.add 497 486 491,.sub 500 497 488,.add 500 480 500,
  .getScalar 55 500,.field .sub 58 50 55,.add 501 512 491,.putScalar 501 58]
def colPre : List Op := [.add 498 487 517]
def colFinish : List Op := [.field .mul 57 58 53,.field .sub 54 54 57,
  .add 501 516 491,.putScalar 501 54]
def advance : List Op := [.add 491 491 492]
def deltas : List Op := [.putScalar 514 51,.putScalar 515 51]

/-- One fixed 90-instruction program. The two cross calls are literal
relocations; each terminating helper instruction becomes a charged jump. -/
def program : Program := boot.map Op.code++[.branchLT 493 524 14 18]++
  zeroBody.map Op.code++[.jump 13]++cache.map Op.code++[.branchLT 491 485 27 55]++
  rowPre.map Op.code++crossProgram.map (relocate 32 47)++rowFinish.map Op.code++
  [.jump 26]++vStart.map Op.code++[.branchLT 491 484 57 87]++vPre.map Op.code++
  [.branchLT 491 492 85 65]++colPre.map Op.code++crossProgram.map (relocate 66 81)++
  colFinish.map Op.code++advance.map Op.code++[.jump 56]++deltas.map Op.code++[.halt]

theorem program_length : program.length=90 := rfl
theorem zero_branch : program[13]?=some (.branchLT 493 524 14 18) := rfl
theorem zero_jump : program[17]?=some (.jump 13) := rfl
theorem row_branch : program[26]?=some (.branchLT 491 485 27 55) := rfl
theorem row_jump : program[54]?=some (.jump 26) := rfl
theorem v_branch : program[56]?=some (.branchLT 491 484 57 87) := rfl
theorem zero_column_branch : program[64]?=some (.branchLT 491 492 85 65) := rfl
theorem v_jump : program[86]?=some (.jump 56) := rfl
theorem halt_at : program[89]?=some .halt := rfl

theorem boot_at : BlockAt boot program 0 := by intro i hi;change i < 13 at hi;interval_cases i <;> rfl
theorem zero_at : BlockAt zeroBody program 14 := by intro i hi;change i < 3 at hi;interval_cases i <;> rfl
theorem cache_at : BlockAt cache program 18 := by intro i hi;change i < 8 at hi;interval_cases i <;> rfl
theorem rowPre_at : BlockAt rowPre program 27 := by intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem rowFinish_at : BlockAt rowFinish program 47 := by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem vStart_at : BlockAt vStart program 55 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem vPre_at : BlockAt vPre program 57 := by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem colPre_at : BlockAt colPre program 65 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem colFinish_at : BlockAt colFinish program 81 := by intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem advance_at : BlockAt advance program 85 := by intro i hi;change i < 1 at hi;interval_cases i;rfl
theorem deltas_at : BlockAt deltas program 87 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem rowCross_at : CodeAt crossProgram program 32 47 := by
  intro i hi;change i < 15 at hi;interval_cases i <;> rfl
theorem colCross_at : CodeAt crossProgram program 66 81 := by
  intro i hi;change i < 15 at hi;interval_cases i <;> rfl

def Frame (p : Parameters) (s t : State) : Prop :=
  t.natHeap=s.natHeap ∧ t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
  (∀r,r < 491 ∨ 524 < r → t.natReg r=s.natReg r) ∧
  (∀r,r < 50 ∨ 59 < r → t.scalarReg r=s.scalarReg r) ∧
  (∀q,q < p.S ∨ p.S+6*p.N ≤ q → t.scalarHeap q=s.scalarHeap q)

theorem Frame.refl (p : Parameters) (s : State) : Frame p s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {p : Parameters} {s t u : State} (f:Frame p s t) (g:Frame p t u) : Frame p s u :=
  ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
    fun r h=>(g.2.2.2.1 r h).trans (f.2.2.2.1 r h),
    fun r h=>(g.2.2.2.2.1 r h).trans (f.2.2.2.2.1 r h),
    fun r h=>(g.2.2.2.2.2 r h).trans (f.2.2.2.2.2 r h)⟩
theorem Frame.withPC {p : Parameters} {s t : State} (f:Frame p s t) (pc : ℕ) : Frame p s {t with pc:=pc} := f

theorem Headers.withPC {p : Parameters} {s : State} (h:Headers p s) (pc : ℕ) : Headers p {s with pc:=pc} := by cases h;constructor <;> assumption

theorem Headers.frame {p : Parameters} {s t : State} (h:Headers p s) (f:Frame p s t) : Headers p t := by
  constructor
  all_goals first
    | exact (f.2.2.2.1 _ (by omega)).trans h.hBase
    | exact (f.2.2.2.1 _ (by omega)).trans h.hSize
    | exact (f.2.2.2.1 _ (by omega)).trans h.gBase
    | exact (f.2.2.2.1 _ (by omega)).trans h.gSize
    | exact (f.2.2.2.1 _ (by omega)).trans h.height
    | exact (f.2.2.2.1 _ (by omega)).trans h.width
    | exact (f.2.2.2.1 _ (by omega)).trans h.row
    | exact (f.2.2.2.1 _ (by omega)).trans h.column
    | exact (f.2.2.2.1 _ (by omega)).trans h.split
    | exact (f.2.2.2.1 _ (by omega)).trans h.fftSize
    | exact (f.2.2.2.1 _ (by omega)).trans h.target

theorem Bank.fullFrame {p : Parameters} {s t : State} {a size : ℕ} {f : ℕ → ℂ}
    (h:Bank a size f s) (hf:Frame p s t) (ha:a+size ≤ p.S) : Bank a size f t := by
  intro i hi
  exact (hf.2.2.2.2.2 (a+i) (Or.inl (by omega))).trans (h i hi)

theorem CrossFrame.fullFrame {p : Parameters} {s t : State} (h:CrossFrame s t) : Frame p s t :=
  ⟨h.1,h.2.2.1,h.2.2.2.1,fun r hr=>h.2.2.2.2.1 r (by omega) (by omega) (by omega) (by omega),
    fun r hr=>h.2.2.2.2.2 r (by omega),fun q _=>congrFun h.2.1 q⟩

structure Fixed (p : Parameters) (s : State) : Prop where
  one : s.natReg 492=1
  zero : s.natReg 517=0
  limit : s.natReg 524=6*p.N
  wBase : s.natReg 511=p.S
  vBase : s.natReg 512=p.S+p.N
  rowBase : s.natReg 513=p.S+2*p.N
  leftDeltaBase : s.natReg 514=p.S+3*p.N
  rightDeltaBase : s.natReg 515=p.S+4*p.N
  colBase : s.natReg 516=p.S+5*p.N
  scalarZero : s.scalarReg 50=prepared 0
  scalarOne : s.scalarReg 51=prepared 1

structure Cached (p : Parameters) (h g : ℕ → ℂ) (s : State) : Prop where
  v0 : s.scalarReg 52=prepared (-h (p.i0-p.split))
  w0 : s.scalarReg 53=prepared (g (p.split-p.j0))

theorem Fixed.withPC {p : Parameters} {s : State} (h:Fixed p s) (pc : ℕ) : Fixed p {s with pc:=pc} := by cases h;constructor <;> assumption
theorem Cached.withPC {p : Parameters} {h g : ℕ → ℂ} {s : State} (c:Cached p h g s) (pc : ℕ) : Cached p h g {s with pc:=pc} := by cases c;constructor <;> assumption

theorem boot_spec (p : Parameters) (s : State) (h:Headers p s) :
    Headers p (applyBlock boot s) ∧ Fixed p (applyBlock boot s) ∧
    (applyBlock boot s).natReg 493=0 ∧ Frame p s (applyBlock boot s) := by
  have f:Frame p s (applyBlock boot s):=by
    refine ⟨rfl,rfl,rfl,?_,?_,fun _ _=>rfl⟩
    · intro r hr;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,writeScalar,next]
    · intro r hr;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,writeScalar,next]
  refine ⟨h.frame f,?_,?_,f⟩
  · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,writeScalar,next,h.fftSize,h.target,prepared]
    all_goals omega
  · simp [boot,applyBlock,Op.apply,writeNat,writeScalar,next]

theorem boot_safe (p : Parameters) (B : ℕ) (s : State) (h:Headers p s) (geo:Geometry p B) :
    readable boot s ∧ peak boot s ≤ B := by
  have hb:=geo.outputBound;have hc:=geo.codeBound
  simp [boot,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,writeScalar,next,h.fftSize,h.target]
  omega


theorem Fixed.crossFrame {p : Parameters} {s t : State} (f:Fixed p s) (h:CrossFrame s t) : Fixed p t := by
  constructor
  all_goals first
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.one
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.zero
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.limit
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.wBase
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.vBase
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.rowBase
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.leftDeltaBase
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.rightDeltaBase
    | exact (h.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans f.colBase
    | exact (h.2.2.2.2.2 _ (by decide)).trans f.scalarZero
    | exact (h.2.2.2.2.2 _ (by decide)).trans f.scalarOne

theorem Cached.crossFrame {p : Parameters} {h g : ℕ → ℂ} {s t : State}
    (c:Cached p h g s) (f:CrossFrame s t) : Cached p h g t :=
  ⟨(f.2.2.2.2.2 52 (by decide)).trans c.v0,(f.2.2.2.2.2 53 (by decide)).trans c.w0⟩

/-- The six slots remain in their frozen right/left order. -/
def Cells (p : Parameters) (f : Fin 6 → Fin p.N → ℂ) (s : State) : Prop :=
  ∀b j,s.scalarHeap (p.S+b.val*p.N+j.val)=some (prepared (f b j))

theorem Cells.withPC {p : Parameters} {f : Fin 6 → Fin p.N → ℂ} {s : State}
    (h:Cells p f s) (pc : ℕ) : Cells p f {s with pc:=pc} := h

theorem Cells.heapEq {p : Parameters} {f : Fin 6 → Fin p.N → ℂ} {s t : State}
    (h:Cells p f s) (he:t.scalarHeap=s.scalarHeap) : Cells p f t := by intro b j;rw [he];exact h b j

theorem cell_address_injective (p : Parameters) (b c : Fin 6) (i j : Fin p.N)
    (he:p.S+b.val*p.N+i.val=p.S+c.val*p.N+j.val) : b=c ∧ i=j := by
  have hb:b.val=c.val:=by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl|hl
    · have hm:=Nat.mul_le_mul_right p.N (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at hm
      have hi:=i.isLt;omega
    · have hm:=Nat.mul_le_mul_right p.N (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at hm
      have hj:=j.isLt;omega
  have hij:i.val=j.val:=by rw [hb] at he;omega
  exact ⟨Fin.ext hb,Fin.ext hij⟩

def changeCell {p : Parameters} (f : Fin 6 → Fin p.N → ℂ) (b : Fin 6) (j : Fin p.N) (v : ℂ) :
    Fin 6 → Fin p.N → ℂ := fun c i=>if c=b ∧ i=j then v else f c i

theorem Cells.update {p : Parameters} {f : Fin 6 → Fin p.N → ℂ} {s t : State}
    (hc:Cells p f s) (b : Fin 6) (j : Fin p.N) (v : ℂ)
    (he:t.scalarHeap=Function.update s.scalarHeap (p.S+b.val*p.N+j.val) (some (prepared v))) :
    Cells p (changeCell f b j v) t := by
  intro c i
  rw [he]
  by_cases h:c=b ∧ i=j
  · rcases h with ⟨rfl,rfl⟩;simp [changeCell]
  · have hn:p.S+c.val*p.N+i.val≠p.S+b.val*p.N+j.val:=by
      intro haddr;exact h (cell_address_injective p c b i j haddr)
    simp only [Function.update_of_ne hn,changeCell,ite_eq_right h]
    exact hc c i

def vValue (p : Parameters) (h : ℕ → ℂ) (i : ℕ) : ℂ := -h (p.i0+i-p.split)
def wValue (p : Parameters) (g : ℕ → ℂ) (j : ℕ) : ℂ := g (p.split-(p.j0+j))
def matrixValue (p : Parameters) (h g : ℕ → ℂ) (i j : ℕ) : ℂ :=
  OAI.ExactFourier.ToeplitzLayers.cross p.split h g (p.i0+i) (p.j0+j)
def rowValue (p : Parameters) (h g : ℕ → ℂ) (j : ℕ) : ℂ :=
  matrixValue p h g 0 j-vValue p h 0*wValue p g j
def colValue (p : Parameters) (h g : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i=0 then 0 else matrixValue p h g i 0-vValue p h i*wValue p g 0

def rowCells (p : Parameters) (h g : ℕ → ℂ) (k : ℕ) : Fin 6 → Fin p.N → ℂ := fun b j=>
  if j.val < k then if b.val=0 then wValue p g j.val else if b.val=2 then rowValue p h g j.val else 0 else 0

def columnCells (p : Parameters) (h g : ℕ → ℂ) (k : ℕ) : Fin 6 → Fin p.N → ℂ := fun b j=>
  if b.val=1 then if j.val < k then vValue p h j.val else 0 else
  if b.val=5 then if j.val < k then colValue p h g j.val else 0 else rowCells p h g p.e b j


theorem zero_spec (p : Parameters) (k B : ℕ) (s : State) (h:Headers p s) (f:Fixed p s)
    (geo:Geometry p B) (hk:k < 6*p.N) (index:s.natReg 493=k)
    (values:Bank p.S k (fun _=>0) s) :
    Fixed p (applyBlock zeroBody s) ∧ Headers p (applyBlock zeroBody s) ∧
    (applyBlock zeroBody s).natReg 493=k+1 ∧ Bank p.S (k+1) (fun _=>0) (applyBlock zeroBody s) ∧
    Frame p s (applyBlock zeroBody s) ∧ readable zeroBody s ∧ peak zeroBody s ≤ B := by
  have fr:Frame p s (applyBlock zeroBody s):=by
    refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
    · intro r hr;simp (disch:=omega) [zeroBody,applyBlock,Op.apply,writeNat,next]
    · intro r hr;rfl
    · intro q hq;simp (disch:=omega) [zeroBody,applyBlock,Op.apply,writeNat,next,h.target,index]
  refine ⟨?_,h.frame fr,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [zeroBody,applyBlock,Op.apply,writeNat,next,f.one,f.zero,f.limit,
      f.wBase,f.vBase,f.rowBase,f.leftDeltaBase,f.rightDeltaBase,f.colBase,f.scalarZero,f.scalarOne]
  · simp [zeroBody,applyBlock,Op.apply,writeNat,next,index,f.one]
  · intro i hi
    by_cases he:i=k
    · subst i;simp [zeroBody,applyBlock,Op.apply,writeNat,next,h.target,index,f.scalarZero]
    · have ht:i < k:=by omega
      simpa [zeroBody,applyBlock,Op.apply,writeNat,next,h.target,index,he] using values i ht
  · simp [zeroBody,readable,Op.readable]
  · have hb:=geo.outputBound
    simp [zeroBody,peak,Op.peak,Op.apply,writeNat,next,h.target,index,f.one];omega

theorem zero_loop (p : Parameters) (k count B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h:Headers p s) (f:Fixed p s) (geo:Geometry p B) (he:k+count=6*p.N)
    (index:s.natReg 493=k) (values:Bank p.S k (fun _=>0) s)
    (pc:s.pc=13) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*count+1) u ∧ Headers p u ∧ Fixed p u ∧
    Bank p.S (6*p.N) (fun _=>0) u ∧ Frame p s u ∧ u.pc=18 := by
  have hcode:=geo.codeBound
  induction count generalizing k s with
  | zero =>
    have he':k=6*p.N:=by omega
    have index' := index.trans he'
    have values' : Bank p.S (6*p.N) (fun _=>0) s := by simpa only [he'] using values
    let u:State:={s with pc:=18}
    have ub:=changePC_bound B s 18 hs (by omega)
    refine ⟨u,?_,h.withPC 18,f.withPC 18,values'.withPC,(Frame.refl p s).withPC 18,rfl⟩
    exact .next hs (by simp [step,pc,zero_branch,index',f.limit,u]) (.refl ub)
  | succ count ih =>
    have hk:k < 6*p.N:=by omega
    let a:State:={s with pc:=14}
    have ab:=changePC_bound B s 14 hs (by omega)
    have first:BoundedRuns program n x B s 1 a:=
      .next hs (by simp [step,pc,zero_branch,index,f.limit,hk,a]) (.refl ab)
    have z:=zero_spec p k B a (h.withPC 14) (f.withPC 14) geo hk index values.withPC
    have body:=block_runs zeroBody program 14 n B x a zero_at rfl ab (by change 17 ≤ B;omega) z.2.2.2.2.2.1 z.2.2.2.2.2.2
    let v:State:={applyBlock zeroBody a with pc:=13}
    have vb:=changePC_bound B _ 13 body.final_bound (by omega)
    have bpc:(applyBlock zeroBody a).pc=17:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
    have jump:BoundedRuns program n x B (applyBlock zeroBody a) 1 v:=
      .next body.final_bound (by simp only [step,bpc,zero_jump,v]) (.refl vb)
    have vf:Frame p s v:=((Frame.refl p s).withPC 14).trans (z.2.2.2.2.1.withPC 13)
    obtain ⟨u,tail,uh,uf,uv,frame,upc⟩:=ih (k+1) v (z.2.1.withPC 13) (z.1.withPC 13)
      (by omega) z.2.2.1 z.2.2.2.1.withPC rfl vb
    refine ⟨u,?_,uh,uf,uv,vf.trans frame,upc⟩
    convert first.trans (body.trans (jump.trans tail)) using 1
    simp only [zeroBody,List.length_cons,List.length_nil]
    omega

theorem zero_cells (p : Parameters) (s : State) (values:Bank p.S (6*p.N) (fun _=>0) s) :
    Cells p (fun _ _=>0) s := by
  intro b j
  have hb:=b.isLt;have hj:=j.isLt
  have hm:=Nat.mul_le_mul_right p.N (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at hm
  simpa [Nat.add_assoc] using values (b.val*p.N+j.val) (by omega)


/-- Static register frame for every non-startup block. -/
def Stable (s t : State) : Prop :=
  t.natHeap=s.natHeap ∧ t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
  (∀r,r ∉ ([491,493,494,497,498,499,500,501] : List ℕ) → t.natReg r=s.natReg r) ∧
  (∀r,r < 52 ∨ 59 < r → t.scalarReg r=s.scalarReg r)

def allowed (o : Op) : Prop := match o with
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ => d ∈ ([491,493,494,497,498,499,500,501] : List ℕ)
  | .literalScalar d _ | .getScalar d _ | .field _ d _ _ => 52 ≤ d ∧ d ≤ 59
  | .putScalar _ _ => True
instance (o : Op) : Decidable (allowed o) := by cases o <;> unfold allowed <;> infer_instance

theorem Stable.refl (s : State) : Stable s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Stable.trans {s t u : State} (h:Stable s t) (g:Stable t u) : Stable s u :=
  ⟨g.1.trans h.1,g.2.1.trans h.2.1,g.2.2.1.trans h.2.2.1,
    fun r hr=>(g.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(g.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem op_stable (o : Op) (s : State) (ha:allowed o) : Stable s (o.apply s) := by
  cases o <;> refine ⟨rfl,rfl,rfl,?_,?_⟩
  all_goals intro r hr
  all_goals simp only [Op.apply,writeNat,writeScalar,next]
  all_goals first | rfl | (apply Function.update_of_ne;intro he;subst_vars;simp_all [allowed];try omega)

theorem block_stable (b : List Op) (s : State) (h:List.Forall allowed b) : Stable s (applyBlock b s) := by
  induction b generalizing s with
  | nil => exact Stable.refl s
  | cons o b ih =>
    have hh:=(List.forall_cons allowed o b).1 h
    exact (op_stable o s hh.1).trans (ih (o.apply s) hh.2)

theorem Stable.fixed {p : Parameters} {s t : State} (h:Stable s t) (f:Fixed p s) : Fixed p t := by
  constructor
  all_goals first
    | exact (h.2.2.2.1 _ (by decide)).trans f.one
    | exact (h.2.2.2.1 _ (by decide)).trans f.zero
    | exact (h.2.2.2.1 _ (by decide)).trans f.limit
    | exact (h.2.2.2.1 _ (by decide)).trans f.wBase
    | exact (h.2.2.2.1 _ (by decide)).trans f.vBase
    | exact (h.2.2.2.1 _ (by decide)).trans f.rowBase
    | exact (h.2.2.2.1 _ (by decide)).trans f.leftDeltaBase
    | exact (h.2.2.2.1 _ (by decide)).trans f.rightDeltaBase
    | exact (h.2.2.2.1 _ (by decide)).trans f.colBase
    | exact (h.2.2.2.2 _ (by decide)).trans f.scalarZero
    | exact (h.2.2.2.2 _ (by decide)).trans f.scalarOne

theorem Stable.frame {p : Parameters} {s t : State} (h:Stable s t)
    (heap:∀q,q < p.S ∨ p.S+6*p.N ≤ q → t.scalarHeap q=s.scalarHeap q) : Frame p s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun r hr=>h.2.2.2.1 r (by simp;omega),
    fun r hr=>h.2.2.2.2 r (by omega),heap⟩

theorem cache_spec (p : Parameters) (B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s) :
    Headers p (applyBlock cache s) ∧ Fixed p (applyBlock cache s) ∧ Cached p h g (applyBlock cache s) ∧
    (applyBlock cache s).natReg 491=0 ∧ Frame p s (applyBlock cache s) ∧
    readable cache s ∧ peak cache s ≤ B := by
  have hh:=bh (p.i0-p.split) (by have :=geo.hRows;have :=geo.positiveA;omega)
  have hg:=bg (p.split-p.j0) (by have :=geo.gSplit;omega)
  have st:=block_stable cache s (by decide)
  have fr:Frame p s (applyBlock cache s):=st.frame (fun _ _=>rfl)
  refine ⟨heads.frame fr,st.fixed f,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [cache,applyBlock,Op.apply,writeNat,writeScalar,next,
      heads.row,heads.split,heads.column,heads.hBase,heads.gBase,f.scalarZero,hh,hg,prepared,evalField]
  · simp [cache,applyBlock,Op.apply,writeNat,writeScalar,next]
  · simp [cache,readable,Op.readable,Op.apply,writeNat,writeScalar,next,
      heads.row,heads.split,heads.column,heads.hBase,heads.gBase,f.scalarZero,hh,hg,prepared,evalField]
  · have hb:=geo.hFresh;have gb:=geo.gFresh;have ob:=geo.outputBound
    have hr:=geo.hRows;have ha:=geo.positiveA;have gs:=geo.gSplit
    simp [cache,peak,Op.peak,Op.apply,writeNat,writeScalar,next,
      heads.row,heads.split,heads.column,heads.hBase,heads.gBase];omega

theorem row_pre_spec (p : Parameters) (k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bg:Bank p.G p.gSize g s) (index:s.natReg 491=k) (hk:k < p.e) :
    Headers p (applyBlock rowPre s) ∧ Fixed p (applyBlock rowPre s) ∧ Cached p h g (applyBlock rowPre s) ∧
    CrossHeaders p.H p.G p.split p.i0 (p.j0+k) (applyBlock rowPre s) ∧
    (applyBlock rowPre s).scalarReg 59=prepared (wValue p g k) ∧
    (applyBlock rowPre s).natReg 491=k ∧ Frame p s (applyBlock rowPre s) ∧
    readable rowPre s ∧ peak rowPre s ≤ B := by
  have hg:=bg (p.split-(p.j0+k)) (by have :=geo.gSplit;omega)
  have st:=block_stable rowPre s (by decide)
  have fr:Frame p s (applyBlock rowPre s):=st.frame (fun _ _=>rfl)
  refine ⟨heads.frame fr,st.fixed f,?_,?_,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [rowPre,applyBlock,Op.apply,writeNat,writeScalar,next,c.v0,c.w0]
  · constructor <;> simp [rowPre,applyBlock,Op.apply,writeNat,writeScalar,next,
      heads.hBase,heads.gBase,heads.split,heads.row,heads.column,index,f.zero,f.one]
  · simp [rowPre,applyBlock,Op.apply,writeNat,writeScalar,next,
      heads.gBase,heads.split,heads.column,index,hg,wValue]
  · simp [rowPre,applyBlock,Op.apply,writeNat,writeScalar,next,index]
  · simp [rowPre,readable,Op.readable,Op.apply,writeNat,next,
      heads.gBase,heads.split,heads.column,index,hg]
  · have gb:=geo.gFresh;have ob:=geo.outputBound;have gs:=geo.gSplit
    have cols:=geo.columns;have hr:=geo.hRows;have hb:=geo.hFresh
    simp [rowPre,peak,Op.peak,Op.apply,writeNat,writeScalar,next,
      heads.gBase,heads.split,heads.column,heads.row,index,f.zero];omega


theorem rowCells_step (p : Parameters) (h g : ℕ → ℂ) (k : ℕ) (hk:k < p.N) :
    changeCell (changeCell (rowCells p h g k) 0 ⟨k,hk⟩ (wValue p g k))
      2 ⟨k,hk⟩ (rowValue p h g k)=rowCells p h g (k+1) := by
  funext b j
  fin_cases b
  all_goals by_cases he:j.val=k
  all_goals by_cases hl:j.val < k
  all_goals simp (disch:=omega) [changeCell,rowCells,Fin.ext_iff,he,hl]
  all_goals omega

theorem columnCells_step (p : Parameters) (h g : ℕ → ℂ) (k : ℕ) (hk:k < p.N) :
    changeCell (changeCell (columnCells p h g k) 1 ⟨k,hk⟩ (vValue p h k))
      5 ⟨k,hk⟩ (colValue p h g k)=columnCells p h g (k+1) := by
  funext b j
  fin_cases b
  all_goals by_cases he:j.val=k
  all_goals by_cases hl:j.val < k
  all_goals simp (disch:=omega) [changeCell,columnCells,Fin.ext_iff,he,hl]
  all_goals omega

theorem columnCells_step_zero (p : Parameters) (h g : ℕ → ℂ) (hn:0 < p.N) :
    changeCell (columnCells p h g 0) 1 ⟨0,hn⟩ (vValue p h 0)=columnCells p h g 1 := by
  funext b j
  fin_cases b
  all_goals by_cases he:j.val=0
  all_goals simp (disch:=omega) [changeCell,columnCells,colValue,Fin.ext_iff,he]

theorem row_finish_spec (p : Parameters) (k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (index:s.natReg 491=k) (hk:k < p.e)
    (w:s.scalarReg 59=prepared (wValue p g k))
    (m:s.scalarReg 54=prepared (matrixValue p h g 0 k))
    (cells:Cells p (rowCells p h g k) s) :
    Headers p (applyBlock rowFinish s) ∧ Fixed p (applyBlock rowFinish s) ∧ Cached p h g (applyBlock rowFinish s) ∧
    (applyBlock rowFinish s).natReg 491=k+1 ∧ Cells p (rowCells p h g (k+1)) (applyBlock rowFinish s) ∧
    Frame p s (applyBlock rowFinish s) ∧ readable rowFinish s ∧ peak rowFinish s ≤ B := by
  have hkN:k < p.N:=hk.trans_le geo.widthE
  have st:=block_stable rowFinish s (by decide)
  have he:(applyBlock rowFinish s).scalarHeap=Function.update
      (Function.update s.scalarHeap (p.S+k) (some (prepared (wValue p g k))))
      (p.S+2*p.N+k) (some (prepared (rowValue p h g k))):=by
    simp [rowFinish,applyBlock,Op.apply,writeNat,writeScalar,next,
      f.wBase,f.rowBase,index,c.v0,w,m,rowValue,vValue,prepared,evalField]
  have fr:Frame p s (applyBlock rowFinish s):=st.frame (by
    intro q hq;rw [he];simp (disch:=omega))
  refine ⟨heads.frame fr,st.fixed f,?_,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [rowFinish,applyBlock,Op.apply,writeNat,writeScalar,next,c.v0,c.w0]
  · simp [rowFinish,applyBlock,Op.apply,writeNat,writeScalar,next,index,f.one]
  · let mid:State:={s with scalarHeap:=Function.update s.scalarHeap (p.S+k) (some (prepared (wValue p g k)))}
    have c1:Cells p (changeCell (rowCells p h g k) 0 ⟨k,hkN⟩ (wValue p g k)) mid:=
      cells.update 0 ⟨k,hkN⟩ _ (by simp [mid])
    have c2:=c1.update 2 ⟨k,hkN⟩ (rowValue p h g k) he
    rw [rowCells_step p h g k hkN] at c2
    exact c2
  · simp [rowFinish,readable,Op.readable,Op.apply,writeScalar,next,c.v0,w,m,prepared,evalField]
  · have ob:=geo.outputBound
    simp [rowFinish,peak,Op.peak,Op.apply,writeNat,writeScalar,next,f.wBase,f.rowBase,index,f.one];omega

/-- The same literal convolution helper is called at either physical site,
without expanding the ambient word bound by its relocation offset. -/
theorem cross_call (p : Parameters) (B I J base ret n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ)
    (s : State) (geo:Geometry p B) (code:CodeAt crossProgram program base ret)
    (hcode:base+15 ≤ B) (hret:ret ≤ B) (hI:I < p.hSize) (hsplit:p.split ≤ I) (hJ:J ≤ p.split)
    (ch:CrossHeaders p.H p.G p.split I J s) (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (pc:s.pc=base) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (11*(p.split-J)+5) u ∧ CrossFrame s u ∧ u.pc=ret ∧
    u.scalarReg 54=prepared (OAI.ExactFourier.ToeplitzLayers.cross p.split h g I J) := by
  let a:State:={s with pc:=0}
  have ab:=changePC_bound B s 0 hs (by omega)
  have cb:CrossBounds p.H p.G p.hSize p.gSize p.split I J B:=
    ⟨by have :=geo.codeBound;omega,
      by have :=geo.hFresh;have :=geo.outputBound;omega,
      by have :=geo.gFresh;have :=geo.outputBound;omega,geo.gSplit,hI,hsplit,hJ⟩
  obtain ⟨u,run,frame,_,_,value⟩:=cross_execution p.H p.G p.hSize p.gSize p.split I J B n h g x a
    ch.withPC bh.withPC bg.withPC cb rfl ab
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed code (by exact hcode) hret run
  have pe:placed base a=s:=by cases s; simp_all [placed,a]
  rw [pe] at placedRun
  refine ⟨{u with pc:=ret},placedRun,?_,rfl,value⟩
  exact (((CrossFrame.refl s).withPC 0).trans frame).withPC ret

theorem row_iteration (p : Parameters) (k B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (index:s.natReg 491=k) (hk:k < p.e) (cells:Cells p (rowCells p h g k) s)
    (pc:s.pc=26) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (19+11*(p.split-(p.j0+k))) u ∧ Headers p u ∧ Fixed p u ∧
    Cached p h g u ∧ u.natReg 491=k+1 ∧ Cells p (rowCells p h g (k+1)) u ∧ Frame p s u ∧ u.pc=26 := by
  have hc:=geo.codeBound
  let a:State:={s with pc:=27}
  have ab:=changePC_bound B s 27 hs (by omega)
  have first:BoundedRuns program n x B s 1 a:=
    .next hs (by simp [step,pc,row_branch,index,heads.width,hk,a]) (.refl ab)
  have prep:=row_pre_spec p k B h g a (heads.withPC 27) (f.withPC 27) (c.withPC 27) geo bg.withPC index hk
  have preRun:=block_runs rowPre program 27 n B x a rowPre_at rfl ab (by change 32 ≤ B;omega)
    prep.2.2.2.2.2.2.2.1 prep.2.2.2.2.2.2.2.2
  let v:=applyBlock rowPre a
  have vpc:v.pc=32:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
  obtain ⟨w,call,frame,wpc,value⟩:=cross_call p B p.i0 (p.j0+k) 32 47 n h g x v geo rowCross_at
    (by omega) (by omega) (by have :=geo.positiveA;have :=geo.hRows;omega) geo.interior
    (by have :=geo.columns;omega) prep.2.2.2.1
    (bh.fullFrame prep.2.2.2.2.2.2.1 geo.hFresh) (bg.fullFrame prep.2.2.2.2.2.2.1 geo.gFresh) vpc preRun.final_bound
  have wheads:=prep.1.frame frame.fullFrame
  have wf:=prep.2.1.crossFrame frame
  have wc:=prep.2.2.1.crossFrame frame
  have wi:w.natReg 491=k:= (frame.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans prep.2.2.2.2.2.1
  have ww:w.scalarReg 59=prepared (wValue p g k):=(frame.2.2.2.2.2 _ (by decide)).trans prep.2.2.2.2.1
  have wm:w.scalarReg 54=prepared (matrixValue p h g 0 k):=by simpa [matrixValue] using value
  have wcell:Cells p (rowCells p h g k) w:=cells.withPC 27 |>.heapEq rfl |>.heapEq frame.2.1
  have done:=row_finish_spec p k B h g w wheads wf wc geo wi hk ww wm wcell
  have body:=block_runs rowFinish program 47 n B x w rowFinish_at wpc call.final_bound
    (by change 54 ≤ B;omega) done.2.2.2.2.2.2.1 done.2.2.2.2.2.2.2
  let u:State:={applyBlock rowFinish w with pc:=26}
  have ub:=changePC_bound B _ 26 body.final_bound (by omega)
  have bpc:(applyBlock rowFinish w).pc=54:=by rw [UniformReciprocalMachine.applyBlock_pc,wpc];rfl
  have jump:BoundedRuns program n x B (applyBlock rowFinish w) 1 u:=
    .next body.final_bound (by simp only [step,bpc,row_jump,u]) (.refl ub)
  refine ⟨u,?_,done.1.withPC 26,done.2.1.withPC 26,done.2.2.1.withPC 26,
    done.2.2.2.1,done.2.2.2.2.1.withPC 26,?_,rfl⟩
  · convert first.trans (preRun.trans (call.trans (body.trans jump))) using 1
    change 19+11*(p.split-(p.j0+k))=1+(5+((11*(p.split-(p.j0+k))+5)+(7+1)))
    omega
  · exact ((Frame.refl p s).withPC 27).trans
      (prep.2.2.2.2.2.2.1.trans (frame.fullFrame.trans (done.2.2.2.2.2.1.withPC 26)))


def rowCost (p : Parameters) : ℕ → ℕ → ℕ
  | _,0 => 1
  | k,f+1 => 19+11*(p.split-(p.j0+k))+rowCost p (k+1) f

theorem rowCost_bound (p : Parameters) (k count : ℕ) :
    rowCost p k count ≤ count*(19+11*p.split)+1 := by
  induction count generalizing k with
  | zero => simp [rowCost]
  | succ count ih =>
    have ht:=Nat.sub_le p.split (p.j0+k)
    have hm:=Nat.mul_le_mul_left 11 ht
    have h:=ih (k+1)
    have eq:(count+1)*(19+11*p.split)=count*(19+11*p.split)+(19+11*p.split):=Nat.succ_mul _ _
    simp only [rowCost]
    rw [eq]
    omega

theorem row_loop (p : Parameters) (k count B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (he:k+count=p.e) (index:s.natReg 491=k) (cells:Cells p (rowCells p h g k) s)
    (pc:s.pc=26) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (rowCost p k count) u ∧ Headers p u ∧ Fixed p u ∧ Cached p h g u ∧
    Cells p (rowCells p h g p.e) u ∧ Frame p s u ∧ u.pc=55 := by
  have hc:=geo.codeBound
  induction count generalizing k s with
  | zero =>
    have he':k=p.e:=by omega
    let u:State:={s with pc:=55}
    have ub:=changePC_bound B s 55 hs (by omega)
    refine ⟨u,?_,heads.withPC 55,f.withPC 55,c.withPC 55,?_,(Frame.refl p s).withPC 55,rfl⟩
    · exact .next hs (by simp [step,pc,row_branch,index,heads.width,he',u]) (.refl ub)
    · simpa only [he'] using cells.withPC 55
  | succ count ih =>
    obtain ⟨v,run,vh,vf,vc,vi,values,frame,vpc⟩:=row_iteration p k B n h g x s heads f c geo bh bg
      index (by omega) cells pc hs
    obtain ⟨u,tail,uh,uf,uc,uv,fr,upc⟩:=ih (k+1) v vh vf vc
      (bh.fullFrame frame geo.hFresh) (bg.fullFrame frame geo.gFresh) (by omega) vi values vpc run.final_bound
    exact ⟨u,run.trans tail,uh,uf,uc,uv,frame.trans fr,upc⟩

theorem v_pre_spec (p : Parameters) (k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (index:s.natReg 491=k) (hk:k < p.a)
    (cells:Cells p (columnCells p h g k) s) :
    Headers p (applyBlock vPre s) ∧ Fixed p (applyBlock vPre s) ∧ Cached p h g (applyBlock vPre s) ∧
    (applyBlock vPre s).natReg 497=p.i0+k ∧ (applyBlock vPre s).natReg 491=k ∧
    (applyBlock vPre s).scalarReg 58=prepared (vValue p h k) ∧
    Cells p (changeCell (columnCells p h g k) 1 ⟨k,hk.trans_le geo.widthA⟩ (vValue p h k)) (applyBlock vPre s) ∧
    Frame p s (applyBlock vPre s) ∧ readable vPre s ∧ peak vPre s ≤ B := by
  have hkN:k < p.N:=hk.trans_le geo.widthA
  have hh:=bh (p.i0+k-p.split) (by have :=geo.hRows;omega)
  have st:=block_stable vPre s (by decide)
  have he:(applyBlock vPre s).scalarHeap=Function.update s.scalarHeap (p.S+p.N+k)
      (some (prepared (vValue p h k))):=by
    simp [vPre,applyBlock,Op.apply,writeNat,writeScalar,next,heads.row,heads.split,heads.hBase,
      f.scalarZero,f.vBase,index,hh,vValue,prepared,evalField]
  have fr:Frame p s (applyBlock vPre s):=st.frame (by intro q hq;rw [he];simp (disch:=omega))
  refine ⟨heads.frame fr,st.fixed f,?_,?_,?_,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [vPre,applyBlock,Op.apply,writeNat,writeScalar,next,c.v0,c.w0]
  · simp [vPre,applyBlock,Op.apply,writeNat,writeScalar,next,heads.row,index]
  · simp [vPre,applyBlock,Op.apply,writeNat,writeScalar,next,index]
  · simp [vPre,applyBlock,Op.apply,writeNat,writeScalar,next,heads.row,heads.split,heads.hBase,
      f.scalarZero,index,hh,vValue,prepared,evalField]
  · exact cells.update 1 ⟨k,hkN⟩ _ (by simpa using he)
  · simp [vPre,readable,Op.readable,Op.apply,writeNat,writeScalar,next,heads.row,heads.split,heads.hBase,
      f.scalarZero,index,hh,prepared,evalField]
  · have ob:=geo.outputBound;have hb:=geo.hFresh;have hr:=geo.hRows
    simp [vPre,peak,Op.peak,Op.apply,writeNat,writeScalar,next,heads.row,heads.split,heads.hBase,
      f.vBase,index];omega

theorem col_finish_spec (p : Parameters) (k B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (index:s.natReg 491=k) (hk:k < p.a) (positive:0 < k)
    (v:s.scalarReg 58=prepared (vValue p h k))
    (m:s.scalarReg 54=prepared (matrixValue p h g k 0))
    (cells:Cells p (changeCell (columnCells p h g k) 1 ⟨k,hk.trans_le geo.widthA⟩ (vValue p h k)) s) :
    Headers p (applyBlock colFinish s) ∧ Fixed p (applyBlock colFinish s) ∧ Cached p h g (applyBlock colFinish s) ∧
    (applyBlock colFinish s).natReg 491=k ∧ Cells p (columnCells p h g (k+1)) (applyBlock colFinish s) ∧
    Frame p s (applyBlock colFinish s) ∧ readable colFinish s ∧ peak colFinish s ≤ B := by
  have hkN:k < p.N:=hk.trans_le geo.widthA
  have st:=block_stable colFinish s (by decide)
  have he:(applyBlock colFinish s).scalarHeap=Function.update s.scalarHeap (p.S+5*p.N+k)
      (some (prepared (colValue p h g k))):=by
    simp [colFinish,applyBlock,Op.apply,writeNat,writeScalar,next,
      f.colBase,index,c.w0,v,m,colValue,wValue,prepared,evalField,show k≠0 by omega]
  have fr:Frame p s (applyBlock colFinish s):=st.frame (by intro q hq;rw [he];simp (disch:=omega))
  refine ⟨heads.frame fr,st.fixed f,?_,?_,?_,fr,?_,?_⟩
  · constructor <;> simp [colFinish,applyBlock,Op.apply,writeNat,writeScalar,next,c.v0,c.w0]
  · simp [colFinish,applyBlock,Op.apply,writeNat,writeScalar,next,index]
  · have hc:=cells.update 5 ⟨k,hkN⟩ (colValue p h g k) he
    rw [columnCells_step p h g k hkN] at hc
    exact hc
  · simp [colFinish,readable,Op.readable,Op.apply,writeScalar,next,c.w0,v,m,prepared,evalField]
  · have ob:=geo.outputBound
    simp [colFinish,peak,Op.peak,Op.apply,writeNat,writeScalar,next,f.colBase,index];omega


theorem col_pre_spec (p : Parameters) (k : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (row:s.natReg 497=p.i0+k) :
    Headers p (applyBlock colPre s) ∧ Fixed p (applyBlock colPre s) ∧ Cached p h g (applyBlock colPre s) ∧
    CrossHeaders p.H p.G p.split (p.i0+k) p.j0 (applyBlock colPre s) ∧ Frame p s (applyBlock colPre s) ∧
    (applyBlock colPre s).scalarReg 58=s.scalarReg 58 ∧ (applyBlock colPre s).natReg 491=s.natReg 491 := by
  have st:=block_stable colPre s (by decide)
  have fr:Frame p s (applyBlock colPre s):=st.frame (fun _ _=>rfl)
  refine ⟨heads.frame fr,st.fixed f,?_,?_,?_,rfl,rfl⟩
  · exact ⟨c.v0,c.w0⟩
  · constructor <;> simp [colPre,applyBlock,Op.apply,writeNat,next,
      heads.hBase,heads.gBase,heads.split,heads.column,f.zero,f.one,row]
  · exact fr

/-- Increment and jump remain charged; no heap or prepared bank is touched. -/
theorem advance_run (p : Parameters) (k B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (index:s.natReg 491=k) (hk:k < p.a) (cells:Cells p (columnCells p h g (k+1)) s)
    (pc:s.pc=85) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 2 u ∧ Headers p u ∧ Fixed p u ∧ Cached p h g u ∧
    u.natReg 491=k+1 ∧ Cells p (columnCells p h g (k+1)) u ∧ Frame p s u ∧ u.pc=56 := by
  have hc:=geo.codeBound;have ha:=geo.widthA;have ob:=geo.outputBound
  have safe:readable advance s ∧ peak advance s ≤ B:=by
    simp [advance,readable,Op.readable,peak,Op.peak,index,f.one];omega
  have body:=block_runs advance program 85 n B x s advance_at pc hs (by change 86 ≤ B;omega) safe.1 safe.2
  let u:State:={applyBlock advance s with pc:=56}
  have ub:=changePC_bound B _ 56 body.final_bound (by omega)
  have bpc:(applyBlock advance s).pc=86:=by rw [UniformReciprocalMachine.applyBlock_pc,pc];rfl
  have jump:BoundedRuns program n x B (applyBlock advance s) 1 u:=
    .next body.final_bound (by simp only [step,bpc,v_jump,u]) (.refl ub)
  have st:=block_stable advance s (by decide)
  have fr:Frame p s (applyBlock advance s):=st.frame (fun _ _=>rfl)
  refine ⟨u,body.trans jump,(heads.frame fr).withPC 56,(st.fixed f).withPC 56,?_,?_,
    (cells.heapEq rfl).withPC 56,fr.withPC 56,rfl⟩
  · constructor <;> simp [u,advance,applyBlock,Op.apply,writeNat,next,c.v0,c.w0]
  · simp [u,advance,applyBlock,Op.apply,writeNat,next,index,f.one]

def vIterationCost (p : Parameters) (k : ℕ) : ℕ := if k=0 then 11 else 21+11*(p.split-p.j0)

theorem v_iteration (p : Parameters) (k B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (index:s.natReg 491=k) (hk:k < p.a) (cells:Cells p (columnCells p h g k) s)
    (pc:s.pc=56) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (vIterationCost p k) u ∧ Headers p u ∧ Fixed p u ∧ Cached p h g u ∧
    u.natReg 491=k+1 ∧ Cells p (columnCells p h g (k+1)) u ∧ Frame p s u ∧ u.pc=56 := by
  have hc:=geo.codeBound
  let a:State:={s with pc:=57}
  have ab:=changePC_bound B s 57 hs (by omega)
  have first:BoundedRuns program n x B s 1 a:=
    .next hs (by simp [step,pc,v_branch,index,heads.height,hk,a]) (.refl ab)
  have pre:=v_pre_spec p k B h g a (heads.withPC 57) (f.withPC 57) (c.withPC 57) geo bh.withPC index hk (cells.withPC 57)
  have preRun:=block_runs vPre program 57 n B x a vPre_at rfl ab (by change 64 ≤ B;omega)
    pre.2.2.2.2.2.2.2.2.1 pre.2.2.2.2.2.2.2.2.2
  let v:=applyBlock vPre a
  have vpc:v.pc=64:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have vf:Frame p s v:=((Frame.refl p s).withPC 57).trans pre.2.2.2.2.2.2.2.1
  by_cases zero:k=0
  · let w:State:={v with pc:=85}
    have wb:=changePC_bound B v 85 preRun.final_bound (by omega)
    have branch:BoundedRuns program n x B v 1 w:=
      .next preRun.final_bound (by simp [step,vpc,zero_column_branch,v,pre.2.2.2.2.1,pre.2.1.one,zero,w]) (.refl wb)
    have cv:Cells p (columnCells p h g (k+1)) v:=by
      have hn:0 < p.N:=by have :=geo.positiveA;have :=geo.widthA;omega
      have old:Cells p (changeCell (columnCells p h g 0) 1 ⟨0,hn⟩ (vValue p h 0)) v:=by
        simpa only [zero] using pre.2.2.2.2.2.2.1
      rw [columnCells_step_zero p h g hn] at old
      simpa only [zero] using old
    obtain ⟨u,tail,uh,uf,uc,ui,uv,fr,upc⟩:=advance_run p k B n h g x w
      (pre.1.withPC 85) (pre.2.1.withPC 85) (pre.2.2.1.withPC 85) geo pre.2.2.2.2.1 hk (cv.withPC 85) rfl wb
    refine ⟨u,?_,uh,uf,uc,ui,uv,(vf.withPC 85).trans fr,upc⟩
    convert first.trans (preRun.trans (branch.trans tail)) using 1
    simp only [vIterationCost,zero,ite_true]
    rfl
  · have positive:0 < k:=by omega
    let w:State:={v with pc:=65}
    have wb:=changePC_bound B v 65 preRun.final_bound (by omega)
    have branch:BoundedRuns program n x B v 1 w:=
      .next preRun.final_bound (by simp [step,vpc,zero_column_branch,v,pre.2.2.2.2.1,pre.2.1.one,show ¬k < 1 by omega,w]) (.refl wb)
    have prep:=col_pre_spec p k h g w (pre.1.withPC 65) (pre.2.1.withPC 65) (pre.2.2.1.withPC 65) pre.2.2.2.1
    have safe:readable colPre w ∧ peak colPre w ≤ B:=by
      have hj:=geo.columns;have hs:=geo.gSplit;have gb:=geo.gFresh;have ob:=geo.outputBound
      simp [colPre,readable,Op.readable,peak,Op.peak,w,v,pre.1.column,pre.2.1.zero];omega
    have setJ:=block_runs colPre program 65 n B x w colPre_at rfl wb (by change 66 ≤ B;omega) safe.1 safe.2
    let z:=applyBlock colPre w
    have zpc:z.pc=66:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
    obtain ⟨r,call,cf,rpc,value⟩:=cross_call p B (p.i0+k) p.j0 66 81 n h g x z geo colCross_at
      (by omega) (by omega) (by have :=geo.hRows;omega) (by have :=geo.interior;omega)
      (by have :=geo.columns;omega) prep.2.2.2.1
      ((bh.fullFrame (vf.withPC 65) geo.hFresh).fullFrame prep.2.2.2.2.1 geo.hFresh)
      ((bg.fullFrame (vf.withPC 65) geo.gFresh).fullFrame prep.2.2.2.2.1 geo.gFresh) zpc setJ.final_bound
    have rh:=prep.1.frame cf.fullFrame
    have rf:=prep.2.1.crossFrame cf
    have rc:=prep.2.2.1.crossFrame cf
    have ri:r.natReg 491=k:=(cf.2.2.2.2.1 _ (by decide) (by decide) (by decide) (by decide)).trans
      (prep.2.2.2.2.2.2.trans pre.2.2.2.2.1)
    have rv:r.scalarReg 58=prepared (vValue p h k):=(cf.2.2.2.2.2 _ (by decide)).trans
      (prep.2.2.2.2.2.1.trans pre.2.2.2.2.2.1)
    have rm:r.scalarReg 54=prepared (matrixValue p h g k 0):=by simpa [matrixValue] using value
    have rcell:Cells p (changeCell (columnCells p h g k) 1 ⟨k,hk.trans_le geo.widthA⟩ (vValue p h k)) r:=
      (pre.2.2.2.2.2.2.1.withPC 65).heapEq rfl |>.heapEq cf.2.1
    have done:=col_finish_spec p k B h g r rh rf rc geo ri hk positive rv rm rcell
    have body:=block_runs colFinish program 81 n B x r colFinish_at rpc call.final_bound
      (by change 85 ≤ B;omega) done.2.2.2.2.2.2.1 done.2.2.2.2.2.2.2
    have bpc:(applyBlock colFinish r).pc=85:=by rw [UniformReciprocalMachine.applyBlock_pc,rpc];rfl
    obtain ⟨u,tail,uh,uf,uc,ui,uv,fr,upc⟩:=advance_run p k B n h g x (applyBlock colFinish r)
      done.1 done.2.1 done.2.2.1 geo done.2.2.2.1 hk done.2.2.2.2.1 bpc body.final_bound
    refine ⟨u,?_,uh,uf,uc,ui,uv,?_,upc⟩
    · convert first.trans (preRun.trans (branch.trans (setJ.trans (call.trans (body.trans tail))))) using 1
      simp only [vIterationCost,zero,ite_false]
      change 21+11*(p.split-p.j0)=1+(7+(1+(1+((11*(p.split-p.j0)+5)+(4+2)))))
      omega
    · exact (vf.withPC 65).trans
        (prep.2.2.2.2.1.trans (cf.fullFrame.trans (done.2.2.2.2.2.1.trans fr)))

def vCost (p : Parameters) : ℕ → ℕ → ℕ
  | _,0 => 1
  | k,f+1 => vIterationCost p k+vCost p (k+1) f

theorem vCost_bound (p : Parameters) (k count : ℕ) : vCost p k count ≤ count*(21+11*p.split)+1 := by
  induction count generalizing k with
  | zero => simp [vCost]
  | succ count ih =>
    have hi:=ih (k+1)
    have hm:=Nat.mul_le_mul_left 11 (Nat.sub_le p.split p.j0)
    have hb:vIterationCost p k ≤ 21+11*p.split:=by unfold vIterationCost;split <;> omega
    have eq:(count+1)*(21+11*p.split)=count*(21+11*p.split)+(21+11*p.split):=Nat.succ_mul _ _
    simp only [vCost];rw [eq];omega

theorem v_loop (p : Parameters) (k count B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (c:Cached p h g s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (he:k+count=p.a) (index:s.natReg 491=k) (cells:Cells p (columnCells p h g k) s)
    (pc:s.pc=56) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (vCost p k count) u ∧ Headers p u ∧ Fixed p u ∧ Cached p h g u ∧
    Cells p (columnCells p h g p.a) u ∧ Frame p s u ∧ u.pc=87 := by
  have hc:=geo.codeBound
  induction count generalizing k s with
  | zero =>
    have he':k=p.a:=by omega
    let u:State:={s with pc:=87}
    have ub:=changePC_bound B s 87 hs (by omega)
    refine ⟨u,?_,heads.withPC 87,f.withPC 87,c.withPC 87,?_,(Frame.refl p s).withPC 87,rfl⟩
    · exact .next hs (by simp [step,pc,v_branch,index,heads.height,he',u]) (.refl ub)
    · simpa only [he'] using cells.withPC 87
  | succ count ih =>
    obtain ⟨v,run,vh,vf,vc,vi,values,frame,vpc⟩:=v_iteration p k B n h g x s heads f c geo bh bg
      index (by omega) cells pc hs
    obtain ⟨u,tail,uh,uf,uc,uv,fr,upc⟩:=ih (k+1) v vh vf vc
      (bh.fullFrame frame geo.hFresh) (bg.fullFrame frame geo.gFresh) (by omega) vi values vpc run.final_bound
    exact ⟨u,run.trans tail,uh,uf,uc,uv,frame.trans fr,upc⟩


/-- Literal finite six-kernel values, including every padded zero. -/
def finalCells (p : Parameters) (h g : ℕ → ℂ) : Fin 6 → Fin p.N → ℂ := fun b j=>
  if b.val=0 then if j.val < p.e then wValue p g j.val else 0 else
  if b.val=1 then if j.val < p.a then vValue p h j.val else 0 else
  if b.val=2 then if j.val < p.e then rowValue p h g j.val else 0 else
  if b.val=3 then if j.val=0 then 1 else 0 else
  if b.val=4 then if j.val=0 then 1 else 0 else
  if j.val < p.a then colValue p h g j.val else 0

theorem columnCells_zero (p : Parameters) (h g : ℕ → ℂ) :
    columnCells p h g 0=rowCells p h g p.e := by
  funext b j;fin_cases b <;> simp [columnCells,rowCells]

theorem delta_cells_step (p : Parameters) (h g : ℕ → ℂ) (hn:0 < p.N) :
    changeCell (changeCell (columnCells p h g p.a) 3 ⟨0,hn⟩ 1) 4 ⟨0,hn⟩ 1=finalCells p h g := by
  funext b j;fin_cases b
  all_goals by_cases hj:j.val=0
  all_goals simp [changeCell,columnCells,rowCells,finalCells,Fin.ext_iff,hj]

theorem delta_spec (p : Parameters) (B : ℕ) (h g : ℕ → ℂ) (s : State)
    (heads:Headers p s) (f:Fixed p s) (geo:Geometry p B) (cells:Cells p (columnCells p h g p.a) s) :
    Headers p (applyBlock deltas s) ∧ Cells p (finalCells p h g) (applyBlock deltas s) ∧
    Frame p s (applyBlock deltas s) ∧ readable deltas s ∧ peak deltas s ≤ B := by
  have hn:0 < p.N:=geo.positiveA.trans_le geo.widthA
  have st:=block_stable deltas s (by decide)
  have he:(applyBlock deltas s).scalarHeap=Function.update
      (Function.update s.scalarHeap (p.S+3*p.N) (some (prepared 1)))
      (p.S+4*p.N) (some (prepared 1)):=by simp [deltas,applyBlock,Op.apply,next,f.leftDeltaBase,f.rightDeltaBase,f.scalarOne]
  have fr:Frame p s (applyBlock deltas s):=st.frame (by intro q hq;rw [he];simp (disch:=omega))
  refine ⟨heads.frame fr,?_,fr,by simp [deltas,readable,Op.readable],?_⟩
  · let mid:State:={s with scalarHeap:=Function.update s.scalarHeap (p.S+3*p.N) (some (prepared 1))}
    have c1:Cells p (changeCell (columnCells p h g p.a) 3 ⟨0,hn⟩ 1) mid:=cells.update 3 ⟨0,hn⟩ 1 (by simp [mid])
    have c2:=c1.update 4 ⟨0,hn⟩ 1 (by simpa using he)
    rw [delta_cells_step p h g hn] at c2
    exact c2
  · have ob:=geo.outputBound
    simp [deltas,peak,Op.peak,Op.apply,next,f.leftDeltaBase,f.rightDeltaBase];omega

/-- Exact instruction count, including all startup, termination branches,
physical stores, helper continuations, and final halt. -/
def runtime (p : Parameters) : ℕ := 26+30*p.N+rowCost p 0 p.e+vCost p 0 p.a

def runtimeBudget (p : Parameters) : ℕ := 28+30*p.N+p.e*(19+11*p.split)+p.a*(21+11*p.split)

theorem runtime_bound (p : Parameters) : runtime p ≤ runtimeBudget p := by
  have hr:=rowCost_bound p 0 p.e;have hv:=vCost_bound p 0 p.a
  unfold runtime runtimeBudget;omega

/-- Actual physical six-kernel production from arbitrary prepared H/G banks
and an arbitrary dirty output region. No output expression/table/action
certificate is assumed. All source, external and master-root cells survive. -/
theorem bounded_execution (p : Parameters) (B n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ)
    (s : State) (heads:Headers p s) (geo:Geometry p B)
    (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (pc:s.pc=0) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime p) u ∧ Headers p u ∧ Cells p (finalCells p h g) u ∧
    Frame p s u ∧ u.pc=89 := by
  have hc:=geo.codeBound
  have bootsafe:=boot_safe p B s heads geo
  have start:=block_runs boot program 0 n B x s boot_at pc hs (by change 13 ≤ B;omega) bootsafe.1 bootsafe.2
  have bs:=boot_spec p s heads
  let a:=applyBlock boot s
  have apc:a.pc=13:=by rw [UniformReciprocalMachine.applyBlock_pc,pc];rfl
  obtain ⟨z,zeros,zh,zf,zv,zframe,zpc⟩:=zero_loop p 0 (6*p.N) B n x a bs.1 bs.2.1 geo (by omega)
    bs.2.2.1 (by intro i hi;omega) apc start.final_bound
  have sourceFrame:Frame p s z:=bs.2.2.2.trans zframe
  have cacheSpec:=cache_spec p B h g z zh zf geo
    (bh.fullFrame sourceFrame geo.hFresh) (bg.fullFrame sourceFrame geo.gFresh)
  have cachedRun:=block_runs cache program 18 n B x z cache_at zpc zeros.final_bound
    (by change 26 ≤ B;omega) cacheSpec.2.2.2.2.2.1 cacheSpec.2.2.2.2.2.2
  let b:=applyBlock cache z
  have bpc:b.pc=26:=by rw [UniformReciprocalMachine.applyBlock_pc,zpc];rfl
  have bframe:Frame p s b:=sourceFrame.trans cacheSpec.2.2.2.2.1
  have bcell:Cells p (rowCells p h g 0) b:=by
    have hzero:Cells p (fun _ _=>0) b:=(zero_cells p z zv).heapEq rfl
    have eq:rowCells p h g 0=(fun _ _=>0):=by funext b j;simp [rowCells]
    rw [eq];exact hzero
  obtain ⟨r,rows,rh,rf,rc,rv,rframe,rpc⟩:=row_loop p 0 p.e B n h g x b cacheSpec.1 cacheSpec.2.1 cacheSpec.2.2.1 geo
    (bh.fullFrame bframe geo.hFresh) (bg.fullFrame bframe geo.gFresh) (by omega) cacheSpec.2.2.2.1 bcell bpc cachedRun.final_bound
  have fullRowFrame:Frame p s r:=bframe.trans rframe
  have reset:=block_runs vStart program 55 n B x r vStart_at rpc rows.final_bound (by change 56 ≤ B;omega)
    (by simp [vStart,readable,Op.readable]) (by simp [vStart,peak,Op.peak])
  let c:=applyBlock vStart r
  have st:=block_stable vStart r (by decide)
  have cf:Frame p r c:=st.frame (fun _ _=>rfl)
  have ch:=rh.frame cf
  have fixed:=st.fixed rf
  have cached:Cached p h g c:=⟨rc.v0,rc.w0⟩
  have ci:c.natReg 491=0:=by simp [c,vStart,applyBlock,Op.apply,writeNat,next]
  have cpc:c.pc=56:=by rw [UniformReciprocalMachine.applyBlock_pc,rpc];rfl
  have ccell:Cells p (columnCells p h g 0) c:=by rw [columnCells_zero];exact rv.heapEq rfl
  have fullResetFrame:Frame p s c:=fullRowFrame.trans cf
  obtain ⟨v,columns,vh,vf,_,vv,vframe,vpc⟩:=v_loop p 0 p.a B n h g x c ch fixed cached geo
    (bh.fullFrame fullResetFrame geo.hFresh) (bg.fullFrame fullResetFrame geo.gFresh) (by omega) ci ccell cpc reset.final_bound
  have done:=delta_spec p B h g v vh vf geo vv
  have lastStores:=block_runs deltas program 87 n B x v deltas_at vpc columns.final_bound
    (by change 89 ≤ B;omega) done.2.2.2.1 done.2.2.2.2
  let u:=applyBlock deltas v
  have upc:u.pc=89:=by rw [UniformReciprocalMachine.applyBlock_pc,vpc];rfl
  have halt:BoundedExecution program n x B u 1 u:=.halt lastStores.final_bound (by simp [step,upc,halt_at])
  refine ⟨u,?_,done.1,done.2.1,fullResetFrame.trans (vframe.trans done.2.2.1),upc⟩
  convert start.executes (zeros.executes (cachedRun.executes (rows.executes (reset.executes (columns.executes (lastStores.executes halt)))))) using 1
  change 26+30*p.N+rowCost p 0 p.e+vCost p 0 p.a=
    13+((5*(6*p.N)+1)+(8+(rowCost p 0 p.e+(1+(vCost p 0 p.a+(2+1))))))
  omega

theorem inputVector_padding (K t : ℕ) (f : Fin t → ℂ) (j : Fin (UniformRadixTwoDAG.width K)) :
    UniformConvolutionDAG.inputVector K t (UniformConvolutionDAG.padInputs K t) f j=
      if hj:j.val < t then f ⟨j.val,hj⟩ else 0 := by
  unfold UniformConvolutionDAG.inputVector UniformConvolutionDAG.padInputs
  split_ifs with hj
  · change (Fin.snoc f (0 : ℂ) : Fin (t+1) → ℂ) (Fin.castSucc ⟨j.val,hj⟩)=f ⟨j.val,hj⟩
    rw [Fin.snoc_castSucc]
  · simp

theorem finalCells_rankKernels (p : Parameters) (B K : ℕ) (h g : ℕ → ℂ)
    (geo:Geometry p B) (width:p.N=UniformRadixTwoDAG.width K)
    (b : Fin 6) (j : Fin (UniformRadixTwoDAG.width K)) :
    finalCells p h g b ⟨j.val,by rw [width];exact j.isLt⟩=
      UniformToeplitzCrossDAG.rankKernels K p.a p.e (matrixValue p h g) (vValue p h) (wValue p g) b j := by
  have ha:=geo.positiveA;have he:=geo.positiveE
  fin_cases b
  all_goals simp only [UniformToeplitzCrossDAG.rankKernels]
  all_goals simp (disch:=omega) [UniformToeplitzCrossDAG.leftFactor,UniformToeplitzCrossDAG.rightFactor,
    finalCells,rowValue,colValue,OAI.ExactFourier.Displacement.delta,inputVector_padding]
  all_goals intro hi hz
  all_goals have hv:=congrArg Fin.val hz
  all_goals simp only [Fin.val_zero] at hv
  all_goals omega

/-- Exact caller-facing rank-kernel bank in the frozen Fin6 order. -/
def KernelBank (p : Parameters) (K : ℕ) (h g : ℕ → ℂ) (s : State) : Prop :=
  ∀b : Fin 6,∀j : Fin (UniformRadixTwoDAG.width K),s.scalarHeap (p.S+b.val*p.N+j.val)=
    some (prepared (UniformToeplitzCrossDAG.rankKernels K p.a p.e
      (matrixValue p h g) (vValue p h) (wValue p g) b j))

theorem rank_kernel_execution (p : Parameters) (B K n : ℕ) (h g : ℕ → ℂ) (x : Fin n → ℂ)
    (s : State) (heads:Headers p s) (geo:Geometry p B)
    (width:p.N=UniformRadixTwoDAG.width K) (bh:Bank p.H p.hSize h s) (bg:Bank p.G p.gSize g s)
    (pc:s.pc=0) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime p) u ∧ KernelBank p K h g u ∧ Headers p u ∧
    Bank p.H p.hSize h u ∧ Bank p.G p.gSize g u ∧ Frame p s u ∧ u.pc=89 := by
  obtain ⟨u,run,uh,cells,frame,upc⟩:=bounded_execution p B n h g x s heads geo bh bg pc hs
  refine ⟨u,run,?_,uh,bh.fullFrame frame geo.hFresh,bg.fullFrame frame geo.gFresh,frame,upc⟩
  intro b j
  have value:=cells b ⟨j.val,by rw [width];exact j.isLt⟩
  rw [finalCells_rankKernels p B K h g geo width b j] at value
  exact value


/-- Local widths and padding bounded by r give a quadratic preparation
charge. This is a producer cost, independent of every input data value. -/
theorem runtime_axis_bound (p : Parameters) (r : ℕ) (hN:p.N ≤ 8*r)
    (ha:p.a ≤ r) (he:p.e ≤ r) (hs:p.split ≤ r) :
    runtime p ≤ 22*r^2+280*r+28 := by
  have hrow:=Nat.mul_le_mul he (show 19+11*p.split ≤ 19+11*r by omega)
  have hcol:=Nat.mul_le_mul ha (show 21+11*p.split ≤ 21+11*r by omega)
  have hbase:=runtime_bound p
  unfold runtimeBudget at hbase
  nlinarith

theorem Frame.master {p : Parameters} {s t : State} (frame:Frame p s t) (fresh:0 < p.S) :
    t.scalarHeap 0=s.scalarHeap 0 := frame.2.2.2.2.2 0 (Or.inl fresh)

theorem Frame.saved {p : Parameters} {s t : State} (frame:Frame p s t) (r : ℕ) (hr:100 ≤ r ∧ r ≤ 106) :
    t.natReg r=s.natReg r := frame.2.2.2.1 r (Or.inl (by omega))

end
end ExactFourierCircuits.UniformRankKernelMachine
