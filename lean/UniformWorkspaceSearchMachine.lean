import UniformWorkspacePlanner
import UniformPreparationRowTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformWorkspaceSearchMachine
open UniformMachine
open UniformPreparationRowTableMachine (Op applyBlock peak readable BlockAt block_runs applyBlock_pc control_run)

/-- Nat290 is the width; Nat291 is the largest fitting chunk width or zero.
Only Nat291..312 are written. Every pair is checked, including ragged tails;
clog2 is calculated by the literal doubling loop at pc33. -/
def program : Program := [
  .natLiteral 292 0,.natLiteral 293 1,.natLiteral 294 2,.natLiteral 295 3,.natLiteral 296 6,
  .natLiteral 291 0,.natBinary .add 297 293 292,.natBinary .div 298 290 294,.natBinary .sub 299 290 298,
  .branchLT 290 297 57 10,
  .natBinary .add 300 299 297,.natBinary .sub 300 300 293,.natBinary .div 300 300 297,
  .natBinary .add 301 298 297,.natBinary .sub 301 301 293,.natBinary .div 301 301 297,
  .natLiteral 302 0,.natLiteral 303 1,
  .branchLT 302 300 19 53,.natLiteral 304 0,.natBinary .mul 305 302 297,.natBinary .sub 306 299 305,
  .branchLT 297 306 23 24,.natBinary .add 306 297 292,
  .branchLT 304 301 25 51,.natBinary .mul 305 304 297,.natBinary .sub 307 298 305,
  .branchLT 297 307 28 29,.natBinary .add 307 297 292,
  .natBinary .add 308 306 307,.natBinary .mul 308 308 294,.natLiteral 309 1,.natLiteral 310 0,
  .branchLT 309 308 34 37,.natBinary .mul 309 309 294,.natBinary .add 310 310 293,.jump 33,
  .natBinary .mul 311 310 295,.natBinary .mul 311 311 309,.natBinary .mul 312 294 309,
  .natBinary .add 311 311 312,.natBinary .mul 311 311 296,.natBinary .mul 312 294 306,
  .natBinary .add 311 311 312,.natBinary .add 311 311 306,.natBinary .add 311 311 307,
  .branchLT 290 311 47 49,.natLiteral 303 0,.jump 49,
  .natBinary .add 304 304 293,.jump 24,.natBinary .add 302 302 293,.jump 18,
  .branchLT 303 293 55 54,.natBinary .add 291 297 292,.natBinary .add 297 297 293,.jump 9,.halt]

theorem program_length : program.length=58 := rfl

def targetWidth (v : ℕ) : ℕ := v-v/2
def sourceWidth (v : ℕ) : ℕ := v/2
def targets (v b : ℕ) : ℕ := UniformWorkspacePlanner.chunkCount (targetWidth v) b
def sources (v b : ℕ) : ℕ := UniformWorkspacePlanner.chunkCount (sourceWidth v) b
def targetSize (v b i : ℕ) : ℕ := min b (targetWidth v-i*b)
def sourceSize (v b j : ℕ) : ℕ := min b (sourceWidth v-j*b)
def pairAmount (v b i j : ℕ) : ℕ :=
  UniformWorkspacePlanner.gateCount (targetSize v b i) (sourceSize v b j)+
    targetSize v b i+sourceSize v b j

def pairFit (v b i j : ℕ) : Bool := decide (pairAmount v b i j ≤ v)
def sourceFits (v b i : ℕ) : ℕ → ℕ → Bool
  | _,0=>true
  | j,f+1=>pairFit v b i j && sourceFits v b i (j+1) f
def targetFits (v b : ℕ) : ℕ → ℕ → Bool
  | _,0=>true
  | i,f+1=>sourceFits v b i 0 (sources v b) && targetFits v b (i+1) f

theorem sourceFits_true (v b i start fuel : ℕ) : sourceFits v b i start fuel=true ↔
    ∀j,start ≤ j → j < start+fuel → pairFit v b i j=true := by
  induction fuel generalizing start with
  | zero=>simp [sourceFits];intro j hj hj';omega
  | succ fuel ih=>
    rw [sourceFits,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨ha,hb⟩ j hj hj'
      by_cases he:j=start
      · simpa [he] using ha
      · exact hb j (by omega) (by omega)
    · intro h
      exact ⟨h start (by omega) (by omega),fun j hj hj'=>h j (by omega) (by omega)⟩

theorem targetFits_true (v b start fuel : ℕ) : targetFits v b start fuel=true ↔
    ∀i,start ≤ i → i < start+fuel → ∀j,j < sources v b → pairFit v b i j=true := by
  induction fuel generalizing start with
  | zero=>simp [targetFits];intro i hi hi';omega
  | succ fuel ih=>
    rw [targetFits,Bool.and_eq_true,sourceFits_true,ih]
    constructor
    · rintro ⟨ha,hb⟩ i hi hi' j hj
      by_cases he:i=start
      · subst i;exact ha j (by omega) (by simpa using hj)
      · exact hb i (by omega) (by omega) j hj
    · intro h
      exact ⟨fun j _ hj=>h start (by omega) (by omega) j (by simpa using hj),
        fun i hi hi' j hj=>h i (by omega) (by omega) j hj⟩

theorem allFits_indices (v b : ℕ) : UniformWorkspacePlanner.allFits v b=true ↔
    ∀i,i < targets v b → ∀j,j < sources v b → pairFit v b i j=true := by
  simp only [pairFit,decide_eq_true_eq]
  simp [UniformWorkspacePlanner.allFits,UniformWorkspacePlanner.chunkSizes,targets,sources,
    targetWidth,sourceWidth,pairAmount,targetSize,sourceSize,List.all_eq_true]

theorem bool_eq_of_true_iff (x y : Bool) (h:x=true↔y=true) : x=y := by cases x <;> cases y <;> simp_all

theorem targetFits_allFits (v b : ℕ) :
    targetFits v b 0 (targets v b)=UniformWorkspacePlanner.allFits v b := by
  apply bool_eq_of_true_iff
  rw [targetFits_true,allFits_indices]
  simp

def Seen (v b best : ℕ) : Prop := best<b ∧
  (best=0 ∨ (0<best ∧ UniformWorkspacePlanner.allFits v best=true)) ∧
  ∀c,0<c → c<b → UniformWorkspacePlanner.allFits v c=true → c ≤ best

theorem seen_zero (v : ℕ) : Seen v 1 0 := by
  refine ⟨by omega,Or.inl rfl,?_⟩;intro c hc hc' _;omega

theorem seen_next {v b best : ℕ} (h:Seen v b best) (hb:0<b) :
    Seen v (b+1) (if UniformWorkspacePlanner.allFits v b then b else best) := by
  cases hf:UniformWorkspacePlanner.allFits v b with
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    refine ⟨by have hl:=h.1;omega,h.2.1,?_⟩
    intro c hc hc' hfit
    have hcb:c<b:=by
      by_contra hge
      have he:c=b:=by omega
      rw [he,hf] at hfit
      cases hfit
    exact h.2.2 c hc hcb hfit
  | true=>
    simp only [ite_true]
    exact ⟨by omega,Or.inr ⟨hb,hf⟩,fun c _ hc _=>by omega⟩

theorem selected_of_seen {v best : ℕ} (h:Seen v (v+1) best) : best=UniformWorkspacePlanner.selected v := by
  apply Nat.le_antisymm
  · rcases h.2.1 with he|⟨hp,hfit⟩
    · omega
    · exact UniformWorkspacePlanner.candidate_le_selected (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr h.1,hp,hfit⟩)
  · apply Finset.sup_le
    intro b hb
    obtain ⟨hr,hpos,hfit⟩:=Finset.mem_filter.mp hb
    exact h.2.2 b hpos (Finset.mem_range.mp hr) hfit

theorem chunkCount_bound {s b v : ℕ} (hs:s ≤ v) (hb:0<b) :
    UniformWorkspacePlanner.chunkCount s b ≤ v := by
  unfold UniformWorkspacePlanner.chunkCount
  apply (Nat.div_le_iff_le_mul_add_pred hb).2
  have hv:v ≤ b*v:=by nlinarith
  omega

theorem targets_bound {v b : ℕ} (hb:0<b) : targets v b ≤ v :=
  chunkCount_bound (Nat.sub_le _ _) hb

theorem sources_bound {v b : ℕ} (hb:0<b) : sources v b ≤ v :=
  chunkCount_bound (Nat.div_le_self _ _) hb

theorem clog_bound (N : ℕ) : Nat.clog 2 N ≤ N :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=N)).le

theorem clog_width_bound (N : ℕ) : 2^Nat.clog 2 N ≤ 2*N+1 := by
  by_cases h:1<N
  · have hp:=Nat.pow_pred_clog_lt_self (by decide : 1<2) h
    simp only [Nat.pred_eq_sub_one] at hp
    have hk:=Nat.clog_pos (by decide : 1<2) h
    rw [show Nat.clog 2 N=(Nat.clog 2 N-1)+1 by omega,pow_succ]
    nlinarith
  · rw [Nat.clog_of_right_le_one (by omega : N ≤ 1)]
    simp

def budget (v : ℕ) : ℕ := 1024*(v+1)^2+256

theorem pair_bound {v a e : ℕ} (ha:a ≤ v) (he:e ≤ v) :
    UniformWorkspacePlanner.gateCount a e+a+e ≤ budget v := by
  have hk:UniformWorkspacePlanner.exponent a e ≤ 4*v:=by
    have h:=clog_bound (2*(a+e));unfold UniformWorkspacePlanner.exponent;omega
  have hp:2^UniformWorkspacePlanner.exponent a e ≤ 8*v+1:=by
    have h:=clog_width_bound (2*(a+e));unfold UniformWorkspacePlanner.exponent;omega
  rw [UniformWorkspacePlanner.gateCount_eq]
  unfold budget
  have hprod:=Nat.mul_le_mul hk hp
  nlinarith

noncomputable section

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀i,(i < 291 ∨ 312 < i) → u.natReg i=s.natReg i

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi=>(h'.2.2.2.2.2 i hi).trans (h.2.2.2.2.2 i hi)⟩

theorem Frame.withPC (s : State) (pc : ℕ) : Frame s {s with pc:=pc} :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩

def allowed : Op → Prop
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ =>291 ≤ d ∧ d ≤ 312
  | _=>False

theorem block_frame (os : List Op) (s : State) (h:∀o∈os,allowed o) : Frame s (applyBlock os s) := by
  induction os generalizing s with
  | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
  | cons o os ih=>
    have ho:=h o (by simp)
    have ht:=ih (o.apply s) (fun t ht=>h t (by simp [ht]))
    apply Frame.trans (u:=o.apply s) ?_ ht
    cases o with
    | get d a=>exact False.elim ho
    | put a r=>exact False.elim ho
    | literal d v | add d l r | sub d l r | mul d l r=>
      refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
      intro i hi
      have hne:i ≠ d:=by dsimp [allowed] at ho;omega
      simp [Op.apply,writeNat,next,hne]


theorem block_nat (os : List Op) (s : State) (i : ℕ)
    (h:∀o∈os,o.scratch ≠ i) : (applyBlock os s).natReg i=s.natReg i := by
  induction os generalizing s with
  | nil=>rfl
  | cons o os ih=>
    have ho:=h o (by simp)
    rw [applyBlock,ih (o.apply s) (fun t ht=>h t (by simp [ht]))]
    cases o <;> simp_all [Op.scratch,Op.apply,writeNat,next,ne_comm]

theorem division_run (p : Program) (n B d l r : ℕ) (x : Fin n → ℂ) (s : State)
    (hc:p[s.pc]?=some (.natBinary .div d l r)) (hr:s.natReg r ≠ 0) (hs:WordBound B s) (hp:s.pc+1 ≤ B) :
    BoundedRuns p n x B s 1 (writeNat s d (s.natReg l/s.natReg r)) := by
  have hv:s.natReg l/s.natReg r ≤ B:=(Nat.div_le_self _ _).trans (hs.2.1 l)
  have hb:=writeNat_bound B s d _ hs hp hv
  exact .next hs (by simp [step,hc,evalNat,hr]) (.refl hb)

theorem division_frame (s : State) (d l r : ℕ) (hd:291 ≤ d ∧ d ≤ 312) :
    Frame s (writeNat s d (s.natReg l/s.natReg r)) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  simp [writeNat,next,show i ≠ d by omega]

structure Constants (v : ℕ) (s : State) : Prop where
  width : s.natReg 290=v
  zero : s.natReg 292=0
  one : s.natReg 293=1
  two : s.natReg 294=2
  three : s.natReg 295=3
  six : s.natReg 296=6

structure Base (v b : ℕ) (s : State) : Prop where
  constants : Constants v s
  candidate : s.natReg 297=b
  source : s.natReg 298=sourceWidth v
  target : s.natReg 299=targetWidth v

structure Candidate (v b i : ℕ) (good : Bool) (s : State) : Prop where
  base : Base v b s
  targets : s.natReg 300=targets v b
  sources : s.natReg 301=sources v b
  index : s.natReg 302=i
  good : s.natReg 303=if good then 1 else 0

structure Inner (v b i j : ℕ) (good : Bool) (s : State) : Prop where
  candidate : Candidate v b i good s
  index : s.natReg 304=j
  target : s.natReg 306=targetSize v b i

structure LogCounters (N j : ℕ) (s : State) : Prop where
  one : s.natReg 293=1
  two : s.natReg 294=2
  goal : s.natReg 308=N
  power : s.natReg 309=2^j
  exponent : s.natReg 310=j

def logStep : List Op := [.mul 309 309 294,.add 310 310 293]

theorem logStep_code : BlockAt logStep program 34 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl

def LogFrame (s u : State) : Prop := Frame s u ∧
  ∀i,i ≠ 309 → i ≠ 310 → u.natReg i=s.natReg i

theorem LogFrame.trans {s u v : State} (h:LogFrame s u) (h':LogFrame u v) : LogFrame s v :=
  ⟨h.1.trans h'.1,fun i h9 h10=>(h'.2 i h9 h10).trans (h.2 i h9 h10)⟩

theorem LogFrame.withPC (s : State) (pc : ℕ) : LogFrame s {s with pc:=pc} :=
  ⟨Frame.withPC s pc,fun _ _ _=>rfl⟩

theorem logStep_frame (s : State) : LogFrame s (applyBlock logStep s) := by
  refine ⟨?_,?_⟩
  · apply block_frame
    intro o ho;simp [logStep] at ho
    rcases ho with rfl|rfl <;> simp [allowed]
  · intro i hi hi'
    apply block_nat
    intro o ho;simp [logStep] at ho
    rcases ho with rfl|rfl <;> simpa [Op.scratch,ne_comm] using (by assumption : i ≠ _)

theorem LogCounters.withPC {N j pc : ℕ} {s : State} (h:LogCounters N j s) :
    LogCounters N j {s with pc:=pc} := ⟨h.one,h.two,h.goal,h.power,h.exponent⟩

/-- The only exponent-producing loop is four charged instructions per
successful doubling and a final branch. No logarithm oracle is executed. -/
theorem doubling_loop (n N j fuel B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc:LogCounters N j s) (hj:j+fuel=Nat.clog 2 N) (hp:s.pc=33)
    (hs:WordBound B s) (hB:2*N+80 ≤ B) : ∃u,
    BoundedRuns program n x B s (4*fuel+1) u ∧ u.pc=37 ∧
    LogCounters N (Nat.clog 2 N) u ∧ LogFrame s u := by
  induction fuel generalizing j s with
  | zero=>
    have he:j=Nat.clog 2 N:=by omega
    have hstop:¬2^j < N:=by rw [he];have h:=Nat.le_pow_clog (by decide : 1<2) N;omega
    have ht:step program n x s=.running {s with pc:=37}:=by
      simp [step,program,hp,hc.power,hc.goal,hstop]
    exact ⟨{s with pc:=37},control_run program n B 37 x s hs (by omega) ht,rfl,
      by simpa [he] using hc.withPC,LogFrame.withPC s 37⟩
  | succ fuel ih=>
    have hlt:j < Nat.clog 2 N:=by omega
    have hpow:2^j < N:=Nat.pow_lt_of_lt_clog hlt
    have he:step program n x s=.running {s with pc:=34}:=by
      simp [step,program,hp,hc.power,hc.goal,hpow]
    have hentry:=control_run program n B 34 x s hs (by omega) he
    let e:State:={s with pc:=34}
    have hpeak:peak logStep e ≤ B:=by
      simp [peak,logStep,Op.peak,Op.apply,writeNat,next,hc.power,hc.two,hc.one,hc.exponent,e]
      have hlog:=clog_bound N;omega
    have hstep:=block_runs logStep program 34 n B x e logStep_code rfl hentry.final_bound
      (by change 34+2 ≤ B;omega) (by simp [logStep,readable,Op.readable]) hpeak
    have hnext:LogCounters N (j+1) (applyBlock logStep e):=by
      constructor
      all_goals simp [applyBlock,logStep,Op.apply,writeNat,next,e,hc.one,hc.two,hc.goal,hc.power,hc.exponent,pow_succ]
    have hpc:(applyBlock logStep e).pc=36:=by rw [applyBlock_pc];rfl
    have ht:step program n x (applyBlock logStep e)=.running {applyBlock logStep e with pc:=33}:=by
      simp [step,program,hpc]
    have hback:=control_run program n B 33 x (applyBlock logStep e) hstep.final_bound (by omega) ht
    obtain ⟨u,hu,hup,huc,huf⟩:=ih (j+1) {applyBlock logStep e with pc:=33} hnext.withPC
      (by omega) rfl hback.final_bound
    refine ⟨u,?_,hup,huc,?_⟩
    · convert ((hentry.trans hstep).trans hback).trans hu using 1
      change 4*(fuel+1)+1=1+2+1+(4*fuel+1)
      omega
    · exact (LogFrame.withPC s 34).trans ((logStep_frame e).trans
        ((LogFrame.withPC _ 33).trans huf))


def Stable (writes : Finset ℕ) (s u : State) : Prop := Frame s u ∧
  ∀i,i∉writes → u.natReg i=s.natReg i

theorem Stable.trans {w : Finset ℕ} {s u v : State} (h:Stable w s u) (h':Stable w u v) :
    Stable w s v := ⟨h.1.trans h'.1,fun i hi=>(h'.2 i hi).trans (h.2 i hi)⟩

theorem Stable.withPC (w : Finset ℕ) (s : State) (pc : ℕ) : Stable w s {s with pc:=pc} :=
  ⟨Frame.withPC s pc,fun _ _=>rfl⟩

theorem Stable.mono {w z : Finset ℕ} {s u : State} (h:Stable w s u) (hz:w⊆z) : Stable z s u :=
  ⟨h.1,fun i hi=>h.2 i (fun hw=>hi (hz hw))⟩

theorem block_stable (os : List Op) (w : Finset ℕ) (s : State)
    (h:∀o∈os,allowed o ∧ o.scratch∈w) : Stable w s (applyBlock os s) := by
  refine ⟨block_frame os s (fun o ho=>(h o ho).1),?_⟩
  intro i hi
  apply block_nat
  intro o ho
  have hm: o.scratch∈w:=(h o ho).2
  intro he;rw [he] at hm;exact hi hm

theorem Constants.transport {v : ℕ} {s u : State} (h:Constants v s)
    (he:∀i,i=290 ∨ (292 ≤ i ∧ i ≤ 296) → u.natReg i=s.natReg i) : Constants v u := by
  constructor
  · rw [he 290 (Or.inl rfl)];exact h.width
  · rw [he 292 (by right;omega)];exact h.zero
  · rw [he 293 (by right;omega)];exact h.one
  · rw [he 294 (by right;omega)];exact h.two
  · rw [he 295 (by right;omega)];exact h.three
  · rw [he 296 (by right;omega)];exact h.six

theorem Base.transport {v b : ℕ} {s u : State} (h:Base v b s)
    (he:∀i,i=290 ∨ (292 ≤ i ∧ i ≤ 299) → u.natReg i=s.natReg i) : Base v b u := by
  refine ⟨h.constants.transport (fun i hi=>he i (by rcases hi with hi|hi;left;exact hi;right;omega)),?_,?_,?_⟩
  · rw [he 297 (by right;omega)];exact h.candidate
  · rw [he 298 (by right;omega)];exact h.source
  · rw [he 299 (by right;omega)];exact h.target

def pairWrites : Finset ℕ := {303,304,305,307,308,309,310,311,312}
def prepWrites : Finset ℕ := {305,307,308,309,310,311,312}
def targetWrites : Finset ℕ := {302,303,304,305,306,307,308,309,310,311,312}

theorem Inner.update {v b i j j' : ℕ} {good good' : Bool} {s u : State}
    (h:Inner v b i j good s) (hf:Stable pairWrites s u)
    (hg:u.natReg 303=if good' then 1 else 0) (hj:u.natReg 304=j') : Inner v b i j' good' u := by
  refine ⟨⟨?_,?_,?_,?_,hg⟩,hj,?_⟩
  · apply h.candidate.base.transport
    intro t ht
    apply hf.2
    simp only [pairWrites,Finset.mem_insert,Finset.mem_singleton]
    omega
  · rw [hf.2 300 (by decide)];exact h.candidate.targets
  · rw [hf.2 301 (by decide)];exact h.candidate.sources
  · rw [hf.2 302 (by decide)];exact h.candidate.index
  · rw [hf.2 306 (by decide)];exact h.target

def minEnd (pc d b R : ℕ) (s : State) : State :=
  if b < R then writeNat {s with pc:=pc+1} d b else {s with pc:=pc+2}

theorem min_execution (n B pc d b R : ℕ) (x : Fin n → ℂ) (s : State)
    (hp:s.pc=pc) (hcode:program[pc]?=some (.branchLT 297 d (pc+1) (pc+2)))
    (hcopy:program[pc+1]?=some (.natBinary .add d 297 292))
    (hb:s.natReg 297=b) (hr:s.natReg d=R) (hz:s.natReg 292=0)
    (hs:WordBound B s) (hB:pc+2 ≤ B) :
    BoundedRuns program n x B s (if b < R then 2 else 1) (minEnd pc d b R s) ∧
    (minEnd pc d b R s).pc=pc+2 ∧ (minEnd pc d b R s).natReg d=min b R := by
  by_cases h:b < R
  · have ht:step program n x s=.running {s with pc:=pc+1}:=by
      simp [step,hp,hcode,hb,hr,h]
    have he:=control_run program n B (pc+1) x s hs (by omega) ht
    have hc:step program n x {s with pc:=pc+1}=.running (writeNat {s with pc:=pc+1} d b):=by
      simp [step,hcopy,evalNat,hb,hz]
    have hw:=writeNat_bound B {s with pc:=pc+1} d b he.final_bound (by change pc+1+1 ≤ B;omega)
      (by simpa [hb] using hs.2.1 297)
    have hu:BoundedRuns program n x B {s with pc:=pc+1} 1 (writeNat {s with pc:=pc+1} d b):=
      .next he.final_bound hc (.refl hw)
    refine ⟨?_,?_,?_⟩
    · simpa [minEnd,h] using he.trans hu
    · simp [minEnd,h,writeNat,next]
    · simp [minEnd,h,writeNat,next,Nat.min_eq_left h.le]
  · have ht:step program n x s=.running {s with pc:=pc+2}:=by
      simp [step,hp,hcode,hb,hr,h]
    refine ⟨?_,by simp [minEnd,h],?_⟩
    · simpa [minEnd,h] using control_run program n B (pc+2) x s hs hB ht
    · simp [minEnd,h,hr,Nat.min_eq_right (by omega : R ≤ b)]

theorem min_stable (pc d b R : ℕ) (s : State) (hd:291 ≤ d ∧ d ≤ 312) :
    Stable {d} s (minEnd pc d b R s) := by
  unfold minEnd;split_ifs
  · refine ⟨⟨rfl,rfl,rfl,rfl,rfl,?_⟩,?_⟩
    · intro i hi;simp [writeNat,next,show i ≠ d by omega]
    · intro i hi;simp only [Finset.mem_singleton] at hi
      simp [writeNat,next,hi]
  · exact Stable.withPC _ _ _

def sourceStart : List Op := [.mul 305 304 297,.sub 307 298 305]
def sizeStart : List Op := [.add 308 306 307,.mul 308 308 294,.literal 309 1,.literal 310 0]
def gateBlock : List Op := [.mul 311 310 295,.mul 311 311 309,.mul 312 294 309,
  .add 311 311 312,.mul 311 311 296,.mul 312 294 306,
  .add 311 311 312,.add 311 311 306,.add 311 311 307]
def advanceSource : List Op := [.add 304 304 293]

theorem sourceStart_code : BlockAt sourceStart program 25 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem sizeStart_code : BlockAt sizeStart program 29 := by
  intro i hi;change i < 4 at hi;interval_cases i <;> rfl
theorem gateBlock_code : BlockAt gateBlock program 37 := by
  intro i hi;change i < 9 at hi;interval_cases i <;> rfl
theorem advanceSource_code : BlockAt advanceSource program 49 := by
  intro i hi;change i < 1 at hi;interval_cases i;rfl

theorem sourceStart_stable (s : State) : Stable prepWrites s (applyBlock sourceStart s) := by
  apply block_stable
  intro o ho;simp [sourceStart] at ho
  rcases ho with rfl|rfl <;> simp [allowed,Op.scratch,prepWrites]

theorem sizeStart_stable (s : State) : Stable prepWrites s (applyBlock sizeStart s) := by
  apply block_stable
  intro o ho;simp [sizeStart] at ho
  rcases ho with rfl|rfl|rfl|rfl <;> simp [allowed,Op.scratch,prepWrites]

theorem gateBlock_stable (s : State) : Stable prepWrites s (applyBlock gateBlock s) := by
  apply block_stable
  intro o ho;simp [gateBlock] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [allowed,Op.scratch,prepWrites]

theorem advanceSource_stable (s : State) : Stable pairWrites s (applyBlock advanceSource s) := by
  apply block_stable
  intro o ho;simp [advanceSource] at ho;subst o;simp [allowed,Op.scratch,pairWrites]

theorem log_stable {s u : State} (h:LogFrame s u) : Stable prepWrites s u := by
  refine ⟨h.1,?_⟩
  intro i hi
  simp only [prepWrites,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2 i (by tauto) (by tauto)


theorem prep_subset_pair : prepWrites⊆pairWrites := by
  intro i hi;simp only [prepWrites,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem prep_inner {v b i j : ℕ} {good : Bool} {s u : State}
    (h:Inner v b i j good s) (hf:Stable prepWrites s u) : Inner v b i j good u :=
  h.update (hf.mono prep_subset_pair)
    (by rw [hf.2 303 (by decide)];exact h.candidate.good)
    (by rw [hf.2 304 (by decide)];exact h.index)

theorem Base.withPC {v b pc : ℕ} {s : State} (h:Base v b s) : Base v b {s with pc:=pc} :=
  h.transport (fun _ _=>rfl)
theorem Candidate.withPC {v b i pc : ℕ} {good : Bool} {s : State} (h:Candidate v b i good s) :
    Candidate v b i good {s with pc:=pc} := ⟨h.base.withPC,h.targets,h.sources,h.index,h.good⟩
theorem Inner.withPC {v b i j pc : ℕ} {good : Bool} {s : State} (h:Inner v b i j good s) :
    Inner v b i j good {s with pc:=pc} := ⟨h.candidate.withPC,h.index,h.target⟩

theorem sourceStart_value {v b i j : ℕ} {good : Bool} {s : State} (h:Inner v b i j good s) :
    (applyBlock sourceStart s).natReg 307=sourceWidth v-j*b := by
  simp [applyBlock,sourceStart,Op.apply,writeNat,next,h.index,h.candidate.base.candidate,h.candidate.base.source]

theorem sourceStart_peak {v b i j B : ℕ} {good : Bool} {s : State}
    (h:Inner v b i j good s) (hb:b ≤ v) (hj:j ≤ v) (hB:budget v ≤ B) : peak sourceStart s ≤ B := by
  simp [peak,sourceStart,Op.peak,Op.apply,writeNat,next,h.index,h.candidate.base.candidate,h.candidate.base.source]
  have hm:=Nat.mul_le_mul hj hb
  have hs:sourceWidth v ≤ v:=Nat.div_le_self _ _
  have hsub:(sourceWidth v-j*b) ≤ v:=(Nat.sub_le _ _).trans hs
  unfold budget at hB
  repeat' apply And.intro
  all_goals nlinarith

theorem sizeStart_values {v b i j : ℕ} {good : Bool} {s : State}
    (h:Inner v b i j good s) (he:s.natReg 307=sourceSize v b j) :
    LogCounters (2*(targetSize v b i+sourceSize v b j)) 0 (applyBlock sizeStart s) ∧
    (applyBlock sizeStart s).natReg 307=sourceSize v b j := by
  refine ⟨?_,?_⟩
  · constructor
    all_goals simp [applyBlock,sizeStart,Op.apply,writeNat,next,h.candidate.base.constants.one,
      h.candidate.base.constants.two,h.target,he,Nat.mul_comm]
  · simpa [applyBlock,sizeStart,Op.apply,writeNat,next] using he

theorem sizeStart_peak {v b i j B : ℕ} {good : Bool} {s : State}
    (h:Inner v b i j good s) (he:s.natReg 307=sourceSize v b j) (hb:b ≤ v) (hB:budget v ≤ B) :
    peak sizeStart s ≤ B := by
  simp [peak,sizeStart,Op.peak,Op.apply,writeNat,next,h.candidate.base.constants.two,h.target,he]
  have ha:targetSize v b i ≤ v:=(min_le_left _ _).trans hb
  have he':sourceSize v b j ≤ v:=(min_le_left _ _).trans hb
  unfold budget at hB
  repeat' apply And.intro
  all_goals nlinarith

theorem gateBlock_value {v b i j : ℕ} {good : Bool} {s : State}
    (h:Inner v b i j good s) (he:s.natReg 307=sourceSize v b j)
    (hl:LogCounters (2*(targetSize v b i+sourceSize v b j))
      (UniformWorkspacePlanner.exponent (targetSize v b i) (sourceSize v b j)) s) :
    (applyBlock gateBlock s).natReg 311=pairAmount v b i j := by
  simp [applyBlock,gateBlock,Op.apply,writeNat,next,h.candidate.base.constants.three,
    h.candidate.base.constants.two,h.candidate.base.constants.six,h.target,he,hl.exponent,hl.power]
  unfold pairAmount
  rw [UniformWorkspacePlanner.gateCount_eq]
  ring

theorem gateBlock_peak {v b i j B : ℕ} {good : Bool} {s : State}
    (h:Inner v b i j good s) (he:s.natReg 307=sourceSize v b j)
    (hl:LogCounters (2*(targetSize v b i+sourceSize v b j))
      (UniformWorkspacePlanner.exponent (targetSize v b i) (sourceSize v b j)) s)
    (hb:b ≤ v) (hB:budget v ≤ B) : peak gateBlock s ≤ B := by
  have ha:targetSize v b i ≤ v:=(min_le_left _ _).trans hb
  have he':sourceSize v b j ≤ v:=(min_le_left _ _).trans hb
  have hg:pairAmount v b i j ≤ B:=(pair_bound ha he').trans hB
  unfold pairAmount at hg
  rw [UniformWorkspacePlanner.gateCount_eq] at hg
  simp [peak,gateBlock,Op.peak,Op.apply,writeNat,next,h.candidate.base.constants.three,
    h.candidate.base.constants.two,h.candidate.base.constants.six,h.target,he,hl.exponent,hl.power]
  have hp:1 ≤ 2^UniformWorkspacePlanner.exponent (targetSize v b i) (sourceSize v b j):=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (pow_pos (by decide : 0<(2:ℕ)) _))
  have hk:=Nat.mul_le_mul_left (UniformWorkspacePlanner.exponent (targetSize v b i) (sourceSize v b j)) hp
  simp only [Nat.mul_one] at hk
  repeat' apply And.intro
  all_goals nlinarith

def fitEnd (_good fit : Bool) (s : State) : State :=
  if fit then {s with pc:=49} else {writeNat {s with pc:=47} 303 0 with pc:=49}

theorem fit_execution (n B v amount : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hp:s.pc=46) (hv:s.natReg 290=v) (ha:s.natReg 311=amount)
    (hg:s.natReg 303=if good then 1 else 0) (hs:WordBound B s) (hB:57 ≤ B) :
    BoundedRuns program n x B s (if amount ≤ v then 1 else 3)
      (fitEnd good (decide (amount ≤ v)) s) ∧
    (fitEnd good (decide (amount ≤ v)) s).natReg 303=(if good && decide (amount ≤ v) then 1 else 0) ∧
    Stable pairWrites s (fitEnd good (decide (amount ≤ v)) s) ∧
    (fitEnd good (decide (amount ≤ v)) s).pc=49 := by
  by_cases hf:amount ≤ v
  · have hlt:¬v<amount:=by omega
    have ht:step program n x s=.running {s with pc:=49}:=by simp [step,program,hp,hv,ha,hlt]
    refine ⟨?_,?_,?_,?_⟩
    · simpa [fitEnd,hf] using control_run program n B 49 x s hs (by omega) ht
    · simpa [fitEnd,hf] using hg
    · simpa [fitEnd,hf] using Stable.withPC pairWrites s 49
    · simp [fitEnd,hf]
  · have hlt:v<amount:=by omega
    have ht:step program n x s=.running {s with pc:=47}:=by simp [step,program,hp,hv,ha,hlt]
    have he:=control_run program n B 47 x s hs (by omega) ht
    let f:=writeNat {s with pc:=47} 303 0
    have hb:WordBound B f:=writeNat_bound B {s with pc:=47} 303 0 he.final_bound (by change 47+1 ≤ B;omega) (by omega)
    have ht:step program n x {s with pc:=47}=.running f:=by simp [step,program,f]
    have hr:BoundedRuns program n x B {s with pc:=47} 1 f:=.next he.final_bound ht (.refl hb)
    have ht:step program n x f=.running {f with pc:=49}:=by simp [step,program,f,writeNat,next]
    have hj:=control_run program n B 49 x f hb (by omega) ht
    refine ⟨?_,?_,?_,?_⟩
    · simpa [fitEnd,hf,f] using (he.trans hr).trans hj
    · simp [fitEnd,hf,writeNat,next]
    · have he':fitEnd good (decide (amount ≤ v)) s={writeNat {s with pc:=47} 303 0 with pc:=49}:=by
        simp [fitEnd,hf]
      rw [he']
      refine ⟨⟨rfl,rfl,rfl,rfl,rfl,?_⟩,?_⟩
      · intro t ht';simp [writeNat,next,show t ≠ 303 by omega]
      · intro t ht'
        have hn:t ≠ 303:=by intro he';subst t;exact ht' (by decide)
        simp [writeNat,next,hn]
    · simp [fitEnd,hf]


/-- An actual ragged pair is sized, counted and tested using only Nat
instructions. The Boolean conjunct is a proved postcondition, not an oracle. -/
theorem source_pair (n v b i j B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc:Inner v b i j good s) (hb:0<b) (hbv:b ≤ v) (hj:j < sources v b)
    (hp:s.pc=24) (hs:WordBound B s) (hB:budget v ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 24+16*v ∧ u.pc=24 ∧
    Inner v b i (j+1) (good && pairFit v b i j) u ∧ Stable pairWrites s u := by
  have hjv:j ≤ v:=by have h:=sources_bound (v:=v) hb;omega
  have hcode:80 ≤ B:=by unfold budget at hB;nlinarith
  have ht:step program n x s=.running {s with pc:=25}:=by
    simp [step,program,hp,hc.index,hc.candidate.sources,hj]
  have hentry:=control_run program n B 25 x s hs (by omega) ht
  let e:State:={s with pc:=25}
  have hec:Inner v b i j good e:=hc.withPC
  have hstart:=block_runs sourceStart program 25 n B x e sourceStart_code rfl hentry.final_bound
    (by change 25+2 ≤ B;omega) (by simp [sourceStart,readable,Op.readable])
    (sourceStart_peak hec hbv hjv hB)
  let f:=applyBlock sourceStart e
  have hfc:Inner v b i j good f:=prep_inner hec (sourceStart_stable e)
  have hfpc:f.pc=27:=by rw [applyBlock_pc];rfl
  have hfval:f.natReg 307=sourceWidth v-j*b:=sourceStart_value hec
  have hmin:=min_execution n B 27 307 b (sourceWidth v-j*b) x f hfpc rfl rfl
    hfc.candidate.base.candidate hfval hfc.candidate.base.constants.zero hstart.final_bound (by omega)
  let m:=minEnd 27 307 b (sourceWidth v-j*b) f
  have hmf:Stable prepWrites f m:=(min_stable 27 307 b (sourceWidth v-j*b) f ⟨by omega,by omega⟩).mono
    (by intro t ht';simp only [Finset.mem_singleton] at ht';subst t;decide)
  have hmc:Inner v b i j good m:=prep_inner hfc hmf
  have hmval:m.natReg 307=sourceSize v b j:=hmin.2.2
  have hsize:=block_runs sizeStart program 29 n B x m sizeStart_code hmin.2.1 hmin.1.final_bound
    (by change 29+4 ≤ B;omega) (by simp [sizeStart,readable,Op.readable]) (sizeStart_peak hmc hmval hbv hB)
  let z:=applyBlock sizeStart m
  let N:=2*(targetSize v b i+sourceSize v b j)
  let K:=UniformWorkspacePlanner.exponent (targetSize v b i) (sourceSize v b j)
  have hzc:Inner v b i j good z:=prep_inner hmc (sizeStart_stable m)
  have hzpc:z.pc=33:=by rw [applyBlock_pc,hmin.2.1];rfl
  have hzval:=sizeStart_values hmc hmval
  have ha:targetSize v b i ≤ v:=(min_le_left _ _).trans hbv
  have he:sourceSize v b j ≤ v:=(min_le_left _ _).trans hbv
  have hN:2*N+80 ≤ B:=by dsimp [N];unfold budget at hB;nlinarith
  obtain ⟨l,hl,hlpc,hlc,hlf⟩:=doubling_loop n N 0 K B x z hzval.1
    (by dsimp [K,N,UniformWorkspacePlanner.exponent];omega) hzpc hsize.final_bound hN
  have hlInner:Inner v b i j good l:=prep_inner hzc (log_stable hlf)
  have hlVal:l.natReg 307=sourceSize v b j:=
    (hlf.2 307 (by omega) (by omega)).trans hzval.2
  have hgate:=block_runs gateBlock program 37 n B x l gateBlock_code hlpc hl.final_bound
    (by change 37+9 ≤ B;omega) (by simp [gateBlock,readable,Op.readable]) (gateBlock_peak hlInner hlVal hlc hbv hB)
  let g:=applyBlock gateBlock l
  have hgc:Inner v b i j good g:=prep_inner hlInner (gateBlock_stable l)
  have hgpc:g.pc=46:=by rw [applyBlock_pc,hlpc];rfl
  have hgv:g.natReg 311=pairAmount v b i j:=gateBlock_value hlInner hlVal hlc
  have hfit:=fit_execution n B v (pairAmount v b i j) good x g hgpc hgc.candidate.base.constants.width
    hgv hgc.candidate.good hgate.final_bound (by omega)
  let q:=fitEnd good (pairFit v b i j) g
  have hq303:q.natReg 303=if good && pairFit v b i j then 1 else 0:=hfit.2.1
  have hq304:q.natReg 304=j:=by
    unfold q pairFit fitEnd
    split_ifs <;> simpa [writeNat,next] using hgc.index
  have hqc:Inner v b i j (good && pairFit v b i j) q:=hgc.update hfit.2.2.1 hq303 hq304
  have hqpc:q.pc=49:=hfit.2.2.2
  have hpeak:peak advanceSource q ≤ B:=by
    simp [peak,advanceSource,Op.peak,hqc.index,hqc.candidate.base.constants.one]
    unfold budget at hB;nlinarith
  have hadv:=block_runs advanceSource program 49 n B x q advanceSource_code hqpc hfit.1.final_bound
    (by change 49+1 ≤ B;omega) (by simp [advanceSource,readable,Op.readable]) hpeak
  let u:=applyBlock advanceSource q
  have hup:u.pc=50:=by rw [applyBlock_pc,hqpc];rfl
  have hu303:u.natReg 303=if good && pairFit v b i j then 1 else 0:=by
    simpa [u,applyBlock,advanceSource,Op.apply,writeNat,next] using hq303
  have hu304:u.natReg 304=j+1:=by
    simp [u,applyBlock,advanceSource,Op.apply,writeNat,next,hqc.index,hqc.candidate.base.constants.one]
  have hui:Inner v b i (j+1) (good && pairFit v b i j) u:=hqc.update (advanceSource_stable q) hu303 hu304
  have ht:step program n x u=.running {u with pc:=24}:=by simp [step,program,hup]
  have hback:=control_run program n B 24 x u hadv.final_bound (by omega) ht
  have hr:=(((((((hentry.trans hstart).trans hmin.1).trans hsize).trans hl).trans hgate).trans hfit.1).trans hadv).trans hback
  refine ⟨{u with pc:=24},_,hr,?_,rfl,hui.withPC,?_⟩
  · have hk:K ≤ 4*v:=by
      have hk:=clog_bound N
      dsimp [N,K,UniformWorkspacePlanner.exponent] at hk ⊢
      omega
    simp only [sourceStart,sizeStart,gateBlock,advanceSource,List.length_cons,List.length_nil]
    split_ifs <;> omega
  · exact (Stable.withPC pairWrites s 25).trans
      (((sourceStart_stable e).mono prep_subset_pair).trans
        ((hmf.mono prep_subset_pair).trans
          (((sizeStart_stable m).mono prep_subset_pair).trans
            (((log_stable hlf).mono prep_subset_pair).trans
              (((gateBlock_stable l).mono prep_subset_pair).trans
                (hfit.2.2.1.trans ((advanceSource_stable q).trans (Stable.withPC pairWrites u 24))))))))


/-- All source chunks are scanned, including the last ragged chunk. -/
theorem source_loop (n v b i j fuel B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc : Inner v b i j good s) (hb : 0<b) (hbv : b≤v)
    (hj : j+fuel=sources v b) (hp : s.pc=24) (hs : WordBound B s)
    (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤(24+16*v)*fuel+1 ∧ u.pc=51 ∧
    Inner v b i (sources v b) (good && sourceFits v b i j fuel) u ∧ Stable pairWrites s u := by
  induction fuel generalizing j good s with
  | zero =>
    have he : j=sources v b := by omega
    have ht : step program n x s=.running {s with pc:=51} := by
      simp [step,program,hp,hc.index,hc.candidate.sources,he]
    refine ⟨{s with pc:=51},1,control_run program n B 51 x s hs (by unfold budget at hB;omega) ht,
      by omega,rfl,?_,Stable.withPC pairWrites s 51⟩
    simpa [sourceFits,he] using hc.withPC (pc:=51)
  | succ fuel ih =>
    obtain ⟨u,t,hu,ht,hup,huc,huf⟩ := source_pair n v b i j B good x s hc hb hbv
      (by omega) hp hs hB
    obtain ⟨z,w,hz,hw,hzp,hzc,hzf⟩ := ih (j+1) (good && pairFit v b i j) u huc
      (by omega) hup hu.final_bound
    refine ⟨z,t+w,hu.trans hz,by nlinarith,hzp,?_,huf.trans hzf⟩
    simpa only [sourceFits,Bool.and_assoc] using hzc

def targetStart : List Op := [.literal 304 0,.mul 305 302 297,.sub 306 299 305]
def advanceTarget : List Op := [.add 302 302 293]

theorem targetStart_code : BlockAt targetStart program 19 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl

theorem advanceTarget_code : BlockAt advanceTarget program 51 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl

theorem targetStart_stable (s : State) : Stable targetWrites s (applyBlock targetStart s) := by
  apply block_stable;intro o ho;simp [targetStart] at ho
  rcases ho with rfl|rfl|rfl <;> simp [allowed,Op.scratch,targetWrites]

theorem advanceTarget_stable (s : State) : Stable targetWrites s (applyBlock advanceTarget s) := by
  apply block_stable;intro o ho;simp [advanceTarget] at ho
  subst o;simp [allowed,Op.scratch,targetWrites]

theorem pair_subset_target : pairWrites⊆targetWrites := by decide

theorem Candidate.update {v b i i' : ℕ} {good good' : Bool} {s u : State}
    (h : Candidate v b i good s) (hf : Stable targetWrites s u)
    (hg : u.natReg 303=if good' then 1 else 0) (hi : u.natReg 302=i') : Candidate v b i' good' u := by
  refine ⟨h.base.transport ?_,?_,?_,hi,hg⟩
  · intro t ht;apply hf.2
    simp only [targetWrites,Finset.mem_insert,Finset.mem_singleton];omega
  · rw [hf.2 300 (by decide)];exact h.targets
  · rw [hf.2 301 (by decide)];exact h.sources

theorem targetStart_peak {v b i : ℕ} {good : Bool} {s : State} (hc : Candidate v b i good s)
    (hb : b≤v) (hi : i≤v) {B : ℕ} (hB : budget v≤B) : peak targetStart s≤B := by
  simp [peak,targetStart,Op.peak,Op.apply,writeNat,next,hc.index,hc.base.candidate,hc.base.target]
  have hv : targetWidth v≤v := Nat.sub_le _ _
  unfold budget at hB
  repeat' apply And.intro
  all_goals nlinarith

/-- One target chunk is paired with every source chunk. -/
theorem target_iteration (n v b i B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc : Candidate v b i good s) (hb : 0<b) (hbv : b≤v) (hi : i<targets v b)
    (hp : s.pc=18) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤9+(24+16*v)*sources v b ∧ u.pc=18 ∧
    Candidate v b (i+1) (good && sourceFits v b i 0 (sources v b)) u ∧ Stable targetWrites s u := by
  have hi' : i≤v := by have h:=targets_bound (v:=v) hb;omega
  have ht : step program n x s=.running {s with pc:=19} := by
    simp [step,program,hp,hc.index,hc.targets,hi]
  have hentry:=control_run program n B 19 x s hs (by unfold budget at hB;omega) ht
  let e : State := {s with pc:=19}
  have hec : Candidate v b i good e := hc.withPC
  have hstart:=block_runs targetStart program 19 n B x e targetStart_code rfl hentry.final_bound
    (by change 19+3≤B;unfold budget at hB;omega) (by simp [targetStart,readable,Op.readable])
    (targetStart_peak hec hbv hi' hB)
  let f:=applyBlock targetStart e
  have hff:=targetStart_stable e
  have hfc : Candidate v b i good f := hec.update hff
    (by simpa [f,applyBlock,targetStart,Op.apply,writeNat,next] using hec.good)
    (by simpa [f,applyBlock,targetStart,Op.apply,writeNat,next] using hec.index)
  have hfpc : f.pc=22 := by rw [applyBlock_pc];rfl
  have hfval : f.natReg 306=targetWidth v-i*b := by
    simp [f,applyBlock,targetStart,Op.apply,writeNat,next,hec.index,hec.base.candidate,hec.base.target]
  have hmin:=min_execution n B 22 306 b (targetWidth v-i*b) x f hfpc rfl rfl
    hfc.base.candidate hfval hfc.base.constants.zero hstart.final_bound (by unfold budget at hB;omega)
  let m:=minEnd 22 306 b (targetWidth v-i*b) f
  have hmSingle := min_stable 22 306 b (targetWidth v-i*b) f ⟨by omega,by omega⟩
  have hmf : Stable targetWrites f m := hmSingle.mono
    (by intro t ht';simp only [Finset.mem_singleton] at ht';subst t;decide)
  have hmc : Candidate v b i good m := hfc.update hmf
    (by rw [hmSingle.2 303 (by decide)];exact hfc.good)
    (by rw [hmSingle.2 302 (by decide)];exact hfc.index)
  have hinner : Inner v b i 0 good m := ⟨hmc,by
    rw [hmSingle.2 304 (by decide)];simp [f,applyBlock,targetStart,Op.apply,writeNat,next],hmin.2.2⟩
  obtain ⟨q,w,hq,hw,hqp,hqc,hqf⟩:=source_loop n v b i 0 (sources v b) B good x m hinner hb hbv
    (by omega) hmin.2.1 hmin.1.final_bound hB
  have hpeak : peak advanceTarget q≤B := by
    simp [peak,advanceTarget,Op.peak,hqc.candidate.index,hqc.candidate.base.constants.one]
    unfold budget at hB;nlinarith
  have hadv:=block_runs advanceTarget program 51 n B x q advanceTarget_code hqp hq.final_bound
    (by change 51+1≤B;unfold budget at hB;omega) (by simp [advanceTarget,readable,Op.readable]) hpeak
  let u:=applyBlock advanceTarget q
  have hup : u.pc=52 := by rw [applyBlock_pc,hqp];rfl
  have hui : Candidate v b (i+1) (good && sourceFits v b i 0 (sources v b)) u :=
    hqc.candidate.update (advanceTarget_stable q)
      (by simpa [u,applyBlock,advanceTarget,Op.apply,writeNat,next] using hqc.candidate.good)
      (by simp [u,applyBlock,advanceTarget,Op.apply,writeNat,next,hqc.candidate.index,hqc.candidate.base.constants.one])
  have hback:=control_run program n B 18 x u hadv.final_bound (by unfold budget at hB;omega)
    (by simp [step,program,hup])
  refine ⟨{u with pc:=18},_,((((hentry.trans hstart).trans hmin.1).trans hq).trans hadv).trans hback,
    ?_,rfl,hui.withPC,?_⟩
  · simp only [targetStart,advanceTarget,List.length_cons,List.length_nil]
    split_ifs <;> omega
  · exact (Stable.withPC targetWrites s 19).trans (hff.trans (hmf.trans
      ((hqf.mono pair_subset_target).trans ((advanceTarget_stable q).trans (Stable.withPC targetWrites u 18)))))

/-- The actual target scan computes the same Boolean as planner.allFits. -/
theorem target_loop (n v b i fuel B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc : Candidate v b i good s) (hb : 0<b) (hbv : b≤v) (hi : i+fuel=targets v b)
    (hp : s.pc=18) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤(9+(24+16*v)*sources v b)*fuel+1 ∧ u.pc=53 ∧
    Candidate v b (targets v b) (good && targetFits v b i fuel) u ∧ Stable targetWrites s u := by
  induction fuel generalizing i good s with
  | zero =>
    have he : i=targets v b := by omega
    have ht : step program n x s=.running {s with pc:=53} := by
      simp [step,program,hp,hc.index,hc.targets,he]
    refine ⟨{s with pc:=53},1,control_run program n B 53 x s hs (by unfold budget at hB;omega) ht,
      by omega,rfl,?_,Stable.withPC targetWrites s 53⟩
    simpa [targetFits,he] using hc.withPC (pc:=53)
  | succ fuel ih =>
    obtain ⟨u,t,hu,ht,hup,huc,huf⟩:=target_iteration n v b i B good x s hc hb hbv (by omega) hp hs hB
    obtain ⟨z,w,hz,hw,hzp,hzc,hzf⟩:=ih (i+1) (good && sourceFits v b i 0 (sources v b)) u huc
      (by omega) hup hu.final_bound
    refine ⟨z,t+w,hu.trans hz,by nlinarith,hzp,?_,huf.trans hzf⟩
    simpa only [targetFits,Bool.and_assoc] using hzc


def candidateWrites : Finset ℕ := Finset.Icc 300 312

theorem target_subset_candidate : targetWrites⊆candidateWrites := by decide

theorem candidate_base {v b : ℕ} {s u : State} (h : Base v b s)
    (hf : Stable candidateWrites s u) : Base v b u := by
  apply h.transport;intro t ht;apply hf.2
  simp only [candidateWrites,Finset.mem_Icc];omega

theorem division_stable (s : State) (d l r : ℕ) (hd : 291≤d ∧ d≤312) :
    Stable {d} s (writeNat s d (s.natReg l/s.natReg r)) := by
  refine ⟨division_frame s d l r hd,?_⟩
  intro t ht;simp only [Finset.mem_singleton] at ht
  simp [writeNat,next,ht]

def targetCeil : List Op := [.add 300 299 297,.sub 300 300 293]
def sourceCeil : List Op := [.add 301 298 297,.sub 301 301 293]
def resetCandidate : List Op := [.literal 302 0,.literal 303 1]

theorem targetCeil_code : BlockAt targetCeil program 10 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl

theorem sourceCeil_code : BlockAt sourceCeil program 13 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl

theorem resetCandidate_code : BlockAt resetCandidate program 16 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl

theorem targetCeil_stable (s : State) : Stable candidateWrites s (applyBlock targetCeil s) := by
  apply block_stable;intro o ho;simp [targetCeil] at ho
  rcases ho with rfl|rfl <;> simp [allowed,Op.scratch,candidateWrites]

theorem sourceCeil_stable (s : State) : Stable candidateWrites s (applyBlock sourceCeil s) := by
  apply block_stable;intro o ho;simp [sourceCeil] at ho
  rcases ho with rfl|rfl <;> simp [allowed,Op.scratch,candidateWrites]

theorem resetCandidate_stable (s : State) : Stable candidateWrites s (applyBlock resetCandidate s) := by
  apply block_stable;intro o ho;simp [resetCandidate] at ho
  rcases ho with rfl|rfl <;> simp [allowed,Op.scratch,candidateWrites]

/-- Ceiling chunk counts and the initial fitting flag are computed by eight
literal instructions, including both guarded divisions. -/
theorem candidate_setup (n v b B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc : Base v b s) (hb : 0<b) (hbv : b≤v) (hp : s.pc=10)
    (hs : WordBound B s) (hB : budget v≤B) : ∃u,
    BoundedRuns program n x B s 8 u ∧ u.pc=18 ∧ Candidate v b 0 true u ∧ Stable candidateWrites s u := by
  have ht : targetWidth v≤v := Nat.sub_le _ _
  have he : sourceWidth v≤v := Nat.div_le_self _ _
  have hpeak : peak targetCeil s≤B := by
    simp [peak,targetCeil,Op.peak,Op.apply,writeNat,next,hc.target,hc.candidate,hc.constants.one]
    unfold budget at hB;nlinarith
  have hfirst:=block_runs targetCeil program 10 n B x s targetCeil_code hp hs
    (by change 10+2≤B;unfold budget at hB;omega) (by simp [targetCeil,readable,Op.readable]) hpeak
  let a:=applyBlock targetCeil s
  have haf:=targetCeil_stable s
  have hac:=candidate_base hc haf
  have hap : a.pc=12 := by rw [applyBlock_pc,hp];rfl
  have hav : a.natReg 300=targetWidth v+b-1 := by
    simp [a,applyBlock,targetCeil,Op.apply,writeNat,next,hc.target,hc.candidate,hc.constants.one]
  have hdiv1:=division_run program n B 300 300 297 x a (by simp [program,hap])
    (by rw [hac.candidate];omega) hfirst.final_bound (by rw [hap];unfold budget at hB;omega)
  let c:=writeNat a 300 (a.natReg 300/a.natReg 297)
  have hcf : Stable candidateWrites a c := (division_stable a 300 300 297 ⟨by omega,by omega⟩).mono
    (by intro t ht';simp only [Finset.mem_singleton] at ht';subst t;decide)
  have hcc:=candidate_base hac hcf
  have hcp : c.pc=13 := by simp [c,writeNat,next,hap]
  have hcv : c.natReg 300=targets v b := by
    change a.natReg 300/a.natReg 297=targets v b
    rw [hav,show a.natReg 297=b from hac.candidate];rfl
  have hpeak2 : peak sourceCeil c≤B := by
    simp [peak,sourceCeil,Op.peak,Op.apply,writeNat,next,hcc.source,hcc.candidate,hcc.constants.one]
    unfold budget at hB;nlinarith
  have hsecond:=block_runs sourceCeil program 13 n B x c sourceCeil_code hcp hdiv1.final_bound
    (by change 13+2≤B;unfold budget at hB;omega) (by simp [sourceCeil,readable,Op.readable]) hpeak2
  let d:=applyBlock sourceCeil c
  have hdf:=sourceCeil_stable c
  have hdc:=candidate_base hcc hdf
  have hdp : d.pc=15 := by rw [applyBlock_pc,hcp];rfl
  have hdv : d.natReg 301=sourceWidth v+b-1 := by
    simp [d,applyBlock,sourceCeil,Op.apply,writeNat,next,hcc.source,hcc.candidate,hcc.constants.one]
  have hdct : d.natReg 300=targets v b := by
    simpa [d,applyBlock,sourceCeil,Op.apply,writeNat,next] using hcv
  have hdiv2:=division_run program n B 301 301 297 x d (by simp [program,hdp])
    (by rw [hdc.candidate];omega) hsecond.final_bound (by rw [hdp];unfold budget at hB;omega)
  let e:=writeNat d 301 (d.natReg 301/d.natReg 297)
  have hef : Stable candidateWrites d e := (division_stable d 301 301 297 ⟨by omega,by omega⟩).mono
    (by intro t ht';simp only [Finset.mem_singleton] at ht';subst t;decide)
  have hec:=candidate_base hdc hef
  have hep : e.pc=16 := by simp [e,writeNat,next,hdp]
  have hect : e.natReg 300=targets v b := by simpa [e,writeNat,next] using hdct
  have hecs : e.natReg 301=sources v b := by
    change d.natReg 301/d.natReg 297=sources v b
    rw [hdv,show d.natReg 297=b from hdc.candidate];rfl
  have hreset:=block_runs resetCandidate program 16 n B x e resetCandidate_code hep hdiv2.final_bound
    (by change 16+2≤B;unfold budget at hB;omega) (by simp [resetCandidate,readable,Op.readable])
    (by simp [peak,resetCandidate,Op.peak];unfold budget at hB;omega)
  let u:=applyBlock resetCandidate e
  have huf:=resetCandidate_stable e
  refine ⟨u,?_,?_,?_,haf.trans (hcf.trans (hdf.trans (hef.trans huf)))⟩
  · exact (((hfirst.trans hdiv1).trans hsecond).trans hdiv2).trans hreset
  · rw [applyBlock_pc,hep];rfl
  · refine ⟨candidate_base hec huf,?_,?_,?_,?_⟩
    · simpa [u,applyBlock,resetCandidate,Op.apply,writeNat,next] using hect
    · simpa [u,applyBlock,resetCandidate,Op.apply,writeNat,next] using hecs
    · simp [u,applyBlock,resetCandidate,Op.apply,writeNat,next]
    · simp [u,applyBlock,resetCandidate,Op.apply,writeNat,next]


def commitBest : List Op := [.add 291 297 292]
def advanceCandidate : List Op := [.add 297 297 293]

theorem commitBest_code : BlockAt commitBest program 54 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl

theorem advanceCandidate_code : BlockAt advanceCandidate program 55 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl

theorem commitBest_stable (s : State) : Stable {291} s (applyBlock commitBest s) := by
  apply block_stable;intro o ho;simp [commitBest] at ho;subst o;simp [allowed,Op.scratch]

theorem advanceCandidate_stable (s : State) : Stable {297} s (applyBlock advanceCandidate s) := by
  apply block_stable;intro o ho;simp [advanceCandidate] at ho;subst o;simp [allowed,Op.scratch]

def commitEnd (good : Bool) (s : State) : State :=
  if good then applyBlock commitBest {s with pc:=54} else {s with pc:=55}

theorem commit_execution (n v b i B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc : Candidate v b i good s) (hp : s.pc=53) (hs : WordBound B s) (hB : budget v≤B) :
    BoundedRuns program n x B s (if good then 2 else 1) (commitEnd good s) ∧
    (commitEnd good s).pc=55 ∧ Base v b (commitEnd good s) ∧
    (commitEnd good s).natReg 291=(if good then b else s.natReg 291) ∧ Stable {291} s (commitEnd good s) := by
  cases good with
  | false =>
    have ht : step program n x s=.running {s with pc:=55} := by
      simp [step,program,hp,hc.good,hc.base.constants.one]
    exact ⟨control_run program n B 55 x s hs (by unfold budget at hB;omega) ht,rfl,
      hc.base.withPC,rfl,Stable.withPC {291} s 55⟩
  | true =>
    have ht : step program n x s=.running {s with pc:=54} := by
      simp [step,program,hp,hc.good,hc.base.constants.one]
    have hentry:=control_run program n B 54 x s hs (by unfold budget at hB;omega) ht
    let e : State := {s with pc:=54}
    have hcopy:=block_runs commitBest program 54 n B x e commitBest_code rfl hentry.final_bound
      (by change 54+1≤B;unfold budget at hB;omega) (by simp [commitBest,readable,Op.readable])
      (by simp [peak,commitBest,Op.peak,e,hc.base.candidate,hc.base.constants.zero];
          simpa [e,hc.base.candidate] using hs.2.1 297)
    have hf : Stable {291} s (applyBlock commitBest e) :=
      (Stable.withPC {291} s 54).trans (commitBest_stable e)
    refine ⟨hentry.trans hcopy,by change (applyBlock commitBest e).pc=55;rw [applyBlock_pc];rfl,?_,?_,hf⟩
    · apply hc.base.transport;intro t ht';apply hf.2
      simp only [Finset.mem_singleton];omega
    · simp [commitEnd,applyBlock,commitBest,Op.apply,writeNat,next,hc.base.candidate,hc.base.constants.zero]

/-- A fitting candidate updates the retained maximum; then the next width is
formed by a charged increment. -/
theorem finish_candidate (n v b i B : ℕ) (good : Bool) (x : Fin n → ℂ) (s : State)
    (hc : Candidate v b i good s) (hbv : b≤v) (hp : s.pc=53) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤4 ∧ u.pc=9 ∧ Base v (b+1) u ∧
    u.natReg 291=(if good then b else s.natReg 291) ∧ Frame s u := by
  have hcommit:=commit_execution n v b i B good x s hc hp hs hB
  let q:=commitEnd good s
  have hqc : Base v b q := hcommit.2.2.1
  have hpeak : peak advanceCandidate q≤B := by
    simp [peak,advanceCandidate,Op.peak,hqc.candidate,hqc.constants.one]
    unfold budget at hB;nlinarith
  have hadv:=block_runs advanceCandidate program 55 n B x q advanceCandidate_code hcommit.2.1 hcommit.1.final_bound
    (by change 55+1≤B;unfold budget at hB;omega) (by simp [advanceCandidate,readable,Op.readable]) hpeak
  let u:=applyBlock advanceCandidate q
  have huf:=advanceCandidate_stable q
  have hup : u.pc=56 := by rw [applyBlock_pc,hcommit.2.1];rfl
  have huc : Base v (b+1) u := by
    refine ⟨hqc.constants.transport ?_,?_,?_,?_⟩
    · intro t ht;apply huf.2;simp only [Finset.mem_singleton];omega
    · simp [u,applyBlock,advanceCandidate,Op.apply,writeNat,next,hqc.candidate,hqc.constants.one]
    · rw [huf.2 298 (by decide)];exact hqc.source
    · rw [huf.2 299 (by decide)];exact hqc.target
  have hback:=control_run program n B 9 x u hadv.final_bound (by unfold budget at hB;omega)
    (by simp [step,program,hup])
  refine ⟨{u with pc:=9},_,(hcommit.1.trans hadv).trans hback,?_,rfl,huc.withPC,?_,
    hcommit.2.2.2.2.1.trans (huf.1.trans (Frame.withPC u 9))⟩
  · simp only [advanceCandidate,List.length_cons,List.length_nil];cases good <;> simp
  · change u.natReg 291=_
    rw [huf.2 291 (by decide)];exact hcommit.2.2.2.1

/-- One whole candidate evaluation; the computed flag is exactly allFits. -/
theorem candidate_iteration (n v b B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc : Base v b s) (hb : 0<b) (hbv : b≤v) (hp : s.pc=9)
    (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤14+(9+(24+16*v)*sources v b)*targets v b ∧
    u.pc=9 ∧ Base v (b+1) u ∧
    u.natReg 291=(if UniformWorkspacePlanner.allFits v b then b else s.natReg 291) ∧ Frame s u := by
  have ht : step program n x s=.running {s with pc:=10} := by
    simp [step,program,hp,hc.constants.width,hc.candidate,show ¬v<b by omega]
  have hentry:=control_run program n B 10 x s hs (by unfold budget at hB;omega) ht
  let e : State := {s with pc:=10}
  obtain ⟨a,ha,hap,hac,haf⟩:=candidate_setup n v b B x e hc.withPC hb hbv rfl hentry.final_bound hB
  obtain ⟨q,w,hq,hw,hqp,hqc,hqf⟩:=target_loop n v b 0 (targets v b) B true x a hac hb hbv
    (by omega) hap ha.final_bound hB
  have hqc' : Candidate v b (targets v b) (UniformWorkspacePlanner.allFits v b) q := by
    simpa [targetFits_allFits] using hqc
  obtain ⟨u,t,hu,htu,hup,huc,hub,huf⟩:=finish_candidate n v b (targets v b) B
    (UniformWorkspacePlanner.allFits v b) x q hqc' hbv hqp hq.final_bound hB
  refine ⟨u,1+8+w+t,((hentry.trans ha).trans hq).trans hu,by omega,hup,huc,?_,
    (Frame.withPC s 10).trans (haf.1.trans (hqf.1.trans huf))⟩
  have hbest : q.natReg 291=s.natReg 291 := (hqf.2 291 (by decide)).trans (haf.2 291 (by decide))
  simpa [hbest] using hub


theorem candidate_time_bound (v b : ℕ) (hb : 0<b) :
    14+(9+(24+16*v)*sources v b)*targets v b≤64*(v+1)^3 := by
  have ht:=targets_bound (v:=v) hb
  have hs:=sources_bound (v:=v) hb
  calc
    _≤14+(9+(24+16*v)*v)*v := by gcongr
    _≤64*(v+1)^3 := by ring_nf;omega

/-- The complete outer loop derives the largest fitting candidate from every
computed pair test. No allFits certificate is supplied at entry. -/
theorem search_loop (n v b fuel B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc : Base v b s) (hb : 0<b) (hstop : b+fuel=v+1)
    (hseen : Seen v b (s.natReg 291)) (hp : s.pc=9) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤64*(v+1)^3*fuel+1 ∧ u.pc=57 ∧
    u.natReg 291=UniformWorkspacePlanner.selected v ∧ Frame s u := by
  induction fuel generalizing b s with
  | zero =>
    have he : b=v+1 := by omega
    have ht : step program n x s=.running {s with pc:=57} := by
      simp [step,program,hp,hc.constants.width,hc.candidate,he]
    refine ⟨{s with pc:=57},1,control_run program n B 57 x s hs (by unfold budget at hB;omega) ht,
      by omega,rfl,?_,Frame.withPC s 57⟩
    exact selected_of_seen (by simpa [he] using hseen)
  | succ fuel ih =>
    obtain ⟨u,t,hu,ht,hup,huc,hub,huf⟩:=candidate_iteration n v b B x s hc hb (by omega) hp hs hB
    have hnext : Seen v (b+1) (u.natReg 291) := by rw [hub];exact seen_next hseen hb
    obtain ⟨z,w,hz,hw,hzp,hzb,hzf⟩:=ih (b+1) u huc (by omega) (by omega) hnext hup hu.final_bound
    refine ⟨z,t+w,hu.trans hz,?_,hzp,hzb,huf.trans hzf⟩
    have hc' := candidate_time_bound v b hb
    nlinarith

def bootOps : List Op := [.literal 292 0,.literal 293 1,.literal 294 2,.literal 295 3,
  .literal 296 6,.literal 291 0,.add 297 293 292]
def targetWidthOp : List Op := [.sub 299 290 298]

theorem bootOps_code : BlockAt bootOps program 0 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl

theorem targetWidthOp_code : BlockAt targetWidthOp program 8 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl

theorem bootOps_frame (s : State) : Frame s (applyBlock bootOps s) := by
  apply block_frame;intro o ho;simp [bootOps] at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [allowed]

theorem targetWidthOp_frame (s : State) : Frame s (applyBlock targetWidthOp s) := by
  apply block_frame;intro o ho;simp [targetWidthOp] at ho;subst o;simp [allowed]

/-- Nine actual startup instructions initialize the constants and split v. -/
theorem startup (n v B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hv : s.natReg 290=v) (hs : WordBound B s) (hB : budget v≤B) : ∃u,
    BoundedRuns program n x B s 9 u ∧ u.pc=9 ∧ Base v 1 u ∧ u.natReg 291=0 ∧ Frame s u := by
  have hboot:=block_runs bootOps program 0 n B x s bootOps_code hp hs
    (by change 0+7≤B;unfold budget at hB;omega) (by simp [bootOps,readable,Op.readable])
    (by simp [peak,bootOps,Op.peak,Op.apply,writeNat,next];unfold budget at hB;omega)
  let a:=applyBlock bootOps s
  have hap : a.pc=7 := by rw [applyBlock_pc,hp];rfl
  have hac : Constants v a := by
    constructor
    all_goals simp [a,applyBlock,bootOps,Op.apply,writeNat,next,hv]
  have hab : a.natReg 297=1 := by simp [a,applyBlock,bootOps,Op.apply,writeNat,next]
  have haz : a.natReg 291=0 := by simp [a,applyBlock,bootOps,Op.apply,writeNat,next]
  have hdiv:=division_run program n B 298 290 294 x a (by simp [program,hap])
    (by rw [hac.two];decide) hboot.final_bound (by rw [hap];unfold budget at hB;omega)
  let c:=writeNat a 298 (a.natReg 290/a.natReg 294)
  have hcp : c.pc=8 := by simp [c,writeNat,next,hap]
  have hcc : Constants v c := by
    apply hac.transport;intro t ht;simp [c,writeNat,next,show t≠298 by omega]
  have hcs : c.natReg 298=sourceWidth v := by
    change a.natReg 290/a.natReg 294=sourceWidth v
    rw [hac.width,hac.two];rfl
  have hcb : c.natReg 297=1 := by simpa [c,writeNat,next] using hab
  have hcz : c.natReg 291=0 := by simpa [c,writeNat,next] using haz
  have htarg:=block_runs targetWidthOp program 8 n B x c targetWidthOp_code hcp hdiv.final_bound
    (by change 8+1≤B;unfold budget at hB;omega) (by simp [targetWidthOp,readable,Op.readable])
    (by
      have hvB : v≤B := by simpa [hv] using hs.2.1 290
      simp [peak,targetWidthOp,Op.peak,hcc.width,hcs]
      omega)
  let u:=applyBlock targetWidthOp c
  refine ⟨u,(hboot.trans hdiv).trans htarg,?_,?_,?_,
    (bootOps_frame s).trans ((division_frame a 298 290 294 ⟨by omega,by omega⟩).trans (targetWidthOp_frame c))⟩
  · rw [applyBlock_pc,hcp];rfl
  · refine ⟨hcc.transport ?_,?_,?_,?_⟩
    · intro t ht;simp [u,applyBlock,targetWidthOp,Op.apply,writeNat,next,show t≠299 by omega]
    · simpa [u,applyBlock,targetWidthOp,Op.apply,writeNat,next] using hcb
    · simpa [u,applyBlock,targetWidthOp,Op.apply,writeNat,next] using hcs
    · simp [u,applyBlock,targetWidthOp,Op.apply,writeNat,next,hcc.width,hcs,targetWidth,sourceWidth]
  · simpa [u,applyBlock,targetWidthOp,Op.apply,writeNat,next] using hcz

/-- An actual fixed RAM search computes the paper's selected chunk width.
All comparisons, ragged chunk arithmetic, divisions, doublings and the halt
are charged. The budget is a same-B integer bound, not a semantic premise. -/
theorem execution (n v B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hv : s.natReg 290=v) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤64*(v+1)^3*v+11 ∧
    u.pc=57 ∧ u.natReg 291=UniformWorkspacePlanner.selected v ∧ Frame s u := by
  obtain ⟨a,ha,hap,hac,haz,haf⟩:=startup n v B x s hp hv hs hB
  have hseen : Seen v 1 (a.natReg 291) := by rw [haz];exact seen_zero v
  obtain ⟨u,t,hu,ht,hup,hub,huf⟩:=search_loop n v 1 v B x a hac (by omega) (by omega) hseen hap ha.final_bound hB
  have hh : BoundedExecution program n x B u 1 u := .halt hu.final_bound (by simp [step,program,hup])
  exact ⟨u,9+t+1,(ha.trans hu).executes hh,by omega,hup,hub,haf.trans huf⟩

theorem execution_polynomial (n v B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hv : s.natReg 290=v) (hs : WordBound B s) (hB : budget v≤B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤256*(v+1)^4 ∧
    u.pc=57 ∧ u.natReg 291=UniformWorkspacePlanner.selected v ∧ Frame s u := by
  obtain ⟨u,t,hu,ht,hup,hub,huf⟩:=execution n v B x s hp hv hs hB
  refine ⟨u,t,hu,ht.trans ?_,hup,hub,huf⟩
  ring_nf;omega


/-- All saved global header registers survive the actual search. -/
theorem Frame.saved_headers {s u : State} (h : Frame s u) (j : Fin 7) :
    u.natReg (100+j.val)=s.natReg (100+j.val) :=
  h.2.2.2.2.2 _ (Or.inl (by have hj:=j.isLt;omega))

theorem Frame.width_header {s u : State} (h : Frame s u) : u.natReg 290=s.natReg 290 :=
  h.2.2.2.2.2 _ (Or.inl (by omega))

theorem budget_polynomial (v : ℕ) : budget v≤2048*(v+1)^2 := by unfold budget;ring_nf;omega

end
end ExactFourierCircuits.UniformWorkspaceSearchMachine
