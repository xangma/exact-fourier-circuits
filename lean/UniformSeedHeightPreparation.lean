import UniformSeedRankCrossPreparation
import UniformCrossHeightPreparationMachine
import UniformWorkspacePlanner

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedHeightPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformAllAxisSeedPreparation (axisCount radix Retained)
open OAI.ExactFourier

/-- Ordinary height-region arguments; every other argument is inherited from
    the ordinary chunk/layout interface. No exponent or produced bank is readied. -/
structure Config where
  a : ℕ
  e : ℕ
  i0 : ℕ
  j0 : ℕ
  split : ℕ
  S : ℕ
  A : ℕ
  d : ℕ
  C : ℕ
  conv : ℕ
  tape : ℕ
  depth : ℕ
  order : ℕ
  directory : ℕ
  negative : ℕ
  constants : ℕ
  rows : ℕ
  colors : ℕ
  palette : ℕ
  heightDirectory : ℕ
  enabled : Bool

def Config.exponent (c : Config) := UniformWorkspacePlanner.exponent c.a c.e
def Config.seed (c : Config) : UniformSeedRankCrossPreparation.Config :=
  ⟨c.exponent,c.a,c.e,c.i0,c.j0,c.split,c.S,c.A,c.d,c.C,c.conv,c.tape,c.depth,
    c.order,c.directory,c.negative,c.constants⟩
def Config.height (c : Config) : UniformCrossHeightPreparationMachine.Parameters :=
  ⟨c.exponent,c.a,c.e,c.tape,c.order,c.directory,c.rows,c.colors,c.palette,
    c.heightDirectory,c.C,c.constants,c.enabled⟩
def Config.register (c : Config) : ℕ→ℕ
  | 1220=>c.rows | 1221=>c.colors | 1222=>c.palette | 1223=>c.heightDirectory
  | 1224=>if c.enabled then 1 else 0
  | q=>c.seed.register q

def sizingBoot : List Op := [.literal 1225 1,.literal 1226 2,.literal 1121 0,
  .literal 1229 1,.add 1227 1122 1123,.mul 1227 1227 1226]
def sizingStep : List Op := [.mul 1229 1229 1226,.add 1121 1121 1225]
def sizing : Program := sizingBoot.map Op.code ++ [.branchLT 1229 1227 7 10] ++
  sizingStep.map Op.code ++ [.jump 6,.halt]
def heightSetup : List Op := [.add 1050 525 670,.add 1051 484 670,.add 1052 485 670,
  .add 1053 564 670,.add 1054 950 670,.add 1055 951 670,
  .add 1056 1220 670,.add 1057 1221 670,.add 1058 1222 670,.add 1059 1223 670,
  .add 1060 529 670,.add 1061 1224 670,.add 1062 953 670]
def beforeSeed : Program := sizing.map (relocate 0 11)
def beforeHeight : Program := beforeSeed ++ UniformSeedRankCrossPreparation.program.map (relocate 11 846) ++ heightSetup.map Op.code
def program : Program := beforeHeight ++ UniformCrossHeightPreparationMachine.program.map (relocate 859 1045) ++ [.halt]

lemma sizingBoot_length : sizingBoot.length=6 := rfl
lemma sizingStep_length : sizingStep.length=2 := rfl
lemma sizing_length : sizing.length=11 := rfl
lemma heightSetup_length : heightSetup.length=13 := rfl
lemma beforeSeed_length : beforeSeed.length=11 := rfl
lemma beforeHeight_length : beforeHeight.length=859 := by
 simp [beforeHeight,beforeSeed_length,UniformSeedRankCrossPreparation.program_length,heightSetup_length]
lemma program_length : program.length=1046 := by
 simp [program,beforeHeight_length,UniformCrossHeightPreparationMachine.program_length]
lemma seed_code : CodeAt UniformSeedRankCrossPreparation.program program 11 846 := by
 let after:=heightSetup.map Op.code ++ UniformCrossHeightPreparationMachine.program.map (relocate 859 1045) ++ [.halt]
 have he:program=beforeSeed ++ UniformSeedRankCrossPreparation.program.map (relocate 11 846) ++ after:=by
  simp [program,beforeHeight,after,List.append_assoc]
 rw [he]
 exact UniformRankCrossPreparationMachine.segment_code beforeSeed after UniformSeedRankCrossPreparation.program 11 846 beforeSeed_length
lemma height_code : CodeAt UniformCrossHeightPreparationMachine.program program 859 1045 :=
 UniformRankCrossPreparationMachine.segment_code beforeHeight [.halt] UniformCrossHeightPreparationMachine.program 859 1045 beforeHeight_length
lemma sizingBoot_code : BlockAt sizingBoot program 0 := by
 intro i hi;change i<6 at hi;interval_cases i <;> rfl
lemma sizingStep_code : BlockAt sizingStep program 7 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma sizing_branch : program[6]?=some (.branchLT 1229 1227 7 10) := rfl
lemma sizing_jump : program[9]?=some (.jump 6) := rfl
lemma sizing_exit : program[10]?=some (.jump 11) := rfl
lemma halt_at : program[1045]?=some .halt := by
 rw [program,List.getElem?_append_right (by simp [beforeHeight_length,UniformCrossHeightPreparationMachine.program_length])]
 simp [beforeHeight_length,UniformCrossHeightPreparationMachine.program_length]

/-- The Nat destination footprint includes literal/load/length instructions;
    scalar/control/store instructions retain every Nat register. -/
def natCeiling : Instruction→ℕ
  | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>d+1
  | _=>0
lemma natCeiling_relocate (base ret : ℕ) (i : Instruction) : natCeiling (relocate base ret i)=natCeiling i := by
 cases i <;> rfl
def below (p : Program) := p.all (fun ins=>decide (natCeiling ins≤1220))
lemma below_append (a b : Program) : below (a++b)= (below a && below b) := List.all_append
lemma below_relocate (p : Program) (base ret : ℕ) : below (p.map (relocate base ret))=below p := by
 simp [below,List.all_map,Function.comp_def,natCeiling_relocate]
lemma seedHead_below : below UniformSeedRankCrossPreparation.head=true := by decide
lemma rankKernel_below : below UniformRankKernelMachine.program=true := by decide
lemma spectrum_below : below UniformKernelSpectrumMachine.program=true := by
 simp only [UniformKernelSpectrumMachine.program,embed,below_append,below_relocate,
  UniformKernelSpectrumMachine.controllerHead,UniformKernelSpectrumMachine.suffix,
  UniformFFTInputMachine.combinedProgram,UniformPreparedFFTMachine.program,Bool.and_eq_true]
 repeat' apply And.intro
 all_goals decide
lemma crossTopology_below : below UniformToeplitzCrossTopologyMachine.program=true := by
 simp only [UniformToeplitzCrossTopologyMachine.program,embed,below_append,below_relocate,Bool.and_eq_true]
 repeat' apply And.intro
 all_goals decide
lemma seed_ceiling : ∀ins∈UniformSeedRankCrossPreparation.program,natCeiling ins≤1220 := by
 have finite:below UniformSeedRankCrossPreparation.program=true := by
  simp only [UniformSeedRankCrossPreparation.program,embed,below_append,below_relocate,
   UniformRankCrossReplayPreparationMachine.program,
   UniformRankCrossReplayPreparationMachine.beforeCoefficient,
   UniformRankCrossReplayPreparationMachine.beforeBucket,
   UniformRankCrossPreparationMachine.program,seedHead_below,rankKernel_below,spectrum_below,crossTopology_below,Bool.and_eq_true]
  repeat' apply And.intro
  all_goals decide
 simpa only [below,List.all_eq_true,decide_eq_true_eq] using finite

noncomputable section

def Args (n : ℕ) (j : Fin (axisCount n)) (c : Config) (s : State) : Prop :=
 s.natReg 1120=j.val ∧ (∀q,1122≤q→q≤1137→s.natReg q=c.register q) ∧
 (∀q,1220≤q→q≤1224→s.natReg q=c.register q)

lemma no_alias (c : Config) : 2*(c.a+c.e)≤UniformRadixTwoDAG.width c.exponent := by
 rw [UniformRadixTwoDAG.width_eq]
 exact UniformWorkspacePlanner.no_alias c.a c.e
lemma widths (c : Config) : c.a≤UniformRadixTwoDAG.width c.exponent ∧ c.e≤UniformRadixTwoDAG.width c.exponent := by
 have h:=no_alias c;omega
lemma selected_divisor (n : ℕ) (j : Fin (axisCount n)) (c : Config)
    (ha:c.a≤radix n j) (he:c.e≤radix n j) (hpos:0<c.a+c.e) :
    UniformRadixTwoDAG.width c.exponent∣UniformMasterRootMachine.order n := by
 apply UniformSeedRankCrossPreparation.selected_divisor n j c.exponent
 have hw:=UniformWorkspacePlanner.width_bound hpos
 rw [UniformRadixTwoDAG.width_eq]
 unfold Config.exponent
 omega

lemma running_highNat {p : Program} {n : ℕ} {x : Fin n→ℂ} {s u : State}
    (bound:∀ins∈p,natCeiling ins≤1220) (h:step p n x s=.running u)
    (q : ℕ) (hq:1220≤q) : u.natReg q=s.natReg q := by
 cases hg:p[s.pc]? with
 | none=>simp [step,hg] at h
 | some ins=>
  have hb:=bound ins (List.mem_of_getElem? hg)
  cases ins <;> simp only [step,hg] at h
  all_goals simp only [natCeiling] at hb
  all_goals repeat' split at h
  all_goals simp_all [writeNat,writeScalar,next]
  all_goals cases h
  all_goals simp (disch:=omega)

lemma execution_highNat {p : Program} {n B t : ℕ} {x : Fin n→ℂ} {s u : State}
    (bound:∀ins∈p,natCeiling ins≤1220) (run:BoundedExecution p n x B s t u)
    (q : ℕ) (hq:1220≤q) : u.natReg q=s.natReg q := by
 induction run with
 | halt _ _=>rfl
 | next _ h _ ih=>exact ih.trans (running_highNat bound h q hq)

/-- Sizing only changes its literal counters and generated exponent. -/
def SizingFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,q≠1121→(q<1225 ∨ 1230≤q)→u.natReg q=s.natReg q)
lemma SizingFrame.trans {s u v : State} (f:SizingFrame s u) (g:SizingFrame u v) : SizingFrame s v :=
 ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
  g.2.2.2.1.trans f.2.2.2.1,g.2.2.2.2.1.trans f.2.2.2.2.1,
  fun q h h'=>(g.2.2.2.2.2 q h h').trans (f.2.2.2.2.2 q h h')⟩
lemma SizingFrame.withPC (s : State) (pc : ℕ) : SizingFrame s (setPC s pc) :=
 ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩
lemma sizingBoot_frame (s : State) : SizingFrame s (applyBlock sizingBoot s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq hr
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [sizingBoot,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma sizingStep_frame (s : State) : SizingFrame s (applyBlock sizingStep s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq hr
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [sizingStep,UniformSeedRankCrossPreparation.KeepsRegister]
 omega

structure SizingCursor (T i : ℕ) (s : State) : Prop where
 one : s.natReg 1225=1
 two : s.natReg 1226=2
 threshold : s.natReg 1227=T
 width : s.natReg 1229=2^i
 exponent : s.natReg 1121=i
lemma SizingCursor.withPC {T i : ℕ} {s : State} (h:SizingCursor T i s) (pc : ℕ) :
 SizingCursor T i (setPC s pc) := ⟨h.one,h.two,h.threshold,h.width,h.exponent⟩
lemma sizingBoot_spec {n : ℕ} (j : Fin (axisCount n)) (c : Config) (s : State)
    (args:Args n j c s) : SizingCursor (2*(c.a+c.e)) 0 (applyBlock sizingBoot s) := by
 have ha:=args.2.1 1122 (by omega) (by omega)
 have he:=args.2.1 1123 (by omega) (by omega)
 constructor
 all_goals simp [sizingBoot,applyBlock,Op.apply,writeNat,next,ha,he,Config.register,Config.seed,
  UniformSeedRankCrossPreparation.Config.register,Nat.mul_comm]
lemma sizingStep_spec (T i : ℕ) (s : State) (h:SizingCursor T i s) :
 SizingCursor T (i+1) (applyBlock sizingStep s) := by
 constructor
 all_goals simp [sizingStep,applyBlock,Op.apply,writeNat,next,h.one,h.two,h.threshold,h.width,h.exponent,pow_succ]

lemma control (n B target : ℕ) (x : Fin n→ℂ) (s : State) (hs:WordBound B s)
    (ht:target≤B) (step:UniformMachine.step program n x s=.running (setPC s target)) :
 BoundedRuns program n x B s 1 (setPC s target) :=
 .next hs step (.refl (changePC_bound B s target hs ht))

/-- Four charged instructions per doubling and the final stopping branch. -/
lemma sizing_loop (n T i fuel B : ℕ) (x : Fin n→ℂ) (s : State)
    (cursor:SizingCursor T i s) (sum:i+fuel=Nat.clog 2 T) (pc:s.pc=6)
    (hs:WordBound B s) (hwidth:2^Nat.clog 2 T≤B) (hc:11≤B) : ∃u,
 BoundedRuns program n x B s (4*fuel+1) u ∧ u.pc=10 ∧
 SizingCursor T (Nat.clog 2 T) u ∧ SizingFrame s u := by
 induction fuel generalizing i s with
 | zero=>
  have hi:i=Nat.clog 2 T:=by omega
  have hstop:¬2^i<T:=by rw [hi];have h:=Nat.le_pow_clog (by decide :1<2) T;omega
  have step:UniformMachine.step program n x s=.running (setPC s 10):=by
   simp [UniformMachine.step,pc,sizing_branch,cursor.width,cursor.threshold,hstop,setPC]
  exact ⟨setPC s 10,control n B 10 x s hs (by omega) step,rfl,
   by simpa only [hi] using cursor.withPC 10,SizingFrame.withPC s 10⟩
 | succ fuel ih=>
  have hi:i<Nat.clog 2 T:=by omega
  have hp:2^i<T:=Nat.pow_lt_of_lt_clog hi
  have step:UniformMachine.step program n x s=.running (setPC s 7):=by
   simp [UniformMachine.step,pc,sizing_branch,cursor.width,cursor.threshold,hp,setPC]
  have entry:=control n B 7 x s hs (by omega) step
  let e:=setPC s 7
  have hw:2^i*2≤B:=by
   rw [←pow_succ]
   exact (Nat.pow_le_pow_right (by decide :0<2) (Nat.succ_le_of_lt hi)).trans hwidth
  have hk:Nat.clog 2 T≤B:=by
   have kt:=Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=T)).le
   have tw:=Nat.le_pow_clog (by decide :1<2) T
   omega
  have safe:peak sizingStep e≤B:=by
   simp [peak,sizingStep,Op.peak,Op.apply,writeNat,next,e,setPC,cursor.width,cursor.two,cursor.one,cursor.exponent]
   omega
  have doubling:=block_runs sizingStep program 7 n B x e sizingStep_code rfl entry.final_bound
   (by rw [sizingStep_length];omega) (by simp [sizingStep,readable,Op.readable]) safe
  have next:=sizingStep_spec T i e (cursor.withPC 7)
  have np:(applyBlock sizingStep e).pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have stepBack:UniformMachine.step program n x (applyBlock sizingStep e)=.running (setPC (applyBlock sizingStep e) 6):=by
   simp [UniformMachine.step,np,sizing_jump,setPC]
  have back:=control n B 6 x (applyBlock sizingStep e) doubling.final_bound (by omega) stepBack
  obtain ⟨u,run,up,uc,uf⟩:=ih (i+1) (setPC (applyBlock sizingStep e) 6) (next.withPC 6)
   (by omega) rfl back.final_bound
  refine ⟨u,?_,up,uc,?_⟩
  · convert ((entry.trans doubling).trans back).trans run using 1
    rw [sizingStep_length];omega
  · exact (SizingFrame.withPC s 7).trans ((sizingStep_frame e).trans
    ((SizingFrame.withPC _ 6).trans uf))

lemma SizingFrame.preserved {n : ℕ} {s u : State} (f:SizingFrame s u) :
    UniformSeedRankCrossPreparation.PreservedFrame n s u :=
 ⟨fun q _=>congrFun f.1 q,fun q _=>congrFun f.2.1 q,
  fun q h h'=>f.2.2.2.2.2 q (by omega) (by omega),f.2.2.2.1,f.2.2.2.2.1⟩

lemma sizing_initialized {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (x : Fin n→ℂ) (s : State) (args:Args n j c s) (pc:s.pc=0) (hs:WordBound B s)
    (hwidth:UniformRadixTwoDAG.width c.exponent≤B) (hc:11≤B) : ∃u,
 BoundedRuns program n x B s (4*c.exponent+8) u ∧ u.pc=11 ∧
 SizingCursor (2*(c.a+c.e)) c.exponent u ∧ SizingFrame s u := by
 have ha:=args.2.1 1122 (by omega) (by omega)
 have he:=args.2.1 1123 (by omega) (by omega)
 have noalias:=no_alias c
 have safe:peak sizingBoot s≤B:=by
  simp [peak,sizingBoot,Op.peak,Op.apply,writeNat,next,ha,he,Config.register,Config.seed,
   UniformSeedRankCrossPreparation.Config.register]
  omega
 have boot:=block_runs sizingBoot program 0 n B x s sizingBoot_code pc hs
  (by rw [sizingBoot_length];omega) (by simp [sizingBoot,readable,Op.readable]) safe
 have bp:(applyBlock sizingBoot s).pc=6:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,sizingBoot_length]
 obtain ⟨u,loop,up,uc,uf⟩:=sizing_loop n (2*(c.a+c.e)) 0 c.exponent B x
  (applyBlock sizingBoot s) (sizingBoot_spec j c s args)
  (by simp [Config.exponent,UniformWorkspacePlanner.exponent]) bp boot.final_bound (by simpa only [UniformRadixTwoDAG.width_eq,Config.exponent,UniformWorkspacePlanner.exponent] using hwidth) hc
 have exit:UniformMachine.step program n x u=.running (setPC u 11):=by
  simp [UniformMachine.step,up,sizing_exit,setPC]
 have last:=control n B 11 x u loop.final_bound hc exit
 refine ⟨setPC u 11,?_,rfl,uc.withPC 11,(sizingBoot_frame s).trans (uf.trans (SizingFrame.withPC u 11))⟩
 convert (boot.trans loop).trans last using 1
 rw [sizingBoot_length];omega

lemma sizing_args {n : ℕ} (j : Fin (axisCount n)) (c : Config) {s u : State}
    (args:Args n j c s) (cursor:SizingCursor (2*(c.a+c.e)) c.exponent u)
    (frame:SizingFrame s u) : UniformSeedRankCrossPreparation.Args n j c.seed u := by
 refine ⟨(frame.2.2.2.2.2 1120 (by decide) (by decide)).trans args.1,?_⟩
 intro q hq hq'
 by_cases eq:q=1121
 · subst q;simpa [Config.seed,UniformSeedRankCrossPreparation.Config.register] using cursor.exponent
 · have old:=(frame.2.2.2.2.2 q eq (by omega)).trans (args.2.1 q (by omega) hq')
   have register:c.register q=c.seed.register q:=by
    interval_cases q <;> rfl
   exact old.trans register

lemma heightSetup_code : BlockAt heightSetup program 846 := by
 intro i hi
 let before:=beforeSeed++UniformSeedRankCrossPreparation.program.map (relocate 11 846)
 let after:=UniformCrossHeightPreparationMachine.program.map (relocate 859 1045)++[.halt]
 have len:before.length=846:=by simp [before,beforeSeed_length,UniformSeedRankCrossPreparation.program_length]
 have he:program=(before++heightSetup.map Op.code)++after:=by
  simp [program,beforeHeight,before,after,List.append_assoc]
 rw [he,List.getElem?_append_left (by simp only [List.length_append,List.length_map,len];omega),
  List.getElem?_append_right (by omega)]
 simp only [len,show 846+i-846=i by omega,List.getElem?_map]
 simp [hi]
lemma heightSetup_frame (s : State) : UniformSeedRankCrossPreparation.SetupFrame s (applyBlock heightSetup s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [heightSetup,UniformSeedRankCrossPreparation.KeepsRegister]
 omega

lemma heightSetup_spec {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedRankCrossPreparation.parameters n j c.seed) B)
    (s : State)
    (post:UniformRankCrossReplayPreparationMachine.PreparedReplay (UniformSeedRankCrossPreparation.parameters n j c.seed) B layout
      (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) s)
    (args:∀q,1220≤q→q≤1224→s.natReg q=c.register q) :
 UniformCrossHeightPreparationMachine.Header c.height (applyBlock heightSetup s) := by
 have h525:=post.ready.1 525 (by decide)
 have h484:=post.ready.1 484 (by decide)
 have h485:=post.ready.1 485 (by decide)
 have h564:=post.ready.1 564 (by decide)
 have h529:=post.ready.1 529 (by decide)
 have high:=args
 have h1220:=args 1220 (by decide) (by decide)
 have h1221:=args 1221 (by decide) (by decide)
 have h1222:=args 1222 (by decide) (by decide)
 have h1223:=args 1223 (by decide) (by decide)
 have h1224:=args 1224 (by decide) (by decide)
 constructor
 all_goals simp [heightSetup,applyBlock,Op.apply,writeNat,next,post.ready.2.2.2,
  h525,h484,h485,h564,h529,post.extra.order,post.extra.directory,post.extra.constants,
  h1220,h1221,h1222,h1223,h1224,UniformRankCrossPreparationMachine.Parameters.register,
  UniformSeedRankCrossPreparation.parameters,Config.seed,Config.height,Config.register]
 all_goals rfl

lemma heightSetup_safe {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedRankCrossPreparation.parameters n j c.seed) B)
    (s : State)
    (post:UniformRankCrossReplayPreparationMachine.PreparedReplay (UniformSeedRankCrossPreparation.parameters n j c.seed) B layout
      (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) s)
    (hs:WordBound B s) : readable heightSetup s ∧ peak heightSetup s≤B := by
 constructor
 · simp [heightSetup,readable,Op.readable]
 · simp [heightSetup,peak,Op.peak,Op.apply,writeNat,next,post.ready.2.2.2]
   repeat' apply And.intro
   all_goals exact hs.2.1 _

lemma height_source {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedRankCrossPreparation.parameters n j c.seed) B)
    {s : State}
    (post:UniformRankCrossReplayPreparationMachine.PreparedReplay (UniformSeedRankCrossPreparation.parameters n j c.seed) B layout
      (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) s) :
 UniformCrossHeightPreparationMachine.Source c.height
  (UniformRankCrossReplayPreparationMachine.cross (UniformSeedRankCrossPreparation.parameters n j c.seed) layout).program s :=
 ⟨post.buckets.bank,post.buckets.directory,post.tape⟩

abbrev parameters (n : ℕ) (j : Fin (axisCount n)) (c : Config) :=
 UniformSeedRankCrossPreparation.parameters n j c.seed
def Config.width (c : Config) := UniformRadixTwoDAG.width c.exponent
def Config.gates (c : Config) := 6*(3*c.exponent*c.width+2*c.width)+2*c.a

/-- Ordinary chunk geometry and disjoint bank placement. The computed width,
    master divisibility, produced tapes and tables are deliberately absent. -/
structure Layout (n : ℕ) (j : Fin (axisCount n)) (c : Config) (B : ℕ) : Prop where
 positiveA : 0<c.a
 positiveE : 0<c.e
 hRows : c.i0+c.a≤radix n j
 gSplit : c.split<radix n j
 interior : c.split≤c.i0
 columns : c.j0+c.e≤c.split
 hFresh : UniformSeedRankCrossPreparation.hBase n j+radix n j≤c.S
 gFresh : UniformSeedRankCrossPreparation.gBase n j+radix n j≤c.S
 masterFresh : 0<c.S
 outputBound : c.S+6*c.width≤B
 sourceEnd : c.S+6*c.width≤c.A
 arenaPositive : 0<c.A
 bankAfter : UniformPreparedFFTMachine.rootAddress c.exponent c.A+1≤c.C
 spectrumEnvelope : UniformKernelSpectrumMachine.wordBudget c.exponent c.S c.A c.d c.C≤B
 convFresh : c.conv+5*UniformToeplitzCrossTopologyMachine.G c.exponent≤c.tape
 topologyEnvelope : UniformToeplitzCrossTopologyMachine.budget c.exponent c.a c.e c.conv c.tape≤B
 tapeFresh : c.tape+5*c.gates≤c.depth
 depthBound : c.depth+c.e+1+c.gates≤B
 fftFresh : c.d+3*UniformRadixTwoDAG.count c.exponent≤c.order
 depthFresh : c.depth+c.e+1+c.gates≤c.order
 directoryFresh : c.order+c.gates*(c.gates+1)≤c.directory
 directoryBound : c.directory+c.gates+2≤B
 negativeFresh : c.C+7*c.width+1≤c.negative
 constantsFresh : c.negative+7*c.width≤c.constants
 constantsBound : c.constants+6≤B
 oldBanks : UniformSeedRankCrossPreparation.Fresh n c.seed
 heightLayout : UniformCrossHeightPreparationMachine.Layout c.height
 heightEnvelope : UniformCrossHeightPreparationMachine.wordBudget c.height≤B
 codeBound : 1046≤B

lemma Layout.replay {n : ℕ} (hn:0<n) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
 (h:Layout n j c B) : UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B := by
 have geo : UniformRankKernelMachine.Geometry (parameters n j c).base.rank B := by
  refine ⟨h.positiveA,h.positiveE,h.hRows,h.gSplit,h.interior,h.columns,
   (widths c).1,(widths c).2,h.hFresh,h.gFresh,h.masterFresh,h.outputBound,?_⟩
  have :=h.codeBound;omega
 have spec : UniformKernelSpectrumMachine.Layout c.exponent c.S c.A c.d c.C
   (UniformMasterRootMachine.order n) B :=
  ⟨h.sourceEnd,h.arenaPositive,h.bankAfter,(UniformMasterRootMachine.order_bounds hn).1,
   selected_divisor n j c (by have :=h.hRows;omega)
    (by have :=h.columns;have :=h.gSplit;omega) (by have :=h.positiveA;omega),h.spectrumEnvelope⟩
 refine ⟨⟨geo,spec,h.convFresh,h.topologyEnvelope,h.tapeFresh,h.depthBound,?_⟩,
  h.fftFresh,h.depthFresh,h.directoryFresh,h.directoryBound,h.negativeFresh,
  h.constantsFresh,h.constantsBound,?_⟩
 all_goals have :=h.codeBound;omega

lemma Layout.width_bound {n : ℕ} {j : Fin (axisCount n)} {c : Config} {B : ℕ}
 (h:Layout n j c B) : c.width≤B := by
 have :=h.outputBound;omega

lemma height_preserved {n : ℕ} {j : Fin (axisCount n)} {c : Config} {B : ℕ}
 (h:Layout n j c B) {s u : State}
 (outside:UniformCrossHeightPreparationMachine.Outside c.height s u)
 (frame:UniformCrossHeightPreparationMachine.Frame s u) :
 UniformSeedRankCrossPreparation.PreservedFrame n s u := by
 refine ⟨?_,fun q _=>congrFun frame.1 q,
  fun q hq hq'=>UniformCrossHeightPreparationMachine.saved_headers frame q ⟨hq,hq'⟩,
  frame.2.2.1,frame.2.2.2.1⟩
 intro q hq
 have fresh:=h.oldBanks.directory
 have hd:=h.heightLayout.directory
 have hr:=h.heightLayout.rows
 have hc:=h.heightLayout.colors
 have hp:=h.heightLayout.palette
 have before : q<c.rows := by
  change UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n≤c.directory at fresh
  change c.directory+c.gates+2≤c.rows at hd
  omega
 have rows : c.rows≤c.colors := by
  change c.rows+6*c.gates*(8*c.exponent+7)≤c.colors at hr;omega
 have colors : c.colors≤c.palette := by
  change c.colors+2*c.gates*(8*c.exponent+7)≤c.palette at hc;omega
 have palette : c.palette+12≤c.heightDirectory := hp
 exact outside q (Or.inl before) (Or.inl (by change q<c.colors;omega))
  (Or.inl (by change q<c.palette;omega)) (Or.inl (by change q<c.heightDirectory;omega))

def runtimeBudget (n : ℕ) (j : Fin (axisCount n)) (c : Config) : ℕ :=
 UniformSeedRankCrossPreparation.runtimeBudget n j c.seed+4*c.exponent+22+
 (4*c.exponent+27+(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56))

/-- Physical producer outputs, including every independently colored depth
    bucket. This is not an execution of those printed shears. -/
structure Result (n : ℕ) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
 (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B)
 (u : State) : Prop where
 source : UniformCrossHeightPreparationMachine.Source c.height
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program u
 cursor : UniformCrossHeightPreparationMachine.Cursor c.height (8*c.exponent+7) u
 processed : UniformCrossHeightPreparationMachine.Processed c.height c.negative
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program
   (8*c.exponent+7) u
 positive : UniformKernelSpectrumMachine.Result c.exponent c.C
   (UniformRankCrossPreparationMachine.kernelValues (parameters n j c).base
     (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) u
 root : u.scalarHeap (c.C+7*c.width)=some (UniformPairMachine.prepared (zeta c.width))
 negative : UniformReplayCoefficientMachine.NegativeBank c.negative (7*c.width)
   (UniformRankCrossReplayPreparationMachine.bankValues (parameters n j c)
     (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) u
 constants : UniformReplayCoefficientMachine.Constants c.exponent c.constants u

/-- One continuous literal execution computes the height before it prepares
    the actual cross DAG, signed banks, sorted order, and colored bucket rows.
    Every producer premise is discharged by the preceding physical phase. -/
theorem execution {n : ℕ} (hn:0<n) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
 (x : Fin n→ℂ) (s : State) (args:Args n j c s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
 (h:Layout n j c B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧ t≤runtimeBudget n j c ∧ u.pc=1045 ∧
 Result n j c B (h.replay hn j c B) u ∧ Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u := by
 have hc:=h.codeBound
 let layout:=h.replay hn j c B
 obtain ⟨v,first,vp,vc,vf⟩:=sizing_initialized j c B x s args pc hs h.width_bound (by omega)
 let seedEntry:=setPC v 0
 have eb:WordBound B seedEntry:=changePC_bound B v 0 first.final_bound (by omega)
 have seedArgs:UniformSeedRankCrossPreparation.Args n j c.seed seedEntry:=
  sizing_args j c args (vc.withPC 0) (vf.trans (SizingFrame.withPC v 0))
 have startFrame:UniformSeedRankCrossPreparation.PreservedFrame n s seedEntry:=
  (vf.trans (SizingFrame.withPC v 0)).preserved
 obtain ⟨w,t,seedRun,seedCost,wp,post,_,_,_,seedFrame⟩:=
  UniformSeedRankCrossPreparation.execution j c.seed B x seedEntry seedArgs
   (startFrame.protected.metadata metadata) (startFrame.retained ret)
   (startFrame.protected.operands ops) layout h.oldBanks rfl eb (by omega)
 have seedPlaced:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedRankCrossPreparation.program_length];omega) (by omega) seedRun
 have entered:placed 11 seedEntry=v:=UniformSeedRankCrossPreparation.placed_zero v 11 vp
 rw [entered] at seedPlaced
 let afterSeed:=setPC w 846
 have oldArgs:∀q,1220≤q→q≤1224→afterSeed.natReg q=c.register q:=by
  intro q hq hq'
  exact (execution_highNat seed_ceiling seedRun q hq).trans
   ((vf.2.2.2.2.2 q (by omega) (by omega)).trans (args.2.2 q hq hq'))
 have post':UniformRankCrossReplayPreparationMachine.PreparedReplay (parameters n j c) B layout
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) afterSeed:=
  ⟨post.toBasePost.withPC 846,post.buckets.withPC 846,post.negative,post.constants⟩
 have safe:=heightSetup_safe j c B layout afterSeed post' seedPlaced.final_bound
 have install:=block_runs heightSetup program 846 n B x afterSeed heightSetup_code rfl
  seedPlaced.final_bound (by rw [heightSetup_length];omega) safe.1 safe.2
 let installed:=applyBlock heightSetup afterSeed
 have ip:installed.pc=859:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have header:=heightSetup_spec j c B layout afterSeed post' oldArgs
 let heightEntry:=setPC installed 0
 have ih:WordBound B heightEntry:=changePC_bound B installed 0 install.final_bound (by omega)
 have source:UniformCrossHeightPreparationMachine.Source c.height
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program heightEntry:=by
  have old:=height_source j c B layout post'
  refine ⟨?_,?_,?_⟩
  · intro q hq;exact old.bank q hq
  · intro q hq;exact old.directory q hq
  · intro q hq;exact old.tape q hq
 have tape:UniformToeplitzCrossTopologyMachine.RowTable
   (UniformToeplitzCrossTopologyMachine.crossRows c.exponent c.a c.e) c.tape heightEntry:=by
  rw [UniformToeplitzCrossTopologyMachine.crossRows_typed c.exponent c.a c.e (widths c).1 (widths c).2]
  exact source.tape
 obtain ⟨z,ticks,heightRun,heightCost,zp,cursor,finalSource,processed,outside,frame⟩:=
  UniformCrossHeightPreparationMachine.cross_execution c.height c.negative B n (widths c).1 (widths c).2
   x heightEntry (header.withPC 0) rfl ih h.heightLayout h.heightEnvelope source.bank source.directory tape
 have heightPlaced:=UniformBoundedAssembly.boundedExecution_placed height_code
  (by rw [UniformCrossHeightPreparationMachine.program_length];omega) (by omega) heightRun
 have enteredHeight:placed 859 heightEntry=installed:=UniformSeedRankCrossPreparation.placed_zero installed 859 ip
 rw [enteredHeight] at heightPlaced
 let u:=setPC z 1045
 have stop:BoundedExecution program n x B u 1 u:=.halt heightPlaced.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:BoundedExecution program n x B s (4*c.exponent+8+t+13+ticks+1) u:=by
  convert first.executes (seedPlaced.executes (install.executes (heightPlaced.executes stop))) using 1
  rw [heightSetup_length];omega
 have middle:UniformSeedRankCrossPreparation.PreservedFrame n s installed:=
  startFrame.trans (seedFrame.trans (heightSetup_frame afterSeed).preserved)
 have last:=height_preserved h outside frame
 have full:UniformSeedRankCrossPreparation.PreservedFrame n s u:=middle.trans last
 have scalar:u.scalarHeap=w.scalarHeap:=frame.1
 refine ⟨u,4*c.exponent+8+t+13+ticks+1,all,?_,rfl,
  ⟨finalSource.withPC,cursor.withPC,processed,?_,?_,?_,?_⟩,full.retained ret,
  full.protected.metadata metadata,full.protected.operands ops,full⟩
 · change ticks≤4*c.exponent+27+(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56) at heightCost
   unfold runtimeBudget;omega
 · intro i;rw [scalar];exact post.positive i
 · rw [scalar];exact post.root
 · intro i hi;rw [scalar];exact post.negative i hi
 · intro i hi;rw [scalar];exact post.constants i hi

/-- A polynomial in the local sizes and logarithm of the true master order;
    placements affect word bounds, but not this charged instruction budget. -/
lemma runtimeBudget_polynomial (n : ℕ) (j : Fin (axisCount n)) (c : Config) (W : ℕ)
 (hk:c.exponent≤W) (hw:c.width≤W) (ha:c.a≤W) (he:c.e≤W) (hs:c.split≤W)
 (hd:Nat.log2 (UniformMasterRootMachine.order n+1)≤W) :
 runtimeBudget n j c≤100000000*(W+1)^5 := by
 let t:=W+1
 have ht:1≤t:=by dsimp [t];omega
 have hkt:c.exponent≤t:=by omega
 have hwt:c.width≤t:=by omega
 have hat:c.a≤t:=by omega
 have het:c.e≤t:=by omega
 have hst:c.split≤t:=by omega
 have hdt:Nat.log2 (UniformMasterRootMachine.order n+1)≤t:=by omega
 have t12:t≤t^2:=by nlinarith
 have t23:t^2≤t^3:=by nlinarith [sq_nonneg (t-1)]
 have t34:t^3≤t^4:=by
  have h:=Nat.mul_le_mul_right (t^2) t12
  convert h using 1 <;> ring
 have t45:t^4≤t^5:=by
  have h:=Nat.mul_le_mul_right (t^3) t12
  convert h using 1 <;> ring
 have prod:c.exponent*c.width≤t^2:=by
  simpa [pow_two] using Nat.mul_le_mul hkt hwt
 have cnt:UniformRadixTwoDAG.count c.exponent≤3*t^2:=by
  have hc:=UniformRadixTwoDAG.count_exact c.exponent
  change 2*UniformRadixTwoDAG.count c.exponent=3*c.exponent*c.width at hc
  nlinarith only [hc,prod]
 have conv:UniformToeplitzCrossTopologyMachine.G c.exponent≤5*t^2:=by
  have hg:=UniformConvolutionDAG.gate_count c.exponent
  rw [UniformConvolutionDAG.records_length] at hg
  rw [UniformToeplitzCrossTopologyMachine.G,hg]
  rw [←UniformRadixTwoDAG.width_eq]
  change 3*c.exponent*c.width+2*c.width≤5*t^2
  nlinarith only [prod,hwt,t12]
 have gates:c.gates≤32*t^2:=by unfold Config.gates;nlinarith only [prod,hwt,hat,t12]
 have powcost:=UniformRootExtractionMachine.runtime_log_bound
  (UniformMasterRootMachine.order n) c.width
 have fft:=UniformPreparedFFTMachine.runtime_log_bound (UniformMasterRootMachine.order n) c.exponent
 have coeffproduct: (19*c.exponent+85)*UniformRadixTwoDAG.count c.exponent≤312*t^3:=by
  have a:19*c.exponent+85≤104*t:=by omega
  have m:=Nat.mul_le_mul a cnt
  convert m using 1;ring
 have fftbound:UniformPreparedFFTMachine.runtime (UniformMasterRootMachine.order n) c.exponent≤400*t^3:=by
  change _≤(19*c.exponent+85)*UniformRadixTwoDAG.count c.exponent+
   4*c.exponent+8*c.width+7*(Nat.log2 (UniformMasterRootMachine.order n+1)+1)+53 at fft
  nlinarith only [fft,coeffproduct,hkt,hwt,hdt,ht,t12,t23]
 have spec:UniformKernelSpectrumMachine.runtimeBudget (UniformMasterRootMachine.order n) c.exponent≤4000*t^3:=by
  unfold UniformKernelSpectrumMachine.runtimeBudget
  change 4*c.exponent+12+6*(7+(4*c.exponent+10*c.width+9+
   UniformPreparedFFTMachine.runtime (UniformMasterRootMachine.order n) c.exponent)+4+(7*c.width+4)+3)+
   1+5+(9+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/c.width))+3+(6*c.width+6)+1≤_
  nlinarith only [fftbound,powcost,hkt,hwt,hdt,ht,t12,t23]
 have kernel:=UniformRankKernelMachine.runtime_bound (parameters n j c).base.rank
 have crossprod:(19*c.exponent+344)*UniformToeplitzCrossTopologyMachine.G c.exponent≤1815*t^3:=by
  have a:19*c.exponent+344≤363*t:=by omega
  have m:=Nat.mul_le_mul a conv
  convert m using 1;ring
 have gateprod:c.gates*(c.gates+1)≤1056*t^4:=by
  have a:c.gates+1≤33*t^2:=by omega
  have m:=Nat.mul_le_mul gates a
  convert m using 1;ring
 have iteration:64*c.gates+200*(2*c.gates+1)^2+56≤900000*t^4:=by
  have a:2*c.gates+1≤65*t^2:=by omega
  have m:=Nat.pow_le_pow_left a 2
  rw [show (65*t^2)^2=4225*t^4 by ring] at m
  nlinarith only [m,gates,ht,t12,t23,t34]
 have heightprod:(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56)≤13500000*t^5:=by
  have a:8*c.exponent+7≤15*t:=by omega
  have m:=Nat.mul_le_mul a iteration
  convert m using 1;ring
 have ea:c.e*c.split≤t^2:=by simpa [pow_two] using Nat.mul_le_mul het hst
 have aa:c.a*c.split≤t^2:=by simpa [pow_two] using Nat.mul_le_mul hat hst
 change UniformRankKernelMachine.runtime (parameters n j c).base.rank≤
  28+30*c.width+c.e*(19+11*c.split)+c.a*(21+11*c.split) at kernel
 unfold runtimeBudget UniformSeedRankCrossPreparation.runtimeBudget
  UniformRankCrossReplayPreparationMachine.runtimeBudget UniformRankCrossPreparationMachine.runtimeBudget
  UniformDAGDepthMachine.runtimeBudget UniformDAGBucketMachine.runtimeBudget UniformReplayCoefficientMachine.runtime
 change 4*c.exponent+9+UniformRankKernelMachine.runtime (parameters n j c).base.rank+
  UniformKernelSpectrumMachine.runtimeBudget (UniformMasterRootMachine.order n) c.exponent+3+
  (4*c.exponent+113+(19*c.exponent+344)*UniformToeplitzCrossTopologyMachine.G c.exponent+40*c.a)+13+
  (5*(c.e+1)+22*c.gates+10)+1+6+(10*c.gates*(c.gates+1)+7*(c.gates+1)+9)+4+
  (5*c.exponent+56*c.width+31)+1+36+4*c.exponent+22+
  (4*c.exponent+27+(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56))≤100000000*t^5
 nlinarith only [kernel,spec,crossprod,gateprod,heightprod,ea,aa,hkt,hwt,hat,het,ht,gates,t12,t23,t34,t45]

lemma Layout.runtime_bound {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
 (h:Layout n j c B) :
 runtimeBudget n j c≤100000000*(8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2)^5 := by
 let W:=8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+1
 have a:c.a≤radix n j:=by have :=h.hRows;omega
 have e:c.e≤radix n j:=by have :=h.gSplit;have :=h.columns;omega
 have width:c.width≤8*radix n j:=by
  have b:=UniformWorkspacePlanner.width_bound (show 0<c.a+c.e by have :=h.positiveA;omega)
  change 2^c.exponent≤4*(c.a+c.e) at b
  rw [Config.width,UniformRadixTwoDAG.width_eq];omega
 have k:c.exponent≤c.width:=by
  have hp:=UniformCrossDepthReplayPreparation.power_ge_successor c.exponent
  change c.exponent+1≤2^c.exponent at hp
  rw [Config.width,UniformRadixTwoDAG.width_eq]
  omega
 simpa [W] using runtimeBudget_polynomial n j c W
  (by omega) (by omega) (by omega) (by omega) (by have :=h.gSplit;omega) (by omega)

lemma master_log_bound {n : ℕ} (hn:0<n) :
 Nat.log2 (UniformMasterRootMachine.order n+1)≤3*Nat.clog 2 (n+1)+10 := by
 have nb:n≤2^Nat.clog 2 (n+1):=(Nat.le_succ n).trans (Nat.le_pow_clog (by decide) (n+1))
 have cube:=Nat.pow_le_pow_left nb 3
 have ob:= (UniformMasterRootMachine.order_bounds hn).2
 have bound:UniformMasterRootMachine.order n+1≤2^(3*Nat.clog 2 (n+1)+10) := by
  calc _≤1024*n^3:=by omega
       _≤1024*(2^Nat.clog 2 (n+1))^3:=Nat.mul_le_mul_left 1024 cube
       _=_:=by rw [←pow_mul,pow_add];norm_num;ring
 rw [Nat.log2_eq_log_two]
 exact (Nat.log_le_clog 2 _).trans (Nat.clog_le_of_le_pow bound)

/-- Concrete selected-axis bound: the only growth terms are the logarithmic
    axis count and a binary logarithm of n. Global scheduling is separate. -/
lemma Layout.selected_runtime_bound {n : ℕ} (hn:0<n) (j : Fin (axisCount n))
 (c : Config) (B : ℕ) (h:Layout n j c B) :
 runtimeBudget n j c≤100000000*(1024*(UniformInitialPreparation.ell n+2)^2+
   3*Nat.clog 2 (n+1)+12)^5 := by
 have r:radix n j≤128*(UniformInitialPreparation.ell n+2)^2:=UniformSelectedCRT.radix_quadratic hn j
 have master:=master_log_bound hn
 have a:8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2≤
   1024*(UniformInitialPreparation.ell n+2)^2+3*Nat.clog 2 (n+1)+12:=by omega
 exact (h.runtime_bound j c B).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a 5))

lemma Layout.logarithmic_runtime_bound {n : ℕ} (hn:0<n) (j : Fin (axisCount n))
 (c : Config) (B : ℕ) (h:Layout n j c B) :
 runtimeBudget n j c≤100000000*(1024*(Nat.log 3 (2*n)+2)^2+
   3*Nat.clog 2 (n+1)+12)^5 := by
 have ell:=UniformWorkingLength.axisCount_log_bound hn
 have square:(UniformInitialPreparation.ell n+2)^2≤(Nat.log 3 (2*n)+2)^2:=
  Nat.pow_le_pow_left (Nat.add_le_add_right ell 2) 2
 have base:1024*(UniformInitialPreparation.ell n+2)^2+3*Nat.clog 2 (n+1)+12≤
  1024*(Nat.log 3 (2*n)+2)^2+3*Nat.clog 2 (n+1)+12:=by omega
 exact (h.selected_runtime_bound hn j c B).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 5))

lemma Result.color_bound {n : ℕ} {j : Fin (axisCount n)} {c : Config} {B : ℕ}
 {layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B}
 {u : State} (result:Result n j c B layout u) (d : ℕ) (hd:d<8*c.exponent+7) :
 let W:=UniformCrossDepthReplayPreparation.bucket
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program c.enabled d
 ∀i:Fin W.length,∃v,v<11 ∧
  u.natHeap (UniformCrossHeightPreparationMachine.colorBase c.height d+i.val)=some v := by
 intro W i
 have degree:=UniformCrossDepthReplayPreparation.cross_bucket_degree c.exponent c.a c.e d
  (widths c).1 (widths c).2 c.enabled
 have shifted:UniformColoring.DegreeBound (UniformCrossDepthReplayPreparation.shiftedEdges 0 W) 6:=
  UniformCrossDepthReplayPreparation.shiftedEdges_degree 0 6 W degree
 exact ⟨_,UniformColoring.coloring_bound _ shifted (by decide) i,(result.processed d hd).2.1 i⟩

lemma Result.same_color_disjoint {n : ℕ} {j : Fin (axisCount n)} {c : Config} {B : ℕ}
 {layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B}
 {u : State} (result:Result n j c B layout u) (d : ℕ) (hd:d<8*c.exponent+7) :
 let W:=UniformCrossDepthReplayPreparation.bucket
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program c.enabled d
 ∀i j:Fin W.length,i≠j→
  u.natHeap (UniformCrossHeightPreparationMachine.colorBase c.height d+i.val)=
    u.natHeap (UniformCrossHeightPreparationMachine.colorBase c.height d+j.val)→
  ¬UniformColoring.Conflict (UniformCrossDepthReplayPreparation.shiftedEdges 0 W i)
    (UniformCrossDepthReplayPreparation.shiftedEdges 0 W j) := by
 intro W i j neq same
 have degree:=UniformCrossDepthReplayPreparation.cross_bucket_degree c.exponent c.a c.e d
  (widths c).1 (widths c).2 c.enabled
 have shifted:UniformColoring.DegreeBound (UniformCrossDepthReplayPreparation.shiftedEdges 0 W) 6:=
  UniformCrossDepthReplayPreparation.shiftedEdges_degree 0 6 W degree
 have colors:=(result.processed d hd).2.1
 rw [colors i,colors j] at same
 exact UniformColoring.same_color_disjoint _ shifted (by decide) i j neq (Option.some.inj same)

end
end ExactFourierCircuits.UniformSeedHeightPreparation
