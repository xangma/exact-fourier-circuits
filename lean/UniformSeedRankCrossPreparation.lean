import UniformAllAxisSeedPreparation
import UniformRankCrossReplayPreparationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedRankCrossPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
open UniformAllAxisSeedPreparation (axisCount radix axisBase directoryBase Retained)
open OAI.ExactFourier

noncomputable section

def omega (n : ℕ) (j : Fin (axisCount n)) : ℂ := zeta (radix n j)
def hValue (n : ℕ) (j : Fin (axisCount n)) (i : ℕ) : ℂ :=
  PowerSeries.coeff i (NewtonFourier.invH (omega n j))
def gValue (n : ℕ) (j : Fin (axisCount n)) (i : ℕ) : ℂ :=
  PowerSeries.coeff i (NewtonFourier.invH (omega n j))⁻¹
def hBase (n : ℕ) (j : Fin (axisCount n)) := axisBase n j.val+3*radix n j
def gBase (n : ℕ) (j : Fin (axisCount n)) := axisBase n j.val+4*radix n j

theorem retained_h {n : ℕ} {s : State} (ret:Retained n (axisCount n) s) (j : Fin (axisCount n)) :
    UniformRankKernelMachine.Bank (hBase n j) (radix n j) (hValue n j) s := by
  intro i hi
  have cell:=(UniformAllAxisSeedPreparation.retained_complete ret j).2.2 (3:Fin 5) ⟨i,hi⟩
  simpa [hBase,hValue,omega,UniformLocalSeedTableMachine.seedValue,
    NewtonFourier.invH,PowerSeries.coeff_mk,Nat.add_assoc] using cell

theorem retained_g {n : ℕ} {s : State} (ret:Retained n (axisCount n) s) (j : Fin (axisCount n)) :
    UniformRankKernelMachine.Bank (gBase n j) (radix n j) (gValue n j) s := by
  intro i hi
  have cell:=(UniformAllAxisSeedPreparation.retained_complete ret j).2.2 (4:Fin 5) ⟨i,hi⟩
  simpa [gBase,gValue,omega,UniformLocalSeedTableMachine.seedValue,Nat.add_assoc] using cell

/-- The actual initial constant bank contains the original master at zero. -/
theorem operands_master {n : ℕ} {x : Fin n→ℂ} {s : State}
    (ops:UniformInitialPreparation.Operands n x s) :
    s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n))) := by
  simpa [UniformCConstantsMachine.bank] using ops.constants (0:Fin 6)

/-- Chunk/workspace data only; H/G bases, lengths and root order are derived. -/
structure Config where
  K : ℕ
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

def Config.register (c : Config) : ℕ→ℕ
  | 1121=>c.K | 1122=>c.a | 1123=>c.e | 1124=>c.i0 | 1125=>c.j0 | 1126=>c.split
  | 1127=>c.S | 1128=>c.A | 1129=>c.d | 1130=>c.C
  | 1131=>c.conv | 1132=>c.tape | 1133=>c.depth | 1134=>c.order
  | 1135=>c.directory | 1136=>c.negative | 1137=>c.constants
  | _=>0

def parameters (n : ℕ) (j : Fin (axisCount n)) (c : Config) :
    UniformRankCrossReplayPreparationMachine.ReplayParameters where
  base:=⟨c.K,hBase n j,gBase n j,radix n j,radix n j,c.a,c.e,c.i0,c.j0,c.split,
    c.S,c.A,c.d,c.C,UniformMasterRootMachine.order n,c.conv,c.tape,c.depth⟩
  order:=c.order
  directory:=c.directory
  negative:=c.negative
  constants:=c.constants

/-- Caller1120=axis;1121..1137=ordinary chunk/layout arguments. -/
def Args (n : ℕ) (j : Fin (axisCount n)) (c : Config) (s : State) : Prop :=
  s.natReg 1120=j.val ∧ ∀r,1121 ≤ r → r ≤ 1137 → s.natReg r=c.register r

end

def sourceSetup : List Op := [.literal 1138 0,.literal 1139 1,.literal 1140 2,
  .literal 1141 3,.literal 1142 4,.add 1143 105 106,.add 1143 1143 103,
  .mul 1146 1120 1140,.add 1143 1143 1146,.getNat 1144 1143,
  .add 1143 1143 1139,.getNat 1145 1143,
  .mul 480 1145 1141,.add 480 1144 480,.mul 482 1145 1142,.add 482 1144 482,
  .add 481 1145 1138,.add 483 1145 1138]
def headerSetup : List Op := [.add 525 1121 1138,.add 484 1122 1138,.add 485 1123 1138,
  .add 486 1124 1138,.add 487 1125 1138,.add 488 1126 1138,
  .add 490 1127 1138,.add 527 1128 1138,.add 528 1129 1138,.add 529 1130 1138,
  .add 563 1131 1138,.add 564 1132 1138,.add 675 1133 1138,
  .add 950 1134 1138,.add 951 1135 1138,.add 952 1136 1138,.add 953 1137 1138]
def setup : List Op := sourceSetup++headerSetup
def head : Program := setup.map Op.code
def program : Program := embed head UniformRankCrossReplayPreparationMachine.program [.halt] 834

theorem sourceSetup_length : sourceSetup.length=18 := rfl
theorem headerSetup_length : headerSetup.length=17 := rfl
theorem setup_length : setup.length=35 := rfl
theorem head_length : head.length=35 := rfl
theorem program_length : program.length=835 := by
  rw [program,embed_length,head_length,UniformRankCrossReplayPreparationMachine.program_length];rfl

theorem sourceSetup_code : BlockAt sourceSetup program 0 := by
  intro i hi;change i<18 at hi;interval_cases i <;> rfl
theorem headerSetup_code : BlockAt headerSetup program 18 := by
  intro i hi;change i<17 at hi;interval_cases i <;> rfl
theorem replay_code : CodeAt UniformRankCrossReplayPreparationMachine.program program 35 834 :=
  by simpa only [program,head_length] using embed_code head UniformRankCrossReplayPreparationMachine.program [.halt] 834
theorem halt_at : program[834]?=some .halt := by
  rw [program,embed]
  rw [List.getElem?_append_right (by simp [head_length,UniformRankCrossReplayPreparationMachine.program_length])]
  simp [head_length,UniformRankCrossReplayPreparationMachine.program_length]

noncomputable section
structure Loaded (n : ℕ) (j : Fin (axisCount n)) (c : Config) (s : State) : Prop where
  args : Args n j c s
  zero : s.natReg 1138=0
  H : s.natReg 480=hBase n j
  G : s.natReg 482=gBase n j
  hSize : s.natReg 481=radix n j
  gSize : s.natReg 483=radix n j
  order : s.natReg 104=UniformMasterRootMachine.order n

/-- Directory loads supply the actual retained bases and radix. -/
theorem sourceSetup_loaded {n : ℕ} (j : Fin (axisCount n)) (c : Config) (s : State)
    (args:Args n j c s) (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) : Loaded n j c (applyBlock sourceSetup s) := by
  obtain ⟨address,width,_⟩:=UniformAllAxisSeedPreparation.retained_complete ret j
  have dir:s.natReg 105+s.natReg 106+s.natReg 103=directoryBase n:=by
    rw [metadata.saved.copyAddress,metadata.saved.copyLength,metadata.saved.workingLength]
    exact UniformAllAxisSeedPreparation.directory_after_protected n
  simp only [Nat.add_assoc,Nat.mul_comm] at address width
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · simp [sourceSetup,applyBlock,Op.apply,writeNat,next,args.1]
  · intro q hq hq'
    simpa (disch:=omega) [sourceSetup,applyBlock,Op.apply,writeNat,next] using args.2 q hq hq'
  all_goals simp [sourceSetup,applyBlock,Op.apply,writeNat,next,dir,args.1,
    address,width,hBase,gBase,metadata.saved.masterRoot,Nat.add_assoc,Nat.mul_comm]


def installedRegister (s : State) (q : ℕ) : ℕ :=
  if q=953 then s.natReg 1137+s.natReg 1138 else
  if q=952 then s.natReg 1136+s.natReg 1138 else
  if q=951 then s.natReg 1135+s.natReg 1138 else
  if q=950 then s.natReg 1134+s.natReg 1138 else
  if q=675 then s.natReg 1133+s.natReg 1138 else
  if q=564 then s.natReg 1132+s.natReg 1138 else
  if q=563 then s.natReg 1131+s.natReg 1138 else
  if q=529 then s.natReg 1130+s.natReg 1138 else
  if q=528 then s.natReg 1129+s.natReg 1138 else
  if q=527 then s.natReg 1128+s.natReg 1138 else
  if q=490 then s.natReg 1127+s.natReg 1138 else
  if q=488 then s.natReg 1126+s.natReg 1138 else
  if q=487 then s.natReg 1125+s.natReg 1138 else
  if q=486 then s.natReg 1124+s.natReg 1138 else
  if q=485 then s.natReg 1123+s.natReg 1138 else
  if q=484 then s.natReg 1122+s.natReg 1138 else
  if q=525 then s.natReg 1121+s.natReg 1138 else s.natReg q

theorem headerSetup_register (s : State) : (applyBlock headerSetup s).natReg=installedRegister s := by
  funext q
  simp [headerSetup,applyBlock,Op.apply,writeNat,next,installedRegister,Function.update_apply]

theorem headerSetup_spec {n : ℕ} (j : Fin (axisCount n)) (c : Config) (s : State)
    (h:Loaded n j c s) :
    UniformRankCrossPreparationMachine.Header (parameters n j c).base (applyBlock headerSetup s) ∧
    UniformRankCrossReplayPreparationMachine.ExtraHeader (parameters n j c) (applyBlock headerSetup s) := by
  have arg:∀q,1121 ≤ q → q ≤ 1137 → s.natReg q=c.register q:=h.args.2
  constructor
  · intro q hq
    simp only [UniformRankCrossPreparationMachine.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rw [headerSetup_register]
    all_goals simp (disch:=omega) [installedRegister,parameters,
      UniformRankCrossPreparationMachine.Parameters.register,h.order,h.H,h.G,h.hSize,h.gSize,h.zero,arg,Config.register]
  · refine ⟨?_,?_,?_,?_⟩
    all_goals rw [headerSetup_register]
    all_goals simp (disch:=omega) [installedRegister,parameters,h.zero,arg,Config.register]


/-- Local compiler widths within the printed eight-radix cap divide the actual
master order chosen during global startup. -/
theorem selected_divisor (n : ℕ) (j : Fin (axisCount n)) (K : ℕ)
    (cap:UniformRadixTwoDAG.width K ≤ 8*radix n j) :
    UniformRadixTwoDAG.width K ∣ UniformMasterRootMachine.order n := by
  rw [UniformRadixTwoDAG.width_eq] at cap ⊢
  exact UniformBatching.localPowerOrder_dvd (UniformGlobalLocalPreparation.radix_le_length n j) cap

def SetupFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,(r < 480 ∨ 1147 ≤ r ∨ (1120 ≤ r ∧ r ≤ 1137))→u.natReg r=s.natReg r)

theorem SetupFrame.trans {s u v : State} (f:SetupFrame s u) (g:SetupFrame u v) : SetupFrame s v :=
  ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
    g.2.2.2.1.trans f.2.2.2.1,g.2.2.2.2.1.trans f.2.2.2.2.1,
    fun r h=>(g.2.2.2.2.2 r h).trans (f.2.2.2.2.2 r h)⟩


def KeepsRegister (r : ℕ) : Op→Prop
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _=>r≠d
  | _=>True

theorem block_register_keeps (os : List Op) (s : State) (r : ℕ)
    (keeps:∀o∈os,KeepsRegister r o) : (applyBlock os s).natReg r=s.natReg r := by
  induction os generalizing s with
  | nil=>rfl
  | cons o os ih=>
    change (applyBlock os (o.apply s)).natReg r=s.natReg r
    rw [ih _ (fun t ht=>keeps t (by simp [ht]))]
    have h:=keeps o (by simp)
    cases o <;> simp only [KeepsRegister] at h
    all_goals simp [Op.apply,writeNat,writeScalar,next,h]

theorem sourceSetup_frame (s : State) : SetupFrame s (applyBlock sourceSetup s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  apply block_register_keeps
  simp [sourceSetup,KeepsRegister]
  omega

theorem headerSetup_frame (s : State) : SetupFrame s (applyBlock headerSetup s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  apply block_register_keeps
  simp [headerSetup,KeepsRegister]
  omega

theorem sourceSetup_safe {n : ℕ} (j : Fin (axisCount n)) (c : Config) (s : State) (B : ℕ)
    (args:Args n j c s) (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B)
    (hs:WordBound B s) : readable sourceSetup s ∧ peak sourceSetup s ≤ B := by
  obtain ⟨address,width,_⟩:=UniformAllAxisSeedPreparation.retained_complete ret j
  have dir:s.natReg 105+s.natReg 106+s.natReg 103=directoryBase n:=by
    rw [metadata.saved.copyAddress,metadata.saved.copyLength,metadata.saved.workingLength]
    exact UniformAllAxisSeedPreparation.directory_after_protected n
  have pointerBound:directoryBase n+2*j.val+1 ≤ B:=(hs.2.2.1 _ _ width).1
  have gb:gBase n j ≤ B:=by
    have a:=layout.original.1.gFresh
    have b:=layout.original.1.outputBound
    change gBase n j+radix n j ≤ c.S at a
    change c.S+6*UniformRadixTwoDAG.width c.K ≤ B at b
    omega
  have code:=layout.codeBound
  simp only [Nat.add_assoc,Nat.mul_comm] at address width
  constructor
  · simp [sourceSetup,readable,Op.readable,Op.apply,writeNat,next,dir,args.1,
      address,width,Nat.add_assoc]
  · simp [sourceSetup,peak,Op.peak,Op.apply,writeNat,next,dir,args.1,
      address,width,Nat.add_assoc,Nat.mul_comm]
    unfold gBase at gb
    omega

theorem headerSetup_safe {n : ℕ} (j : Fin (axisCount n)) (c : Config) (s : State) (B : ℕ)
    (h:Loaded n j c s) (hs:WordBound B s) : readable headerSetup s ∧ peak headerSetup s ≤ B := by
  constructor
  · simp [readable,headerSetup,Op.readable]
  · simp [peak,headerSetup,Op.peak,Op.apply,writeNat,next,h.zero]
    repeat' constructor
    all_goals exact hs.2.1 _

/-- Ordinary fresh-region restrictions protect all retained axes and global operands. -/
structure Fresh (n : ℕ) (c : Config) : Prop where
  row : directoryBase n+2*axisCount n ≤ c.d
  convolution : directoryBase n+2*axisCount n ≤ c.conv
  tape : directoryBase n+2*axisCount n ≤ c.tape
  depth : directoryBase n+2*axisCount n ≤ c.depth
  order : directoryBase n+2*axisCount n ≤ c.order
  directory : directoryBase n+2*axisCount n ≤ c.directory
  kernels : axisBase n (axisCount n) ≤ c.S
  fft : axisBase n (axisCount n) ≤ c.A
  positive : axisBase n (axisCount n) ≤ c.C
  negative : axisBase n (axisCount n) ≤ c.negative
  constants : axisBase n (axisCount n) ≤ c.constants

/-- Frame for the caller and799, restricted to all old global/retained banks. -/
def PreservedFrame (n : ℕ) (s u : State) : Prop :=
  (∀q,q < directoryBase n+2*axisCount n→u.natHeap q=s.natHeap q) ∧
  (∀q,q < axisBase n (axisCount n)→u.scalarHeap q=s.scalarHeap q) ∧
  (∀q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders

theorem PreservedFrame.trans {n : ℕ} {s u v : State} (f:PreservedFrame n s u)
    (g:PreservedFrame n u v) : PreservedFrame n s v :=
  ⟨fun q h=>(g.1 q h).trans (f.1 q h),fun q h=>(g.2.1 q h).trans (f.2.1 q h),
    fun q h h'=>(g.2.2.1 q h h').trans (f.2.2.1 q h h'),
    g.2.2.2.1.trans f.2.2.2.1,g.2.2.2.2.trans f.2.2.2.2⟩

theorem SetupFrame.preserved {n : ℕ} {s u : State} (f:SetupFrame s u) : PreservedFrame n s u :=
  ⟨fun q _=>congrFun f.1 q,fun q _=>congrFun f.2.1 q,
    fun q h h'=>f.2.2.2.2.2 q (by omega),f.2.2.2.1,f.2.2.2.2.1⟩

theorem replay_frame {n : ℕ} (j : Fin (axisCount n)) (c : Config) {s u : State}
    (fresh:Fresh n c)
    (f:UniformRankCrossReplayPreparationMachine.ExternalFrame (parameters n j c) s u) :
    PreservedFrame n s u := by
  refine ⟨?_,?_,?_,f.outputs,f.roots⟩
  · intro q hq
    exact f.nat q (Or.inl (by exact hq.trans_le fresh.row))
      (Or.inl (by exact hq.trans_le fresh.convolution)) (Or.inl (by exact hq.trans_le fresh.tape))
      (Or.inl (by exact hq.trans_le fresh.depth)) (Or.inl (by exact hq.trans_le fresh.order))
      (Or.inl (by exact hq.trans_le fresh.directory))
  · intro q hq
    exact f.scalar q (Or.inl (hq.trans_le fresh.kernels)) (Or.inl (hq.trans_le fresh.fft))
      (Or.inl (hq.trans_le fresh.positive)) (Or.inl (hq.trans_le fresh.negative)) (Or.inl (hq.trans_le fresh.constants))
  · intro q hq hq';exact f.saved q ⟨hq,hq'⟩

theorem PreservedFrame.protected {n : ℕ} {s u : State} (f:PreservedFrame n s u) :
    UniformAllAxisSeedPreparation.ProtectedFrame n s u := by
  refine ⟨fun q _ hq=>f.1 q (by omega),?_,f.2.2.1,f.2.2.2.1,f.2.2.2.2⟩
  intro q hq
  have global:UniformGlobalLocalPreparation.globalEnd n ≤ axisBase n (axisCount n):=by
    unfold axisBase UniformLocalSeedTableMachine.poolBase
    omega
  exact f.2.1 q (hq.trans_le global)

theorem PreservedFrame.retained {n k : ℕ} {s u : State} (f:PreservedFrame n s u)
    (ret:Retained n k s) : Retained n k u := by
  refine ⟨?_,?_,?_⟩
  · intro j hj q l
    have bound:=UniformAllAxisSeedPreparation.compact_address_before j (by omega :j.val < axisCount n) q l
    exact (f.2.1 _ bound).trans (ret.coefficients j hj q l)
  · intro j hj
    exact (f.1 _ (by have h:=j.isLt;omega)).trans (ret.address j hj)
  · intro j hj
    exact (f.1 _ (by have h:=j.isLt;omega)).trans (ret.width j hj)


theorem placed_zero (s : State) (base : ℕ) (pc:s.pc=base) : placed base (setPC s 0)=s := by
  cases s
  cases pc
  simp [placed,setPC]

def runtimeBudget (n : ℕ) (j : Fin (axisCount n)) (c : Config) :=
  UniformRankCrossReplayPreparationMachine.runtimeBudget (parameters n j c)+36

/-- A continuous charged caller reads retained lanes and installs all799
headers. No H/G/master, kernel/spectrum/tape/depth/order/signed-bank output
certificate is supplied separately. Geometry and fresh layout are ordinary inputs. -/
theorem execution {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (x : Fin n→ℂ) (s : State) (args:Args n j c s)
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B)
    (fresh:Fresh n c) (pc:s.pc=0) (hs:WordBound B s) (hB:835 ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget n j c ∧ u.pc=834 ∧
    UniformRankCrossReplayPreparationMachine.PreparedReplay (parameters n j c) B layout
      (hValue n j) (gValue n j) u ∧ Retained n (axisCount n) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    PreservedFrame n s u := by
  have safe:=sourceSetup_safe j c s B args metadata ret layout hs
  have first:=block_runs sourceSetup program 0 n B x s sourceSetup_code pc hs
    (by rw [sourceSetup_length];omega) safe.1 safe.2
  let loaded:=applyBlock sourceSetup s
  have head:=sourceSetup_loaded j c s args metadata ret
  have lp:loaded.pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,sourceSetup_length]
  have installSafe:=headerSetup_safe j c loaded B head first.final_bound
  have second:=block_runs headerSetup program 18 n B x loaded headerSetup_code lp first.final_bound
    (by rw [headerSetup_length];omega) installSafe.1 installSafe.2
  let installed:=applyBlock headerSetup loaded
  have installedPC:installed.pc=35:=by rw [UniformTensorMonomialMachine.applyBlock_pc,lp,headerSetup_length]
  have installedHeaders:=headerSetup_spec j c loaded head
  let entry:=setPC installed 0
  have eb:=changePC_bound B installed 0 second.final_bound (by omega)
  have entryH:UniformRankKernelMachine.Bank (parameters n j c).base.H (parameters n j c).base.hSize
      (hValue n j) entry:=retained_h ret j
  have entryG:UniformRankKernelMachine.Bank (parameters n j c).base.G (parameters n j c).base.gSize
      (gValue n j) entry:=retained_g ret j
  have master:entry.scalarHeap 0=some (prepared (zeta (parameters n j c).base.D)):=by
    change s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n)))
    exact operands_master ops
  obtain ⟨v,t,run,tc,vp,post,frame⟩:=UniformRankCrossReplayPreparationMachine.execution
    (parameters n j c) B n layout (hValue n j) (gValue n j) x entry
    (installedHeaders.1.withPC 0) (installedHeaders.2.withPC 0) entryH entryG master rfl eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed replay_code
    (by rw [UniformRankCrossReplayPreparationMachine.program_length];omega) (by omega) run
  have placedEq:placed 35 entry=installed:=placed_zero installed 35 installedPC
  rw [placedEq] at placedRun
  let u:=setPC v 834
  have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
    (by simp [step,u,setPC,halt_at])
  have total:BoundedExecution program n x B s (t+36) u:=by
    convert first.executes (second.executes (placedRun.executes stop)) using 1
    simp only [sourceSetup_length,headerSetup_length];omega
  have startFrame:=SetupFrame.trans (sourceSetup_frame s) (headerSetup_frame loaded)
  have finalFrame:PreservedFrame n s u:=startFrame.preserved.trans (replay_frame j c fresh frame)
  refine ⟨u,t+36,total,by unfold runtimeBudget;omega,rfl,
    ⟨post.toBasePost.withPC 834,post.buckets.withPC 834,post.negative,post.constants⟩,
    finalFrame.retained ret,finalFrame.protected.metadata metadata,
    finalFrame.protected.operands ops,finalFrame⟩

/-- The source-bank and real-master link also follows from the actual closed
initial-state preparation, without caller-supplied retained banks. Caller header
installation and its835 execution remain the separate theorem above. -/
theorem initial_banks {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (axisCount n)) : ∃t u,
    BoundedExecution UniformAllAxisSeedPreparation.fullProgram n x ((n+2)^19) initial
      (t+UniformAllAxisSeedPreparation.preparationRuntime n+1) u ∧
    UniformRankKernelMachine.Bank (hBase n j) (radix n j) (hValue n j) u ∧
    UniformRankKernelMachine.Bank (gBase n j) (radix n j) (gValue n j) u ∧
    u.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n))) ∧
    Retained n (axisCount n) u ∧ UniformPermutationInversePreparation.Metadata n u ∧
    UniformInitialPreparation.Operands n x u ∧ u.rootOrders=[UniformMasterRootMachine.order n] ∧
    t+UniformAllAxisSeedPreparation.preparationRuntime n+1 ≤ UniformAllAxisSeedPreparation.fullBudget n := by
  obtain ⟨t,u,run,_,ret,metadata,ops,_,_,roots,_,_,cost⟩:=UniformAllAxisSeedPreparation.initial_execution hn x
  exact ⟨t,u,run,retained_h ret j,retained_g ret j,operands_master ops,ret,metadata,ops,roots,cost⟩

end
end ExactFourierCircuits.UniformSeedRankCrossPreparation
