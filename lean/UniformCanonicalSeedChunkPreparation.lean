import UniformSeedChunkAllocation
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalSeedChunkPreparation
open UniformMachine UniformAssembly
open UniformAllAxisSeedPreparation (axisCount radix Retained)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformSeedChunkAllocation (slot allocate)

/-- Ordinary selected-axis geometry and bucket choice. No allocation pointers,
    exponent, bank, row table or helper-readiness predicate is an input. -/
structure Parameters where
  a : ℕ
  e : ℕ
  i0 : ℕ
  j0 : ℕ
  split : ℕ
  enabled : Bool
  layer : ℕ
  color : ℕ

def seed (n : ℕ) (p : Parameters) := allocate n p.a p.e p.i0 p.j0 p.split p.enabled

/-- Fixed-pool offsets avoid recomputing K for address allocation. -/
def config (n : ℕ) (p : Parameters) : UniformSeedChunkPreparation.Config :=
  ⟨seed n p,30*slot n,31*slot n,32*slot n,33*slot n,34*slot n,
    35*slot n,36*slot n,37*slot n,p.layer,p.color⟩

structure Valid (n : ℕ) (j : Fin (axisCount n)) (p : Parameters) : Prop where
  target : 0 < p.a
  source : 0 < p.e
  rows : p.i0+p.a ≤ radix n j
  split : p.split < radix n j
  interior : p.split ≤ p.i0
  columns : p.j0+p.e ≤ p.split
  capacity : UniformWorkspacePlanner.gateCount p.a p.e+p.a+p.e ≤ radix n j
  layer : p.layer < 8*UniformWorkspacePlanner.exponent p.a p.e+7
  color : p.color < 11

lemma radix_slot {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) : radix n j ≤ slot n := by
  have r : radix n j ≤ UniformInitialPreparation.len n := UniformGlobalLocalPreparation.radix_le_length n j
  have L : UniformInitialPreparation.len n < 4*n := UniformWorkingLength.workingLength_upper hn
  unfold slot
  nlinarith

lemma code_bound {n : ℕ} (hn : 0 < n) : 1317 ≤ (n+2)^19 := by
  have b:=UniformSeedChunkAllocation.slot_canonical hn
  have small : 1317 ≤ 200*slot n := by unfold slot;nlinarith
  exact small.trans b

lemma layout {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (p : Parameters)
    (h : Valid n j p) : UniformSeedChunkPreparation.Layout n j (config n p) ((n+2)^19) := by
  let K:=UniformWorkspacePlanner.exponent p.a p.e
  let N:=UniformRadixTwoDAG.width K
  let t:=UniformRadixTwoDAG.count K
  let V:=UniformConvolutionDAG.total K
  let G:=6*(3*K*N+2*N)+2*p.a
  let u:=slot n
  have base:=UniformSeedChunkAllocation.allocate_layout hn j p.a p.e p.i0 p.j0 p.split p.enabled
    h.target h.source h.rows h.split h.interior h.columns h.capacity
  obtain ⟨linear,_,_,_,rows⟩:=UniformSeedChunkAllocation.sizes_arithmetic
    (UniformSeedChunkAllocation.capacity_sizes hn j h.capacity)
  change 100*(K+N+t+V+p.a+p.e+G+1)+1000 ≤ u at linear
  change 6*G*(8*K+7) ≤ u at rows
  have r : radix n j ≤ u:=radix_slot hn j
  have bound : 200*u ≤ (n+2)^19:=UniformSeedChunkAllocation.slot_canonical hn
  have gc : (seed n p).gates=UniformWorkspacePlanner.gateCount p.a p.e :=
    UniformSeedChunkAllocation.allocated_gates _ _ _ _ _ _ _
  constructor
  · exact base
  · change (seed n p).gates+p.e+p.a ≤ radix n j;rw [gc];have :=h.capacity;omega
  · change 7*u+6*G*(8*K+7) ≤ 30*u;omega
  · change 8*u+2*G*(8*K+7) ≤ 30*u;nlinarith only [rows]
  · change 10*u+3*(8*K+7) ≤ 30*u;omega
  · change 30*u+G ≤ 31*u;omega
  · change 31*u+6*G ≤ 32*u;omega
  · change 32*u+2*G ≤ 33*u;omega
  · change 33*u+6*G ≤ 34*u;omega
  · change 34*u+radix n j ≤ 35*u;omega
  · change 35*u+radix n j ≤ 36*u;omega
  · change 36*u+radix n j ≤ 37*u;omega
  · change 37*u+4 ≤ (n+2)^19;omega
  · exact h.layer
  · exact h.color
  · have :=code_bound hn;omega

/-- Thirty charged arithmetic/header instructions; the saved n is read from
    register101. Every allocation header may initially contain dirty values. -/
def sizing : List Op := [
  .literal 1801 2,.add 1802 101 1801,.mul 1803 1802 1802,
  .literal 1804 100000,.mul 1800 1803 1804,.literal 1805 0]

def seedPointers : List Op := [
  .add 1127 1800 1805,.add 1128 1127 1800,.add 1129 1127 1805,
  .add 1130 1128 1800,.add 1131 1128 1805,.add 1132 1130 1805,
  .add 1133 1130 1800,.add 1134 1133 1800,.add 1135 1134 1800,
  .add 1136 1133 1805,.add 1137 1134 1805,
  .add 1220 1135 1800,.add 1221 1220 1800,.add 1222 1221 1800,.add 1223 1222 1800]

def chunkPointers : List Op := [
  .literal 1806 30,.mul 1230 1800 1806,.add 1231 1230 1800,.add 1232 1231 1800,
  .add 1233 1232 1800,.add 1234 1233 1800,.add 1235 1234 1800,.add 1236 1235 1800,
  .add 1237 1236 1800]

def head : List Op := sizing++seedPointers++chunkPointers

def headerProgram : Program := head.map Op.code++[.halt]
def program : Program := head.map Op.code++
  UniformSeedChunkPreparation.program.map (relocate 30 1316)++[.halt]

lemma head_length : head.length=30 := rfl
lemma headerProgram_length : headerProgram.length=31 := rfl
lemma program_length : program.length=1317 := by
  simp [program,head_length,UniformSeedChunkPreparation.program_length]
lemma head_code : BlockAt head program 0 := by
  intro i hi;change i < 30 at hi;interval_cases i <;> rfl
lemma chunk_code : CodeAt UniformSeedChunkPreparation.program program 30 1316 :=
  UniformRankCrossPreparationMachine.segment_code (head.map Op.code) [.halt]
    UniformSeedChunkPreparation.program 30 1316 (by simp [head_length])
lemma halt_at : program[1316]?=some .halt := by
  rw [program,List.getElem?_append_right
    (by simp [head_length,UniformSeedChunkPreparation.program_length])]
  simp [head_length,UniformSeedChunkPreparation.program_length]

noncomputable section

structure Args (n : ℕ) (j : Fin (axisCount n)) (p : Parameters) (s : State) : Prop where
  axis : s.natReg 1120=j.val
  target : s.natReg 1122=p.a
  source : s.natReg 1123=p.e
  targetOffset : s.natReg 1124=p.i0
  sourceOffset : s.natReg 1125=p.j0
  split : s.natReg 1126=p.split
  enabled : s.natReg 1224=if p.enabled then 1 else 0
  layer : s.natReg 1238=p.layer
  color : s.natReg 1239=p.color

def Protected (q : ℕ) : Prop :=
  (q < 1127 ∨ 1138 ≤ q) ∧ (q < 1220 ∨ 1224 ≤ q) ∧
  (q < 1230 ∨ 1238 ≤ q) ∧ (q < 1800 ∨ 1807 ≤ q)
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀q,Protected q→u.natReg q=s.natReg q

lemma head_frame (s : State) : Frame s (applyBlock head s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  unfold Protected at hq
  simp (disch:=omega) [head,sizing,seedPointers,chunkPointers,applyBlock,Op.apply,writeNat,next]

lemma Frame.preserved {n : ℕ} {s u : State} (f : Frame s u) :
    UniformSeedRankCrossPreparation.PreservedFrame n s u :=
  ⟨fun q _=>congrFun f.1 q,fun q _=>congrFun f.2.1 q,
    fun q lo hi=>f.2.2.2.2.2 q (by unfold Protected;omega),f.2.2.2.1,f.2.2.2.2.1⟩

lemma head_safe {n : ℕ} (s : State) (hn : s.natReg 101=n) :
    readable head s ∧ peak head s ≤ 200*slot n := by
  constructor
  · simp [head,sizing,seedPointers,chunkPointers,readable,Op.readable]
  · simp [head,sizing,seedPointers,chunkPointers,peak,Op.peak,Op.apply,writeNat,next,hn]
    repeat' apply And.intro
    all_goals
      have sq : (n+2)*(n+2)*100000=slot n := by unfold slot;ring
      have c : 100000 ≤ slot n := by unfold slot;nlinarith
      have n' : n+2 ≤ slot n := by unfold slot;nlinarith
      have q : (n+2)*(n+2) ≤ slot n := by unfold slot;nlinarith
      try simp only [sq]
      omega


structure SlotReady (n : ℕ) (s : State) : Prop where
  value : s.natReg 1800=slot n
  zero : s.natReg 1805=0

lemma sizing_spec {n : ℕ} (s : State) (saved : s.natReg 101=n) :
    SlotReady n (applyBlock sizing s) := by
  constructor
  all_goals simp [sizing,applyBlock,Op.apply,writeNat,next,saved,slot] <;> ring

lemma seedPointers_frame (s : State) (q : ℕ)
    (hq : (q < 1127 ∨ 1138 ≤ q) ∧ (q < 1220 ∨ 1224 ≤ q)) :
    (applyBlock seedPointers s).natReg q=s.natReg q := by
  simp (disch:=omega) [seedPointers,applyBlock,Op.apply,writeNat,next]

lemma chunkPointers_frame (s : State) (q : ℕ)
    (hq : (q < 1230 ∨ 1238 ≤ q) ∧ q≠1806) :
    (applyBlock chunkPointers s).natReg q=s.natReg q := by
  simp (disch:=omega) [chunkPointers,applyBlock,Op.apply,writeNat,next]

lemma seedPointers_slot {n : ℕ} {s : State} (h : SlotReady n s) :
    SlotReady n (applyBlock seedPointers s) := by
  refine ⟨?_,?_⟩
  · exact (seedPointers_frame s 1800 (by omega)).trans h.value
  · exact (seedPointers_frame s 1805 (by omega)).trans h.zero

lemma seedPointers_core {n : ℕ} (p : Parameters) (s : State) (h : SlotReady n s)
    (q : ℕ) (lo : 1127 ≤ q) (hi : q ≤ 1137) :
    (applyBlock seedPointers s).natReg q=(seed n p).register q := by
  interval_cases q <;>
    simp [seedPointers,applyBlock,Op.apply,writeNat,next,h.value,h.zero,
      seed,allocate,UniformSeedHeightPreparation.Config.register,
      UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] <;> ring

lemma seedPointers_height {n : ℕ} (p : Parameters) (s : State) (h : SlotReady n s)
    (q : ℕ) (lo : 1220 ≤ q) (hi : q ≤ 1223) :
    (applyBlock seedPointers s).natReg q=(seed n p).register q := by
  interval_cases q <;>
    simp [seedPointers,applyBlock,Op.apply,writeNat,next,h.value,h.zero,
      seed,allocate,UniformSeedHeightPreparation.Config.register] <;> ring

lemma chunkPointers_spec {n : ℕ} (p : Parameters) (s : State) (h : SlotReady n s)
    (q : ℕ) (lo : 1230 ≤ q) (hi : q ≤ 1237) :
    (applyBlock chunkPointers s).natReg q=(config n p).register q := by
  interval_cases q <;>
    simp [chunkPointers,applyBlock,Op.apply,writeNat,next,h.value,
      config,UniformSeedChunkPreparation.Config.register] <;> ring

lemma head_apply (s : State) : applyBlock head s=
    applyBlock chunkPointers (applyBlock seedPointers (applyBlock sizing s)) := by
  simp only [head,UniformSeedChunkPreparation.applyBlock_append]

lemma installed_args {n : ℕ} (j : Fin (axisCount n)) (p : Parameters) (s : State)
    (h : Args n j p s) (saved : s.natReg 101=n) :
    UniformSeedChunkPreparation.Args n j (config n p) (setPC (applyBlock head s) 0) := by
  let u:=applyBlock sizing s
  let v:=applyBlock seedPointers u
  have su : SlotReady n u:=sizing_spec s saved
  have sv : SlotReady n v:=seedPointers_slot su
  have unchanged : ∀q,Protected q→(setPC (applyBlock head s) 0).natReg q=s.natReg q :=
    (head_frame s).2.2.2.2.2
  constructor
  · refine ⟨(unchanged 1120 (by unfold Protected;omega)).trans h.axis,?_,?_⟩
    · intro q lo hi
      by_cases old : q ≤ 1126
      · rw [unchanged q (by unfold Protected;omega)]
        interval_cases q <;> simp [config,seed,allocate,UniformSeedHeightPreparation.Config.register,
          UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register,
          h.target,h.source,h.targetOffset,h.sourceOffset,h.split]
      · change (applyBlock head s).natReg q=(seed n p).register q
        rw [head_apply,chunkPointers_frame v q (by omega)]
        exact seedPointers_core p u su q (by omega) hi
    · intro q lo hi
      by_cases old : q=1224
      · subst q
        rw [unchanged 1224 (by unfold Protected;omega)]
        exact h.enabled
      · change (applyBlock head s).natReg q=(seed n p).register q
        rw [head_apply,chunkPointers_frame v q (by omega)]
        exact seedPointers_height p u su q lo (by omega)
  · intro q lo hi
    by_cases old : 1238 ≤ q
    · rw [unchanged q (by unfold Protected;omega)]
      interval_cases q <;> simp [config,UniformSeedChunkPreparation.Config.register,h.layer,h.color]
    · change (applyBlock head s).natReg q=(config n p).register q
      rw [head_apply]
      exact chunkPointers_spec p v sv q lo (by omega)

lemma args_fromPC {n q : ℕ} {j : Fin (axisCount n)} {c : UniformSeedChunkPreparation.Config}
    {s : State} (h : UniformSeedChunkPreparation.Args n j c (setPC s q)) :
    UniformSeedChunkPreparation.Args n j c s := by
  rcases h with ⟨⟨index,core,height⟩,extra⟩
  exact ⟨⟨index,core,height⟩,extra⟩

lemma result_withPC {n B : ℕ} {j : Fin (axisCount n)} {c : UniformSeedChunkPreparation.Config}
    {hn : 0 < n} {h : UniformSeedChunkPreparation.Layout n j c B} {s : State}
    (post : UniformSeedChunkPreparation.Result n j c B hn h s) (q : ℕ) :
    UniformSeedChunkPreparation.Result n j c B hn h (setPC s q) := by
  constructor
  · exact ⟨post.prepared.source.withPC,post.prepared.cursor.withPC,post.prepared.processed,
      post.prepared.positive,post.prepared.root,post.prepared.negative,post.prepared.constants⟩
  · exact post.header.withPC q
  · exact post.count
  · exact post.rows
  · exact post.widths
  · exact post.permutations
  · exact post.mapped

lemma header_code : BlockAt head headerProgram 0 := by
  intro i hi;change i < 30 at hi;interval_cases i <;> rfl
lemma header_halt : headerProgram[30]?=some .halt := rfl

/-- This standalone preparation phase also covers small actual inputs whose
    selected axes cannot fit a nonempty cross. All allocation writes are charged. -/
theorem header_execution {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (p : Parameters)
    (x : Fin n→ℂ) (s : State) (args : Args n j p s)
    (metadata : UniformPermutationInversePreparation.Metadata n s)
    (pc : s.pc=0) (hs : WordBound ((n+2)^19) s) :
    ∃u,BoundedExecution headerProgram n x ((n+2)^19) s 31 u ∧ u.pc=30 ∧
      UniformSeedChunkPreparation.Args n j (config n p) u ∧ Frame s u := by
  have B:=code_bound hn
  have safe:=head_safe s metadata.saved.inputLength
  have run:=block_runs head headerProgram 0 n ((n+2)^19) x s header_code pc hs
    (by rw [head_length];omega) safe.1
    (safe.2.trans (UniformSeedChunkAllocation.slot_canonical hn))
  let u:=applyBlock head s
  have up : u.pc=30 := by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,head_length]
  have stop : BoundedExecution headerProgram n x ((n+2)^19) u 1 u :=
    .halt run.final_bound (by simp [step,up,header_halt])
  refine ⟨u,?_,up,?_,head_frame s⟩
  · simpa only [head_length] using run.executes stop
  · exact args_fromPC (installed_args j p s args metadata.saved.inputLength)

def runtimeBudget (n : ℕ) (j : Fin (axisCount n)) (p : Parameters) : ℕ :=
  UniformSeedChunkPreparation.runtimeBudget n j (config n p)+31

/-- Actual continuous canonical allocation/header preparation and the entire
    seed/chunk producer. Only original retained inputs and ordinary geometry
    are supplied; every generated readiness/table predicate is derived. -/
theorem execution {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (p : Parameters)
    (good : Valid n j p) (x : Fin n→ℂ) (s : State) (args : Args n j p s)
    (metadata : UniformPermutationInversePreparation.Metadata n s)
    (ret : Retained n (axisCount n) s) (ops : UniformInitialPreparation.Operands n x s)
    (pc : s.pc=0) (hs : WordBound ((n+2)^19) s) : ∃u t,
    BoundedExecution program n x ((n+2)^19) s t u ∧ t ≤ runtimeBudget n j p ∧ u.pc=1316 ∧
    UniformSeedChunkPreparation.Result n j (config n p) ((n+2)^19) hn (layout hn j p good) u ∧
    Retained n (axisCount n) u ∧ UniformPermutationInversePreparation.Metadata n u ∧
    UniformInitialPreparation.Operands n x u ∧ UniformSeedRankCrossPreparation.PreservedFrame n s u := by
  have B:=code_bound hn
  have safe:=head_safe s metadata.saved.inputLength
  have first:=block_runs head program 0 n ((n+2)^19) x s head_code pc hs
    (by rw [head_length];omega) safe.1
    (safe.2.trans (UniformSeedChunkAllocation.slot_canonical hn))
  let v:=applyBlock head s
  have vp : v.pc=30 := by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,head_length]
  let entry:=setPC v 0
  have eb : WordBound ((n+2)^19) entry:=changePC_bound _ v 0 first.final_bound (by omega)
  have old : UniformSeedRankCrossPreparation.PreservedFrame n s entry:=(head_frame s).preserved
  have startProtected:=old.protected
  obtain ⟨z,t,run,cost,_,post,_,_,_,frame⟩:=
    UniformSeedChunkPreparation.execution hn j (config n p) ((n+2)^19) x entry
      (installed_args j p s args metadata.saved.inputLength) (startProtected.metadata metadata)
      (old.retained ret) (startProtected.operands ops) (layout hn j p good) rfl eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed chunk_code
    (by rw [UniformSeedChunkPreparation.program_length];omega) (by omega) run
  rw [UniformSeedRankCrossPreparation.placed_zero v 30 vp] at placedRun
  let u:=setPC z 1316
  have stop : BoundedExecution program n x ((n+2)^19) u 1 u:=
    .halt placedRun.final_bound (by simp [step,u,setPC,halt_at])
  have all : BoundedExecution program n x ((n+2)^19) s (30+t+1) u := by
    simpa only [head_length,Nat.add_assoc] using first.executes (placedRun.executes stop)
  have full : UniformSeedRankCrossPreparation.PreservedFrame n s u:=old.trans frame
  refine ⟨u,30+t+1,all,?_,rfl,result_withPC post 1316,full.retained ret,full.protected.metadata metadata,
    full.protected.operands ops,full⟩
  unfold runtimeBudget
  omega

/-- A genuine selected-axis nonempty input contract for the continuous caller. -/
lemma exists_selected_valid : ∃n,0 < n ∧ ∃j:Fin (axisCount n),
    Valid n j ⟨1,1,1,0,1,false,0,0⟩ := by
  obtain ⟨n,hn,j,capacity⟩:=UniformSeedChunkPreparation.exists_selected_capacity
  have cg : UniformWorkspacePlanner.gateCount 1 1+1+1=196 := by decide
  refine ⟨n,hn,j,⟨by decide,by decide,by dsimp;omega,by dsimp;omega,by dsimp;omega,by dsimp;omega,?_,by decide,by decide⟩⟩
  simpa only [cg] using capacity

end
end ExactFourierCircuits.UniformCanonicalSeedChunkPreparation
