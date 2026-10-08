import UniformSeedChunkPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedChunkAllocation
open UniformAllAxisSeedPreparation (axisCount radix axisBase directoryBase)

/-- Sum of the actual ends of the three retained height-table regions. -/
def heightEnd (c : UniformSeedHeightPreparation.Config) : ℕ :=
  UniformCrossHeightPreparationMachine.rowBase c.height (8*c.exponent+7)+
  UniformCrossHeightPreparationMachine.colorBase c.height (8*c.exponent+7)+
  UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7)

/-- Exactly the fresh coordinates of the old existential allocator. -/
def extend (n : ℕ) (j : Fin (axisCount n)) (c : UniformSeedHeightPreparation.Config) :
    UniformSeedChunkPreparation.Config :=
  ⟨c,heightEnd c,heightEnd c+c.gates,heightEnd c+7*c.gates,
    heightEnd c+9*c.gates,heightEnd c+15*c.gates,
    heightEnd c+15*c.gates+radix n j,heightEnd c+15*c.gates+2*radix n j,
    heightEnd c+15*c.gates+3*radix n j,0,0⟩

lemma height_headroom {n B : ℕ} {j : Fin (axisCount n)}
    {c : UniformSeedHeightPreparation.Config} (h : UniformSeedHeightPreparation.Layout n j c B) :
    heightEnd c+15*c.gates+3*radix n j+4 ≤
      UniformCrossHeightPreparationMachine.wordBudget c.height := by
  have fresh : directoryBase n+2*axisCount n ≤ c.tape := h.oldBanks.tape
  have r : radix n j ≤ UniformInitialPreparation.len n :=
    UniformGlobalLocalPreparation.radix_le_length n j
  rw [UniformAllAxisSeedPreparation.directory_formula] at fresh
  have room : 3*radix n j ≤ 2*c.tape := by omega
  dsimp only [heightEnd,UniformCrossHeightPreparationMachine.wordBudget,
    UniformCrossDepthReplayPreparation.wordBudget,
    UniformCrossHeightPreparationMachine.height]
  change _ ≤ 186+c.exponent+c.width+c.gates+(8*c.exponent+7)+
    c.tape+c.order+c.directory+c.C+c.constants+c.e+c.palette+
    UniformCrossHeightPreparationMachine.rowBase c.height (8*c.exponent+7)+
    UniformCrossHeightPreparationMachine.colorBase c.height (8*c.exponent+7)+
    UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7)+
    (132+c.tape+5*c.gates+c.order+c.gates+c.directory+c.gates+2+
    UniformCrossHeightPreparationMachine.rowBase c.height (8*c.exponent+7)+6*c.gates+0+c.e+1+
    c.gates+c.C+7*c.width+c.constants+2+
    UniformCrossHeightPreparationMachine.colorBase c.height (8*c.exponent+7)+2*c.gates+c.palette+12)
  omega

/-- No enlarged ambient budget: the original height envelope pays for all
    extra physical chunk pools. This installs no machine headers. -/
lemma extend_same_budget {n B : ℕ} {j : Fin (axisCount n)}
    {c : UniformSeedHeightPreparation.Config} (h : UniformSeedHeightPreparation.Layout n j c B)
    (capacity : c.gates+c.e+c.a ≤ radix n j) (code : 1286 ≤ B) :
    UniformSeedChunkPreparation.Layout n j (extend n j c) B := by
  have bound := (height_headroom h).trans h.heightEnvelope
  constructor
  · exact h
  · exact capacity
  · dsimp [extend,heightEnd];omega
  · dsimp [extend,heightEnd];omega
  · dsimp [extend,heightEnd];omega
  · change heightEnd c+c.gates ≤ heightEnd c+c.gates;omega
  · change heightEnd c+c.gates+6*c.gates ≤ heightEnd c+7*c.gates;omega
  · change heightEnd c+7*c.gates+2*c.gates ≤ heightEnd c+9*c.gates;omega
  · change heightEnd c+9*c.gates+6*c.gates ≤ heightEnd c+15*c.gates;omega
  · change heightEnd c+15*c.gates+radix n j ≤ heightEnd c+15*c.gates+radix n j;omega
  · change heightEnd c+15*c.gates+radix n j+radix n j ≤ heightEnd c+15*c.gates+2*radix n j;omega
  · change heightEnd c+15*c.gates+2*radix n j+radix n j ≤ heightEnd c+15*c.gates+3*radix n j;omega
  · exact bound
  · change 0 < 8*c.exponent+7;omega
  · change 0 < 11;decide
  · exact code

/-- A quadratic region size, computed from the original input length. -/
def slot (n : ℕ) : ℕ := 100000*(n+2)^2

lemma slot_global {n : ℕ} (hn : 0 < n) :
    axisBase n (axisCount n) ≤ slot n ∧ directoryBase n+2*axisCount n ≤ slot n := by
  have he : UniformInitialPreparation.ell n ≤ 2*n := by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformInitialPreparation.ell UniformWorkingLength.axisCount
    omega
  have hL : UniformInitialPreparation.len n < 4*n := UniformWorkingLength.workingLength_upper hn
  have hp:=UniformAllAxisSeedPreparation.prefix_bound n (axisCount n) (le_refl _)
  have hprod : (UniformInitialPreparation.ell n+1)*UniformInitialPreparation.len n ≤ (2*n+1)*(4*n) :=
    Nat.mul_le_mul (by omega) (by omega)
  constructor
  · unfold axisBase UniformLocalSeedTableMachine.poolBase
    rw [UniformGlobalLocalPreparation.globalEnd_formula]
    dsimp [slot]
    nlinarith
  · rw [UniformAllAxisSeedPreparation.directory_formula]
    unfold axisCount slot
    nlinarith

lemma slot_canonical {n : ℕ} (hn : 0 < n) : 200*slot n ≤ (n+2)^19 := by
  have hs : 20000000 ≤ (n+2)^17 := by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 17
    norm_num at h
    omega
  unfold slot
  rw [show 19=17+2 by decide,pow_add]
  nlinarith only [Nat.mul_le_mul_right ((n+2)^2) hs]

/-- Explicit scalar/Nat regions. Separate heaps may reuse the same addresses;
    all regions within each heap are ordered and disjoint. -/
def allocate (n a e i0 j0 split : ℕ) (enabled : Bool) : UniformSeedHeightPreparation.Config :=
  ⟨a,e,i0,j0,split,slot n,2*slot n,slot n,3*slot n,2*slot n,3*slot n,
    4*slot n,5*slot n,6*slot n,4*slot n,5*slot n,7*slot n,8*slot n,
    9*slot n,10*slot n,enabled⟩

/-- These inequalities are derived from measured physical capacity, not supplied
    word envelopes or an initialized bank. -/
structure Sizes (n K a e : ℕ) : Prop where
  exponent : K ≤ 4*n
  width : UniformRadixTwoDAG.width K ≤ 4*n
  count : UniformRadixTwoDAG.count K ≤ 4*n
  convolution : UniformConvolutionDAG.total K ≤ 4*n
  gates : 6*(3*K*UniformRadixTwoDAG.width K+2*UniformRadixTwoDAG.width K)+2*a ≤ 4*n
  target : a ≤ 4*n
  source : e ≤ 4*n

lemma capacity_sizes {n a e : ℕ} (hn : 0 < n) (j : Fin (axisCount n))
    (capacity : UniformWorkspacePlanner.gateCount a e+a+e ≤ radix n j) :
    Sizes n (UniformWorkspacePlanner.exponent a e) a e := by
  let K:=UniformWorkspacePlanner.exponent a e
  have r : radix n j ≤ UniformInitialPreparation.len n := UniformGlobalLocalPreparation.radix_le_length n j
  have hL : UniformInitialPreparation.len n < 4*n := UniformWorkingLength.workingLength_upper hn
  have total : UniformConvolutionDAG.total K ≤ 4*n := by
    unfold UniformWorkspacePlanner.gateCount at capacity
    change 6*UniformConvolutionDAG.total K+2*a+a+e ≤ radix n j at capacity
    omega
  have w : UniformRadixTwoDAG.width K ≤ 4*n := by
    dsimp [UniformConvolutionDAG.total] at total
    omega
  have ct : UniformRadixTwoDAG.count K ≤ 4*n := by
    dsimp [UniformConvolutionDAG.total] at total
    omega
  have kg : K ≤ UniformRadixTwoDAG.width K := by
    have p:=UniformCrossDepthReplayPreparation.power_ge_successor K
    rw [UniformRadixTwoDAG.width_eq]
    omega
  have gc : 6*(3*K*UniformRadixTwoDAG.width K+2*UniformRadixTwoDAG.width K)+2*a ≤ 4*n := by
    rw [UniformWorkspacePlanner.gateCount_eq] at capacity
    rw [UniformRadixTwoDAG.width_eq]
    dsimp [K] at *
    omega
  exact ⟨by omega,w,ct,total,gc,by omega,by omega⟩

lemma sizes_arithmetic {n K a e : ℕ} (h : Sizes n K a e) :
    let N:=UniformRadixTwoDAG.width K
    let t:=UniformRadixTwoDAG.count K
    let V:=UniformConvolutionDAG.total K
    let G:=6*(3*K*N+2*N)+2*a
    100*(K+N+t+V+a+e+G+1)+1000 ≤ slot n ∧
    UniformRadixInstructionMachine.cap N t K ≤ slot n ∧
    10000*(N+V+a+e+K+1)^2 ≤ 50*slot n ∧
    G*(G+1) ≤ slot n ∧ 6*G*(8*K+7) ≤ slot n := by
  intro N t V G
  have k:K ≤ 4*n:=h.exponent
  have w:N ≤ 4*n:=h.width
  have ct:t ≤ 4*n:=h.count
  have cv:V ≤ 4*n:=h.convolution
  have g:G ≤ 4*n:=h.gates
  have a':a ≤ 4*n:=h.target
  have e':e ≤ 4*n:=h.source
  have cp : (N+t+K+1)^2 ≤ (12*n+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have tp : (N+V+a+e+K+1)^2 ≤ (20*n+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have gp : G*(G+1) ≤ (4*n)*(4*n+1) := Nat.mul_le_mul g (by omega)
  have hp : (6*G)*(8*K+7) ≤ (24*n)*(32*n+7) := Nat.mul_le_mul (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold slot;nlinarith
  · unfold UniformRadixInstructionMachine.cap
    calc
      100*(N+t+K+1)^2+200 ≤ 100*(12*n+1)^2+200:=Nat.add_le_add_right (Nat.mul_le_mul_left 100 cp) 200
      _ ≤ slot n:=by unfold slot;nlinarith
  · calc
      10000*(N+V+a+e+K+1)^2 ≤ 10000*(20*n+1)^2:=Nat.mul_le_mul_left 10000 tp
      _ ≤ 50*slot n:=by unfold slot;nlinarith
  · unfold slot;nlinarith only [gp]
  · unfold slot;nlinarith only [hp]

/-- Construct the full seed-height layout from actual retained bank ends and
    ordinary measured chunk geometry. No target layout or budget premise. -/
lemma allocate_layout {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n))
    (a e i0 j0 split : ℕ) (enabled : Bool)
    (ha : 0 < a) (he : 0 < e) (hRows : i0+a ≤ radix n j)
    (hSplit : split < radix n j) (hInterior : split ≤ i0) (hColumns : j0+e ≤ split)
    (capacity : UniformWorkspacePlanner.gateCount a e+a+e ≤ radix n j) :
    UniformSeedHeightPreparation.Layout n j (allocate n a e i0 j0 split enabled) ((n+2)^19) := by
  let K:=UniformWorkspacePlanner.exponent a e
  let N:=UniformRadixTwoDAG.width K
  let t:=UniformRadixTwoDAG.count K
  let V:=UniformConvolutionDAG.total K
  let G:=6*(3*K*N+2*N)+2*a
  let u:=slot n
  have sizes:=capacity_sizes hn j capacity
  obtain ⟨linear,cap,top,order,rows⟩:=sizes_arithmetic sizes
  change 100*(K+N+t+V+a+e+G+1)+1000 ≤ u at linear
  change UniformRadixInstructionMachine.cap N t K ≤ u at cap
  change 10000*(N+V+a+e+K+1)^2 ≤ 50*u at top
  change G*(G+1) ≤ u at order
  change 6*G*(8*K+7) ≤ u at rows
  have final : 200*u ≤ (n+2)^19:=slot_canonical hn
  obtain ⟨pool,dir⟩:=slot_global hn
  change axisBase n (axisCount n) ≤ u at pool
  change directoryBase n+2*axisCount n ≤ u at dir
  have endAxis:=UniformAllAxisSeedPreparation.axisBase_mono n
    (show j.val+1 ≤ axisCount n by omega)
  rw [UniformAllAxisSeedPreparation.axisBase_next] at endAxis
  have hg : UniformSeedRankCrossPreparation.gBase n j+radix n j ≤ u := by
    dsimp [UniformSeedRankCrossPreparation.gBase]
    omega
  have hh : UniformSeedRankCrossPreparation.hBase n j+radix n j ≤ u := by
    dsimp [UniformSeedRankCrossPreparation.hBase]
    omega
  have positive : 0 < u := by omega
  constructor
  · exact ha
  · exact he
  · exact hRows
  · exact hSplit
  · exact hInterior
  · exact hColumns
  · exact hh
  · exact hg
  · exact positive
  · change u+6*N ≤ (n+2)^19;omega
  · change u+6*N ≤ 2*u;omega
  · change 0 < 2*u;omega
  · change UniformPreparedFFTMachine.rootAddress K (2*u)+1 ≤ 3*u
    dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
    change 2*u+N+t+5*N+4+1 ≤ 3*u
    omega
  · change UniformKernelSpectrumMachine.wordBudget K u (2*u) u (3*u) ≤ (n+2)^19
    have shape : UniformKernelSpectrumMachine.wordBudget K u (2*u) u (3*u)=
        12*u+UniformRadixInstructionMachine.cap N t K+8*t+14*N+850 := by
      dsimp only [UniformKernelSpectrumMachine.wordBudget,UniformPreparedFFTMachine.wordBudget,
        UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
      change _=12*u+UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K)
        (UniformRadixTwoDAG.count K) K+8*UniformRadixTwoDAG.count K+14*UniformRadixTwoDAG.width K+850
      ring
    rw [shape]
    omega
  · change 2*u+5*V ≤ 3*u;omega
  · change UniformToeplitzCrossTopologyMachine.budget K a e (2*u) (3*u) ≤ (n+2)^19
    have shape : UniformToeplitzCrossTopologyMachine.budget K a e (2*u) (3*u)=
        5*u+35*V+10*a+UniformRadixInstructionMachine.cap N t K+
        10000*(N+V+a+e+K+1)^2 := by
      dsimp only [UniformToeplitzCrossTopologyMachine.budget,UniformToeplitzCrossTopologyMachine.G]
      ring
    rw [shape]
    omega
  · change 3*u+5*G ≤ 4*u;omega
  · change 4*u+e+1+G ≤ (n+2)^19;omega
  · change u+3*t ≤ 5*u;omega
  · change 4*u+e+1+G ≤ 5*u;omega
  · change 5*u+G*(G+1) ≤ 6*u;omega
  · change 6*u+G+2 ≤ (n+2)^19;omega
  · change 3*u+7*N+1 ≤ 4*u;omega
  · change 4*u+7*N ≤ 5*u;omega
  · change 5*u+6 ≤ (n+2)^19;omega
  · constructor
    · change directoryBase n+2*axisCount n ≤ u;exact dir
    · change directoryBase n+2*axisCount n ≤ 2*u;omega
    · change directoryBase n+2*axisCount n ≤ 3*u;omega
    · change directoryBase n+2*axisCount n ≤ 4*u;omega
    · change directoryBase n+2*axisCount n ≤ 5*u;omega
    · change directoryBase n+2*axisCount n ≤ 6*u;omega
    · exact pool
    · change axisBase n (axisCount n) ≤ 2*u;omega
    · change axisBase n (axisCount n) ≤ 3*u;omega
    · change axisBase n (axisCount n) ≤ 4*u;omega
    · change axisBase n (axisCount n) ≤ 5*u;omega
  · constructor
    · change 3*u+5*G ≤ 7*u;omega
    · change 5*u+G ≤ 7*u;omega
    · change 6*u+G+2 ≤ 7*u;omega
    · change 7*u+6*G*(8*K+7) ≤ 8*u;omega
    · change 8*u+2*G*(8*K+7) ≤ 9*u;nlinarith only [rows]
    · change 9*u+12 ≤ 10*u;omega
  · change UniformCrossHeightPreparationMachine.wordBudget
      (⟨K,a,e,3*u,5*u,6*u,7*u,8*u,9*u,10*u,3*u,5*u,enabled⟩) ≤ (n+2)^19
    have shape : UniformCrossHeightPreparationMachine.wordBudget
        (⟨K,a,e,3*u,5*u,6*u,7*u,8*u,9*u,10*u,3*u,5*u,enabled⟩)=
        102*u+16*G*(8*K+7)+K+8*N+17*G+4*(8*K+7)+2*e+335 := by
      dsimp only [UniformCrossHeightPreparationMachine.wordBudget,
        UniformCrossDepthReplayPreparation.wordBudget,UniformCrossHeightPreparationMachine.rowBase,
        UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.recordBase,
        UniformCrossHeightPreparationMachine.height,UniformCrossHeightPreparationMachine.gates,
        UniformCrossHeightPreparationMachine.widthOf]
      ring
    rw [shape]
    nlinarith only [rows,linear,final]
  · omega

/-- The complete seed/chunk allocation is computable, with all coordinates
    determined by input length, selected radix and ordinary chunk parameters. -/
def chunk (n : ℕ) (j : Fin (axisCount n)) (a e i0 j0 split : ℕ) (enabled : Bool) :=
  extend n j (allocate n a e i0 j0 split enabled)

lemma allocated_gates (n a e i0 j0 split : ℕ) (enabled : Bool) :
    (allocate n a e i0 j0 split enabled).gates=UniformWorkspacePlanner.gateCount a e := by
  dsimp only [allocate,UniformSeedHeightPreparation.Config.gates,
    UniformSeedHeightPreparation.Config.exponent,UniformSeedHeightPreparation.Config.width]
  rw [UniformWorkspacePlanner.gateCount_eq,UniformRadixTwoDAG.width_eq]

/-- Actual constructive layout at exactly the global machine word budget. -/
lemma chunk_layout {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n))
    (a e i0 j0 split : ℕ) (enabled : Bool)
    (ha : 0 < a) (he : 0 < e) (hRows : i0+a ≤ radix n j)
    (hSplit : split < radix n j) (hInterior : split ≤ i0) (hColumns : j0+e ≤ split)
    (capacity : UniformWorkspacePlanner.gateCount a e+a+e ≤ radix n j) :
    UniformSeedChunkPreparation.Layout n j (chunk n j a e i0 j0 split enabled) ((n+2)^19) := by
  apply extend_same_budget
    (allocate_layout hn j a e i0 j0 split enabled ha he hRows hSplit hInterior hColumns capacity)
  · change (allocate n a e i0 j0 split enabled).gates+e+a ≤ radix n j
    rw [allocated_gates]
    omega
  · have big:=slot_canonical hn
    have small : 1286 ≤ 200*slot n := by unfold slot;nlinarith
    exact small.trans big

/-- The capacity condition is nonvacuous on a genuine selected axis, with
    nonempty source and target chunks; no startup array is materialized. -/
lemma exists_selected_unit_layout : ∃n,0 < n ∧ ∃j:Fin (axisCount n),
    UniformSeedChunkPreparation.Layout n j (chunk n j 1 1 1 0 1 false) ((n+2)^19) := by
  obtain ⟨n,hn,j,capacity⟩:=UniformSeedChunkPreparation.exists_selected_capacity
  have gc : UniformWorkspacePlanner.gateCount 1 1+1+1=196 := by decide
  refine ⟨n,hn,j,chunk_layout hn j 1 1 1 0 1 false (by decide) (by decide)
    (by omega) (by omega) (by omega) (by omega) ?_⟩
  simpa only [gc] using capacity

end ExactFourierCircuits.UniformSeedChunkAllocation
