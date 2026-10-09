import UniformJointCacheAllocation
import UniformLocalRectanglePhaseBanks
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointCacheWorkspace
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRectangleDescriptors
abbrev stride (n : ℕ) : ℕ := (n+2)^19
abbrev budget (n : ℕ) : ℕ := 2000*stride n
/-- Only ordinary measured geometry from a genuine rectangle row. -/
structure Geometry (n : ℕ) (j : Fin (axisCount n)) (q : Row) : Prop where
 positiveA : 0 < q.a
 positiveE : 0 < q.e
 hRows : q.i0+q.a ≤ radix n j
 gSplit : q.split < radix n j
 interior : q.split ≤ q.i0
 columns : q.j0+q.e ≤ q.split
 capacity : UniformWorkspacePlanner.gateCount q.a q.e+q.a+q.e ≤ radix n j
/-- Reused addresses depend only on input length; geometry is loaded from the row. -/
def original (n : ℕ) (q : Row) : UniformSeedHeightPreparation.Config :=
 let u:=stride n
 ⟨q.a,q.e,q.i0,q.j0,q.split,2*u,3*u,2*u,4*u,3*u,4*u,5*u,
  6*u,7*u,5*u,6*u,8*u,9*u,10*u,11*u,true⟩
def work (n : ℕ) : UniformRankCrossPreparationMachine.Parameters :=
 let u:=stride n
 ⟨0,0,0,0,0,0,0,0,0,0,8*u,9*u,13*u,10*u,0,14*u,15*u,16*u⟩
abbrev lowRow (n : ℕ) := stride n
abbrev conjugate (n : ℕ) := 11*stride n
abbrev control (n : ℕ) := 17*stride n
abbrev falseRows (n : ℕ) := 18*stride n
abbrev falseColors (n : ℕ) := 19*stride n
abbrev falsePalette (n : ℕ) := 20*stride n
abbrev falseDirectory (n : ℕ) := 21*stride n
abbrev borrowed (n : ℕ) := 23*stride n
abbrev selected (n : ℕ) := 24*stride n
abbrev ordinals (n : ℕ) := 25*stride n
abbrev mapped (n : ℕ) := 26*stride n
abbrev permutation (n : ℕ) := 27*stride n
abbrev widths (n : ℕ) := 28*stride n
abbrev markers (n : ℕ) := 29*stride n
abbrev axis (n : ℕ) := 30*stride n
abbrev translated (n : ℕ) := 31*stride n
abbrev inverse (n : ℕ) := 32*stride n
lemma arithmetic {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row) (g : Geometry n j q) :
 let c:=original n q
 let K:=c.exponent
 let N:=c.width
 let t:=UniformRadixTwoDAG.count K
 let V:=UniformConvolutionDAG.total K
 let G:=c.gates
 100*(K+N+t+V+q.a+q.e+G+1)+1000 ≤ stride n ∧
 UniformRadixInstructionMachine.cap N t K ≤ stride n ∧
 10000*(N+V+q.a+q.e+K+1)^2 ≤ 50*stride n ∧
 G*(G+1) ≤ stride n ∧ 6*G*(8*K+7) ≤ stride n := by
 intro c K N t V G
 have h:=UniformSeedChunkAllocation.sizes_arithmetic
  (UniformSeedChunkAllocation.capacity_sizes hn j g.capacity)
 have small : UniformSeedChunkAllocation.slot n ≤ stride n := by
  have h:=UniformSeedChunkAllocation.slot_canonical hn
  change 200*UniformSeedChunkAllocation.slot n ≤ stride n at h
  omega
 dsimp only [c,K,N,t,V,G,original,UniformSeedHeightPreparation.Config.exponent,
  UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.gates] at *
 exact ⟨h.1.trans small,h.2.1.trans small,
  h.2.2.1.trans (Nat.mul_le_mul_left 50 small),h.2.2.2.1.trans small,h.2.2.2.2.trans small⟩
lemma retained {n : ℕ} (hn : 0 < n) :
 UniformAllAxisSeedPreparation.axisBase n (axisCount n) ≤ stride n ∧
 UniformAllAxisConjugatePreparation.axisBase n (axisCount n) ≤ stride n ∧
 UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n ≤ stride n ∧
 UniformConjugateRankSpectrumPreparation.dirEnd n ≤ stride n := by
 obtain ⟨_,a,b⟩:=UniformAllAxisSeedPreparation.word_setup hn
 obtain ⟨_,c,d⟩:=UniformAllAxisConjugatePreparation.word_setup hn
 exact ⟨a,c,b,d⟩
lemma original_layout {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) : UniformSeedHeightPreparation.Layout n j (original n q) (budget n) := by
 let c:=original n q
 let K:=c.exponent
 let N:=c.width
 let t:=UniformRadixTwoDAG.count K
 let V:=UniformConvolutionDAG.total K
 let G:=c.gates
 let u:=stride n
 obtain ⟨linear,cap,top,ord,rows⟩:=arithmetic hn j q g
 change 100*(K+N+t+V+q.a+q.e+G+1)+1000 ≤ u at linear
 change UniformRadixInstructionMachine.cap N t K ≤ u at cap
 change 10000*(N+V+q.a+q.e+K+1)^2 ≤ 50*u at top
 change G*(G+1) ≤ u at ord
 change 6*G*(8*K+7) ≤ u at rows
 obtain ⟨pool,_,dir,_⟩:=retained hn
 change _ ≤ u at pool dir
 have endAxis:=UniformAllAxisSeedPreparation.axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
 rw [UniformAllAxisSeedPreparation.axisBase_next] at endAxis
 have hh : UniformSeedRankCrossPreparation.hBase n j+radix n j ≤ 2*u := by
  dsimp [UniformSeedRankCrossPreparation.hBase];omega
 have hg : UniformSeedRankCrossPreparation.gBase n j+radix n j ≤ 2*u := by
  dsimp [UniformSeedRankCrossPreparation.gBase];omega
 constructor
 · exact g.positiveA
 · exact g.positiveE
 · exact g.hRows
 · exact g.gSplit
 · exact g.interior
 · exact g.columns
 · exact hh
 · exact hg
 · change 0 < 2*u;omega
 · change 2*u+6*N ≤ 2000*u;omega
 · change 2*u+6*N ≤ 3*u;omega
 · change 0 < 3*u;omega
 · change UniformPreparedFFTMachine.rootAddress K (3*u)+1 ≤ 4*u
   dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
   change 3*u+N+t+5*N+4+1 ≤ 4*u;omega
 · change UniformKernelSpectrumMachine.wordBudget K (2*u) (3*u) (2*u) (4*u) ≤ 2000*u
   dsimp only [UniformKernelSpectrumMachine.wordBudget,UniformPreparedFFTMachine.wordBudget,
    UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
   change UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K)
    (UniformRadixTwoDAG.count K) K ≤ u at cap
   change 100*(K+UniformRadixTwoDAG.width K+UniformRadixTwoDAG.count K+V+q.a+q.e+G+1)+1000 ≤ u at linear
   omega
 · change 3*u+5*V ≤ 4*u;omega
 · change UniformToeplitzCrossTopologyMachine.budget K q.a q.e (3*u) (4*u) ≤ 2000*u
   dsimp only [UniformToeplitzCrossTopologyMachine.budget,UniformToeplitzCrossTopologyMachine.G]
   change 3*u+4*u+5*(7*V+2*q.a)+UniformRadixInstructionMachine.cap N t K+
    10000*(N+V+q.a+q.e+K+1)^2 ≤ 2000*u
   omega
 · change 4*u+5*G ≤ 5*u;omega
 · change 5*u+q.e+1+G ≤ 2000*u;omega
 · change 2*u+3*t ≤ 6*u;omega
 · change 5*u+q.e+1+G ≤ 6*u;omega
 · change 6*u+G*(G+1) ≤ 7*u;omega
 · change 7*u+G+2 ≤ 2000*u;omega
 · change 4*u+7*N+1 ≤ 5*u;omega
 · change 5*u+7*N ≤ 6*u;omega
 · change 6*u+6 ≤ 2000*u;omega
 · constructor
   all_goals dsimp only [original,UniformSeedHeightPreparation.Config.seed]
   all_goals omega
 · constructor
   · change 4*u+5*G ≤ 8*u;omega
   · change 6*u+G ≤ 8*u;omega
   · change 7*u+G+2 ≤ 8*u;omega
   · change 8*u+6*G*(8*K+7) ≤ 9*u;omega
   · change 9*u+2*G*(8*K+7) ≤ 10*u;nlinarith only [rows]
   · change 10*u+12 ≤ 11*u;omega
 · change UniformCrossHeightPreparationMachine.wordBudget
    (⟨K,q.a,q.e,4*u,6*u,7*u,8*u,9*u,10*u,11*u,4*u,6*u,true⟩) ≤ 2000*u
   have shape : UniformCrossHeightPreparationMachine.wordBudget
    (⟨K,q.a,q.e,4*u,6*u,7*u,8*u,9*u,10*u,11*u,4*u,6*u,true⟩)=
    119*u+16*G*(8*K+7)+K+8*N+17*G+4*(8*K+7)+2*q.e+335 := by
    dsimp only [UniformCrossHeightPreparationMachine.wordBudget,UniformCrossDepthReplayPreparation.wordBudget,
     UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.colorBase,
     UniformCrossHeightPreparationMachine.recordBase,UniformCrossHeightPreparationMachine.height,
     UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf]
    dsimp only [G,c,K,N,original,UniformSeedHeightPreparation.Config.exponent,
     UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.gates]
    ring
   rw [shape]
   nlinarith only [rows,linear]
 · change 1046 ≤ 2000*u;omega

lemma actual_original (n : ℕ) (q : Row) :
 UniformLocalRectanglePhaseBanks.actual q (original n q)=original n q := by rfl
lemma prefix_fresh {n : ℕ} (hn : 0 < n) (q : Row) :
 UniformLocalRectangleCoefficientMachine.PrefixFresh n (original n q) := by
 obtain ⟨_,pool,_,dir⟩:=retained hn
 change UniformConjugateRankSpectrumPreparation.seedEnd n ≤ stride n at pool
 constructor
 · intro b hb
   have lower : stride n ≤ b := by
    change b ∈ [2*stride n,3*stride n,4*stride n,5*stride n,6*stride n] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with h|h|h|h|h
    all_goals omega
   exact pool.trans lower
 · intro b hb
   have lower : stride n ≤ b := by
    change b ∈ [2*stride n,3*stride n,4*stride n,5*stride n,6*stride n,7*stride n,8*stride n,9*stride n,10*stride n,11*stride n] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with h|h|h|h|h|h|h|h|h|h
    all_goals omega
   exact dir.trans lower
lemma work_allocation {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 UniformConjugateRankSpectrumPreparation.Allocation n j
  (UniformLocalRectangleCoefficientMachine.nextParameters n j q (original n q) (work n))
  (conjugate n) (budget n) := by
 let c:=original n q
 let K:=c.exponent
 let N:=c.width
 let t:=UniformRadixTwoDAG.count K
 let V:=UniformConvolutionDAG.total K
 let G:=c.gates
 let u:=stride n
 obtain ⟨linear,cap,top,ord,rows⟩:=arithmetic hn j q g
 change 100*(K+N+t+V+q.a+q.e+G+1)+1000 ≤ u at linear
 change UniformRadixInstructionMachine.cap N t K ≤ u at cap
 change 10000*(N+V+q.a+q.e+K+1)^2 ≤ 50*u at top
 have old:=original_layout hn j q g
 obtain ⟨pool,conj,dir,cdir⟩:=retained hn
 change _ ≤ u at pool conj dir cdir
 have endAxis:=UniformAllAxisConjugatePreparation.axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
 rw [UniformAllAxisConjugatePreparation.axisBase_next] at endAxis
 have widths:=UniformSeedHeightPreparation.widths c
 have rk : UniformRankKernelMachine.Geometry
  (UniformConjugateRankSpectrumPreparation.selected n j
   (UniformLocalRectangleCoefficientMachine.nextParameters n j q c (work n))).rank (budget n) := by
  constructor
  · exact g.positiveA
  · exact g.positiveE
  · exact g.hRows
  · exact g.gSplit
  · exact g.interior
  · exact g.columns
  · exact widths.1
  · exact widths.2
  · change UniformAllAxisConjugatePreparation.axisBase n j.val+3*radix n j+radix n j ≤ 8*u;omega
  · change UniformAllAxisConjugatePreparation.axisBase n j.val+4*radix n j+radix n j ≤ 8*u;omega
  · change 0 < 8*u;omega
  · change 8*u+6*N ≤ 2000*u;omega
  · change 90 ≤ 2000*u;omega
 have spec : UniformKernelSpectrumMachine.Layout K (8*u) (9*u) (13*u) (10*u)
  (UniformMasterRootMachine.order n) (budget n) := by
  constructor
  · change 8*u+6*N ≤ 9*u;omega
  · omega
  · dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
    change 9*u+N+t+5*N+4+1 ≤ 10*u;omega
  · exact (UniformMasterRootMachine.order_bounds hn).1
  · exact UniformSeedHeightPreparation.selected_divisor n j c
     (by change q.a ≤ _;have:=g.hRows;omega)
     (by change q.e ≤ _;have:=g.columns;have:=g.gSplit;omega)
     (by change 0 < q.a+q.e;have:=g.positiveA;omega)
  · dsimp only [UniformKernelSpectrumMachine.wordBudget,UniformPreparedFFTMachine.wordBudget,
     UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase]
    change _ ≤ 2000*u
    change UniformRadixInstructionMachine.cap (UniformRadixTwoDAG.width K)
     (UniformRadixTwoDAG.count K) K ≤ u at cap
    change 100*(K+UniformRadixTwoDAG.width K+UniformRadixTwoDAG.count K+V+q.a+q.e+G+1)+1000 ≤ u at linear
    omega
 constructor
 · refine ⟨rk,spec,?_,?_,?_,?_,?_⟩
   · change 14*u+5*V ≤ 15*u;omega
   · change UniformToeplitzCrossTopologyMachine.budget K q.a q.e (14*u) (15*u) ≤ 2000*u
     dsimp only [UniformToeplitzCrossTopologyMachine.budget,UniformToeplitzCrossTopologyMachine.G]
     change 14*u+15*u+5*(7*V+2*q.a)+UniformRadixInstructionMachine.cap N t K+
      10000*(N+V+q.a+q.e+K+1)^2 ≤ 2000*u
     omega
   · change 15*u+5*G ≤ 16*u;omega
   · change 16*u+q.e+1+G ≤ 2000*u;omega
   · change 722 ≤ 2000*u;omega
 · change UniformAllAxisConjugatePreparation.axisBase n (axisCount n) ≤ 8*u;omega
 · change UniformGlobalLocalPreparation.globalEnd n ≤ 8*u
   dsimp only [UniformAllAxisSeedPreparation.axisBase,UniformLocalSeedTableMachine.poolBase] at pool
   omega
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 13*u;omega
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 14*u;omega
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 15*u;omega
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 16*u;omega
 · change UniformConjugateRankSpectrumPreparation.dirEnd n ≤ 2000*u;omega
 · change 10*u+7*N+1 ≤ 11*u;omega
 · change 11*u+7*N ≤ 2000*u;omega
 · change 763 ≤ 2000*u;omega


lemma geometry_of_rows {n v o : ℕ} (j : Fin (axisCount n)) (q : Row)
 (hv : 2 ≤ v) (hp : 0 < UniformWorkspacePlanner.selected v)
 (hr : v ≤ radix n j) (hq : q ∈ rows v o (UniformWorkspacePlanner.selected v)) : Geometry n j q := by
 obtain ⟨a,e,h,sp,i,c,fit,_,_⟩:=UniformLocalRectangleBankMachine.rows_geometry v o q hv hp hq
 exact ⟨a,e,h.trans hr,lt_of_lt_of_le sp hr,i,c,fit.trans hr⟩

lemma row_before {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 ∀ b ∈ [(original n q).d,(original n q).conv,(original n q).tape,(original n q).depth,
  (original n q).order,(original n q).directory,(original n q).rows,(original n q).colors,
  (original n q).palette,(original n q).heightDirectory],lowRow n+7 ≤ b := by
 have h:1000 ≤ stride n:=by have:= (arithmetic hn j q g).1;omega
 intro b hb
 change b ∈ [2*stride n,3*stride n,4*stride n,5*stride n,6*stride n,7*stride n,8*stride n,9*stride n,10*stride n,11*stride n] at hb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
 change stride n+7 ≤ b
 rcases hb with h|h|h|h|h|h|h|h|h|h
 all_goals omega
lemma native_before {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 ∀ b ∈ [(work n).d,(work n).conv,(work n).tape,(work n).depth],
 UniformCrossHeightPreparationMachine.recordBase (original n q).height
  (8*(original n q).exponent+7) ≤ b := by
 have h:100*((original n q).exponent)+1000 ≤ stride n:=by have:= (arithmetic hn j q g).1;omega
 intro b hb
 change b ∈ [13*stride n,14*stride n,15*stride n,16*stride n] at hb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
 change 11*stride n+3*(8*(original n q).exponent+7) ≤ b
 rcases hb with h|h|h|h
 all_goals omega
lemma scalar_before {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 (original n q).C+7*(original n q).width+1 ≤ (work n).S ∧
 (original n q).negative+7*(original n q).width ≤ (work n).S ∧
 (original n q).constants+6 ≤ (work n).S := by
 have h:100*(original n q).width+1000 ≤ stride n:=by have:= (arithmetic hn j q g).1;omega
 change 4*stride n+7*(original n q).width+1 ≤ 8*stride n ∧
 5*stride n+7*(original n q).width ≤ 8*stride n ∧ 6*stride n+6 ≤ 8*stride n
 omega
lemma phase_fit {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 55*UniformLocalReplayAssembly.phasePrefix (8*(original n q).exponent+6) 6 ≤ stride n := by
 have k: (original n q).exponent ≤ 4*n :=
  (UniformSeedChunkAllocation.capacity_sizes hn j g.capacity).exponent
 have old:=UniformSeedChunkAllocation.slot_canonical hn
 change 200*UniformSeedChunkAllocation.slot n ≤ stride n at old
 have small:55*UniformLocalReplayAssembly.phasePrefix (8*(original n q).exponent+6) 6 ≤ UniformSeedChunkAllocation.slot n := by
  rw [UniformLocalReplayAssembly.prefix_total]
  unfold UniformSeedChunkAllocation.slot
  nlinarith only [k]
 omega
lemma slots_before {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 UniformCrossHeightPreparationMachine.recordBase (original n q).height
  (8*(original n q).exponent+7) ≤ control n ∧
 UniformCrossHeightPreparationMachine.recordBase (original n q).height
  (8*(original n q).exponent+7) ≤ falseRows n ∧
 control n+55*UniformLocalReplayAssembly.phasePrefix (8*(original n q).exponent+6) 6 ≤ falseRows n ∧
 falseDirectory n+3*(8*(original n q).exponent+7) ≤ borrowed n := by
 have h:100*(original n q).exponent+1000 ≤ stride n:=by have:= (arithmetic hn j q g).1;omega
 have p:=phase_fit hn j q g
 change 11*stride n+3*(8*(original n q).exponent+7) ≤ 17*stride n ∧
 11*stride n+3*(8*(original n q).exponent+7) ≤ 18*stride n ∧
 17*stride n+55*UniformLocalReplayAssembly.phasePrefix (8*(original n q).exponent+6) 6 ≤ 18*stride n ∧
 21*stride n+3*(8*(original n q).exponent+7) ≤ 23*stride n
 omega
abbrev disabled (n : ℕ) (q : Row) := UniformLocalDisabledHeightMachine.disabled
 (original n q).height (falseRows n) (falseColors n) (falsePalette n) (falseDirectory n)
lemma false_layout {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) : UniformCrossHeightPreparationMachine.Layout (disabled n q) := by
 let K:=(original n q).exponent
 let G:=(original n q).gates
 let u:=stride n
 have h:=arithmetic hn j q g
 have linear:100*(K+G+1)+1000 ≤ u:=by have:=h.1;omega
 have rows:6*G*(8*K+7) ≤ u:=h.2.2.2.2
 constructor
 · change 4*u+5*G ≤ 18*u;omega
 · change 6*u+G ≤ 18*u;omega
 · change 7*u+G+2 ≤ 18*u;omega
 · change 18*u+6*G*(8*K+7) ≤ 19*u;omega
 · change 19*u+2*G*(8*K+7) ≤ 20*u;nlinarith only [rows]
 · change 20*u+12 ≤ 21*u;omega
lemma height_budget_formula (K a e T Q R D F U J C P : ℕ) (enabled : Bool) :
 let N:=UniformRadixTwoDAG.width K
 let G:=6*(3*K*N+2*N)+2*a
 let H:=8*K+7
 UniformCrossHeightPreparationMachine.wordBudget ⟨K,a,e,T,Q,R,D,F,U,J,C,P,enabled⟩=
 2*T+2*Q+2*R+2*D+2*F+2*U+J+2*C+2*P+16*G*H+K+8*N+17*G+4*H+2*e+335 := by
 intro N G H
 dsimp only [UniformCrossHeightPreparationMachine.wordBudget,UniformCrossDepthReplayPreparation.wordBudget,
  UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.colorBase,
  UniformCrossHeightPreparationMachine.recordBase,UniformCrossHeightPreparationMachine.height,
  UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,N,G,H]
 ring
lemma false_budget {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) : UniformCrossHeightPreparationMachine.wordBudget (disabled n q) ≤ budget n := by
 let K:=(original n q).exponent
 let N:=(original n q).width
 let G:=(original n q).gates
 let u:=stride n
 have h:=arithmetic hn j q g
 have linear:100*(K+N+G+q.e+1)+1000 ≤ u:=by have:=h.1;omega
 have rows:6*G*(8*K+7) ≤ u:=h.2.2.2.2
 change UniformCrossHeightPreparationMachine.wordBudget
  ⟨K,q.a,q.e,4*u,6*u,7*u,18*u,19*u,20*u,21*u,4*u,6*u,false⟩ ≤ 2000*u
 rw [height_budget_formula]
 change 2*(4*u)+2*(6*u)+2*(7*u)+2*(18*u)+2*(19*u)+2*(20*u)+21*u+2*(4*u)+2*(6*u)+
  16*G*(8*K+7)+K+8*N+17*G+4*(8*K+7)+2*q.e+335 ≤ 2000*u
 nlinarith only [rows,linear]
lemma below_cache (c : Constants) (n : ℕ) : budget n ≤ slab c n := by
 have f:=fixed_large c
 unfold slab budget
 exact Nat.mul_le_mul_right (stride n) (by omega)
lemma all_reused_below_cache (c : Constants) (n : ℕ) :
 inverse n+stride n ≤ slab c n := by
 have h:=below_cache c n
 change 32*stride n+stride n ≤ slab c n
 change 2000*stride n ≤ slab c n at h
 omega

lemma layout_mono {n B B' : ℕ} {j : Fin (axisCount n)}
 {c : UniformSeedHeightPreparation.Config} (h : UniformSeedHeightPreparation.Layout n j c B)
 (hb : B ≤ B') : UniformSeedHeightPreparation.Layout n j c B' :=
 {h with
  outputBound:=h.outputBound.trans hb, spectrumEnvelope:=h.spectrumEnvelope.trans hb,
  topologyEnvelope:=h.topologyEnvelope.trans hb, depthBound:=h.depthBound.trans hb,
  directoryBound:=h.directoryBound.trans hb, constantsBound:=h.constantsBound.trans hb,
  heightEnvelope:=h.heightEnvelope.trans hb, codeBound:=h.codeBound.trans hb}
lemma allocation_mono {n B B' dest : ℕ} {j : Fin (axisCount n)}
 {p : UniformRankCrossPreparationMachine.Parameters}
 (h : UniformConjugateRankSpectrumPreparation.Allocation n j p dest B) (hb : B ≤ B') :
 UniformConjugateRankSpectrumPreparation.Allocation n j p dest B' := by
 refine {h with
  layout:=?_,directoryBound:=h.directoryBound.trans hb,
  reversedBound:=h.reversedBound.trans hb,code:=h.code.trans hb}
 rcases h.layout with ⟨rank,spec,conv,top,tape,depth,code⟩
 exact ⟨{rank with outputBound:=rank.outputBound.trans hb,codeBound:=rank.codeBound.trans hb},
  {spec with envelope:=spec.envelope.trans hb},conv,top.trans hb,tape,depth.trans hb,code.trans hb⟩
lemma ambient_budget (c : Constants) (n : ℕ) : budget n ≤ envelope c n :=
 (below_cache c n).trans (by unfold envelope;omega)
lemma ambient_layout (c : Constants) {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) : UniformSeedHeightPreparation.Layout n j (original n q) (envelope c n) :=
 layout_mono (original_layout hn j q g) (ambient_budget c n)
lemma ambient_allocation (c : Constants) {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) : UniformConjugateRankSpectrumPreparation.Allocation n j
 (UniformLocalRectangleCoefficientMachine.nextParameters n j q (original n q) (work n))
 (conjugate n) (envelope c n) := allocation_mono (work_allocation hn j q g) (ambient_budget c n)

/-- Entry uses only actual state data and ordinary charged caller headers.
All workspace, fresh-region and word inequalities are derived here. -/
lemma entry (c : Constants) {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) (x : Fin n → ℂ) (s : State)
 (args : UniformLocalRectangleBankMachine.Args j (lowRow n) (original n q) s)
 (nextArgs : UniformLocalRectangleCoefficientMachine.NextArgs (work n) (conjugate n) s)
 (slot : s.natReg 4230=control n)
 (source : UniformLocalRectangleBankMachine.RowSource (lowRow n) q s)
 (metadata : UniformPermutationInversePreparation.Metadata n s)
 (seedRetained : UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjRetained : UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (operands : UniformInitialPreparation.Operands n x s) :
 UniformLocalRectanglePhaseBanks.Entry hn j (lowRow n) q (original n q) (work n)
 (conjugate n) (control n) (envelope c n) x s (by
  rw [actual_original];exact ambient_layout c hn j q g) := by
 have linear:100*((original n q).exponent)+1000 ≤ stride n := by
  have:=(arithmetic hn j q g).1;omega
 have b:=ambient_budget c n
 have d:=retained hn
 refine ⟨args,nextArgs,slot,source,metadata,seedRetained,conjRetained,operands,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw [actual_original];exact prefix_fresh hn q
 · rw [actual_original];exact row_before hn j q g
 · exact ambient_allocation c hn j q g
 · rw [actual_original];exact native_before hn j q g
 · rw [actual_original];exact (scalar_before hn j q g).1
 · rw [actual_original];exact (scalar_before hn j q g).2.1
 · rw [actual_original];exact (scalar_before hn j q g).2.2
 · rw [actual_original];exact (slots_before hn j q g).1
 · have h:=d.2.2.1
   change _ ≤ 17*stride n;omega
 · have h:=d.2.2.2
   change _ ≤ 17*stride n;omega
 · rw [actual_original]
   change 2000*stride n ≤ envelope c n at b
   omega
 · rw [actual_original]
   have fit:=(slots_before hn j q g).2.2.1
   change 17*stride n+_ ≤ envelope c n
   change 2000*stride n ≤ envelope c n at b
   change 17*stride n+_ ≤ 18*stride n at fit
   omega
 · change stride n+6 ≤ envelope c n
   change 2000*stride n ≤ envelope c n at b
   omega

lemma radix_linear {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) :
 100*radix n j+1000 ≤ stride n := by
 have r:radix n j ≤ 4*n :=
  (UniformGlobalLocalPreparation.radix_le_length n j).trans (actual_sizes n hn).2.1
 have small:100*radix n j+1000 ≤ UniformSeedChunkAllocation.slot n := by
  unfold UniformSeedChunkAllocation.slot
  nlinarith only [r]
 have old:=UniformSeedChunkAllocation.slot_canonical hn
 change 200*UniformSeedChunkAllocation.slot n ≤ stride n at old
 omega
lemma mapping_regions {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n)) (q : Row)
 (g : Geometry n j q) :
 borrowed n+(original n q).gates ≤ selected n ∧
 selected n+6*(original n q).gates ≤ ordinals n ∧
 ordinals n+2*(original n q).gates ≤ mapped n ∧
 mapped n+6*(original n q).gates ≤ permutation n ∧
 permutation n+radix n j ≤ widths n ∧ widths n+radix n j ≤ markers n ∧
 markers n+radix n j ≤ axis n ∧ axis n+4 ≤ translated n ∧
 translated n+3*radix n j ≤ inverse n ∧ inverse n+radix n j ≤ 33*stride n := by
 have h:100*(original n q).gates+1000 ≤ stride n := by have:=(arithmetic hn j q g).1;omega
 have r:=radix_linear hn j
 dsimp only [borrowed,selected,ordinals,mapped,permutation,widths,markers,axis,translated,inverse]
 omega
lemma matching_source_below (c : Constants) {n : ℕ} (hn : 0 < n) (j : Fin (axisCount n))
 (M k : ℕ) (size : M ≤ radix n j) :
 translated n+3*M ≤ (UniformJointCacheAllocation.slot (UniformJointCacheAllocation.axis c n j) k).permutation := by
 have rb:=radix_linear hn j
 have low:translated n+3*M ≤ slab c n := by
  have bound:=below_cache c n
  change 2000*stride n ≤ slab c n at bound
  change 31*stride n+3*M ≤ slab c n
  omega
 have high:slab c n ≤ (UniformJointCacheAllocation.slot (UniformJointCacheAllocation.axis c n j) k).permutation := by
  dsimp only [UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis,
   UniformJointCacheAllocation.axisBank,UniformJointCacheAllocation.natStart]
  omega
 exact low.trans high
end ExactFourierCircuits.UniformJointCacheWorkspace
