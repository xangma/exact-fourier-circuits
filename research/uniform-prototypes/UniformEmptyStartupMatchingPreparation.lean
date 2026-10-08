import UniformSeedHighDataMatchingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformEmptyStartupMatchingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len)
open UniformAllAxisSeedPreparation (axisCount radix)
attribute [local irreducible] UniformToeplitzCrossDAG.crossDAG UniformChunkMatchingPreparation.crossWord UniformChunkMatchingPreparation.colors

noncomputable section

/-- The small nonempty cross needs196 physical ports. This selected-axis
branch is explicit; smaller startup lengths are outside this component. -/
def selectedAxis (n : ℕ) (h : 194 ≤ ell n) : Fin (axisCount n) := ⟨193,by unfold axisCount;omega⟩
lemma selectedAxis_capacity (n : ℕ) (h : 194 ≤ ell n) : 196 ≤ radix n (selectedAxis n h) := by
 have hl : 193 < ell n := by omega
 have eq : selectedAxis n h = (⟨193,hl⟩ : Fin (ell n)).castSucc := Fin.ext rfl
 change 196 ≤ UniformSelectedCRT.radices n (selectedAxis n h)
 rw [eq,UniformSelectedCRT.radices,Fin.snoc_castSucc]
 exact UniformWorkingLength.oddPrime_lower 193

/-- Deliberately coarse, physically computed from the saved original length. -/
def arena (n : ℕ) := 100000*(n+2)^2
def budget (n : ℕ) := (n+2)^19
def seed (n : ℕ) : UniformSeedChunkPreparation.Config where
 seed := ⟨1,1,1,0,1,2*arena n,3*arena n,2*arena n,4*arena n,
  3*arena n,4*arena n,5*arena n,6*arena n,7*arena n,5*arena n,6*arena n,
  8*arena n,9*arena n,10*arena n,11*arena n,true⟩
 borrowed := 12*arena n
 selected := 13*arena n
 ordinals := 14*arena n
 mapped := 15*arena n
 permutation := 16*arena n
 widths := 17*arena n
 markers := 18*arena n
 axis := 19*arena n
 layer := 2
 color := 1

lemma seed_exponent (n : ℕ) : (seed n).seed.exponent=2 := by
 change UniformWorkspacePlanner.exponent 1 1=2;decide
lemma seed_width (n : ℕ) : (seed n).seed.width=4 := by
 rw [UniformSeedHeightPreparation.Config.width,seed_exponent];rfl
lemma seed_gates (n : ℕ) : (seed n).seed.gates=194 := by
 rw [UniformSeedHeightPreparation.Config.gates,seed_exponent,seed_width];rfl

lemma ell_bound (n : ℕ) : ell n ≤ 2*n := by
 have h:=UniformWorkingLength.firstExceed_bound n
 unfold ell UniformWorkingLength.axisCount;omega
lemma radix_bound {n : ℕ} (hn : 0<n) (j : Fin (axisCount n)) : radix n j < 4*n :=
 lt_of_le_of_lt (UniformGlobalLocalPreparation.radix_le_length n j)
  (UniformWorkingLength.workingLength_upper hn)

lemma protected_bound {n : ℕ} (hn : 0<n) :
 UniformAllAxisConjugatePreparation.axisBase n (axisCount n) ≤ 1000*(n+2)^2 ∧
 UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n ≤ 1000*(n+2)^2 ∧
 UniformGlobalLocalPreparation.globalEnd n ≤ 1000*(n+2)^2 := by
 have he:=ell_bound n
 have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
 have hp:=UniformAllAxisSeedPreparation.prefix_bound n (axisCount n) (le_refl _)
 have hprod:(ell n+1)*len n ≤ (2*n+1)*(4*n):=Nat.mul_le_mul (by omega) (by omega)
 refine ⟨?_,?_,?_⟩
 · dsimp only [UniformAllAxisConjugatePreparation.axisBase,UniformAllAxisConjugatePreparation.pool,
    UniformSeedConjugatePreparation.destination,UniformSeedConjugatePreparation.O.axisBase,
    UniformSeedConjugatePreparation.O.axisCount,UniformAllAxisSeedPreparation.axisBase,
    UniformLocalSeedTableMachine.poolBase]
   rw [UniformGlobalLocalPreparation.globalEnd_formula]
   change UniformAllAxisSeedPreparation.prefixSum n (ell n+1) ≤ (ell n+1)*len n at hp
   nlinarith
 · dsimp only [UniformAllAxisConjugatePreparation.directoryBase]
   rw [UniformAllAxisSeedPreparation.directory_formula]
   unfold axisCount;nlinarith
 · rw [UniformGlobalLocalPreparation.globalEnd_formula];nlinarith

lemma arena_bounds {n : ℕ} (hn : 0<n) :
 900000 ≤ arena n ∧ 200*arena n ≤ budget n ∧ 4*n ≤ arena n := by
 have hbase : 3 ≤ n+2 := by omega
 have hsq : 9 ≤ (n+2)^2 := (show 9=3^2 by decide) ▸ Nat.pow_le_pow_left hbase 2
 have hexp : 20000000 ≤ (n+2)^17 :=
  (show 20000000 ≤ 3^17 by decide).trans (Nat.pow_le_pow_left hbase 17)
 have hm := Nat.mul_le_mul_right ((n+2)^2) hexp
 rw [←pow_add] at hm
 unfold arena budget
 constructor
 · nlinarith
 constructor
 · convert hm using 1;ring
 · nlinarith

lemma old_scalar_end {n : ℕ} :
 UniformAllAxisSeedPreparation.axisBase n (axisCount n) ≤
 UniformAllAxisConjugatePreparation.axisBase n (axisCount n) := by
 unfold UniformAllAxisConjugatePreparation.axisBase UniformAllAxisConjugatePreparation.pool
 unfold UniformSeedConjugatePreparation.destination
 change _ ≤ UniformAllAxisSeedPreparation.axisBase n (axisCount n)+5*len n+5*UniformAllAxisSeedPreparation.prefixSum n (axisCount n)
 omega
lemma old_directory_end (n : ℕ) :
 UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n ≤
 UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n := by
 unfold UniformAllAxisConjugatePreparation.directoryBase;omega

lemma source_ends (n : ℕ) (j : Fin (axisCount n)) :
 UniformSeedRankCrossPreparation.hBase n j+radix n j ≤
  UniformAllAxisSeedPreparation.axisBase n (axisCount n) ∧
 UniformSeedRankCrossPreparation.gBase n j+radix n j ≤
  UniformAllAxisSeedPreparation.axisBase n (axisCount n) := by
 have h:=UniformAllAxisSeedPreparation.axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
 rw [UniformAllAxisSeedPreparation.axisBase_next] at h
 unfold UniformSeedRankCrossPreparation.hBase UniformSeedRankCrossPreparation.gBase
 omega

lemma height_layout {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformSeedHeightPreparation.Layout n (selectedAxis n hc) (seed n).seed (budget n) := by
 have ha:=arena_bounds hn
 have hp:=protected_bound hn
 have oldS:=old_scalar_end (n:=n)
 have oldN:=old_directory_end n
 have ends:=source_ends n (selectedAxis n hc)
 have cap:=selectedAxis_capacity n hc
 have oldBank : UniformSeedRankCrossPreparation.Fresh n (seed n).seed.seed := by
  constructor <;> dsimp [seed,UniformSeedHeightPreparation.Config.seed] <;>
   unfold arena at * <;> omega
 have hl : UniformCrossHeightPreparationMachine.Layout (seed n).seed.height := by
  constructor <;>
   simp only [seed,UniformSeedHeightPreparation.Config.height,
    UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.colorBase,
    UniformCrossHeightPreparationMachine.recordBase,UniformCrossHeightPreparationMachine.height,
    UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,
    seed_exponent]
  all_goals change _ ≤ _
  all_goals norm_num [UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent,
    UniformRadixTwoDAG.width] <;> omega
 constructor
 all_goals try first | exact oldBank | exact hl
 all_goals try simp only [seed,
  UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent,
  UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.gates,
  UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase,
  UniformKernelSpectrumMachine.wordBudget,UniformPreparedFFTMachine.wordBudget,
  UniformRadixInstructionMachine.cap,UniformToeplitzCrossTopologyMachine.budget,
  UniformToeplitzCrossTopologyMachine.G,UniformConvolutionDAG.total,
  UniformCrossHeightPreparationMachine.wordBudget,UniformSeedHeightPreparation.Config.height,
  UniformCrossHeightPreparationMachine.widthOf,UniformCrossHeightPreparationMachine.gates,
  UniformCrossHeightPreparationMachine.height,UniformCrossHeightPreparationMachine.rowBase,
  UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.recordBase,
  UniformCrossDepthReplayPreparation.wordBudget]
 all_goals norm_num [UniformRadixTwoDAG.width,UniformRadixTwoDAG.count]
 all_goals unfold arena at *;omega

lemma chunk_layout {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformSeedChunkPreparation.Layout n (selectedAxis n hc) (seed n) (budget n) := by
 have ha:=arena_bounds hn
 have hr:=radix_bound hn (selectedAxis n hc)
 have cap:=selectedAxis_capacity n hc
 refine ⟨height_layout hn hc,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals try simp only [seed,UniformSeedHeightPreparation.Config.gates,UniformSeedHeightPreparation.Config.width,seed_exponent,
  UniformSeedHeightPreparation.Config.height,UniformCrossHeightPreparationMachine.rowBase,
  UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.recordBase,
  UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,
  UniformCrossHeightPreparationMachine.height,UniformSeedHeightPreparation.Config.exponent,
  UniformWorkspacePlanner.exponent]
 all_goals norm_num [UniformRadixTwoDAG.width]
 all_goals omega

def packing {n : ℕ} (hn : 0<n) (r : ℕ) (hr : r ≤ 4*n) : UniformSectorPackingMachine.Layout := by
 have ha:=arena_bounds hn
 refine ⟨1,19*arena n,20*arena n,21*arena n,22*arena n,12*arena n,13*arena n,r,budget n,
  ?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals omega

def packingLayout {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformSeedChunkPackingPreparation.Layout n (selectedAxis n hc) (seed n) (budget n) := by
 have ha:=arena_bounds hn
 have hr:=radix_bound hn (selectedAxis n hc)
 refine ⟨chunk_layout hn hc,packing hn (radix n (selectedAxis n hc)) (by omega),rfl,rfl,rfl,rfl,
  ?_,?_,?_,?_,?_⟩
 · have hs:=old_scalar_end (n:=n);have hp:=protected_bound hn
   change _ ≤ 13*arena n
   unfold arena;omega
 all_goals try simp only [seed,packing,seed_width,
  UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.exponent,
  UniformWorkspacePlanner.exponent]
 all_goals norm_num [UniformRadixTwoDAG.width]
 all_goals omega

def work (n : ℕ) : UniformRankCrossPreparationMachine.Parameters :=
 ⟨2,0,0,0,0,1,1,1,0,1,7*arena n,8*arena n,23*arena n,9*arena n,
  UniformMasterRootMachine.order n,24*arena n,25*arena n,26*arena n⟩

lemma seedRows_capacity {n B : ℕ} {j : Fin (axisCount n)} {c : UniformSeedChunkPreparation.Config}
 (p : UniformSeedChunkPackingPreparation.Layout n j c B) :
 2*(UniformPackedMatchingShearMachine.seedRows p).length ≤ p.packing.total := by
 let par:=c.chunk n j
 let W:=UniformPackedMatchingShearMachine.seedWord n j c
 have dom:=UniformChunkMatchingPreparation.cross_domain par (UniformSeedHeightPreparation.widths c.seed).1
  (UniformSeedHeightPreparation.widths c.seed).2
 have degree:=UniformChunkMatchingPreparation.cross_degree par (UniformSeedHeightPreparation.widths c.seed).1
  (UniformSeedHeightPreparation.widths c.seed).2
 have cap:=UniformMatchingAxisTableMachine.matching_capacity par.radix
  (UniformChunkMatchingPreparation.physicalEdges p.seed.chunk W dom)
  (UniformChunkMatchingPreparation.physical_matching p.seed.chunk dom degree)
  (UniformChunkMatchingPreparation.physical_range p.seed.chunk dom)
 change 2*(UniformChunkMatchingPreparation.mappedRows par p.seed.chunk.capacity W
  (UniformChunkMatchingPreparation.crossLocations par c.seed.negative)).length ≤ _
 change 2*(UniformChunkMatchingPreparation.indices par W).length ≤ radix n j at cap
 simpa only [UniformChunkMatchingPreparation.mappedRows,UniformChunkMatchingPreparation.selectedRows,
  List.length_map,p.volume] using cap

lemma conjugate_source_ends (n : ℕ) (j : Fin (axisCount n)) :
 UniformAllAxisConjugatePreparation.axisBase n j.val+3*radix n j+radix n j ≤
  UniformAllAxisConjugatePreparation.axisBase n (axisCount n) ∧
 UniformAllAxisConjugatePreparation.axisBase n j.val+4*radix n j+radix n j ≤
  UniformAllAxisConjugatePreparation.axisBase n (axisCount n) := by
 have h:=UniformAllAxisConjugatePreparation.axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
 rw [UniformAllAxisConjugatePreparation.axisBase_next] at h
 omega

lemma spectrum_layout {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformConjugateRankSpectrumPreparation.Allocation n (selectedAxis n hc)
  (UniformConjugatePackedMatchingPreparation.workParameters n (selectedAxis n hc) (seed n) (work n))
  (10*arena n) (budget n) := by
 have ha:=arena_bounds hn
 have hp:=protected_bound hn
 have ends:=conjugate_source_ends n (selectedAxis n hc)
 have cap:=selectedAxis_capacity n hc
 have order:0<UniformMasterRootMachine.order n:=(UniformMasterRootMachine.order_bounds hn).1
 have divisor:UniformRadixTwoDAG.width 2 ∣ UniformMasterRootMachine.order n:=by
  simpa only [seed_exponent] using UniformSeedHeightPreparation.selected_divisor n (selectedAxis n hc)
   (seed n).seed (by change 1≤radix n _;omega) (by change 1≤radix n _;omega) (by change 0<1+1;decide)
 let wp:=UniformConjugateRankSpectrumPreparation.selected n (selectedAxis n hc)
  (UniformConjugatePackedMatchingPreparation.workParameters n (selectedAxis n hc) (seed n) (work n))
 have geo:UniformRankKernelMachine.Geometry wp.rank (budget n):=by
  constructor
  all_goals try simp only [wp,UniformConjugateRankSpectrumPreparation.selected,
   UniformConjugatePackedMatchingPreparation.workParameters,UniformConjugateRankSpectrumPreparation.relocated,
   UniformSeedHeightPreparation.parameters,UniformSeedRankCrossPreparation.parameters,
   UniformSeedHeightPreparation.Config.seed,UniformSeedHeightPreparation.Config.exponent,
   UniformWorkspacePlanner.exponent,seed,work,UniformRankCrossPreparationMachine.Parameters.rank,
   UniformRankKernelMachine.Parameters.N,UniformConjugateRankSpectrumPreparation.O.radix]
  all_goals norm_num [UniformRadixTwoDAG.width]
  all_goals unfold arena at *;omega
 have spec:UniformKernelSpectrumMachine.Layout 2 (7*arena n) (8*arena n) (23*arena n) (9*arena n)
  (UniformMasterRootMachine.order n) (budget n):=by
  refine ⟨?_,?_,?_,order,divisor,?_⟩
  all_goals try simp only [UniformKernelSpectrumMachine.wordBudget,UniformPreparedFFTMachine.wordBudget,
   UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase,UniformRadixInstructionMachine.cap]
  all_goals norm_num [UniformRadixTwoDAG.width,UniformRadixTwoDAG.count]
  all_goals omega
 constructor
 · refine ⟨geo,?_,?_,?_,?_,?_,?_⟩
   · change UniformKernelSpectrumMachine.Layout ((seed n).seed.exponent) (7*arena n) (8*arena n)
      (23*arena n) (9*arena n) (UniformMasterRootMachine.order n) (budget n)
     rw [seed_exponent];exact spec
   all_goals try simp only [UniformConjugateRankSpectrumPreparation.selected,
    UniformConjugatePackedMatchingPreparation.workParameters,UniformConjugateRankSpectrumPreparation.relocated,
    UniformSeedHeightPreparation.parameters,UniformSeedRankCrossPreparation.parameters,
    UniformSeedHeightPreparation.Config.seed,UniformSeedHeightPreparation.Config.exponent,
    UniformWorkspacePlanner.exponent,seed,work,UniformRankCrossPreparationMachine.Shape,
    UniformToeplitzCrossTopologyMachine.budget,UniformToeplitzCrossTopologyMachine.G,
    UniformConvolutionDAG.total,UniformRadixInstructionMachine.cap]
   all_goals norm_num [UniformRadixTwoDAG.width,UniformRadixTwoDAG.count]
   all_goals omega
 all_goals try simp only [UniformConjugateRankSpectrumPreparation.seedEnd,
  UniformConjugateRankSpectrumPreparation.dirEnd,UniformConjugateRankSpectrumPreparation.O.axisCount,
  UniformConjugatePackedMatchingPreparation.workParameters,UniformConjugateRankSpectrumPreparation.relocated,
  UniformSeedHeightPreparation.parameters,UniformSeedRankCrossPreparation.parameters,
  UniformSeedHeightPreparation.Config.seed,UniformSeedHeightPreparation.Config.exponent,
  UniformWorkspacePlanner.exponent,seed,work]
 all_goals norm_num [UniformRadixTwoDAG.width]
 all_goals unfold arena at *;omega

lemma allocation {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformConjugatePackedMatchingPreparation.Allocation (packingLayout hn hc) (work n)
  (10*arena n) (11*arena n) (11*arena n+1) := by
 have ha:=arena_bounds hn
 have hr:=radix_bound hn (selectedAxis n hc)
 have capacity:=seedRows_capacity (packingLayout hn hc)
 change 2*(UniformPackedMatchingShearMachine.seedRows (packingLayout hn hc)).length ≤ radix n _ at capacity
 refine ⟨spectrum_layout hn hc,?_,?_,?_,?_,?_,?_,?_⟩
 · constructor
   · constructor
     all_goals try simp only [UniformConjugatePackedMatchingPreparation.matchingConfig,
      UniformPackedMatchingShearMachine.packingConfig,packingLayout,packing,seed,
      UniformToeplitzCrossDAG.bankSize,UniformSeedHeightPreparation.Config.exponent,
      UniformWorkspacePlanner.exponent]
     all_goals norm_num [UniformRadixTwoDAG.width]
     all_goals omega
   · exact capacity
   all_goals try simp only [UniformConjugatePackedMatchingPreparation.matchingConfig,
    UniformPackedMatchingShearMachine.packingConfig,packingLayout,packing,seed,
    UniformScalarScatterMachine.Disjoint] at capacity ⊢
   all_goals first | omega | exact Or.inr (by omega)
 all_goals try simp only [seed,work,seed_width,packingLayout,packing,
  UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent] at capacity ⊢
 all_goals norm_num [UniformRadixTwoDAG.width]
 all_goals repeat' apply And.intro
 all_goals omega

lemma placement {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformHighDataPackingPreparation.RetentionPlacement (packingLayout hn hc) := by
 have hp:=protected_bound hn
 have old:=old_scalar_end (n:=n)
 constructor <;> change _ ≤ _
 all_goals dsimp only [packingLayout,packing]
 all_goals unfold arena;omega

lemma freshness {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformSeedConjugatePreservation.Fresh
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n))
   (UniformPaddedInputPreparation.dataBase n+radix n (selectedAxis n hc)))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) (seed n).seed.seed := by
 have hp:=protected_bound hn
 have he:=ell_bound n
 have hr:=radix_bound hn (selectedAxis n hc)
 have low:UniformPaddedInputPreparation.dataBase n+radix n (selectedAxis n hc) ≤ 1000*(n+2)^2 := by
  unfold UniformPaddedInputPreparation.dataBase;nlinarith
 have hmax:max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n))
  (UniformPaddedInputPreparation.dataBase n+radix n (selectedAxis n hc)) ≤1000*(n+2)^2:=max_le hp.1 low
 constructor <;> dsimp [seed,UniformSeedHeightPreparation.Config.seed] <;> unfold arena <;> omega

end
end ExactFourierCircuits.UniformEmptyStartupMatchingPreparation
