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
    UniformCrossHeightPreparationMachine.height,
    UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,
    ]
  all_goals norm_num [UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent,
    UniformRadixTwoDAG.width];all_goals omega
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
 all_goals try simp only [seed,UniformSeedHeightPreparation.Config.gates,UniformSeedHeightPreparation.Config.width,
  UniformSeedHeightPreparation.Config.height,UniformCrossHeightPreparationMachine.rowBase,
  UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.recordBase,
  UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,
  UniformSeedHeightPreparation.Config.exponent,
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
 all_goals try simp only [seed,packing,
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
   UniformConjugateRankSpectrumPreparation.O.radix]
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
   all_goals omega
 all_goals try simp only [seed,work,packingLayout,packing,
  UniformSeedHeightPreparation.Config.width,UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent] at capacity ⊢
 all_goals norm_num [UniformRadixTwoDAG.width]
 all_goals repeat' apply And.intro
 all_goals omega

lemma placement {n : ℕ} (hn : 0<n) (hc : 194 ≤ ell n) :
 UniformHighDataPackingPreparation.RetentionPlacement (packingLayout hn hc) := by
 have hp:=protected_bound hn
 have old:=old_scalar_end (n:=n)
 constructor
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

/-- Every header here is a constant or an arithmetic address derived from
actual saved metadata. The list is fixed, independently of n and of the data. -/
def sizeBoot : List Op := [.literal 3200 0,.literal 3201 1,.literal 3202 2,
 .add 3206 101 3202,.mul 3207 3206 3206,.literal 3208 100000,.mul 3203 3207 3208]
def multiple (d k : ℕ) : List Op := [.literal 3204 k,.mul d 3203 3204]
def scaled (xs : List (ℕ×ℕ)) : List Op := xs.flatMap (fun p=>multiple p.1 p.2)
def seedScales : List (ℕ×ℕ) := [(1127,2),(1128,3),(1129,2),(1130,4),(1131,3),(1132,4),
 (1133,5),(1134,6),(1135,7),(1136,5),(1137,6),(1220,8),(1221,9),(1222,10),(1223,11)]
def chunkScales : List (ℕ×ℕ) := [(1230,12),(1231,13),(1232,14),(1233,15),
 (1234,16),(1235,17),(1236,18),(1237,19),(1450,20),(1451,21),(1452,22),(1453,12),(1454,13)]
def futureScales : List (ℕ×ℕ) := [(2250,10),(2257,7),(2259,8),(2260,23),
 (2261,9),(2262,24),(2263,25),(2264,26)]
def matchingScales : List (ℕ×ℕ) := [(2201,13),(2202,12),(2203,22),(2204,15),
 (2205,4),(2206,5),(2207,6),(2208,10),(2209,11),(2210,11)]
def literalHeaders : List Op := [.literal 1120 193,.literal 1122 1,.literal 1123 1,
 .literal 1124 1,.literal 1125 0,.literal 1126 1,.literal 1224 1,.literal 1238 2,.literal 1239 1,
 .literal 2251 193,.literal 2252 1,.literal 2253 1,.literal 2254 1,.literal 2255 0,
 .literal 2256 1,.literal 2258 2]
def dataAddress : List Op := [.mul 3205 101 3202,.add 2240 102 3205,
 .literal 3209 7,.add 2240 2240 3209]
def selectedWidth : List Op := [.add 3205 105 106,.add 3205 3205 103,
 .literal 3209 387,.add 3205 3205 3209,.getNat 2200 3205]
def conjugateMuAddress : List Op := [.add 2210 2210 3201]
def allScales : List (ℕ×ℕ) := seedScales++chunkScales++futureScales++matchingScales
def initializer : List Op := sizeBoot ++ scaled allScales ++ literalHeaders ++ dataAddress ++ selectedWidth ++ conjugateMuAddress
lemma initializer_length : initializer.length=125 := rfl

/-- A generic Nat-only frame, used to retain the actual physical startup banks. -/
def natOnly : Op→Bool
 | .literal _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .getNat _ _ => true
 | _ => false
lemma natOnly_frame (ops : List Op) (h:ops.all natOnly=true) (s:State) :
 (applyBlock ops s).natHeap=s.natHeap ∧ (applyBlock ops s).scalarHeap=s.scalarHeap ∧
 (applyBlock ops s).scalarReg=s.scalarReg ∧ (applyBlock ops s).outputs=s.outputs ∧
 (applyBlock ops s).rootOrders=s.rootOrders := by
 induction ops generalizing s with
 | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons o ops ih =>
   simp only [List.all_cons,Bool.and_eq_true] at h
   have ho:natOnly o=true:=h.1
   have ht:ops.all natOnly=true:=h.2
   have f:=ih ht (o.apply s)
   cases o <;> simp only [natOnly,Bool.false_eq_true] at ho
   all_goals simpa only [applyBlock,Op.apply,writeNat,next] using f
lemma initializer_natOnly : initializer.all natOnly=true := by decide
lemma initializer_frame (s:State) :
 (applyBlock initializer s).natHeap=s.natHeap ∧ (applyBlock initializer s).scalarHeap=s.scalarHeap ∧
 (applyBlock initializer s).scalarReg=s.scalarReg ∧ (applyBlock initializer s).outputs=s.outputs ∧
 (applyBlock initializer s).rootOrders=s.rootOrders := natOnly_frame _ initializer_natOnly s

lemma scaled_append (xs ys : List (ℕ×ℕ)) : scaled (xs++ys)=scaled xs++scaled ys := List.flatMap_append
lemma applyBlock_append (a b:List Op) (s:State) : applyBlock (a++b) s=applyBlock b (applyBlock a s) :=
 UniformSeedChunkPreparation.applyBlock_append a b s
lemma multiple_register (s:State) (d k q:ℕ) (_hd:d≠3203) (hq:s.natReg 3203=q) (r:ℕ) (hr:r≠3204) :
 (applyBlock (multiple d k) s).natReg r=if r=d then q*k else s.natReg r := by
 by_cases he:r=d
 · subst r;simp (disch:=omega) [multiple,applyBlock,Op.apply,writeNat,next,hq]
 · simp (disch:=omega) [multiple,applyBlock,Op.apply,writeNat,next,hq,he]

lemma scaled_register (xs:List (ℕ×ℕ)) (s:State) (q:ℕ)
 (hq:s.natReg 3203=q) (hd:∀p∈xs,p.1≠3203 ∧ p.1≠3204) :
 ∀r,r≠3204→(applyBlock (scaled xs) s).natReg r=
   (xs.foldl (fun f p=>Function.update f p.1 (q*p.2)) s.natReg) r := by
 induction xs generalizing s with
 | nil => intro r hr;rfl
 | cons p xs ih =>
   have hp:=hd p (by simp)
   have ht:∀v∈xs,v.1≠3203 ∧ v.1≠3204:=by intro v hv;exact hd v (by simp [hv])
   have root:(applyBlock (multiple p.1 p.2) s).natReg 3203=q:=by
    rw [multiple_register s p.1 p.2 q hp.1 hq 3203 (by decide),ite_eq_right (Ne.symm hp.1)];exact hq
   intro r hr
   simp only [scaled,List.flatMap_cons,applyBlock_append]
   change (applyBlock (scaled xs) (applyBlock (multiple p.1 p.2) s)).natReg r = _
   rw [ih _ root ht r hr]
   have congruent : ∀(ys:List (ℕ×ℕ)) (a b:ℕ→ℕ),
    (∀v,v≠3204→a v=b v)→
    ∀v,v≠3204→(ys.foldl (fun f p=>Function.update f p.1 (q*p.2)) a) v=
      (ys.foldl (fun f p=>Function.update f p.1 (q*p.2)) b) v:=by
    intro ys
    induction ys with
    | nil => intro a b hab v hv;exact hab v hv
    | cons w ys ih =>
      intro a b hab v hv
      apply ih _ _ _ v hv
      intro t ht
      by_cases he:t=w.1
      · subst t;simp
      · simpa only [Function.update_of_ne he] using hab t ht
   simp only [List.foldl_cons]
   apply congruent xs _ _ _ r hr
   intro v hv
   rw [multiple_register s p.1 p.2 q hp.1 hq v hv]
   by_cases he:v=p.1
   · subst v;simp
   · simp [he]

lemma scaled_safe (xs:List (ℕ×ℕ)) (s:State) (q B:ℕ)
 (hq:s.natReg 3203=q) (hd:∀p∈xs,p.1≠3203 ∧ p.1≠3204)
 (fit:∀p∈xs,p.2≤B ∧ q*p.2≤B) : readable (scaled xs) s ∧ peak (scaled xs) s≤B := by
 induction xs generalizing s with
 | nil => simp [scaled,readable,peak]
 | cons p xs ih =>
   have hp:=hd p (by simp)
   have ht:∀v∈xs,v.1≠3203 ∧ v.1≠3204:=by intro v hv;exact hd v (by simp [hv])
   have root:(applyBlock (multiple p.1 p.2) s).natReg 3203=q:=by
    rw [multiple_register s p.1 p.2 q hp.1 hq 3203 (by decide),ite_eq_right (Ne.symm hp.1)];exact hq
   have f:=fit p (by simp)
   have tail:=ih _ root ht (fun v hv=>fit v (by simp [hv]))
   constructor
   · change True ∧ True ∧ readable (scaled xs) (applyBlock (multiple p.1 p.2) s)
     exact ⟨True.intro,True.intro,tail.1⟩
   · change max p.2 (max (s.natReg 3203*p.2) (peak (scaled xs) (applyBlock (multiple p.1 p.2) s)))≤B
     rw [hq,max_le_iff,max_le_iff];exact ⟨f.1,f.2,tail.2⟩


lemma scaled_keeps (xs:List (ℕ×ℕ)) (s:State) (q:ℕ) (hq:s.natReg 3203=q)
 (hd:∀p∈xs,p.1≠3203 ∧ p.1≠3204) (r:ℕ) (hr:r≠3204) (hne:∀p∈xs,r≠p.1) :
 (applyBlock (scaled xs) s).natReg r=s.natReg r := by
 rw [scaled_register xs s q hq hd r hr]
 have f:∀(ys:List (ℕ×ℕ)) (g:ℕ→ℕ),(∀p∈ys,r≠p.1)→
  (ys.foldl (fun f p=>Function.update f p.1 (q*p.2)) g) r=g r:=by
  intro ys;induction ys with
  | nil => intro g _;rfl
  | cons p ys ih =>
    intro g h
    rw [List.foldl_cons,ih _ (fun v hv=>h v (by simp [hv])),Function.update_of_ne (h p (by simp))]
 exact f xs _ hne


lemma scaled_value (xs:List (ℕ×ℕ)) (s:State) (q:ℕ) (hq:s.natReg 3203=q)
 (hd:∀p∈xs,p.1≠3203 ∧ p.1≠3204) (unique:(xs.map Prod.fst).Nodup)
 (r k:ℕ) (member:(r,k)∈xs) : (applyBlock (scaled xs) s).natReg r=q*k := by
 induction xs generalizing s with
 | nil => simp at member
 | cons p xs ih =>
  have hp:=hd p (by simp)
  have ht:∀v∈xs,v.1≠3203 ∧ v.1≠3204:=by intro v hv;exact hd v (by simp [hv])
  simp only [List.map_cons,List.nodup_cons] at unique
  have root:(applyBlock (multiple p.1 p.2) s).natReg 3203=q:=by
   rw [multiple_register s p.1 p.2 q hp.1 hq 3203 (by decide),ite_eq_right (Ne.symm hp.1)];exact hq
  simp only [scaled,List.flatMap_cons,applyBlock_append]
  change (applyBlock (scaled xs) (applyBlock (multiple p.1 p.2) s)).natReg r=q*k
  rcases List.mem_cons.mp member with eq|mem
  · cases eq
    rw [scaled_keeps xs _ q root ht r hp.2]
    · simpa only [ite_true] using multiple_register s r k q hp.1 hq r hp.2
    · intro v hv he
      exact unique.1 (List.mem_map.mpr ⟨v,hv,he.symm⟩)
  · exact ih _ root ht unique.2 mem

lemma allScales_unique : (allScales.map Prod.fst).Nodup := by decide

def scaledState (s:State) := applyBlock (scaled allScales) (applyBlock sizeBoot s)
lemma prefix_split (s:State) : applyBlock (sizeBoot++scaled allScales) s=scaledState s :=
 applyBlock_append _ _ _
def post : List Op := literalHeaders++dataAddress++selectedWidth++conjugateMuAddress
lemma initializer_split (s:State) : applyBlock initializer s=applyBlock post (scaledState s) := by
 simp only [initializer,post,scaledState,applyBlock_append]
lemma sizeBoot_frame (s:State) :
 (applyBlock sizeBoot s).natHeap=s.natHeap ∧ (applyBlock sizeBoot s).scalarHeap=s.scalarHeap ∧
 (applyBlock sizeBoot s).scalarReg=s.scalarReg ∧ (applyBlock sizeBoot s).outputs=s.outputs ∧
 (applyBlock sizeBoot s).rootOrders=s.rootOrders := natOnly_frame _ (by decide) s
lemma sizeBoot_root {n:ℕ} {s:State} (hn:s.natReg 101=n) :
 (applyBlock sizeBoot s).natReg 3203=arena n := by
 simp [sizeBoot,applyBlock,Op.apply,writeNat,next,hn,arena,pow_two,Nat.mul_comm]
lemma allScales_distinct : ∀p∈allScales,p.1≠3203 ∧ p.1≠3204 := by decide
lemma prefix_frame (s:State) :
 (scaledState s).natHeap=s.natHeap ∧ (scaledState s).scalarHeap=s.scalarHeap ∧
 (scaledState s).scalarReg=s.scalarReg ∧ (scaledState s).outputs=s.outputs ∧ (scaledState s).rootOrders=s.rootOrders :=
 by
 simpa only [scaledState,applyBlock_append] using natOnly_frame (sizeBoot++scaled allScales) (by decide) s
lemma prefix_register {n:ℕ} {s:State} (hn:s.natReg 101=n) (r:ℕ) (hr:r≠3204) :
 (scaledState s).natReg r=(allScales.foldl (fun f p=>Function.update f p.1 (arena n*p.2))
  (applyBlock sizeBoot s).natReg) r :=
 scaled_register _ _ _ (sizeBoot_root hn) allScales_distinct r hr

lemma prefix_value {n:ℕ} {s:State} (hn:s.natReg 101=n) (r k:ℕ) (member:(r,k)∈allScales) :
 (scaledState s).natReg r=arena n*k :=
 scaled_value _ _ _ (sizeBoot_root hn) allScales_distinct allScales_unique r k member
def scaleFactor : ℕ→ℕ
 | 1127 | 1129 => 2
 | 1128 | 1131 => 3
 | 1130 | 1132 | 2205 => 4
 | 1133 | 1136 | 2206 => 5
 | 1134 | 1137 | 2207 => 6
 | 1135 | 2257 => 7
 | 1220 | 2259 => 8
 | 1221 | 2261 => 9
 | 1222 | 2250 | 2208 => 10
 | 1223 | 2209 | 2210 => 11
 | 1230 | 1453 | 2202 => 12
 | 1231 | 1454 | 2201 => 13
 | 1232 => 14
 | 1233 | 2204 => 15
 | 1234 => 16
 | 1235 => 17
 | 1236 => 18
 | 1237 => 19
 | 1450 => 20
 | 1451 => 21
 | 1452 | 2203 => 22
 | 2260 => 23
 | 2262 => 24
 | 2263 => 25
 | 2264 => 26
 | _ => 0
lemma allScales_factor : ∀p∈allScales,p.2=scaleFactor p.1 := by decide
lemma prefix_declared {n:ℕ} {s:State} (hn:s.natReg 101=n) (r:ℕ)
 (member:r∈allScales.map Prod.fst) :
 (scaledState s).natReg r=arena n*scaleFactor r := by
 obtain ⟨p,hp,hr⟩:=List.mem_map.mp member
 have hv:=prefix_value hn p.1 p.2 hp
 rw [allScales_factor p hp,hr] at hv
 exact hv

lemma prefix_saved {n:ℕ} {s:State} (hn:s.natReg 101=n) (r:ℕ) (lo:100≤r) (hi:r≤106) :
 (scaledState s).natReg r=s.natReg r := by
 rw [prefix_register hn r (by omega)]
 simp (disch:=omega) [allScales,seedScales,chunkScales,futureScales,matchingScales,List.foldl,
  sizeBoot,applyBlock,Op.apply,writeNat,next]

lemma post_saved (s:State) (r:ℕ) (lo:100≤r) (hi:r≤106) :
 (applyBlock post s).natReg r=s.natReg r := by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp (disch:=omega) [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,
  UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma initializer_saved (s:State) (r:ℕ) (lo:100≤r) (hi:r≤106) :
 (applyBlock initializer s).natReg r=s.natReg r := by
 rw [initializer_split,post_saved _ _ lo hi]
 change (applyBlock (scaled allScales) (applyBlock sizeBoot s)).natReg r=s.natReg r
 rw [←applyBlock_append]
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp (disch:=omega) [sizeBoot,scaled,allScales,seedScales,chunkScales,futureScales,matchingScales,multiple,
  UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma initializer_metadata {n:ℕ} {s:State} (h:UniformPermutationInversePreparation.Metadata n s) :
 UniformPermutationInversePreparation.Metadata n (applyBlock initializer s) := by
 apply h.transport_saved
 · constructor
   all_goals rw [initializer_saved s _ (by decide) (by decide)]
   all_goals first
    | exact h.saved.nextPrime
    | exact h.saved.inputLength
    | exact h.saved.count
    | exact h.saved.workingLength
    | exact h.saved.masterRoot
    | exact h.saved.copyAddress
    | exact h.saved.copyLength
 · intro a _;exact congrFun (initializer_frame s).1 _

/-- These projected register semantics are only26 instructions deep. The
separate prefix lemma avoids expanding the entire125-instruction state term. -/
lemma post_register (s:State) (r:ℕ) (hr:r<3000) :
 (applyBlock post s).natReg r=
 if r=2210 then s.natReg 2210+s.natReg 3201 else
 if r=2200 then (s.natHeap (s.natReg 105+s.natReg 106+s.natReg 103+387)).getD 0 else
 if r=2240 then s.natReg 102+s.natReg 101*s.natReg 3202+7 else
 (applyBlock literalHeaders s).natReg r := by
 by_cases h0:r=2210
 · subst r;simp [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,
   applyBlock,Op.apply,writeNat,next]
 by_cases h1:r=2200
 · subst r;simp [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,
   applyBlock,Op.apply,writeNat,next]
 by_cases h2:r=2240
 · subst r;simp [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,
   applyBlock,Op.apply,writeNat,next]
 · simp (disch:=omega) [post,applyBlock_append,dataAddress,selectedWidth,conjugateMuAddress,
   applyBlock,Op.apply,writeNat,next,h0,h1,h2]

lemma literalHeaders_register (s:State) (r:ℕ) : (applyBlock literalHeaders s).natReg r=
 ([(1120,193),(1122,1),(1123,1),(1124,1),(1125,0),(1126,1),(1224,1),(1238,2),(1239,1),
 (2251,193),(2252,1),(2253,1),(2254,1),(2255,0),(2256,1),(2258,2)] : List (ℕ×ℕ)).foldl
  (fun f p=>Function.update f p.1 p.2) s.natReg r := rfl

lemma initializer_seed_args {n:ℕ} (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedChunkPreparation.Args n (selectedAxis n hc) (seed n) (applyBlock initializer s) := by
 constructor
 · refine ⟨?_,?_,?_⟩
   · rw [initializer_split,post_register _ _ (by decide)]
     simp [literalHeaders,applyBlock,Op.apply,writeNat,next,selectedAxis]
   · intro r lo hi
     interval_cases r
     all_goals rw [initializer_split,post_register _ _ (by decide)]
     all_goals simp [literalHeaders_register,List.foldl]
     all_goals try rw [prefix_declared metadata.saved.inputLength _ (by decide)]
     all_goals simp [scaleFactor,
      UniformSeedHeightPreparation.Config.register,UniformSeedHeightPreparation.Config.seed,
      UniformSeedRankCrossPreparation.Config.register,seed,arena,
      ]
     all_goals ring
   · intro r lo hi
     interval_cases r
     all_goals rw [initializer_split,post_register _ _ (by decide)]
     all_goals simp [literalHeaders_register,List.foldl]
     all_goals try rw [prefix_declared metadata.saved.inputLength _ (by decide)]
     all_goals simp [scaleFactor,
      UniformSeedHeightPreparation.Config.register,seed,arena,
      ]
     all_goals ring
 · intro r lo hi
   interval_cases r
   all_goals rw [initializer_split,post_register _ _ (by decide)]
   all_goals simp [literalHeaders_register,List.foldl]
   all_goals try rw [prefix_declared metadata.saved.inputLength _ (by decide)]
   all_goals simp [scaleFactor,
    UniformSeedChunkPreparation.Config.register,seed,arena,
    ]
   all_goals ring

attribute [local irreducible] initializer scaledState packingLayout

lemma prefix_one_two {n:ℕ} {s:State} (hn:s.natReg 101=n) :
 (scaledState s).natReg 3201=1 ∧ (scaledState s).natReg 3202=2 ∧ (scaledState s).natReg 3203=arena n := by
 constructor
 · rw [prefix_register hn _ (by decide)]
   simp [allScales,seedScales,chunkScales,futureScales,matchingScales,List.foldl,
    sizeBoot,applyBlock,Op.apply,writeNat,next]
 constructor
 · rw [prefix_register hn _ (by decide)]
   simp [allScales,seedScales,chunkScales,futureScales,matchingScales,List.foldl,
    sizeBoot,applyBlock,Op.apply,writeNat,next]
 · rw [prefix_register hn _ (by decide)]
   simp [allScales,seedScales,chunkScales,futureScales,matchingScales,List.foldl,
    sizeBoot,applyBlock,Op.apply,writeNat,next,hn,arena,pow_two,Nat.mul_comm]

lemma prefix_width_cell {n:ℕ} (hc:194≤ell n) {s:State}
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 (scaledState s).natHeap ((scaledState s).natReg 105+(scaledState s).natReg 106+
   (scaledState s).natReg 103+387)=some (radix n (selectedAxis n hc)) := by
 rw [(prefix_frame s).1,prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
  prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
  prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
  metadata.saved.copyAddress,metadata.saved.copyLength,metadata.saved.workingLength,
  UniformAllAxisSeedPreparation.directory_after_protected]
 simpa only [selectedAxis,show 2*193+1=387 by decide,Nat.add_assoc] using ret.width (selectedAxis n hc) (selectedAxis n hc).isLt

lemma initializer_low {n:ℕ} {s:State} (metadata:UniformPermutationInversePreparation.Metadata n s) :
 (applyBlock initializer s).natReg 2240=UniformPaddedInputPreparation.dataBase n := by
 rw [initializer_split,post_register _ _ (by decide)]
 norm_num only
 rw [prefix_saved metadata.saved.inputLength 102 (by decide) (by decide),
  prefix_saved metadata.saved.inputLength 101 (by decide) (by decide),
  (prefix_one_two metadata.saved.inputLength).2.1,metadata.saved.count,metadata.saved.inputLength]
 simp only [ite_false,ite_true]
 change ell n+n*2+7=ell n+7+2*n
 omega

lemma initializer_packing_args {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedChunkPackingPreparation.Args (packingLayout hn hc) (applyBlock initializer s) := by
 refine ⟨?_,?_,?_,?_,?_⟩
 all_goals rw [initializer_split,post_register _ _ (by decide)]
 all_goals simp [literalHeaders_register,List.foldl]
 all_goals rw [prefix_declared metadata.saved.inputLength _ (by decide)]
 all_goals simp [scaleFactor,packingLayout,packing,Nat.mul_comm]

lemma initializer_future_args {n:ℕ} (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedHighDataMatchingPreparation.FutureArgs
  (UniformConjugatePackedMatchingPreparation.workParameters n (selectedAxis n hc) (seed n) (work n))
  (10*arena n) (selectedAxis n hc) (applyBlock initializer s) := by
 constructor
 all_goals rw [initializer_split,post_register _ _ (by decide)]
 all_goals simp [literalHeaders_register,List.foldl]
 all_goals try rw [prefix_declared metadata.saved.inputLength _ (by decide)]
 all_goals simp [scaleFactor,
  UniformConjugatePackedMatchingPreparation.workParameters,UniformConjugateRankSpectrumPreparation.relocated,
  UniformSeedHeightPreparation.parameters,UniformSeedRankCrossPreparation.parameters,
  UniformSeedHeightPreparation.Config.seed,seed,work,selectedAxis,Nat.mul_comm]
 all_goals norm_num [UniformSeedHeightPreparation.Config.exponent,UniformWorkspacePlanner.exponent]

lemma initializer_matching_args {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig (packingLayout hn hc)
   (10*arena n) (11*arena n) (11*arena n+1)) (applyBlock initializer s) := by
 intro r lo hi
 interval_cases r
 all_goals rw [initializer_split,post_register _ _ (by decide)]
 all_goals simp only [literalHeaders_register,List.foldl_cons,List.foldl_nil]
 all_goals simp []
 all_goals try rw [prefix_width_cell hc metadata ret]
 all_goals try rw [(prefix_one_two metadata.saved.inputLength).1]
 all_goals try rw [prefix_declared metadata.saved.inputLength _ (by decide)]
 all_goals simp [scaleFactor,
  UniformConjugatePackedMatchingPreparation.register,UniformConjugatePackedMatchingPreparation.matchingConfig,
  UniformPackedMatchingShearMachine.packingConfig,packingLayout,packing,seed,Nat.mul_comm]

lemma readable_append (a b:List Op) (s:State) : readable (a++b) s ↔
 readable a s ∧ readable b (applyBlock a s) := by
 induction a generalizing s with
 | nil=>simp [readable,applyBlock]
 | cons o a ih=>simp only [List.cons_append,readable,applyBlock,ih,and_assoc]
lemma peak_append (a b:List Op) (s:State) : peak (a++b) s=max (peak a s) (peak b (applyBlock a s)) := by
 induction a generalizing s with
 | nil=>simp [peak,applyBlock]
 | cons o a ih=>simp only [List.cons_append,peak,applyBlock,ih,max_assoc]

lemma sizeBoot_safe {n:ℕ} (hn:0<n) (s:State) (length:s.natReg 101=n) :
 readable sizeBoot s ∧ peak sizeBoot s≤budget n := by
 have ha:=arena_bounds hn
 have sq:(n+2)^2≤arena n:=by unfold arena;nlinarith
 have le:n+2≤(n+2)^2:=by nlinarith
 constructor
 · simp [sizeBoot,readable,Op.readable]
 · simp [sizeBoot,peak,Op.peak,Op.apply,writeNat,next,length]
   unfold arena at ha sq
   repeat' apply And.intro
   all_goals nlinarith

lemma allScales_fit {n:ℕ} (hn:0<n) : ∀p∈allScales,p.2≤budget n ∧ arena n*p.2≤budget n := by
 have ha:=arena_bounds hn
 have hf:∀p∈allScales,p.2≤26:=by decide
 intro p hp
 have hc:=hf p hp
 have hmul:=Nat.mul_le_mul_left (arena n) hc
 omega

lemma post_safe {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 readable post (scaledState s) ∧ peak post (scaledState s)≤budget n := by
 have ha:=arena_bounds hn
 have hp:=protected_bound hn
 have hr:=radix_bound hn (selectedAxis n hc)
 have he:=ell_bound n
 have cell:=prefix_width_cell hc metadata ret
 have one:=(prefix_one_two metadata.saved.inputLength).1
 have two:=(prefix_one_two metadata.saved.inputLength).2.1
 have mu:(scaledState s).natReg 2210=11*arena n:=by
  simpa only [Nat.mul_comm] using prefix_value metadata.saved.inputLength 2210 11 (by decide)
 have dir:(scaledState s).natReg 105+(scaledState s).natReg 106+(scaledState s).natReg 103+387=
   UniformAllAxisSeedPreparation.directoryBase n+387:=by
  rw [prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
   prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
   prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
   metadata.saved.copyAddress,metadata.saved.copyLength,metadata.saved.workingLength,
   UniformAllAxisSeedPreparation.directory_after_protected]
 have db:UniformAllAxisSeedPreparation.directoryBase n+387≤1000*(n+2)^2:=by
  have old:=old_directory_end n
  have haxis:194≤axisCount n:=by unfold axisCount;omega
  omega
 constructor
 · simp [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,readable,Op.readable,
    Op.apply,writeNat,next,cell]
 · simp [post,literalHeaders,dataAddress,selectedWidth,conjugateMuAddress,peak,Op.peak,
    Op.apply,writeNat,next,cell,mu,one,two]
   rw [prefix_saved metadata.saved.inputLength _ (by decide) (by decide),
    prefix_saved metadata.saved.inputLength _ (by decide) (by decide),metadata.saved.inputLength,metadata.saved.count]
   have fields:=prefix_saved metadata.saved.inputLength
   have small:1000*(n+2)^2≤arena n:=by unfold arena;omega
   omega

lemma initializer_safe {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 readable initializer s ∧ peak initializer s≤budget n := by
 have boot:=sizeBoot_safe hn s metadata.saved.inputLength
 have mid:=scaled_safe allScales (applyBlock sizeBoot s) (arena n) (budget n)
  (sizeBoot_root metadata.saved.inputLength) allScales_distinct (allScales_fit hn)
 have last:=post_safe hn hc s metadata ret
 have eq:initializer=sizeBoot++scaled allScales++post:=by simp only [initializer,post,List.append_assoc]
 have read1:readable (sizeBoot++scaled allScales) s:=
  (readable_append _ _ _).mpr ⟨boot.1,mid.1⟩
 have peak1:peak (sizeBoot++scaled allScales) s≤budget n:=by
  rw [peak_append];exact max_le boot.2 mid.2
 have read2:readable ((sizeBoot++scaled allScales)++post) s:=by
  apply (readable_append _ _ _).mpr
  refine ⟨read1,?_⟩
  rw [prefix_split]
  exact last.1
 have peak2:peak ((sizeBoot++scaled allScales)++post) s≤budget n:=by
  rw [peak_append]
  apply max_le peak1
  rw [prefix_split]
  exact last.2
 rw [eq]
 exact ⟨read2,peak2⟩


lemma packing_shape {n:ℕ} (hn:0<n) (hc:194≤ell n) :
 (packingLayout hn hc).packing.total=radix n (selectedAxis n hc) ∧
 (packingLayout hn hc).packing.source=12*arena n := by
 unfold packingLayout
 exact ⟨rfl,rfl⟩

/-- Actual startup input cells, including their actual mixed dependency tags. -/
def original {n:ℕ} (hn:0<n) (hc:194≤ell n) (x:Fin n→ℂ) :
 Fin (packingLayout hn hc).packing.total→Scalar :=
 fun i=>UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x i.val
lemma original_present {n:ℕ} (hn:0<n) (hc:194≤ell n) (x:Fin n→ℂ) {s:State}
 (ops:UniformInitialPreparation.Operands n x s) :
 ∀i,s.scalarHeap (UniformPaddedInputPreparation.dataBase n+i.val)=some (original hn hc x i) := by
 intro i
 have hr:=UniformGlobalLocalPreparation.radix_le_length n (selectedAxis n hc)
 change radix n (selectedAxis n hc)≤len n at hr
 rw [←(packing_shape hn hc).1] at hr
 exact ops.input i.val (lt_of_lt_of_le i.isLt hr)
lemma low_separated {n:ℕ} (hn:0<n) (hc:194≤ell n) :
 UniformPaddedInputPreparation.dataBase n+(packingLayout hn hc).packing.total≤(packingLayout hn hc).packing.source := by
 have hp:=protected_bound hn
 have hr:=UniformGlobalLocalPreparation.radix_le_length n (selectedAxis n hc)
 change radix n (selectedAxis n hc)≤len n at hr
 rw [(packing_shape hn hc).1,(packing_shape hn hc).2]
 have hsum:UniformPaddedInputPreparation.dataBase n+radix n (selectedAxis n hc)≤UniformGlobalLocalPreparation.globalEnd n:=by
  rw [UniformGlobalLocalPreparation.globalEnd_formula]
  unfold UniformPaddedInputPreparation.dataBase
  change ell n+7+2*n+radix n (selectedAxis n hc)≤ell n+8+2*n+3*len n
  omega
 change UniformPaddedInputPreparation.dataBase n+radix n (selectedAxis n hc)≤12*arena n
 unfold arena
 omega

def entry (s:State):State:=setPC (applyBlock initializer s) 0
lemma entry_frame (s:State) : (entry s).natHeap=s.natHeap ∧ (entry s).scalarHeap=s.scalarHeap ∧
 (entry s).scalarReg=s.scalarReg ∧ (entry s).outputs=s.outputs ∧ (entry s).rootOrders=s.rootOrders := initializer_frame s
lemma entry_metadata {n:ℕ} {s:State} (h:UniformPermutationInversePreparation.Metadata n s) :
 UniformPermutationInversePreparation.Metadata n (entry s) :=
 (initializer_metadata h).transport (fun _ _=>rfl) (fun _ _=>rfl)
lemma entry_operands {n:ℕ} {s:State} {x:Fin n→ℂ} (h:UniformInitialPreparation.Operands n x s) :
 UniformInitialPreparation.Operands n x (entry s) := h.transport (entry_frame s).2.1
lemma entry_original {n:ℕ} {s:State} (h:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 UniformAllAxisSeedPreparation.Retained n (axisCount n) (entry s) :=
 h.transport_before (fun _ _=>congrFun (entry_frame s).2.1 _) (entry_frame s).1
lemma entry_conjugate {n:ℕ} {s:State} (h:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s) :
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) (entry s) :=
 h.transport (fun _ _ _=>congrFun (entry_frame s).2.1 _) (entry_frame s).1
lemma entry_seed_args {n:ℕ} (hc:194≤ell n) (s:State)
 (m:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedChunkPreparation.Args n (selectedAxis n hc) (seed n) (entry s) := by
 have h:=initializer_seed_args hc s m
 exact ⟨⟨h.seed.1,h.seed.2.1,h.seed.2.2⟩,h.extra⟩
lemma entry_packing_args {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (m:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedChunkPackingPreparation.Args (packingLayout hn hc) (entry s) := initializer_packing_args hn hc s m
lemma entry_future_args {n:ℕ} (hc:194≤ell n) (s:State)
 (m:UniformPermutationInversePreparation.Metadata n s) :
 UniformSeedHighDataMatchingPreparation.FutureArgs
  (UniformConjugatePackedMatchingPreparation.workParameters n (selectedAxis n hc) (seed n) (work n))
  (10*arena n) (selectedAxis n hc) (entry s) := by
 have h:=initializer_future_args hc s m
 exact ⟨h.V,h.axis,h.a,h.e,h.i0,h.j0,h.split,h.S,h.K,h.A,h.d,h.C,h.conv,h.tape,h.depth⟩
lemma entry_matching_args {n:ℕ} (hn:0<n) (hc:194≤ell n) (s:State)
 (m:UniformPermutationInversePreparation.Metadata n s)
 (ret:UniformAllAxisSeedPreparation.Retained n (axisCount n) s) :
 UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig (packingLayout hn hc)
   (10*arena n) (11*arena n) (11*arena n+1)) (entry s) := initializer_matching_args hn hc s m ret
lemma entry_low {n:ℕ} {s:State} (m:UniformPermutationInversePreparation.Metadata n s) :
 (entry s).natReg 2240=UniformPaddedInputPreparation.dataBase n := initializer_low m

/-- The single stored4255-instruction selected-axis program. Its only root
request is inside the original1460 startup prefix. -/
def head : Program := UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460) ++ initializer.map Op.code
def program : Program := head ++ UniformSeedHighDataMatchingPreparation.program.map (relocate 1585 4254) ++ [.halt]
lemma head_length : head.length=1585 := by
 simp only [head,List.length_append,List.length_map,UniformAllAxisConjugatePreparation.fullProgram_length,initializer_length]
lemma program_length : program.length=4255 := by
 simp only [program,List.length_append,List.length_map,head_length,UniformSeedHighDataMatchingPreparation.program_length];rfl
attribute [local irreducible] UniformAllAxisConjugatePreparation.fullProgram UniformSeedHighDataMatchingPreparation.program
lemma startup_code : CodeAt UniformAllAxisConjugatePreparation.fullProgram program 0 1460 := by
 have eq:program=UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460) ++
   (initializer.map Op.code++UniformSeedHighDataMatchingPreparation.program.map (relocate 1585 4254)++[.halt]):=by
  simp only [program,head,List.append_assoc]
 rw [eq]
 exact UniformAllAxisConjugatePreparation.relocated_prefix_code _ _ _
lemma initializer_code : BlockAt initializer program 1460 := by
 intro i hi
 have hs:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformAllAxisConjugatePreparation.fullProgram.map (relocate 0 1460)) (initializer.map Op.code)
  (UniformSeedHighDataMatchingPreparation.program.map (relocate 1585 4254)++[.halt]) i (by simpa using hi)
 simpa only [program,head,List.append_assoc,List.length_map,UniformAllAxisConjugatePreparation.fullProgram_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using hs
lemma matching_code : CodeAt UniformSeedHighDataMatchingPreparation.program program 1585 4254 :=
 UniformRankCrossPreparationMachine.segment_code head [.halt] _ _ _ head_length
lemma halt_at : program[4254]?=some .halt := by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (head++UniformSeedHighDataMatchingPreparation.program.map (relocate 1585 4254)) [.halt] [] 0 (by decide)
 simpa only [List.append_nil,List.append_assoc,program,List.length_append,List.length_map,
  head_length,UniformSeedHighDataMatchingPreparation.program_length,List.getElem?_cons_zero,show 1585+2669+0=4254 by decide] using h
lemma word_code {n:ℕ} (hn:0<n) :4255≤budget n := by
 have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
 norm_num at h
 unfold budget;omega


def runtimeBudget {n:ℕ} (hn:0<n) (hc:194≤ell n) :ℕ :=
 UniformAllAxisConjugatePreparation.fullBudget n+125+
 UniformSeedChunkPreparation.runtimeBudget n (selectedAxis n hc) (seed n)+
 UniformConjugatePackedMatchingPreparation.runtimeBudget (packingLayout hn hc) (work n)+
 220*(packingLayout hn hc).packing.total+62+1

/-- Closed empty-start selected-axis execution. The input is the physically
prepared mixed-tag startup array. All headers, all retained seeds, matching
count, packing, spectra and six-C action are produced by this stored program.
The selected-axis capacity hypothesis remains explicit. -/
theorem initial_execution {n:ℕ} (hn:0<n) (hc:194≤ell n) (x:Fin n→ℂ) : ∃u ticks,
 BoundedExecution program n x (budget n) initial ticks u ∧ ticks≤runtimeBudget hn hc ∧
 u.pc=4254 ∧ UniformHighDataConjugateMatchingPreparation.FullAction (packingLayout hn hc) (original hn hc x) u ∧
 UniformHighDataConjugateMatchingPreparation.LogicalPairs (packingLayout hn hc) (allocation hn hc).matching.capacity (original hn hc x) u ∧
 UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs := by
 obtain ⟨t,v,hv,hcost,hcRet,hoRet,hm,ho,hroots,hout,vp,hbudget⟩:=UniformAllAxisConjugatePreparation.initial_execution hn x
 have code:=word_code hn
 have first:=UniformBoundedAssembly.boundedExecution_placed startup_code
  (by rw [UniformAllAxisConjugatePreparation.fullProgram_length];omega :0+UniformAllAxisConjugatePreparation.fullProgram.length≤budget n)
  (by omega :1460≤budget n) hv
 rw [show placed 0 initial=initial by rfl] at first
 let s:State:={v with pc:=1460}
 have ms:UniformPermutationInversePreparation.Metadata n s:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
 have os:UniformInitialPreparation.Operands n x s:=ho.transport rfl
 have rs:UniformAllAxisSeedPreparation.Retained n (axisCount n) s:=hoRet.withPC
 have cs:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s:=hcRet.withPC
 have safe:=initializer_safe hn hc s ms rs
 have install:=block_runs initializer program 1460 n (budget n) x s initializer_code rfl first.final_bound
  (by rw [initializer_length];omega) safe.1 safe.2
 let e:=entry s
 have eb:WordBound (budget n) e:=changePC_bound _ _ 0 install.final_bound (by omega)
 have em:=entry_metadata ms
 have eo:=entry_operands os
 have er:=entry_original rs
 have ec:=entry_conjugate cs
 have low:=(entry_low ms)
 have present:=original_present hn hc x eo
 obtain ⟨z,tm,last,mcost,zp,action,logical,rz,cz,mz,oz,out,roots⟩:=
  UniformSeedHighDataMatchingPreparation.execution hn x (packingLayout hn hc)
   (UniformPaddedInputPreparation.dataBase n) (original hn hc x) e
   (entry_seed_args hc s ms) (entry_packing_args hn hc s ms) low present
   (low_separated hn hc) (placement hn hc) (work n) (10*arena n) (11*arena n) (11*arena n+1)
   (allocation hn hc) (entry_future_args hc s ms) (entry_matching_args hn hc s ms rs)
   em eo er ec (by rw [(packing_shape hn hc).1];exact freshness hn hc) (by omega) rfl eb
 have tail:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformSeedHighDataMatchingPreparation.program_length];omega :1585+UniformSeedHighDataMatchingPreparation.program.length≤budget n)
  (by omega :4254≤budget n) last
 have ep:(applyBlock initializer s).pc=1585:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,initializer_length]
 have eq:placed 1585 e=applyBlock initializer s:=UniformSeedRankCrossPreparation.placed_zero _ _ ep
 rw [eq] at tail
 let u:=setPC z 4254
 have stop:BoundedExecution program n x (budget n) u 1 u:=.halt tail.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:=first.executes (install.executes (tail.executes stop))
 refine ⟨u,t+UniformAllAxisSeedPreparation.preparationRuntime n+1+
   UniformAllAxisConjugatePreparation.preparationRuntime n+1+125+tm+1,?_,?_,rfl,
   action,logical,rz.withPC,cz.withPC,mz.transport (fun _ _=>rfl) (fun _ _=>rfl),oz.transport rfl,?_,?_⟩
 · simpa only [initializer_length,Nat.add_assoc] using all
 · unfold runtimeBudget;omega
 · exact roots.trans ((entry_frame s).2.2.2.2.trans hroots)
 · exact out.trans ((entry_frame s).2.2.2.1.trans hout)

end
end ExactFourierCircuits.UniformEmptyStartupMatchingPreparation
