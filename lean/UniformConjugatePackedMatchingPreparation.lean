import UniformConjugateRankSpectrumPreparation
import UniformPackedMatchingShearMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformConjugatePackedMatchingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformNewtonTableMachine (KeepsNat)
open UniformAllAxisSeedPreparation (axisCount)
namespace S
abbrev Parameters := UniformRankCrossPreparationMachine.Parameters
end S

/-- Actual conjugate producer writes below676 or in1800..1829. -/
def writeAllowed : Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
   decide (d < 676 ∨ (1800 ≤ d ∧ d < 1830))
 | _ => true
def footprint (p : Program) := p.all writeAllowed
lemma footprint_append (p q : Program) : footprint (p++q)= (footprint p && footprint q) := List.all_append
lemma writeAllowed_relocate (base ret : ℕ) (i : Instruction) :
 writeAllowed (relocate base ret i)=writeAllowed i := by cases i <;> rfl
lemma footprint_relocate (p : Program) (base ret : ℕ) :
 footprint (p.map (relocate base ret))=footprint p := by
 simp only [footprint,List.all_map,Function.comp_def,writeAllowed_relocate]
lemma rank_footprint : footprint UniformRankCrossPreparationMachine.program=true := by decide +kernel
lemma spectrum_footprint : footprint UniformConjugateRankSpectrumPreparation.program=true := by
 simp only [UniformConjugateRankSpectrumPreparation.program,footprint_append,
  footprint_relocate,rank_footprint,Bool.and_true]
 decide

def Stable (q : ℕ) : Prop := (676 ≤ q ∧ q < 1800) ∨ 1830 ≤ q
lemma spectrum_keeps (q : ℕ) (hq : Stable q) :
 ∀i∈UniformConjugateRankSpectrumPreparation.program,KeepsNat q i := by
 intro i hi
 dsimp only [Stable] at hq
 have allowed:=List.all_eq_true.mp spectrum_footprint i hi
 cases i <;> simp only [writeAllowed,decide_eq_true_eq] at allowed
 all_goals simp only [KeepsNat]
 all_goals omega

def setup : List Op := [.literal 2211 0,
 .add 1640 2200 2211,.add 1641 2201 2211,.add 1642 2202 2211,
 .add 1643 2203 2211,.add 1644 2204 2211,.add 1645 2205 2211,
 .add 1646 2206 2211,.add 1647 2207 2211,.add 1648 2208 2211,
 .add 1649 2209 2211,.add 1650 2210 2211]
def program : Program :=
 UniformConjugateRankSpectrumPreparation.program.map (relocate 0 763) ++
 setup.map Op.code ++ UniformPackedMatchingShearMachine.program.map (relocate 775 1197) ++ [.halt]
lemma setup_length : setup.length=12 := rfl
lemma program_length : program.length=1198 := by
 simp only [program,List.length_append,List.length_map,UniformConjugateRankSpectrumPreparation.program_length,
  setup_length,UniformPackedMatchingShearMachine.program_length,List.length_singleton]

attribute [local irreducible] UniformConjugateRankSpectrumPreparation.program UniformPackedMatchingShearMachine.program
lemma spectrum_code : CodeAt UniformConjugateRankSpectrumPreparation.program program 0 763 := by
 let rest:=setup.map Op.code ++ UniformPackedMatchingShearMachine.program.map (relocate 775 1197) ++ [.halt]
 have eq:program=[]++UniformConjugateRankSpectrumPreparation.program.map (relocate 0 763)++rest:=by
  simp only [program,rest,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] rest _ 0 763 rfl
lemma setup_code : BlockAt setup program 763 := by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformConjugateRankSpectrumPreparation.program.map (relocate 0 763)) (setup.map Op.code)
  (UniformPackedMatchingShearMachine.program.map (relocate 775 1197)++[.halt]) i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_map,UniformConjugateRankSpectrumPreparation.program_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using lookup
lemma matching_code : CodeAt UniformPackedMatchingShearMachine.program program 775 1197 := by
 let before:=UniformConjugateRankSpectrumPreparation.program.map (relocate 0 763)++setup.map Op.code
 have eq:program=before++UniformPackedMatchingShearMachine.program.map (relocate 775 1197)++[.halt]:=by
  simp only [program,before,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code before [.halt] _ 775 1197 (by
  simp only [before,List.length_append,List.length_map,UniformConjugateRankSpectrumPreparation.program_length,setup_length])
lemma halt_at : program[1197]?=some .halt := by
 let before:=UniformConjugateRankSpectrumPreparation.program.map (relocate 0 763)++setup.map Op.code++
  UniformPackedMatchingShearMachine.program.map (relocate 775 1197)
 have len:before.length=1197:=by
  simp only [before,List.length_append,List.length_map,UniformConjugateRankSpectrumPreparation.program_length,
   setup_length,UniformPackedMatchingShearMachine.program_length]
 change (before++[.halt])[1197]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
variable {n B : ℕ} {j : Fin (axisCount n)} {seed : UniformSeedChunkPreparation.Config}
abbrev workParameters (n : ℕ) (j : Fin (axisCount n)) (seed : UniformSeedChunkPreparation.Config) (work : S.Parameters) :=
 UniformConjugateRankSpectrumPreparation.relocated (UniformSeedHeightPreparation.parameters n j seed.seed).base work
abbrev coefficients (n : ℕ) (j : Fin (axisCount n)) (seed : UniformSeedChunkPreparation.Config) :
 Fin (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) → ℂ := fun i =>
 UniformRankCrossReplayPreparationMachine.bankValues (UniformSeedHeightPreparation.parameters n j seed.seed)
  (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val
abbrev matchingConfig (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (V mu bar : ℕ) :=
 UniformPackedMatchingShearMachine.packingConfig p.packing seed.mapped seed.seed.C seed.seed.negative seed.seed.constants V mu bar
def register (c : UniformPackedMatchingShearMachine.Config) : ℕ → ℕ
 | 2200=>c.length | 2201=>c.packed | 2202=>c.destination | 2203=>c.inverse | 2204=>c.rows
 | 2205=>c.positive | 2206=>c.negative | 2207=>c.constants | 2208=>c.conjugates
 | 2209=>c.mu | _=>c.conjugateMu
def HeaderArgs (c : UniformPackedMatchingShearMachine.Config) (s : State) : Prop :=
 ∀q,2200 ≤ q → q ≤ 2210 → s.natReg q=register c q

/-- Placement facts only. No generated table, spectrum or action is supplied.
Data arrays lie above the new coefficient bank, as required by Packed422. -/
structure Allocation (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (work : S.Parameters) (V mu bar : ℕ) : Prop where
 spectrum : UniformConjugateRankSpectrumPreparation.Allocation n j (workParameters n j seed work) V B
 matching : UniformPackedMatchingShearMachine.Layout (matchingConfig p V mu bar)
  (UniformPackedMatchingShearMachine.seedRows p).length (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) B
 positiveBefore : seed.seed.C+7*seed.seed.width ≤ work.S
 negativeBefore : seed.seed.negative+7*seed.seed.width ≤ work.S
 constantsBefore : seed.seed.constants+6 ≤ work.S
 rowsBefore : seed.mapped+3*(UniformPackedMatchingShearMachine.seedRows p).length ≤ work.d ∧
  seed.mapped+3*(UniformPackedMatchingShearMachine.seedRows p).length ≤ work.conv ∧
  seed.mapped+3*(UniformPackedMatchingShearMachine.seedRows p).length ≤ work.tape ∧
  seed.mapped+3*(UniformPackedMatchingShearMachine.seedRows p).length ≤ work.depth
 inverseBefore : p.packing.inverse+p.packing.total ≤ work.d ∧ p.packing.inverse+p.packing.total ≤ work.conv ∧
  p.packing.inverse+p.packing.total ≤ work.tape ∧ p.packing.inverse+p.packing.total ≤ work.depth
 code : 1198 ≤ B

lemma setup_frame (s : State) : (applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧ (applyBlock setup s).scalarReg=s.scalarReg ∧
 (applyBlock setup s).outputs=s.outputs ∧ (applyBlock setup s).rootOrders=s.rootOrders ∧
 (∀q,q≠2211 → (q<1640 ∨ 1650<q) → (applyBlock setup s).natReg q=s.natReg q) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q h0 h1
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_spec (c : UniformPackedMatchingShearMachine.Config) (s : State) (h : HeaderArgs c s) :
 UniformPackedMatchingShearMachine.Header c (applyBlock setup s) := by
 have h0:=h 2200 (by omega) (by omega);have h1:=h 2201 (by omega) (by omega)
 have h2:=h 2202 (by omega) (by omega);have h3:=h 2203 (by omega) (by omega)
 have h4:=h 2204 (by omega) (by omega);have h5:=h 2205 (by omega) (by omega)
 have h6:=h 2206 (by omega) (by omega);have h7:=h 2207 (by omega) (by omega)
 have h8:=h 2208 (by omega) (by omega);have h9:=h 2209 (by omega) (by omega)
 have h10:=h 2210 (by omega) (by omega)
 constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,register]
lemma setup_safe (s : State) (hb : WordBound B s) : readable setup s ∧ peak setup s ≤ B := by
 refine ⟨by simp [setup,readable,Op.readable],?_⟩
 simp only [setup,peak,Op.peak,Op.apply,writeNat,next]
 simp
 repeat' apply And.intro
 all_goals exact hb.2.1 _

lemma scalar_above {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters} {V mu bar : ℕ}
 (a : Allocation p work V mu bar) {s u : State}
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u)
 (i : ℕ) (hi : V+7*seed.seed.width ≤ i) : u.scalarHeap i=s.scalarHeap i := by
 have hw:UniformRadixTwoDAG.width (UniformSeedHeightPreparation.parameters n j seed.seed).base.K=seed.seed.width:=rfl
 have chain:=a.spectrum.scalar_chain
 have h0:=a.spectrum.layout.2.1.sourceEnd
 have h1:=a.spectrum.layout.2.1.bankAfter
 have h2:=a.spectrum.reversedFresh
 apply f.2.1 i <;> apply Or.inr
 all_goals dsimp only [workParameters,UniformConjugateRankSpectrumPreparation.relocated,
  UniformConjugateRankSpectrumPreparation.selected] at *
 all_goals rw [hw] at *
 all_goals omega

lemma nat_below {work : S.Parameters} {V : ℕ} {s u : State}
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u)
 (i : ℕ) (h0 : i<work.d) (h1 : i<work.conv) (h2 : i<work.tape) (h3 : i<work.depth) :
 u.natHeap i=s.natHeap i := f.1 i (Or.inl h0) (Or.inl h1) (Or.inl h2) (Or.inl h3)

lemma generated_table_retained {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters}
 {V mu bar : ℕ} (a : Allocation p work V mu bar) {origin s u : State}
 (hn : 0<n) (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 (original : Fin p.packing.total → Scalar) (packed : UniformSeedChunkPackingPreparation.Packed p original origin s)
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u) :
 UniformCrossShearTableMachine.Table seed.mapped (UniformPackedMatchingShearMachine.seedRows p) u := by
 have old:=UniformPackedMatchingShearMachine.generated_table hn p post packed
 intro i hi
 have bound:=a.rowsBefore;have same:=nat_below f
 rcases old i hi with ⟨h0,h1,h2⟩
 refine ⟨?_,?_,?_⟩
 all_goals rw [same _ (by omega) (by omega) (by omega) (by omega)]
 · exact h0
 · exact h1
 · exact h2

lemma generated_inverse_retained {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters}
 {V mu bar : ℕ} (a : Allocation p work V mu bar) {origin s u : State}
 (original : Fin p.packing.total → Scalar) (packed : UniformSeedChunkPackingPreparation.Packed p original origin s)
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u) :
 UniformGlobalNatPreparation.PermutationBank p.packing.total p.packing.inverse u.natHeap
  (UniformSeedChunkPackingPreparation.unpacking p) := by
 intro i
 have bound:=a.inverseBefore;have hi:=i.isLt
 rw [nat_below f _ (by omega) (by omega) (by omega) (by omega)]
 exact packed.inverse i

def packedValues (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (original : Fin p.packing.total → Scalar) (i : ℕ) : Scalar :=
 if hi:i<p.packing.total then original (UniformSeedChunkPackingPreparation.unpacking p ⟨i,hi⟩) else Scalar.zero

lemma generated_data_retained {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters}
 {V mu bar : ℕ} (a : Allocation p work V mu bar) {origin s u : State}
 (original : Fin p.packing.total → Scalar) (packed : UniformSeedChunkPackingPreparation.Packed p original origin s)
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u) :
 UniformPackedMatchingShearMachine.Packed (matchingConfig p V mu bar) (packedValues p original) u := by
 intro i hi
 have hi':i<p.packing.total:=hi
 have hw:UniformRadixTwoDAG.width seed.seed.exponent=seed.seed.width:=rfl
 have hr:=a.matching.coefficient.conjugatesBelow
 have hm:=a.matching.coefficient.destinations
 have hd:=a.matching.packedFresh
 change u.scalarHeap (p.packing.destination+i)=_
 rw [scalar_above a f _ (by
  change V+UniformToeplitzCrossDAG.bankSize seed.seed.exponent ≤ mu at hr
  unfold UniformToeplitzCrossDAG.bankSize at hr
  rw [hw] at hr
  change bar<p.packing.destination at hd
  change mu<bar at hm
  omega)]
 simpa only [packedValues,dite_eq_left hi'] using packed.values ⟨i,hi'⟩

/-- Guarded coefficient sources are derived from the actual old banks through
packing retention and the newly executed spectrum producer. -/
lemma produced_sources {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters}
 {V mu bar : ℕ} (a : Allocation p work V mu bar) {origin s u : State}
 (hn : 0<n) (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 (original : Fin p.packing.total → Scalar) (packed : UniformSeedChunkPackingPreparation.Packed p original origin s)
 (new : UniformConjugateRankSpectrumPreparation.Result n j (workParameters n j seed work) V u)
 (f : UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s u) :
 UniformMatchingConjugateLoadMachine.Sources seed.seed.exponent seed.seed.C seed.seed.negative seed.seed.constants V
  (coefficients n j seed) u := by
 let par:=UniformSeedHeightPreparation.parameters n j seed.seed
 have old:=packed.coefficientBanks hn p post
 have pos:=UniformRankCrossReplayPreparationMachine.bank_source (p:=par) old.1
 have hw:UniformRadixTwoDAG.width seed.seed.exponent=seed.seed.width:=rfl
 refine ⟨?_,?_,?_,?_⟩
 · intro i
   have hi:i.val<7*seed.seed.width:=by have:=i.isLt;change i.val<seed.seed.width+6*seed.seed.width at this;omega
   exact (f.scalar_before a.spectrum _ (by have:=a.positiveBefore;change _<work.S;omega)).trans (pos i.val hi)
 · intro i
   have hi:i.val<7*seed.seed.width:=by have:=i.isLt;change i.val<seed.seed.width+6*seed.seed.width at this;omega
   exact (f.scalar_before a.spectrum _ (by have:=a.negativeBefore;change _<work.S;omega)).trans (old.2.2.1 i.val hi)
 · intro i
   have hi:i.val<7*UniformRadixTwoDAG.width par.base.K:=by
    have:=i.isLt;change i.val<UniformRadixTwoDAG.width seed.seed.exponent+6*UniformRadixTwoDAG.width seed.seed.exponent at this
    change i.val<7*UniformRadixTwoDAG.width seed.seed.exponent;omega
   have value:=new ⟨i.val,hi⟩
   change u.scalarHeap (V+i.val)=some (UniformPairMachine.prepared (starRingEnd ℂ
    (UniformConjugateRankSpectrumPreparation.bankValue par.base.K
     (UniformRankCrossPreparationMachine.kernelValues
      (UniformConjugateRankSpectrumPreparation.selected n j
       (UniformConjugateRankSpectrumPreparation.relocated par.base work))
      (UniformConjugateRankSpectrumPreparation.originalH n j) (UniformConjugateRankSpectrumPreparation.originalG n j)) ⟨i.val,hi⟩))) at value
   rw [UniformConjugateRankSpectrumPreparation.kernelValues_selected_relocated,
    UniformConjugateRankSpectrumPreparation.originalH_eq,UniformConjugateRankSpectrumPreparation.originalG_eq] at value
   have hib:i.val<UniformToeplitzCrossDAG.bankSize (UniformSeedHeightPreparation.parameters n j seed.seed).base.K:=i.isLt
   simpa only [coefficients,UniformRankCrossReplayPreparationMachine.bankValues,dite_eq_left hib,
    UniformConjugateRankSpectrumPreparation.bankValue,par] using value
 · intro i hi
   exact (f.scalar_before a.spectrum _ (by have:=a.constantsBefore;change _<work.S;omega)).trans (old.2.2.2 i hi)

lemma sources_transport {R K C T P V : ℕ} {bank : Fin R→ℂ} {s u : State}
 (h : UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (heap : u.scalarHeap=s.scalarHeap) : UniformMatchingConjugateLoadMachine.Sources K C T P V bank u := by
 constructor
 · intro i;rw [heap];exact h.positive i
 · intro i;rw [heap];exact h.negative i
 · intro i;rw [heap];exact h.conjugate i
 · intro i hi;rw [heap];exact h.constants i hi
lemma constants_transport {s u : State} (h : UniformHadamardPairMachine.Constants s)
 (heap : u.scalarHeap=s.scalarHeap) : UniformHadamardPairMachine.Constants u := by
 rcases h with ⟨h0,h1,h2,h3,h4⟩
 exact ⟨(congrFun heap 1).trans h0,(congrFun heap 2).trans h1,(congrFun heap 3).trans h2,
  (congrFun heap 4).trans h3,(congrFun heap 5).trans h4⟩

lemma matching_scalar_before {p : UniformSeedChunkPackingPreparation.Layout n j seed B} {work : S.Parameters}
 {V mu bar : ℕ} (a : Allocation p work V mu bar) {s u : State}
 (f : UniformPackedMatchingShearMachine.Frame (matchingConfig p V mu bar) s u)
 (i : ℕ) (hi : i<work.S) : u.scalarHeap i=s.scalarHeap i := by
 have chain:=a.spectrum.scalar_chain
 have hv:=a.matching.coefficient.conjugatesBelow
 have hm:=a.matching.coefficient.destinations
 have hd:=a.matching.packedFresh
 have he:=a.matching.destinationFresh
 apply f.scalarHeap
 dsimp only [UniformPackedMatchingShearMachine.HeapStable,matchingConfig,
  UniformPackedMatchingShearMachine.packingConfig] at *
 dsimp only [workParameters,UniformConjugateRankSpectrumPreparation.relocated] at chain
 refine ⟨by omega,by omega,Or.inl (by omega),Or.inl (by omega)⟩

/-- Postcondition uses the helper's original PC only as a semantic projection;
all actual execution ends at1197 in the literal1198 caller. -/
def MatchedResult (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (V mu bar : ℕ)
 (original : Fin p.packing.total → Scalar) (s u : State) : Prop :=
 UniformPackedMatchingShearMachine.Result (matchingConfig p V mu bar)
  (UniformPackedMatchingShearMachine.seedRows p) seed.seed.exponent (coefficients n j seed)
  (UniformPackedMatchingShearMachine.seedLabels n j seed) (UniformSeedChunkPackingPreparation.unpacking p)
  (packedValues p original) s (setPC u 421)

def runtimeBudget (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (work : S.Parameters) : ℕ :=
 UniformRankCrossPreparationMachine.runtimeBudget (UniformConjugateRankSpectrumPreparation.selected n j (workParameters n j seed work))+
 91*seed.seed.width+388*(UniformPackedMatchingShearMachine.seedRows p).length+9*p.packing.total+63

/-- Actual763 producer, twelve charged header instructions, actual422 six-C
matching loop and scatter, then a charged halt. No new table, conjugate source,
count or intermediate action certificate is supplied. -/
theorem execution (hn : 0<n) (x : Fin n→ℂ)
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (work : S.Parameters) (V mu bar : ℕ)
 (origin s : State) (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed origin)
 (original : Fin p.packing.total → Scalar) (packed : UniformSeedChunkPackingPreparation.Packed p original origin s)
 (metadata : UniformPermutationInversePreparation.Metadata n s)
 (ops : UniformInitialPreparation.Operands n x s)
 (retained : UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate : UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (spectrumArgs : UniformConjugateRankSpectrumPreparation.Arguments n j (workParameters n j seed work) V s)
 (matchingArgs : HeaderArgs (matchingConfig p V mu bar) s)
 (a : Allocation p work V mu bar) (pc : s.pc=0) (bound : WordBound B s) : ∃u t v,
 BoundedExecution program n x B s t u ∧ t≤runtimeBudget p work ∧ u.pc=1197 ∧
 UniformConjugateRankSpectrumPreparation.Result n j (workParameters n j seed work) V v ∧
 UniformConjugateRankSpectrumPreparation.Frame (workParameters n j seed work) V s v ∧
 MatchedResult p V mu bar original (applyBlock setup (setPC v 763)) u ∧
 UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 UniformCrossShearTableMachine.Table seed.mapped (UniformPackedMatchingShearMachine.seedRows p) u ∧
 UniformGlobalNatPreparation.PermutationBank p.packing.total p.packing.inverse u.natHeap
  (UniformSeedChunkPackingPreparation.unpacking p) ∧ u.natReg 894=(UniformPackedMatchingShearMachine.seedRows p).length := by
 have code:=a.code
 obtain ⟨v,t,run,tb,vpc,result,f,rv,cv,mv,ov,master⟩:=
  UniformConjugateRankSpectrumPreparation.execution_retained j (workParameters n j seed work) V B x s
   metadata ops retained conjugate spectrumArgs a.spectrum pc bound
 have first:=UniformBoundedAssembly.boundedExecution_placed spectrum_code
  (by rw [UniformConjugateRankSpectrumPreparation.program_length];omega) (by omega) run
 have same0:placed 0 s=s:=by cases s;simp [placed]
 rw [same0] at first
 let w:=setPC v 763
 have wb:WordBound B w:=first.final_bound
 have wh:HeaderArgs (matchingConfig p V mu bar) w:=by
  intro q h0 h1
  exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (spectrum_keeps q (by unfold Stable;omega))).trans (matchingArgs q h0 h1)
 have safe:=setup_safe w wb
 have install:=block_runs setup program 763 n B x w setup_code rfl wb
  (by rw [setup_length];omega) safe.1 safe.2
 let z:=applyBlock setup w
 have zp:z.pc=775:=by rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
 let e:=setPC z 0
 have eb:WordBound B e:=changePC_bound B z 0 install.final_bound (by omega)
 have eh:e.natHeap=v.natHeap:=(setup_frame w).1
 have es:e.scalarHeap=v.scalarHeap:=(setup_frame w).2.1
 have headers:UniformPackedMatchingShearMachine.Header (matchingConfig p V mu bar) e:=by
  have h:=setup_spec _ w wh
  exact ⟨h.length,h.packed,h.destination,h.inverse,h.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu⟩
 have count:e.natReg 894=(UniformPackedMatchingShearMachine.seedRows p).length:=by
  have kept:=UniformNewtonTableMachine.Executes.keeps_nat run.executes (spectrum_keeps 894 (by unfold Stable;omega))
  have setupKept: z.natReg 894=w.natReg 894:=(setup_frame w).2.2.2.2.2 _ (by omega) (Or.inl (by omega))
  exact setupKept.trans (kept.trans (UniformPackedMatchingShearMachine.generated_count hn p post packed))
 have table:UniformCrossShearTableMachine.Table seed.mapped (UniformPackedMatchingShearMachine.seedRows p) e:=by
  intro i hi
  change _ ∧ _ ∧ _
  rw [eh]
  exact generated_table_retained a hn post original packed f i hi
 have inverse:UniformGlobalNatPreparation.PermutationBank p.packing.total p.packing.inverse e.natHeap
  (UniformSeedChunkPackingPreparation.unpacking p):=by
  rw [eh];exact generated_inverse_retained a original packed f
 have data:UniformPackedMatchingShearMachine.Packed (matchingConfig p V mu bar) (packedValues p original) e:=by
  intro i hi
  rw [es];exact generated_data_retained a original packed f i hi
 have sources:UniformMatchingConjugateLoadMachine.Sources seed.seed.exponent seed.seed.C seed.seed.negative seed.seed.constants V
  (coefficients n j seed) e:=sources_transport (produced_sources a hn post original packed result f) es
 have constants:UniformHadamardPairMachine.Constants e:=by
  apply UniformHadamardPairMachine.constants_from_bank n e
  intro i
  rw [es];exact ov.constants i
 obtain ⟨q,matchRun,matchResult⟩:=UniformPackedMatchingShearMachine.execution x (matchingConfig p V mu bar)
  (UniformPackedMatchingShearMachine.seedRows p) a.matching (coefficients n j seed)
  (UniformPackedMatchingShearMachine.seedLabels n j seed)
  (fun i hi=>UniformPackedMatchingShearMachine.mappedRows_reference (seed.chunk n j) p.seed.chunk.capacity
   (UniformPackedMatchingShearMachine.seedWord n j seed) seed.seed.C seed.seed.negative seed.seed.constants i hi)
  (UniformSeedChunkPackingPreparation.unpacking p) (packedValues p original) e headers count sources table inverse data constants rfl eb
 have third:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformPackedMatchingShearMachine.program_length];omega) (by omega) matchRun
 have eqz:placed 775 e=z:=UniformPreparedFFTMachine.reset_placed z 775 zp
 rw [eqz] at third
 let u:=setPC q 1197
 have stop:BoundedExecution program n x B u 1 u:=.halt third.final_bound (by simp [step,u,setPC,halt_at])
 have all:=first.executes (install.executes (third.executes stop))
 have matching:MatchedResult p V mu bar original z u:=
  ⟨rfl,matchResult.packed,matchResult.destination,sources_transport matchResult.coefficients rfl,
   constants_transport matchResult.constants rfl,matchResult.frame.from_setPC.setPC 421⟩
 have scal:∀i,i<work.S→u.scalarHeap i=v.scalarHeap i:=by
  intro i hi
  exact matching_scalar_before a matchResult.frame i hi
 have nh:u.natHeap=v.natHeap:=matchResult.frame.natHeap
 have rn:∀(i : ℕ),100 ≤ i → i ≤ 106 → u.natReg i=v.natReg i:=by
  intro i h0 h1
  have h:=matchResult.frame.natReg i (by unfold UniformPackedMatchingShearMachine.NatStable;omega)
  exact h.trans ((setup_frame w).2.2.2.2.2 i (by omega) (Or.inl (by omega)))
 have out:u.outputs=v.outputs:=matchResult.frame.outputs
 have roots:u.rootOrders=v.rootOrders:=matchResult.frame.rootOrders
 have pf:UniformAllAxisSeedPreparation.ProtectedFrame n v u:=⟨fun i _ _=>congrFun nh i,
  fun i hi=>scal i (lt_of_lt_of_le hi a.spectrum.globalFresh),rn,out,roots⟩
 have rr:UniformAllAxisSeedPreparation.Retained n (axisCount n) u:=rv.transport_before
  (fun i hi=>scal i (lt_of_lt_of_le hi ((UniformConjugateRankSpectrumPreparation.originalEnd_le_seedEnd n).trans a.spectrum.seedFresh))) nh
 have cc:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=cv.transport
  (fun i _ hi=>scal i (lt_of_lt_of_le hi a.spectrum.seedFresh)) nh
 have nth:u.natHeap=e.natHeap:=matchResult.frame.natHeap
 have finalTable:UniformCrossShearTableMachine.Table seed.mapped (UniformPackedMatchingShearMachine.seedRows p) u:=by
  intro i hi
  change _ ∧ _ ∧ _
  rw [nth];exact table i hi
 have finalInverse:UniformGlobalNatPreparation.PermutationBank p.packing.total p.packing.inverse u.natHeap
  (UniformSeedChunkPackingPreparation.unpacking p):=by
  rw [nth];exact inverse
 have finalCount:u.natReg 894=(UniformPackedMatchingShearMachine.seedRows p).length:=
  (matchResult.frame.natReg 894 (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans count
 refine ⟨u,_,v,all,?_,rfl,result,f,matching,rr,cc,
  pf.metadata mv,pf.operands ov,out.trans f.2.2.1,roots.trans f.2.2.2.1,finalTable,finalInverse,finalCount⟩
 have cost:=UniformPackedMatchingShearMachine.matchingCost_bound (UniformPackedMatchingShearMachine.seedLabels n j seed)
  0 (UniformPackedMatchingShearMachine.seedRows p).length
 change @UniformPackedMatchingShearMachine.matchingCost (UniformToeplitzCrossDAG.bankSize seed.seed.exponent)
  (UniformPackedMatchingShearMachine.seedLabels n j seed) 0 (UniformPackedMatchingShearMachine.seedRows p).length≤388*(UniformPackedMatchingShearMachine.seedRows p).length at cost
 dsimp only [runtimeBudget,workParameters,UniformConjugateRankSpectrumPreparation.relocated,setup_length,matchingConfig,UniformPackedMatchingShearMachine.packingConfig] at *
 change t≤UniformRankCrossPreparationMachine.runtimeBudget _+91*seed.seed.width+29 at tb
 omega

end
end ExactFourierCircuits.UniformConjugatePackedMatchingPreparation
