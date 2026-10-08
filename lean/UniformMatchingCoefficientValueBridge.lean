import UniformPackedMatchingShearMachine
import UniformConjugateRankSpectrumPreparation

set_option autoImplicit false

/-! Value correctness for the actual forward corrected-cross coefficient leaves.
The frozen pointer decoder is deliberately forward-only: its fallback constant
is valid here because the generated rational leaves are exactly 1, -1, or 1/N.
Inverse normalization uses a separate signed routing policy below. -/
namespace ExactFourierCircuits.UniformMatchingCoefficientValueBridge
open UniformReplayPrint UniformMachine
open UniformPairMachine (prepared)
noncomputable section

/-- The actual forward syntax, independently of any coefficient-bank values. -/
def ForwardLeaf {R : ℕ} (K : ℕ) (c : UniformReplayPrint.Coefficient R) : Prop :=
 c = .rational 1 ∨ c = .rational (-1) ∨
 c = .rational ((UniformRadixTwoDAG.width K : ℚ)⁻¹) ∨
 ∃ i, c = .prepared i false

lemma reference_leaf {R : ℕ} {ι : Type} (K : ℕ) (d : ι) (ref : Option ι)
 (c : UniformReplayPrint.Coefficient R) (h : ∀ i, ref = some i → d ≠ i)
 (hc : ForwardLeaf K c) (s : ShearCode ι R) (hs : s ∈ reference d ref c h) :
 ForwardLeaf K s.coefficient := by
 cases ref with
 | none => simp [reference] at hs
 | some a =>
   simp only [reference,List.mem_singleton] at hs
   subst s
   exact hc

lemma gate_leaf {R w : ℕ} (K : ℕ) (d : ℕ) (refs : Fin w → Option ℕ)
 (h : ∀ a i, refs a = some i → d ≠ i) (g : UniformReplayPrint.Gate R w)
 (hg : UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K)
   (UniformToeplitzCrossDAG.gateRecord g))
 (s : ShearCode ℕ R) (hs : s ∈ gateCode d refs h g) : ForwardLeaf K s.coefficient := by
 cases g with
 | add a b =>
   simp only [gateCode,List.mem_append] at hs
   rcases hs with hs | hs
   · exact reference_leaf K _ _ _ _ (Or.inl rfl) s hs
   · exact reference_leaf K _ _ _ _ (Or.inl rfl) s hs
 | sub a b =>
   simp only [gateCode,List.mem_append] at hs
   rcases hs with hs | hs
   · exact reference_leaf K _ _ _ _ (Or.inl rfl) s hs
   · exact reference_leaf K _ _ _ _ (Or.inr (Or.inl rfl)) s hs
 | scale c a =>
   change UniformCrossShearTableMachine.GoodCoefficient (UniformRadixTwoDAG.width K) c at hg
   have hc : ForwardLeaf K c := by
     rcases hg with hq | ⟨i,hi⟩
     · exact Or.inr (Or.inr (Or.inl hq))
     · exact Or.inr (Or.inr (Or.inr ⟨i,hi⟩))
   exact reference_leaf K _ _ _ _ hc s hs

/-- Program-level induction uses actual typed gates, with no supplied shear list. -/
theorem natSweep_leaf {R n t : ℕ} (K : ℕ) (p : UniformReplayPrint.Program R n t)
 (good : ∀ g ∈ UniformToeplitzCrossDAG.programRecords p,
   UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K) g)
 (enabled : Bool) (s : ShearCode ℕ R) (hs : s ∈ UniformDAGLayers.natSweep p enabled) :
 ForwardLeaf K s.coefficient := by
 induction p with
 | nil => simp [UniformDAGLayers.natSweep,UniformReplayPrint.Program.sweep] at hs
 | @step t p g ih =>
   rw [UniformDAGLayers.natSweep_step] at hs
   rcases List.mem_append.mp hs with hs | hs
   · apply ih (fun g hg => good g (by simp only [UniformToeplitzCrossDAG.programRecords,List.mem_append];exact Or.inl hg)) hs
   · apply gate_leaf K _ _ _ g (good _ (by simp [UniformToeplitzCrossDAG.programRecords])) s hs

/-- Every actual depth bucket has only the three forward rational leaves and
positive prepared references. Disabled input ports and literal zero are removed
by the existing sweep, rather than by any coefficient-value test. -/
theorem cross_bucket_leaf (K a e : ℕ) (ha : a ≤ UniformRadixTwoDAG.width K)
 (he : e ≤ UniformRadixTwoDAG.width K) (enabled : Bool) (depth : ℕ)
 (s : ShearCode ℕ (UniformToeplitzCrossDAG.bankSize K))
 (hs : s ∈ UniformCrossDepthReplayPreparation.bucket
   (UniformToeplitzCrossDAG.crossDAG K a e ha he).program enabled depth) :
 ForwardLeaf K s.coefficient := by
 exact natSweep_leaf K _ (UniformCrossShearTableMachine.cross_records_good K a e ha he)
  enabled s (List.mem_filter.mp hs).1

lemma reciprocal_cast (K : ℕ) :
 (((UniformRadixTwoDAG.width K : ℚ)⁻¹ : ℚ) : ℂ) = ((2 : ℂ)^K)⁻¹ := by
 simp [UniformRadixTwoDAG.width_eq]

/-- Correctness of the frozen forward-only decoder on its proved syntax domain. -/
theorem forward_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 UniformMatchingConjugateLoadMachine.value K bank
   (UniformMatchingConjugateLoadMachine.fromReference c) = c.eval bank := by
 rcases hc with rfl | rfl | rfl | ⟨i,rfl⟩
 · norm_num [UniformMatchingConjugateLoadMachine.fromReference,
     UniformMatchingConjugateLoadMachine.value,UniformReplayCoefficientMachine.constant,
     UniformReplayPrint.Coefficient.eval]
 · norm_num [UniformMatchingConjugateLoadMachine.fromReference,
     UniformMatchingConjugateLoadMachine.value,UniformReplayCoefficientMachine.constant,
     UniformReplayPrint.Coefficient.eval]
 · have pos : 0 < (UniformRadixTwoDAG.width K : ℚ)⁻¹ :=
     inv_pos.mpr (by exact_mod_cast UniformRadixTwoDAG.width_pos K)
   have ne : (UniformRadixTwoDAG.width K : ℚ)⁻¹ ≠ -1 := by linarith
   by_cases one : (UniformRadixTwoDAG.width K : ℚ)⁻¹ = 1
   · simp [UniformMatchingConjugateLoadMachine.fromReference,one,
       UniformMatchingConjugateLoadMachine.value,UniformReplayCoefficientMachine.constant,
       UniformReplayPrint.Coefficient.eval]
   · simp only [UniformMatchingConjugateLoadMachine.fromReference,ite_eq_right one,
       ite_eq_right ne,UniformMatchingConjugateLoadMachine.value,UniformReplayPrint.Coefficient.eval]
     simpa [UniformReplayCoefficientMachine.constant] using (reciprocal_cast K).symm
 · simp [UniformMatchingConjugateLoadMachine.fromReference,
     UniformMatchingConjugateLoadMachine.value,UniformReplayPrint.Coefficient.eval]

/-- Actual physical positive/negative/constants banks supply exactly the
logical forward coefficient; the numeric equality is not a new entry premise. -/
theorem forward_source {R K C T P V : ℕ} {bank : Fin R → ℂ} {s : State}
 (src : UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 s.scalarHeap ((UniformCrossShearTableMachine.locations R C T P).address c) =
   some (prepared (c.eval bank)) := by
 rw [UniformMatchingConjugateLoadMachine.reference_address]
 rw [← forward_value K bank c hc]
 exact UniformMatchingConjugateLoadMachine.source src _


/-- Route the inverse of a proved forward leaf, including signed normalization.
This is separate from the frozen forward-only `fromReference`. -/
def inverseReference {R : ℕ} : UniformReplayPrint.Coefficient R →
 UniformMatchingConjugateLoadMachine.Coefficient R
 | .prepared i negative => if negative then .positive i else .negative i
 | .rational q => if q = 1 then .constant 1 else if q = -1 then .constant 0
   else .constant 3

theorem inverse_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 UniformMatchingConjugateLoadMachine.value K bank (inverseReference c) =
   c.negate.eval bank := by
 rw [UniformReplayPrint.Coefficient.eval_negate]
 rcases hc with rfl | rfl | rfl | ⟨i,rfl⟩
 · norm_num [inverseReference,UniformMatchingConjugateLoadMachine.value,
     UniformReplayCoefficientMachine.constant,UniformReplayPrint.Coefficient.eval]
 · norm_num [inverseReference,UniformMatchingConjugateLoadMachine.value,
     UniformReplayCoefficientMachine.constant,UniformReplayPrint.Coefficient.eval]
 · have pos : 0 < (UniformRadixTwoDAG.width K : ℚ)⁻¹ :=
     inv_pos.mpr (by exact_mod_cast UniformRadixTwoDAG.width_pos K)
   have ne : (UniformRadixTwoDAG.width K : ℚ)⁻¹ ≠ -1 := by linarith
   by_cases one : (UniformRadixTwoDAG.width K : ℚ)⁻¹ = 1
   · simp [inverseReference,one,UniformMatchingConjugateLoadMachine.value,
       UniformReplayCoefficientMachine.constant,UniformReplayPrint.Coefficient.eval]
   · simp only [inverseReference,ite_eq_right one,ite_eq_right ne,
       UniformMatchingConjugateLoadMachine.value,UniformReplayPrint.Coefficient.eval]
     simpa [UniformReplayCoefficientMachine.constant] using congrArg Neg.neg (reciprocal_cast K).symm
 · simp [inverseReference,UniformMatchingConjugateLoadMachine.value,
     UniformReplayPrint.Coefficient.eval]

/-- The normalization inverse aliases rational -1 only at width one. -/
theorem inverse_reciprocal_address {R : ℕ} (K C T P : ℕ) :
 UniformMatchingConjugateLoadMachine.address C T P
   (inverseReference (R := R) (.rational ((UniformRadixTwoDAG.width K : ℚ)⁻¹))) =
   if UniformRadixTwoDAG.width K = 1 then P+1 else P+3 := by
 have pos : 0 < (UniformRadixTwoDAG.width K : ℚ)⁻¹ :=
   inv_pos.mpr (by exact_mod_cast UniformRadixTwoDAG.width_pos K)
 have ne : (UniformRadixTwoDAG.width K : ℚ)⁻¹ ≠ -1 := by linarith
 by_cases one : UniformRadixTwoDAG.width K = 1
 · simp [inverseReference,UniformMatchingConjugateLoadMachine.address,one]
 · simp [inverseReference,UniformMatchingConjugateLoadMachine.address,
     UniformCrossShearTableMachine.reciprocal_eq_one _ (UniformRadixTwoDAG.width_pos K),ne,one]

theorem inverse_reciprocal_width_one {R : ℕ} (K C T P : ℕ)
 (h : UniformRadixTwoDAG.width K = 1) :
 UniformMatchingConjugateLoadMachine.address C T P
   (inverseReference (R := R) (.rational ((UniformRadixTwoDAG.width K : ℚ)⁻¹))) = P+1 := by
 rw [inverse_reciprocal_address,ite_eq_left h]

theorem inverse_reciprocal_width_gt_one {R : ℕ} (K C T P : ℕ)
 (h : 1 < UniformRadixTwoDAG.width K) :
 UniformMatchingConjugateLoadMachine.address C T P
   (inverseReference (R := R) (.rational ((UniformRadixTwoDAG.width K : ℚ)⁻¹))) = P+3 := by
 rw [inverse_reciprocal_address,ite_eq_right (by omega)]

theorem inverse_source {R K C T P V : ℕ} {bank : Fin R → ℂ} {s : State}
 (src : UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 s.scalarHeap (UniformMatchingConjugateLoadMachine.address C T P (inverseReference c)) =
   some (prepared (c.negate.eval bank)) := by
 rw [← inverse_value K bank c hc]
 exact UniformMatchingConjugateLoadMachine.source src _

/-- The positive-bank conjugate cell is supplied by the genuine producer
contract. Rational leaves are real; negative inverse leaves use its negation. -/
def conjugateValue {R : ℕ} (K : ℕ) (bank : Fin R → ℂ) :
 UniformMatchingConjugateLoadMachine.Coefficient R → ℂ
 | .positive i => starRingEnd ℂ (bank i)
 | .negative i => -(starRingEnd ℂ (bank i))
 | .constant i => UniformReplayCoefficientMachine.constant K i.val

lemma conjugateValue_eq {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (c : UniformMatchingConjugateLoadMachine.Coefficient R) :
 conjugateValue K bank c = starRingEnd ℂ (UniformMatchingConjugateLoadMachine.value K bank c) := by
 cases c with
 | positive i => rfl
 | negative i => simp [conjugateValue,UniformMatchingConjugateLoadMachine.value]
 | constant i => exact (UniformMatchingConjugateLoadMachine.constant_conjugate K i).symm

theorem forward_conjugate_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 conjugateValue K bank (UniformMatchingConjugateLoadMachine.fromReference c) =
   starRingEnd ℂ (c.eval bank) := by
 rw [conjugateValue_eq,forward_value K bank c hc]

theorem inverse_conjugate_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (c : UniformReplayPrint.Coefficient R) (hc : ForwardLeaf K c) :
 conjugateValue K bank (inverseReference c) = starRingEnd ℂ (c.negate.eval bank) := by
 rw [conjugateValue_eq,inverse_value K bank c hc]

/-- Literal code coefficient selected by the existing ordered color filter. -/
def selectedReference {R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (i : Fin (UniformChunkMatchingPreparation.indices p W).length) :
 UniformReplayPrint.Coefficient R :=
 (W[(UniformColorLayerTableMachine.selectionIndex W.length p.color
   (UniformChunkMatchingPreparation.colors W) i).val]).coefficient

lemma selectedReference_leaf {R : ℕ} (K : ℕ) (p : UniformChunkMatchingPreparation.Parameters)
 (W : List (ShearCode ℕ R)) (good : ∀ s ∈ W, ForwardLeaf K s.coefficient)
 (i : Fin (UniformChunkMatchingPreparation.indices p W).length) :
 ForwardLeaf K (selectedReference p W i) := by
 exact good _ (List.getElem_mem _)

theorem selected_labels_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (p : UniformChunkMatchingPreparation.Parameters) (W : List (ShearCode ℕ R))
 (good : ∀ s ∈ W, ForwardLeaf K s.coefficient)
 (i : Fin (UniformChunkMatchingPreparation.indices p W).length) :
 UniformMatchingConjugateLoadMachine.value K bank
   (UniformPackedMatchingShearMachine.selectedLabels p W i.val) =
   (selectedReference p W i).eval bank := by
 simp only [UniformPackedMatchingShearMachine.selectedLabels,dite_eq_left i.isLt]
 exact forward_value K bank _ (selectedReference_leaf K p W good i)

theorem crossWord_leaf (p : UniformChunkMatchingPreparation.Parameters)
 (ha : p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he : p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (s : ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K))
 (hs : s ∈ UniformChunkMatchingPreparation.crossWord p ha he) :
 ForwardLeaf p.height.K s.coefficient :=
 cross_bucket_leaf p.height.K p.height.a p.height.e ha he p.height.enabled p.depth s hs

theorem cross_selected_value (p : UniformChunkMatchingPreparation.Parameters)
 (ha : p.height.a ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (he : p.height.e ≤ UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize p.height.K) → ℂ)
 (i : Fin (UniformChunkMatchingPreparation.indices p
   (UniformChunkMatchingPreparation.crossWord p ha he)).length) :
 UniformMatchingConjugateLoadMachine.value p.height.K bank
   (UniformPackedMatchingShearMachine.selectedLabels p
     (UniformChunkMatchingPreparation.crossWord p ha he) i.val) =
   (selectedReference p (UniformChunkMatchingPreparation.crossWord p ha he) i).eval bank :=
 selected_labels_value p.height.K bank p _ (crossWord_leaf p ha he) i

/-- Value equality accompanies the frozen physical mapped-pointer equality. -/
theorem mapped_source {R K C T P V : ℕ} {bank : Fin R → ℂ} {s : State}
 (src : UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (p : UniformChunkMatchingPreparation.Parameters)
 (fit : UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix)
 (W : List (ShearCode ℕ R)) (good : ∀ row ∈ W, ForwardLeaf K row.coefficient)
 (i : Fin (UniformChunkMatchingPreparation.indices p W).length) :
 s.scalarHeap (((UniformChunkMatchingPreparation.mappedRows p fit W
   (UniformCrossShearTableMachine.locations R C T P))[i.val]'(by
      rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt)).coefficient) =
   some (prepared ((selectedReference p W i).eval bank)) := by
 rw [UniformPackedMatchingShearMachine.mappedRows_reference]
 rw [← selected_labels_value K bank p W good i]
 exact UniformMatchingConjugateLoadMachine.source src _


theorem seedWord_leaf (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n))
 (seed : UniformSeedChunkPreparation.Config)
 (s : ShearCode ℕ (UniformToeplitzCrossDAG.bankSize seed.seed.exponent))
 (hs : s ∈ UniformPackedMatchingShearMachine.seedWord n j seed) :
 ForwardLeaf seed.seed.exponent s.coefficient :=
 crossWord_leaf (seed.chunk n j) (UniformSeedHeightPreparation.widths seed.seed).1
   (UniformSeedHeightPreparation.widths seed.seed).2 s hs

theorem seed_labels_value (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n))
 (seed : UniformSeedChunkPreparation.Config)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) → ℂ)
 (i : Fin (UniformChunkMatchingPreparation.indices (seed.chunk n j)
   (UniformPackedMatchingShearMachine.seedWord n j seed)).length) :
 UniformMatchingConjugateLoadMachine.value seed.seed.exponent bank
   (UniformPackedMatchingShearMachine.seedLabels n j seed i.val) =
   (selectedReference (seed.chunk n j) (UniformPackedMatchingShearMachine.seedWord n j seed) i).eval bank :=
 selected_labels_value seed.seed.exponent bank (seed.chunk n j) _ (seedWord_leaf n j seed) i

/-- Reinterpret the actual compiled-pair result with its original logical
coefficient, not merely a pointer label. The result hypothesis is exactly the
proved postcondition of the frozen literal422 execution. -/
theorem seed_result_pair_values {n B : ℕ} {j : Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed : UniformSeedChunkPreparation.Config}
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 {c : UniformPackedMatchingShearMachine.Config} {s u : State}
 {bank : Fin (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) → ℂ}
 {phi : Fin c.length ≃ Fin c.length} {v : ℕ → Scalar}
 (h : UniformPackedMatchingShearMachine.Result c (UniformPackedMatchingShearMachine.seedRows p)
   seed.seed.exponent bank (UniformPackedMatchingShearMachine.seedLabels n j seed) phi v s u)
 (cap : 2*(UniformPackedMatchingShearMachine.seedRows p).length ≤ c.length)
 (i : Fin (UniformChunkMatchingPreparation.indices (seed.chunk n j)
   (UniformPackedMatchingShearMachine.seedWord n j seed)).length) :
 u.scalarHeap (c.destination+(phi ⟨2*i.val,by
   have hi : i.val < (UniformPackedMatchingShearMachine.seedRows p).length := by
     rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt
   omega⟩).val) =
 some ⟨(v (2*i.val)).value+
   (selectedReference (seed.chunk n j) (UniformPackedMatchingShearMachine.seedWord n j seed) i).eval bank*
     (v (2*i.val+1)).value,(v (2*i.val)).dependent||(v (2*i.val+1)).dependent⟩ ∧
 u.scalarHeap (c.destination+(phi ⟨2*i.val+1,by
   have hi : i.val < (UniformPackedMatchingShearMachine.seedRows p).length := by
     rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt
   omega⟩).val) =
 some ⟨(v (2*i.val+1)).value,(v (2*i.val)).dependent||(v (2*i.val+1)).dependent⟩ := by
 have hi : i.val < (UniformPackedMatchingShearMachine.seedRows p).length := by
   rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt
 have out := h.pair_coordinates cap ⟨i.val,hi⟩
 rw [seed_labels_value n j seed bank i] at out
 exact out

/-- The producer's finite bank index is converted by the proved cardinal
identity only; stored natural addresses and values are unchanged. -/
lemma producer_bank_size (K : ℕ) :
 UniformToeplitzCrossDAG.bankSize K = 7*UniformRadixTwoDAG.width K := by
 unfold UniformToeplitzCrossDAG.bankSize
 omega

def seedBank (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n))
 (seed : UniformSeedChunkPreparation.Config) :
 Fin (UniformToeplitzCrossDAG.bankSize seed.seed.exponent) → ℂ := fun i =>
 UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n j seed.seed)
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) i.val

/-- Consume both real producer postconditions. Original coefficient banks
are retained by the actual fresh-workspace frame; the conjugate values come
from the new producer, rather than a newly supplied conjugate-bank oracle. -/
theorem produced_sources {n : ℕ} (hn : 0 < n)
 (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (seed : UniformSeedChunkPreparation.Config)
 (B dest : ℕ) (layout : UniformSeedChunkPreparation.Layout n j seed B)
 (work : UniformRankCrossPreparationMachine.Parameters) (s u : State)
 (orig : UniformSeedChunkPreparation.Result n j seed B hn layout s)
 (new : UniformConjugateRankSpectrumPreparation.Result n j
   (UniformConjugateRankSpectrumPreparation.relocated
     (UniformSeedHeightPreparation.parameters n j seed.seed).base work) dest u)
 (alloc : UniformConjugateRankSpectrumPreparation.Allocation n j
   (UniformConjugateRankSpectrumPreparation.relocated
     (UniformSeedHeightPreparation.parameters n j seed.seed).base work) dest B)
 (frame : UniformConjugateRankSpectrumPreparation.Frame
   (UniformConjugateRankSpectrumPreparation.relocated
     (UniformSeedHeightPreparation.parameters n j seed.seed).base work) dest s u)
 (positive : seed.seed.C+7*seed.seed.width ≤ work.S)
 (negative : seed.seed.negative+7*seed.seed.width ≤ work.S)
 (constants : seed.seed.constants+6 ≤ work.S) :
 UniformMatchingConjugateLoadMachine.Sources seed.seed.exponent seed.seed.C seed.seed.negative
   seed.seed.constants dest (seedBank n j seed) u := by
 have src := UniformConjugateRankSpectrumPreparation.seedHeight_sources_retained j seed.seed B dest
   (layout.seed.replay hn j seed.seed B) work s u orig.prepared new alloc frame positive negative constants
 have size : UniformToeplitzCrossDAG.bankSize seed.seed.exponent = 7*seed.seed.width :=
   producer_bank_size seed.seed.exponent
 refine ⟨?_,?_,?_,src.constants⟩
 · intro i
   exact src.positive ⟨i.val,by rw [← size];exact i.isLt⟩
 · intro i
   exact src.negative ⟨i.val,by rw [← size];exact i.isLt⟩
 · intro i
   exact src.conjugate ⟨i.val,by rw [← size];exact i.isLt⟩

/-- Actual mapped forward rows now have both a printed address and the exact
logical value, using the freshly computed conjugate-spectrum source join. -/
theorem produced_mapped_value {n B : ℕ} {j : Fin (UniformAllAxisSeedPreparation.axisCount n)}
 {seed : UniformSeedChunkPreparation.Config} (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 {V : ℕ} {s : State}
 (src : UniformMatchingConjugateLoadMachine.Sources seed.seed.exponent seed.seed.C seed.seed.negative
   seed.seed.constants V (seedBank n j seed) s)
 (i : Fin (UniformChunkMatchingPreparation.indices (seed.chunk n j)
   (UniformPackedMatchingShearMachine.seedWord n j seed)).length) :
 s.scalarHeap (((UniformPackedMatchingShearMachine.seedRows p)[i.val]'(by
      rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt)).coefficient) =
   some (prepared ((selectedReference (seed.chunk n j)
     (UniformPackedMatchingShearMachine.seedWord n j seed) i).eval (seedBank n j seed))) :=
 mapped_source src (seed.chunk n j) p.seed.chunk.capacity _ (seedWord_leaf n j seed) i


lemma forward_rational_iff {R : ℕ} (K : ℕ) (q : ℚ) :
 ForwardLeaf (R := R) K (.rational q) ↔
 q = 1 ∨ q = -1 ∨ q = (UniformRadixTwoDAG.width K : ℚ)⁻¹ := by
 simp [ForwardLeaf]

/-- An explicit rational-domain statement about actual generated typed rows. -/
theorem cross_rational_domain (K a e : ℕ) (ha : a ≤ UniformRadixTwoDAG.width K)
 (he : e ≤ UniformRadixTwoDAG.width K) (enabled : Bool) (depth : ℕ)
 (row : ShearCode ℕ (UniformToeplitzCrossDAG.bankSize K))
 (member : row ∈ UniformCrossDepthReplayPreparation.bucket
   (UniformToeplitzCrossDAG.crossDAG K a e ha he).program enabled depth)
 (q : ℚ) (rational : row.coefficient = .rational q) :
 q = 1 ∨ q = -1 ∨ q = (UniformRadixTwoDAG.width K : ℚ)⁻¹ := by
 have h := cross_bucket_leaf K a e ha he enabled depth row member
 rwa [rational,forward_rational_iff] at h

/-- Reverse-code chronology is the existing reversed list with every exact
logical coefficient negated; the new routing agrees on every retained row. -/
theorem reverseCode_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (W : List (ShearCode ℕ R)) (good : ∀ row ∈ W, ForwardLeaf K row.coefficient)
 (row : ShearCode ℕ R) (member : row ∈ reverseCode W) :
 ∃ forward ∈ W, row = forward.inverse ∧
   UniformMatchingConjugateLoadMachine.value K bank (inverseReference forward.coefficient) =
     row.coefficient.eval bank := by
 obtain ⟨forward,mem,eq⟩ := List.mem_map.mp member
 have old : forward ∈ W := List.mem_reverse.mp mem
 refine ⟨forward,old,eq.symm,?_⟩
 rw [← eq]
 exact inverse_value K bank forward.coefficient (good forward old)

/-- The old fallback is intentionally not valid for negative normalization
at width greater than one. A future inverse-table caller must use the new route. -/
theorem forward_decoder_negative_normalization_address {R : ℕ} (K C T P : ℕ)
 (h : 1 < UniformRadixTwoDAG.width K) :
 UniformMatchingConjugateLoadMachine.address C T P
   (UniformMatchingConjugateLoadMachine.fromReference (R := R)
     (.rational (-((UniformRadixTwoDAG.width K : ℚ)⁻¹)))) = P+2 := by
 have pos : 0 < (UniformRadixTwoDAG.width K : ℚ)⁻¹ :=
   inv_pos.mpr (by exact_mod_cast UniformRadixTwoDAG.width_pos K)
 have ne : (UniformRadixTwoDAG.width K : ℚ)⁻¹ ≠ 1 := by
   intro one
   have eq := (UniformCrossShearTableMachine.reciprocal_eq_one _
     (UniformRadixTwoDAG.width_pos K)).mp one
   omega
 have negOne : -((UniformRadixTwoDAG.width K : ℚ)⁻¹) ≠ 1 := by linarith
 have negNegOne : -((UniformRadixTwoDAG.width K : ℚ)⁻¹) ≠ -1 := by
   intro eq
   apply ne
   linarith
 simp [UniformMatchingConjugateLoadMachine.fromReference,
   UniformMatchingConjugateLoadMachine.address,negOne,negNegOne]

/-- Lift the real row loader's execution proof using the just-proved value
bridge. The physical row table and header allocations are honest entry facts;
no scalar value, conjugate scale, pointer or resulting action is supplied. -/
theorem selected_row_execution {R K C T P V a b B n D : ℕ}
 {bank : Fin R → ℂ} {s : State} (p : UniformChunkMatchingPreparation.Parameters)
 (fit : UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a ≤ p.radix)
 (W : List (ShearCode ℕ R)) (good : ∀ row ∈ W, ForwardLeaf K row.coefficient)
 (i : Fin (UniformChunkMatchingPreparation.indices p W).length)
 (args : UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val s)
 (layout : UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (src : UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (table : UniformCrossShearTableMachine.Table D
   (UniformChunkMatchingPreparation.mappedRows p fit W (UniformCrossShearTableMachine.locations R C T P)) s)
 (rowBound : D+3*(UniformChunkMatchingPreparation.mappedRows p fit W
   (UniformCrossShearTableMachine.locations R C T P)).length ≤ B)
 (code : 25 ≤ B) (x : Fin n → ℂ) (pc : s.pc = 0) (bound : WordBound B s) : ∃ u,
 BoundedExecution UniformMatchingConjugateLoadMachine.rowProgram n x B s
   (UniformMatchingConjugateLoadMachine.runtime (UniformPackedMatchingShearMachine.selectedLabels p W i.val)+7) u ∧
 u.scalarHeap a = some (prepared ((selectedReference p W i).eval bank)) ∧
 u.scalarHeap b = some (prepared (starRingEnd ℂ ((selectedReference p W i).eval bank))) ∧
 (∀ q, q ≠ a → q ≠ b → u.scalarHeap q = s.scalarHeap q) ∧
 u.natHeap = s.natHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.pc = 24 ∧
 UniformMatchingConjugateLoadMachine.RowFrame s u := by
 have hi : i.val < (UniformChunkMatchingPreparation.mappedRows p fit W
   (UniformCrossShearTableMachine.locations R C T P)).length := by
   rw [UniformPackedMatchingShearMachine.mappedRows_length];exact i.isLt
 obtain ⟨u,run,mu,bar,other,nh,out,roots,pcu,frame⟩ :=
   UniformMatchingConjugateLoadMachine.execution_from_row _ ⟨i.val,hi⟩
     (UniformPackedMatchingShearMachine.selectedLabels p W i.val) args layout src table
     (UniformPackedMatchingShearMachine.mappedRows_reference p fit W C T P i.val hi)
     rowBound code x pc bound
 rw [selected_labels_value K bank p W good i] at mu bar
 exact ⟨u,run,mu,bar,other,nh,out,roots,pcu,frame⟩

/-- Fixed exact diagnostics: width one aliases -1, width two needs -1/2. -/
theorem inverse_width_one_fixture (C T P : ℕ) :
 UniformMatchingConjugateLoadMachine.address C T P
   (inverseReference (R := 1) (.rational 1)) = P+1 := by
 norm_num [inverseReference,UniformMatchingConjugateLoadMachine.address]

theorem inverse_width_two_fixture (C T P : ℕ) :
 UniformMatchingConjugateLoadMachine.address C T P
   (inverseReference (R := 1) (.rational (1/2))) = P+3 := by
 norm_num [inverseReference,UniformMatchingConjugateLoadMachine.address]

theorem arbitrary_rational_rejected_fixture :
 ¬ ForwardLeaf (R := 1) 1 (.rational (2/3)) := by
 norm_num [forward_rational_iff,UniformRadixTwoDAG.width]

theorem negative_normalization_forward_rejected_fixture :
 ¬ ForwardLeaf (R := 1) 1 (.rational (-1/2)) := by
 norm_num [forward_rational_iff,UniformRadixTwoDAG.width]

/-- A concrete guard against treating the frozen forward decoder as generic. -/
theorem forward_decoder_negative_value_fixture (bank : Fin 1 → ℂ) :
 UniformMatchingConjugateLoadMachine.value 1 bank
   (UniformMatchingConjugateLoadMachine.fromReference (R := 1) (.rational (-1/2))) = (1/2 : ℂ) ∧
 UniformMatchingConjugateLoadMachine.value 1 bank
   (inverseReference (R := 1) (.rational (1/2))) = (-1/2 : ℂ) := by
 norm_num [UniformMatchingConjugateLoadMachine.value,UniformMatchingConjugateLoadMachine.fromReference,
   inverseReference,UniformReplayCoefficientMachine.constant]

end
end ExactFourierCircuits.UniformMatchingCoefficientValueBridge
