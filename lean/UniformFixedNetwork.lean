import ExplicitSeed
import UniformExponent

/- The actual fixed network for arbitrary columns. This is a literal algebraic
   word and fixed geometric metadata; it is not a RAM execution theorem. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetwork
open OAI.ExactFourier BinaryFrames BinaryTensor BinaryProjection FramedScheduleWords
open scoped BigOperators
noncomputable section

abbrev m : ℕ := ExplicitSeedBudget.m
abbrev W : ℕ := ExplicitSeedBudget.paddedRoles
abbrev S : ℕ := ExplicitSeedBudget.residuals
abbrev pointwiseCalls : ℕ := ExplicitSeedBudget.pointwiseCalls
abbrev hh : 7 ≤ ExplicitSeedBudget.h := ExplicitSeed.h_large

lemma dimension_eq : ExplicitSeedBudget.h ^ 3 = m :=
  ExplicitSeedBudget.parameter_formulas.2.2.1.symm
lemma W_eq : W = 2 ^ 71 := by
  simpa only [ExplicitSeedBudget.roleBits] using ExplicitSeedBudget.padding.1
lemma residual_balance : S + ExplicitSeedBudget.margin = W * m :=
  ExplicitSeedBudget.residual_balance
lemma address_positive (q : ℕ) (hq : 1 ≤ q) : 1 ≤ q * m := by
  have hm : 1 ≤ m := by norm_num [m, ExplicitSeedBudget.m]
  exact le_trans (by simpa using hq) (Nat.le_mul_of_pos_right q hm)

/-- Three literal stages in their physical order, then the signed/translated correction. -/
def correctedWord (q : ℕ) :
    List (WordStep C (TripleSchedule.Global.size ExplicitSeedBudget.h * 2 ^ (q * m))) :=
  MasterBudget.actualCorrectedWord q hh
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection q)

lemma correctedWord_chronology (q : ℕ) : correctedWord q =
    TripleSchedule.Global.stageWordColumns q 0 hh ++
    TripleSchedule.Global.stageWordColumns q 1 hh ++
    TripleSchedule.Global.stageWordColumns q 2 hh ++
    TerminalWords.correctionWord (TripleSchedule.Global.coordinates ExplicitSeedBudget.h)
      (TripleColumnAction.globalDirection q) := rfl

lemma correctedWord_matrix (q : ℕ) :
    wordMatrix (correctedWord q) = PaddingWords.copiesMatrix
      (TripleSchedule.Global.size ExplicitSeedBudget.h) (q * m)
      (wordMatrix (TensorWords.unitAxesWord (q * m))) := by
  change wordMatrix (MasterBudget.actualCorrectedWord q hh
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection q)) =
    PaddingWords.copiesMatrix _ (q * ExplicitSeedBudget.h ^ 3)
      (wordMatrix (TensorWords.unitAxesWord (q * ExplicitSeedBudget.h ^ 3)))
  unfold MasterBudget.actualCorrectedWord
  rw [TerminalWords.master_terminal_bridge_of_endpoint
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection q)
    (TripleSchedule.Global.masterWordColumns q hh) (TripleColumnAction.endpoint q)
    (TripleSchedule.Global.masterWordColumns_packed_endpoint q hh)
    (TripleColumnAction.corrected_stages_endpoint hh q), MasterBudget.ordinaryWord_matrix]

/-- No special choice of q is used: this count follows from the actual master word. -/
lemma correctedWord_calls (q : ℕ) (hq : 1 ≤ q) :
    wordCalls (correctedWord q) =
      (q * TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hh + 2 * pointwiseCalls) * 2 ^ (q * m - 1) := by
  have hn := address_positive q hq
  change wordCalls (MasterBudget.actualCorrectedWord q hh
    (TripleSchedule.Global.coordinates ExplicitSeedBudget.h) (TripleColumnAction.globalDirection q)) = _
  unfold MasterBudget.actualCorrectedWord
  rw [TerminalWords.master_terminal_calls,
    TripleSchedule.Global.masterWordColumns_calls q hq hh]
  have hscalar : 3 * (3 * (Nat.choose ExplicitSeedBudget.h 3) ^ 2 *
      TripleSchedule.Global.invocationScalars ExplicitSeedBudget.h) = pointwiseCalls := by
    unfold TripleSchedule.Global.invocationScalars
    rw [← MasterBudget.invocation_scalar_total]
    exact MasterBudget.seed_pointwise_calls
  rw [dimension_eq, hscalar, MasterBudget.pow_address_factor _ hn]
  ring

/-- Only addresses are transformed in each role. There is no role-axis word. -/
def simultaneousWord (q : ℕ) : List (WordStep C (W * 2 ^ (q * m))) :=
  PaddingWords.fillWord (q * m)
    (PaddingWords.paddingRoles (TripleSchedule.Global.size ExplicitSeedBudget.h)
      ExplicitSeedBudget.roleBits MasterBudget.seed_actual_padding)
    (PaddingWords.canonicalNetworkWord (TripleSchedule.Global.size ExplicitSeedBudget.h)
      (q * m) (correctedWord q))

/-- Every padded role may contain arbitrary values, including all auxiliary roles. -/
theorem simultaneousWord_matrix (q : ℕ) :
    wordMatrix (simultaneousWord q) = PaddingWords.copiesMatrix W (q * m) (tensorPower C (q * m)) := by
  exact PaddingWords.fillWord_matrix _ _ _
    (PaddingWords.canonicalNetworkWord_matrix _ _ _ (correctedWord_matrix q))

theorem simultaneousWord_array (q : ℕ) (X : Fin W → Fin (2 ^ (q * m)) → ℂ) :
    (wordMatrix (simultaneousWord q)).mulVec (RoleWords.arrayValues (q * m) X) =
      RoleWords.arrayValues (q * m) (fun i => (tensorPower C (q * m)).mulVec (X i)) := by
  rw [simultaneousWord_matrix]
  funext k
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses W (q * m)).surjective k
  rw [RoleWords.arrayValues_at]
  unfold Matrix.mulVec dotProduct
  rw [← (RoleWords.roleAddresses W (q * m)).sum_comp, Fintype.sum_prod_type]
  simp [PaddingWords.copiesMatrix, Matrix.reindex_apply, Matrix.one_apply, RoleWords.arrayValues_at]

/-- A generic polynomial identity avoids reducing any fixed finite-index schedule. -/
lemma fill_calls_from_cost {w p v : ℕ} (q n d R P S₀ : ℕ)
    (e : Fin w ⊕ Fin p ≃ Fin v) (T : List (WordStep C (w * 2 ^ n)))
    (hn : n = q * d)
    (hc : wordCalls T = (q * R + 2 * P) * 2 ^ (n - 1))
    (hr : R + p * d = S₀) :
    wordCalls (PaddingWords.fillWord n e T) = (q * S₀ + 2 * P) * 2 ^ (n - 1) := by
  rw [PaddingWords.fillWord_calls, hc]
  calc
    _ = (q * (R + p * d) + 2 * P) * 2 ^ (n - 1) := by rw [hn]; ring
    _ = _ := by rw [hr]

lemma transfer_padding {R d S₀ w w₀ v v₀ : ℕ} (hw : w = w₀) (hv : v = v₀)
    (hr : R + (v₀ - w₀) * d = S₀) : R + (v - w) * d = S₀ := by
  rw [hw, hv]
  exact hr

lemma seedPaddingResiduals (hl : 7 ≤ ExplicitSeedBudget.h) :
    TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hl +
      (W - ExplicitSeedBudget.roles) * m = S := by
  exact MasterBudget.seed_padding_residuals _ (MasterBudget.seed_master_residual_balance hl)

/-- The pair-call count, split into copied residuals and fixed pointwise three-C words. -/
theorem simultaneousWord_calls (q : ℕ) (hq : 1 ≤ q) :
    wordCalls (simultaneousWord q) = (q * S + 2 * pointwiseCalls) * 2 ^ (q * m - 1) := by
  have hp : TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hh +
      (2 ^ ExplicitSeedBudget.roleBits - TripleSchedule.Global.size ExplicitSeedBudget.h) * m = S :=
    transfer_padding (R := TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hh) (d := m) (S₀ := S)
      (w := TripleSchedule.Global.size ExplicitSeedBudget.h) (w₀ := ExplicitSeedBudget.roles)
      (v := 2 ^ ExplicitSeedBudget.roleBits) (v₀ := W)
      MasterBudget.seed_actual_size ExplicitSeedBudget.padding.1.symm
      (seedPaddingResiduals hh)
  exact fill_calls_from_cost q (q * m) m (TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hh) pointwiseCalls S _ _ rfl
    ((PaddingWords.canonicalNetworkWord_calls _ _ _).trans (correctedWord_calls q hq)) hp

/-- The exact coefficient saving, without natural-number subtraction. -/
theorem simultaneousWord_balance (q : ℕ) (hq : 1 ≤ q) :
    wordCalls (simultaneousWord q) +
      (q * ExplicitSeedBudget.margin) * 2 ^ (q * m - 1) =
    (W * (q * m) + 2 * pointwiseCalls) * 2 ^ (q * m - 1) := by
  rw [simultaneousWord_calls q hq]
  calc
    _ = (q * (S + ExplicitSeedBudget.margin) + 2 * pointwiseCalls) * 2 ^ (q * m - 1) := by ring
    _ = _ := by rw [residual_balance]; ring

/-- Small q need not save after expanding pointwise shears into three-C words. -/
theorem simultaneousWord_saves (q : ℕ) (hq : 1 ≤ q)
    (hsave : 2 * pointwiseCalls < ExplicitSeedBudget.margin * q) :
    wordCalls (simultaneousWord q) < W * (q * m) * 2 ^ (q * m - 1) := by
  rw [simultaneousWord_calls q hq]
  have hcoeff : q * S + 2 * pointwiseCalls < W * (q * m) := by
    have hb := congrArg (fun a : ℕ => q * a) residual_balance
    nlinarith
  exact Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)


section Metadata
variable {r n : ℕ}

/-- Fixed metadata retains the actual residual basis or the actual scalar shear. -/
inductive Macro (r n : ℕ) where
  | edge (old new : Label n) (role : Fin r) (data : NestedEdge old new)
  | shear (dest source : Fin r) (distinct : dest ≠ source)
      (coefficient : ℂ) (nonzero : coefficient ≠ 0)

def Macro.residuals : Macro r n → ℕ
  | .edge _ _ _ e => e.dimension
  | .shear _ _ _ _ _ => 0

def Macro.scalars : Macro r n → ℕ
  | .edge _ _ _ _ => 0
  | .shear _ _ _ _ _ => 1

/-- Copy columns of each geometric edge; retain scalar roles and coefficients literally. -/
def Macro.compile (q : ℕ) : Macro r n → List (WordStep C (r * 2 ^ (q * n)))
  | .edge _ _ i e => (ColumnSchedule.edgeColumns q e).word i
  | .shear dest source distinct coefficient nonzero =>
      RoleWords.pointwiseShearWord (q * n) dest source distinct coefficient nonzero

def tapeResiduals (T : List (Macro r n)) : ℕ := (T.map Macro.residuals).sum
def tapeScalars (T : List (Macro r n)) : ℕ := (T.map Macro.scalars).sum
def compileTape (q : ℕ) (T : List (Macro r n)) : List (WordStep C (r * 2 ^ (q * n))) :=
  (T.map (Macro.compile q)).flatten

lemma compileTape_append (q : ℕ) (T U : List (Macro r n)) :
    compileTape q (T ++ U) = compileTape q T ++ compileTape q U := by
  simp only [compileTape, List.map_append, List.flatten_append]

lemma Macro.compile_calls (q : ℕ) (hn : 1 ≤ q * n) (a : Macro r n) :
    wordCalls (a.compile q) = (q * a.residuals + 2 * (3 * a.scalars)) * 2 ^ (q * n - 1) := by
  cases a with
  | edge old new i e =>
    simp only [Macro.compile, NestedEdge.word_calls hn, ColumnSchedule.edgeColumns_dimension,
      Macro.residuals, Macro.scalars, mul_zero, add_zero]
  | shear dest source distinct coefficient nonzero =>
    rw [Macro.compile, RoleWords.pointwiseShearWord_calls, MasterBudget.pow_address_factor _ hn]
    simp only [Macro.residuals, Macro.scalars]
    ring

lemma compileTape_calls (q : ℕ) (hn : 1 ≤ q * n) (T : List (Macro r n)) :
    wordCalls (compileTape q T) =
      (q * tapeResiduals T + 2 * (3 * tapeScalars T)) * 2 ^ (q * n - 1) := by
  induction T with
  | nil => simp [compileTape, tapeResiduals, tapeScalars, wordCalls]
  | cons a T ih =>
    simp only [compileTape, List.map_cons, List.flatten_cons, TypedKernelWords.wordCalls_append]
    rw [Macro.compile_calls q hn, ← compileTape, ih]
    simp only [tapeResiduals, tapeScalars, List.map_cons, List.sum_cons]
    ring

def edgesTape {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) : List (Macro r n) :=
  Finset.univ.toList.map (fun i => .edge (F i) (G i) i (edges i))

def eventTape {F G : Labels r n} (e : Event F G) : List (Macro r n) :=
  edgesTape e.edges ++ [.shear e.dest e.source e.distinct e.coefficient e.nonzero]

def scheduleTape : ∀ {F G : Labels r n}, Schedule F G → List (Macro r n)
  | _, _, .nil _ => []
  | _, _, .cons e s => eventTape e ++ scheduleTape s

def finishTape {F G H : Labels r n} (s : Schedule F G)
    (edges : ∀ i, NestedEdge (G i) (H i)) : List (Macro r n) :=
  scheduleTape s ++ edgesTape edges

lemma edgesTape_compile (q : ℕ) {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) :
    compileTape q (edgesTape edges) = edgesWord (ColumnSchedule.edgesColumns q edges) Finset.univ.toList := by
  simp only [compileTape, edgesTape, List.map_map, edgesWord, Function.comp_def,
    Macro.compile, ColumnSchedule.edgesColumns]
  rfl

lemma eventTape_compile (q : ℕ) {F G : Labels r n} (e : Event F G) :
    compileTape q (eventTape e) = (ColumnSchedule.eventColumns q e).word := by
  rw [eventTape, compileTape_append, edgesTape_compile]
  simp only [compileTape, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Macro.compile, Event.word, ColumnSchedule.eventColumns]

lemma scheduleTape_compile (q : ℕ) {F G : Labels r n} (s : Schedule F G) :
    compileTape q (scheduleTape s) = (ColumnSchedule.scheduleColumns q s).word := by
  induction s with
  | nil F => rfl
  | cons e s ih =>
    rw [scheduleTape, compileTape_append, eventTape_compile, ih]
    rfl

/-- The metadata compiles to the actual schedule word, in the same order. -/
lemma finishTape_compile (q : ℕ) {F G H : Labels r n} (s : Schedule F G)
    (edges : ∀ i, NestedEdge (G i) (H i)) :
    compileTape q (finishTape s edges) =
      (ColumnSchedule.scheduleColumns q s).finishWord (ColumnSchedule.edgesColumns q edges) := by
  rw [finishTape, compileTape_append, scheduleTape_compile, edgesTape_compile]
  rfl

lemma edgesTape_residuals {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) :
    tapeResiduals (edgesTape edges) = ∑ i, (edges i).dimension := by
  simp only [tapeResiduals, edgesTape, List.map_map, Function.comp_def, Macro.residuals]
  exact Finset.sum_map_toList _ _

lemma edgesTape_scalars {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) :
    tapeScalars (edgesTape edges) = 0 := by
  simp [tapeScalars, edgesTape, Macro.scalars]

lemma eventTape_residuals {F G : Labels r n} (e : Event F G) :
    tapeResiduals (eventTape e) = e.residualDimension := by
  simp only [tapeResiduals, eventTape, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Macro.residuals, add_zero]
  exact edgesTape_residuals e.edges

lemma eventTape_scalars {F G : Labels r n} (e : Event F G) :
    tapeScalars (eventTape e) = 1 := by
  simp only [tapeScalars, eventTape, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Macro.scalars, add_zero]
  change tapeScalars (edgesTape e.edges) + 1 = 1
  rw [edgesTape_scalars, zero_add]

lemma scheduleTape_residuals {F G : Labels r n} (s : Schedule F G) :
    tapeResiduals (scheduleTape s) = s.residualDimension := by
  induction s with
  | nil F => rfl
  | cons e s ih =>
    change tapeResiduals (eventTape e ++ scheduleTape s) = _
    simp only [tapeResiduals, List.map_append, List.sum_append]
    change tapeResiduals (eventTape e) + tapeResiduals (scheduleTape s) = _
    rw [eventTape_residuals, ih]
    rfl

lemma scheduleTape_scalars {F G : Labels r n} (s : Schedule F G) :
    tapeScalars (scheduleTape s) = s.scalarCount := by
  induction s with
  | nil F => rfl
  | cons e s ih =>
    change tapeScalars (eventTape e ++ scheduleTape s) = _
    simp only [tapeScalars, List.map_append, List.sum_append]
    change tapeScalars (eventTape e) + tapeScalars (scheduleTape s) = _
    rw [eventTape_scalars, ih]
    rfl

lemma finishTape_residuals {F G H : Labels r n} (s : Schedule F G)
    (edges : ∀ i, NestedEdge (G i) (H i)) :
    tapeResiduals (finishTape s edges) = s.residualDimension + ∑ i, (edges i).dimension := by
  simp only [finishTape, tapeResiduals, List.map_append, List.sum_append]
  change tapeResiduals (scheduleTape s) + tapeResiduals (edgesTape edges) = _
  rw [scheduleTape_residuals, edgesTape_residuals]

lemma finishTape_scalars {F G H : Labels r n} (s : Schedule F G)
    (edges : ∀ i, NestedEdge (G i) (H i)) :
    tapeScalars (finishTape s edges) = s.scalarCount := by
  simp only [finishTape, tapeScalars, List.map_append, List.sum_append]
  change tapeScalars (scheduleTape s) + tapeScalars (edgesTape edges) = _
  rw [scheduleTape_scalars, edgesTape_scalars, add_zero]


/-- The fixed basis of an edge is independent of the column count. -/
def edgeVectors {A B : Label n} : (e : NestedEdge A B) → Fin e.dimension → Vec (Fin n)
  | .increasing _ _ b _ => fun i => b i
  | .decreasing _ _ b _ => fun i => b i

def edgeInverse {A B : Label n} : NestedEdge A B → Bool
  | .increasing _ _ _ _ => false
  | .decreasing _ _ _ _ => true

lemma edgeVectors_orthonormal {A B : Label n} (e : NestedEdge A B) :
    Orthonormal (edgeVectors e) := by
  cases e <;> assumption

/-- Residual direction k in column c, in the actual column-coordinate equivalence. -/
def columnDirection (q : ℕ) {A B : Label n} (e : NestedEdge A B)
    (c : Fin q) (k : Fin e.dimension) : Vec (Fin (q * n)) :=
  StageFrames.coordinates finProdFinEquiv (tensor (unit c) (edgeVectors e k))

lemma columnDirections_orthonormal (q : ℕ) {A B : Label n} (e : NestedEdge A B) :
    Orthonormal (fun ck : Fin q × Fin e.dimension => columnDirection q e ck.1 ck.2) := by
  intro i j
  unfold columnDirection
  rw [StageFrames.coordinates_dot]
  exact BinaryColumns.columnFamily_orthonormal (edgeVectors e) (edgeVectors_orthonormal e) i j

lemma columnDirection_nonzero (q : ℕ) {A B : Label n} (e : NestedEdge A B)
    (c : Fin q) (k : Fin e.dimension) : columnDirection q e c k ≠ 0 := by
  apply FrameWords.norm_one_nonzero
  simpa using columnDirections_orthonormal q e (c, k) (c, k)

lemma copied_event_data (q : ℕ) {F G : Labels r n} (e : Event F G) :
    (ColumnSchedule.eventColumns q e).dest = e.dest ∧
    (ColumnSchedule.eventColumns q e).source = e.source ∧
    (ColumnSchedule.eventColumns q e).coefficient = e.coefficient := ⟨rfl, rfl, rfl⟩

lemma copied_edge_vector (q : ℕ) {A B : Label n} (e : NestedEdge A B)
    (c : Fin q) (k : Fin e.dimension) :
    edgeVectors (ColumnSchedule.edgeColumns q e)
      (Fin.cast (ColumnSchedule.edgeColumns_dimension q e).symm (finProdFinEquiv (c, k))) =
    columnDirection q e c k := by
  cases e with
  | increasing h d b hb =>
    change Fin d at k
    change (ColumnSchedule.columnResidualBasis q A B h b hb (finProdFinEquiv (c, k)) : Vec (Fin (q * n))) = _
    rw [ColumnSchedule.columnResidualBasis, BinaryResiduals.residualBasis_apply,
      ColumnSchedule.columnBasis_vector]
    rfl
  | decreasing h d b hb =>
    change Fin d at k
    change (ColumnSchedule.columnResidualBasis q B A h b hb (finProdFinEquiv (c, k)) : Vec (Fin (q * n))) = _
    rw [ColumnSchedule.columnResidualBasis, BinaryResiduals.residualBasis_apply,
      ColumnSchedule.columnBasis_vector]
    rfl

lemma copied_edge_inverse (q : ℕ) {A B : Label n} (e : NestedEdge A B) :
    edgeInverse (ColumnSchedule.edgeColumns q e) = edgeInverse e := by cases e <;> rfl

/-- One metadata block of q-independent size, attached to the actual physical embedding. -/
def blockTape {R d : ℕ} (b : MasterBudget.InvocationBlock R d) : List (Macro b.width d) :=
  finishTape b.schedule b.sinkEdges

lemma blockTape_compile {R d : ℕ} (q : ℕ) (b : MasterBudget.InvocationBlock R d) :
    TripleSchedule.Global.liftWord b.embedding (compileTape q (blockTape b)) = b.word q := by
  rw [blockTape, finishTape_compile]
  rfl

lemma blockTape_residuals {R d : ℕ} (b : MasterBudget.InvocationBlock R d) :
    tapeResiduals (blockTape b) = b.residuals := finishTape_residuals _ _

lemma blockTape_scalars {R d : ℕ} (b : MasterBudget.InvocationBlock R d) :
    tapeScalars (blockTape b) = b.schedule.scalarCount := finishTape_scalars _ _

end Metadata

/-- Explicit stage-major order; no order is inferred from a Sigma-type enumeration. -/
def fixedInvocations : List (MasterBudget.Invocation ExplicitSeedBudget.h) :=
  (Finset.univ.toList.map (fun profile => ⟨0, profile⟩)) ++
  (Finset.univ.toList.map (fun profile => ⟨1, profile⟩)) ++
  (Finset.univ.toList.map (fun profile => ⟨2, profile⟩))

lemma fixedInvocations_cover (a : MasterBudget.Invocation ExplicitSeedBudget.h) :
    a ∈ fixedInvocations := by
  obtain ⟨p, profile⟩ := a
  simp only [fixedInvocations, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  fin_cases p
  · exact Or.inl (Or.inl ⟨profile, rfl⟩)
  · exact Or.inl (Or.inr ⟨profile, rfl⟩)
  · exact Or.inr ⟨profile, rfl⟩

lemma fixedInvocations_length : fixedInvocations.length = ExplicitSeedBudget.invocations := by
  simp only [fixedInvocations, List.length_append, List.length_map, Finset.length_toList,
    Finset.card_univ, TripleNetwork.profile_card, Fintype.card_fin]
  rw [← ExplicitSeedBudget.parameter_formulas.1]
  change _ = 3 * ExplicitSeedBudget.v ^ 2
  ring

lemma fixedInvocations_nodup : fixedInvocations.Nodup := by
  have ht : fixedInvocations.toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    exact List.mem_toFinset.mpr (fixedInvocations_cover a)
  apply List.nodup_iff_length_dedup_eq.mpr
  rw [← List.card_toFinset, ht, Finset.card_univ, MasterBudget.seed_invocation_card,
    fixedInvocations_length]

def fixedBlock (a : MasterBudget.Invocation ExplicitSeedBudget.h) :=
  MasterBudget.actualBlock ExplicitSeedBudget.h hh a

lemma actualBlock_word (h q : ℕ) (hl : 7 ≤ h) (p : Fin 3)
    (profile : TripleNetwork.Profile (Fin h) p) :
    (MasterBudget.actualBlock h hl ⟨p, profile⟩).word q =
      TripleSchedule.Global.liftWord (TripleSchedule.Global.invocationFinEmbedding p profile)
        (TripleSchedule.Global.invocationWordColumns q p profile hl) := by
  unfold MasterBudget.actualBlock TripleSchedule.Global.invocationWordColumns
  dsimp only
  by_cases hp : p = 1
  · rw [ite_eq_left hp, ite_eq_left hp]
    rfl
  · rw [ite_eq_right hp, ite_eq_right hp]
    rfl

lemma fixedBlock_word (q : ℕ) (p : Fin 3)
    (profile : TripleNetwork.Profile (Fin ExplicitSeedBudget.h) p) :
    (fixedBlock ⟨p, profile⟩).word q =
      TripleSchedule.Global.liftWord (TripleSchedule.Global.invocationFinEmbedding p profile)
        (TripleSchedule.Global.invocationWordColumns q p profile hh) :=
  actualBlock_word _ q hh p profile

/-- The finite metadata list is the actual master word's literal chronology. -/
lemma fixedInvocations_compile (q : ℕ) :
    (fixedInvocations.map (fun a => (fixedBlock a).word q)).flatten =
      TripleSchedule.Global.masterWordColumns q hh := by
  simp only [fixedInvocations, List.map_append, List.flatten_append, List.map_map,
    Function.comp_def, TripleSchedule.Global.masterWordColumns, TripleSchedule.Global.stageWordColumns,
    TripleSchedule.Global.profileWords]
  simp_rw [fixedBlock_word]

/-- Each metadata block supplies its actual directions, inverses, and scalar coefficients. -/
lemma fixedMetadata_compile (q : ℕ) :
    (fixedInvocations.map (fun a => TripleSchedule.Global.liftWord (fixedBlock a).embedding
      (compileTape q (blockTape (fixedBlock a))))).flatten =
      TripleSchedule.Global.masterWordColumns q hh := by
  simp_rw [blockTape_compile]
  exact fixedInvocations_compile q

lemma metadata_pointwise_total (h : ℕ) (hl : 7 ≤ h) :
    (∑ a : MasterBudget.Invocation h, tapeScalars (blockTape (MasterBudget.actualBlock h hl a))) =
      MasterBudget.invocationScalarTotal h := by
  simp only [blockTape_scalars]
  exact MasterBudget.actualBlocks_scalars h hl

lemma scale_equality (a b c d : ℕ) (hab : a = b) (hbd : c * b = d) : c * a = d := by
  rw [hab]
  exact hbd

lemma add_equality (a b c d : ℕ) (hab : a = b) (hbd : b + c = d) : a + c = d := by
  rw [hab]
  exact hbd

lemma fixedMetadata_pointwise_total :
    3 * (∑ a : MasterBudget.Invocation ExplicitSeedBudget.h, tapeScalars (blockTape (fixedBlock a))) =
      pointwiseCalls := by
  exact scale_equality _ (MasterBudget.invocationScalarTotal ExplicitSeedBudget.h) 3 pointwiseCalls
    (metadata_pointwise_total ExplicitSeedBudget.h hh) MasterBudget.seed_pointwise_calls

lemma metadata_residual_total (h : ℕ) (hl : 7 ≤ h) :
    (∑ a : MasterBudget.Invocation h, tapeResiduals (blockTape (MasterBudget.actualBlock h hl a))) =
      TripleSchedule.Global.masterResidual hl := by
  simp only [blockTape_residuals]
  unfold TripleSchedule.Global.masterResidual
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro profile hprofile
  unfold MasterBudget.InvocationBlock.residuals MasterBudget.actualBlock
  dsimp only
  by_cases he : p = 1
  · rw [ite_eq_left he]
    rw [TripleSchedule.ReverseLocal.localSchedule_residualDimension]
    exact TripleSchedule.Global.local_residual_reindex _ _
  · rw [ite_eq_right he]
    rw [TripleSchedule.localSchedule_residualDimension]
    exact TripleSchedule.Global.local_residual_reindex _ _

lemma fixedMetadata_residual_total :
    (∑ a : MasterBudget.Invocation ExplicitSeedBudget.h, tapeResiduals (blockTape (fixedBlock a))) +
      (W - ExplicitSeedBudget.roles) * m = S := by
  exact add_equality _ (TripleSchedule.Global.masterResidual (h := ExplicitSeedBudget.h) hh) ((W - ExplicitSeedBudget.roles) * m) S
    (metadata_residual_total ExplicitSeedBudget.h hh)
    (seedPaddingResiduals hh)

lemma normalized_residuals : (S : ℝ) / (W : ℝ) = UniformExponent.lambda := rfl

end
end ExactFourierCircuits.UniformFixedNetwork
