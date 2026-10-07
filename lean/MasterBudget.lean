import ColumnSchedule
import TerminalWords
import TripleSchedule
import ExplicitSeedBudget
import PaddingWords
import ConstructiveBridge
import InvocationBudget

set_option autoImplicit false
namespace ExactFourierCircuits.MasterBudget
open OAI.ExactFourier BinaryFrames BinaryTensor FrameSpectrum FramedScheduleWords
open scoped BigOperators
noncomputable section

variable {r m n : ℕ}

/-- The loss is read from the actual oriented geometric edge, not from a proposed count. -/
def edgeLoss {A S : Label n} : NestedEdge A S → ℕ
  | .increasing _ _ _ _ => 0
  | .decreasing _ d _ _ => d

theorem edge_balance {A S : Label n} (e : NestedEdge A S) :
    e.dimension + A.dimension = S.dimension + 2 * edgeLoss e := by
  cases e with
  | increasing h d b hb =>
    have he := ResidualBudget.nested_residual_dimension A.space S.space h A.basis b S.basis
      A.orthonormal hb
    simp only [NestedEdge.dimension, edgeLoss, mul_zero, add_zero]
    omega
  | decreasing h d b hb =>
    have he := ResidualBudget.nested_residual_dimension S.space A.space h S.basis b A.basis
      S.orthonormal hb
    simp only [NestedEdge.dimension, edgeLoss]
    omega

def labelDimensionSum (F : Labels r n) : ℕ := ∑ i, (F i).dimension

def edgesLoss {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) : ℕ :=
  ∑ i, edgeLoss (edges i)

theorem edges_balance {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) :
    (∑ i, (edges i).dimension) + labelDimensionSum F =
      labelDimensionSum G + 2 * edgesLoss edges := by
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => edge_balance (edges i))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, labelDimensionSum, edgesLoss] using hh

def scheduleLoss : ∀ {F G : Labels r n}, Schedule F G → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons e s => edgesLoss e.edges + scheduleLoss s

theorem schedule_balance {F G : Labels r n} (s : Schedule F G) :
    s.residualDimension + labelDimensionSum F = labelDimensionSum G + 2 * scheduleLoss s := by
  induction s with
  | nil F => simp [Schedule.residualDimension, scheduleLoss]
  | cons e s ih =>
    have he := edges_balance e.edges
    change e.residualDimension + s.residualDimension + _ = _ + 2 * (_ + _)
    change e.residualDimension + labelDimensionSum _ = _ + 2 * edgesLoss e.edges at he
    omega

/-- Sink-only edges are counted once, after the last scalar event. -/
theorem finish_balance {F G H : Labels r n} (s : Schedule F G)
    (sinkEdges : ∀ i, NestedEdge (G i) (H i)) :
    (s.residualDimension + ∑ i, (sinkEdges i).dimension) + labelDimensionSum F =
      labelDimensionSum H + 2 * (scheduleLoss s + edgesLoss sinkEdges) := by
  have hs := schedule_balance s
  have he := edges_balance sinkEdges
  omega

/-- Actual axis/profile invocation indices; their cardinality is proved symbolically. -/
abbrev Invocation (h : ℕ) := Σ p : Fin 3, TripleNetwork.Profile (Fin h) p

theorem invocation_card (h : ℕ) : Fintype.card (Invocation h) = 3 * (Nat.choose h 3) ^ 2 := by
  simp [Invocation, Fintype.card_sigma]

theorem sum_invocation (h : ℕ) (g : Invocation h → ℕ) :
    (∑ a, g a) = ((∑ a : TripleNetwork.Profile (Fin h) 0, g ⟨0,a⟩) +
      ∑ a : TripleNetwork.Profile (Fin h) 1, g ⟨1,a⟩) +
      ∑ a : TripleNetwork.Profile (Fin h) 2, g ⟨2,a⟩ := by
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change (∑ a : TripleNetwork.Profile (Fin h) 0, g ⟨0,a⟩) +
      ((∑ a : TripleNetwork.Profile (Fin h) 1, g ⟨1,a⟩) +
        ∑ a : TripleNetwork.Profile (Fin h) 2, g ⟨2,a⟩) = _
  omega

/-- The total of the actual eight-row support counts over these invocation indices.
    A master schedule must separately prove its scalarCount equals this total,
    including the reversed middle stage's support-cardinality bridge. -/
def invocationScalarTotal (h : ℕ) : ℕ :=
  ∑ _ : Invocation h, ∑ row : Fin 8, Fintype.card (TripleSchedule.RowEntry (h := h) row)

theorem invocation_scalar_total (h : ℕ) : invocationScalarTotal h =
    (3 * (Nat.choose h 3) ^ 2) *
      (4 * Nat.choose h 3 * TripleCounting.neighborDegree h + 16 * Nat.choose h 3) := by
  simp only [invocationScalarTotal, TripleSchedule.local_scalar_count, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, invocation_card]

theorem seed_role_card : Fintype.card (TripleCounting.Role (Fin ExplicitSeedBudget.h)) =
    ExplicitSeedBudget.roles := by
  rw [TripleCounting.role_card]
  simp only [Fintype.card_fin]
  have hv := ExplicitSeedBudget.parameter_formulas.1
  have hd := ExplicitSeedBudget.parameter_formulas.2.1
  change ExplicitSeedBudget.degree = TripleCounting.neighborDegree ExplicitSeedBudget.h at hd
  rw [← hv, ← hd]
  exact ExplicitSeedBudget.parameter_formulas.2.2.2.1.symm

theorem seed_invocation_card : Fintype.card (Invocation ExplicitSeedBudget.h) =
    ExplicitSeedBudget.invocations := by
  rw [invocation_card, ← ExplicitSeedBudget.parameter_formulas.1]
  rfl

theorem seed_bank_card : Fintype.card (TripleNetwork.Bank (Fin ExplicitSeedBudget.h)) =
    ExplicitSeedBudget.v ^ 3 := by
  rw [TripleNetwork.bank_card, Fintype.card_fin, ← ExplicitSeedBudget.parameter_formulas.1]

theorem seed_pointwise_calls : 3 * invocationScalarTotal ExplicitSeedBudget.h =
    ExplicitSeedBudget.pointwiseCalls := by
  rw [invocation_scalar_total, ← ExplicitSeedBudget.parameter_formulas.1]
  have hd := ExplicitSeedBudget.parameter_formulas.2.1
  change ExplicitSeedBudget.degree = TripleCounting.neighborDegree ExplicitSeedBudget.h at hd
  rw [← hd]
  change 3 * (ExplicitSeedBudget.invocations * _) = _
  rw [ExplicitSeedBudget.parameter_formulas.2.2.2.2.2]
  ring

theorem seed_loss_margin : ExplicitSeedBudget.margin +
    2 * (ExplicitSeedBudget.invocations * (ExplicitSeedBudget.h + 1) * ExplicitSeedBudget.h) =
      2 * ExplicitSeedBudget.v ^ 3 := by
  norm_num [ExplicitSeedBudget.margin, ExplicitSeedBudget.invocations, ExplicitSeedBudget.h,
    ExplicitSeedBudget.v]

/-- Each actual invocation has one decreasing row for each actual central role. -/
def centralDecreaseTotal (h : ℕ) : ℕ := ∑ _ : Invocation h × Option (Fin h), h

theorem central_decrease_total (h : ℕ) : centralDecreaseTotal h =
    (3 * (Nat.choose h 3) ^ 2) * (h + 1) * h := by
  simp [centralDecreaseTotal]

theorem seed_central_decrease_total : centralDecreaseTotal ExplicitSeedBudget.h =
    ExplicitSeedBudget.invocations * (ExplicitSeedBudget.h + 1) * ExplicitSeedBudget.h := by
  rw [central_decrease_total, ← ExplicitSeedBudget.parameter_formulas.1]
  rfl

/-- The h=100 residual budget follows from actual schedule geometry and concrete endpoint/loss facts. -/
theorem seed_residual_balance {F G H : Labels ExplicitSeedBudget.roles ExplicitSeedBudget.m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (hsource : labelDimensionSum F = ExplicitSeedBudget.v ^ 3)
    (hsink : labelDimensionSum H + ExplicitSeedBudget.v ^ 3 =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m)
    (hloss : scheduleLoss s + edgesLoss sinkEdges =
      ExplicitSeedBudget.invocations * (ExplicitSeedBudget.h + 1) * ExplicitSeedBudget.h) :
    (s.residualDimension + ∑ i, (sinkEdges i).dimension) + ExplicitSeedBudget.margin =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m := by
  have hb := ResidualBudget.network_residual_balance (finish_balance s sinkEdges) hsource hsink
  exact ResidualBudget.residual_saving_balance hb (by rw [hloss]; exact seed_loss_margin)

theorem pow_address_factor (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ n => simp [pow_succ, Nat.mul_comm]

/-- This count comes from the compiled column schedule, including its actual sink edges. -/
theorem column_finish_factored_calls (f : ℕ) (hn : 1 ≤ f * m) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i)) :
    wordCalls ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges)) =
      (f * (s.residualDimension + ∑ i, (sinkEdges i).dimension) + 2 * (3 * s.scalarCount)) *
        2 ^ (f * m - 1) := by
  rw [ColumnSchedule.finishColumns_word_calls _ hn, pow_address_factor _ hn]
  ring

theorem column_finish_saves (f Δ : ℕ) (hn : 1 ≤ f * m) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (hbalance : (s.residualDimension + ∑ i, (sinkEdges i).dimension) + Δ = r * m)
    (hmargin : 2 * (3 * s.scalarCount) < Δ * f) :
    wordCalls ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges)) < r * (f * m) * 2 ^ (f * m - 1) := by
  rw [column_finish_factored_calls _ hn]
  have hc := SavingBudget.factored_saving (r := 0) hbalance
    (show 0 < 2 ^ (f * m - 1) by positivity) hmargin
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc

/-- Equality of the binary whole-array action determines its packed matrix. -/
theorem binaryAction_injective (n : ℕ) : Function.Injective (FrameWords.binaryAction (n := n)) := by
  intro M N h
  apply (Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n).symm).injective
  ext i j
  have he := congrFun (LinearMap.congr_fun h (fun k => if k = j then 1 else 0)) i
  simpa [FrameWords.binaryAction, Matrix.mulVec, dotProduct, mul_ite] using he

theorem axes_list_action (L : List (Fin n)) :
    FrameWords.binaryAction (wordMatrix ((L.map (fun p => TensorWords.unitAxisWord p)).flatten)) =
      signedWord (unit : Fin n → Vec (Fin n)) false L := by
  induction L with
  | nil => simpa [wordMatrix, signedWord] using (FrameWords.binaryAction_one (n := n))
  | cons p L ih =>
    simp only [List.map_cons, List.flatten_cons, TypedKernelWords.wordMatrix_append,
      FrameWords.binaryAction_mul]
    rw [ih, TensorWords.unitAxisWord_matrix, FrameWords.binaryAction_directional]
    rw [signedWord, signedMap_unit]

theorem signed_units_reverse (L : List (Fin n)) :
    signedWord (unit : Fin n → Vec (Fin n)) false L.reverse =
      signedWord (unit : Fin n → Vec (Fin n)) false L := by
  apply operator_eq_of_characters
  intro ξ
  have hu : ∀ i : Fin n, dot (unit i) (unit i) = 1 := by intro i; rw [dot_units]; simp
  rw [signedWord_character _ _ hu, signedWord_character _ _ hu]
  simp

theorem unitAxesWord_action (n : ℕ) :
    FrameWords.binaryAction (wordMatrix (TensorWords.unitAxesWord n)) = frameMap weightModFour := by
  rw [TensorWords.unitAxesWord, ← List.map_reverse, axes_list_action,
    signed_units_reverse, coordinate_word_standard]

/-- The terminal module's coordinate frame and the padding module's raw tensor-axis word agree exactly. -/
theorem coordinateWord_matrix (n : ℕ) :
    wordMatrix (TerminalWords.coordinateWord n) = wordMatrix (TensorWords.unitAxesWord n) := by
  apply binaryAction_injective n
  rw [TerminalWords.coordinateWord_action, unitAxesWord_action]

theorem ordinaryWord_matrix (w n : ℕ) :
    wordMatrix (TerminalWords.ordinaryWord w n) =
      PaddingWords.copiesMatrix w n (wordMatrix (TensorWords.unitAxesWord n)) := by
  rw [TerminalWords.ordinaryWord_matrix]
  unfold TerminalWords.ordinaryMatrix PaddingWords.copiesMatrix
  rw [coordinateWord_matrix]
  rfl

variable {δ β : Type*}

/-- The exact corrected word consists of the compiled columns/sink edges and the actual free correction. -/
def correctedColumnWord (f : ℕ) {F G H : Labels r m} (s : Schedule F G)
    (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin r) (u : δ → Vec (Fin (f * m))) :
    List (WordStep C (r * 2 ^ (f * m))) :=
  (ColumnSchedule.scheduleColumns f s).finishWord (ColumnSchedule.edgesColumns f sinkEdges) ++
    TerminalWords.correctionWord e u

theorem correctedColumnWord_calls (f : ℕ) (hn : 1 ≤ f * m) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin r) (u : δ → Vec (Fin (f * m))) :
    wordCalls (correctedColumnWord f s sinkEdges e u) =
      (f * (s.residualDimension + ∑ i, (sinkEdges i).dimension) + 2 * (3 * s.scalarCount)) *
        2 ^ (f * m - 1) := by
  rw [correctedColumnWord, TerminalWords.master_terminal_calls, column_finish_factored_calls _ hn]

/-- The actual master action and terminal identity are required on all states, including dirty arrays. -/
theorem correctedColumnWord_matrix (f : ℕ) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin r) (u : δ → Vec (Fin (f * m)))
    (endpoint : NetworkTerminal.State δ β (Fin (f * m)) → NetworkTerminal.State δ β (Fin (f * m)))
    (hmaster : ∀ X, (wordMatrix ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges))).mulVec (TerminalWords.pack e X) =
        TerminalWords.pack e (endpoint X))
    (hterminal : ∀ X, NetworkTerminal.correction u (endpoint X) = NetworkTerminal.ordinary X) :
    wordMatrix (correctedColumnWord f s sinkEdges e u) =
      PaddingWords.copiesMatrix r (f * m) (wordMatrix (TensorWords.unitAxesWord (f * m))) := by
  rw [correctedColumnWord,
    TerminalWords.master_terminal_bridge_of_endpoint e u _ endpoint hmaster hterminal,
    ordinaryWord_matrix]

theorem correctedColumnWord_saves (f Δ : ℕ) (hn : 1 ≤ f * m) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin r) (u : δ → Vec (Fin (f * m)))
    (hbalance : (s.residualDimension + ∑ i, (sinkEdges i).dimension) + Δ = r * m)
    (hmargin : 2 * (3 * s.scalarCount) < Δ * f) :
    wordCalls (correctedColumnWord f s sinkEdges e u) < r * (f * m) * 2 ^ (f * m - 1) := by
  rw [correctedColumnWord, TerminalWords.master_terminal_calls]
  exact column_finish_saves _ _ hn s sinkEdges hbalance hmargin

theorem seed_address_positive (f : ℕ) (hf : f = ExplicitSeedBudget.columns) :
    1 ≤ f * ExplicitSeedBudget.m := by
  rw [hf, ExplicitSeedBudget.columns_value]
  norm_num [ExplicitSeedBudget.m]

theorem seed_bits (f : ℕ) (hf : f = ExplicitSeedBudget.columns) :
    ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.m = ExplicitSeedBudget.bits := by
  rw [hf]
  unfold ExplicitSeedBudget.bits
  ring

theorem seed_padding_bound : ExplicitSeedBudget.roles ≤ 2 ^ ExplicitSeedBudget.roleBits := by
  rw [← ExplicitSeedBudget.padding.1]
  exact ExplicitSeedBudget.padding.2.2

theorem seed_padding_residuals (R : ℕ)
    (hR : R + ExplicitSeedBudget.margin = ExplicitSeedBudget.roles * ExplicitSeedBudget.m) :
    R + (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * ExplicitSeedBudget.m =
      ExplicitSeedBudget.residuals := by
  have hp := Nat.add_sub_of_le ExplicitSeedBudget.padding.2.2
  apply Nat.add_right_cancel (m := ExplicitSeedBudget.margin)
  calc
    _ = (R + ExplicitSeedBudget.margin) +
        (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * ExplicitSeedBudget.m := by ring
    _ = (ExplicitSeedBudget.roles +
        (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles)) * ExplicitSeedBudget.m := by
      rw [hR]
      ring
    _ = ExplicitSeedBudget.paddedRoles * ExplicitSeedBudget.m := by rw [hp]
    _ = _ := ExplicitSeedBudget.residual_balance.symm

variable {F G H : Labels ExplicitSeedBudget.roles ExplicitSeedBudget.m}

/-- This is the literal padded/fused word; no arithmetic statement supplies its master action. -/
def seedWord (f : ℕ) (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m))) :
    List (WordStep C (2 ^ (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.m))) :=
  PaddingWords.extendedWord ExplicitSeedBudget.roles ExplicitSeedBudget.roleBits (f * ExplicitSeedBudget.m)
    seed_padding_bound (correctedColumnWord f s sinkEdges e u)

/-- Actual geometric endpoint and loss facts specialize the symbolic count to the paper's h=100 formula. -/
theorem seedWord_calls (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m)))
    (hsource : labelDimensionSum F = ExplicitSeedBudget.v ^ 3)
    (hsink : labelDimensionSum H + ExplicitSeedBudget.v ^ 3 =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m)
    (hloss : scheduleLoss s + edgesLoss sinkEdges = centralDecreaseTotal ExplicitSeedBudget.h)
    (hscalar : s.scalarCount = invocationScalarTotal ExplicitSeedBudget.h) :
    wordCalls (seedWord f s sinkEdges e u) = ExplicitSeedBudget.calls (f * ExplicitSeedBudget.m) := by
  have hbalance := seed_residual_balance s sinkEdges hsource hsink
    (hloss.trans seed_central_decrease_total)
  have hres := seed_padding_residuals _ hbalance
  have hpointwise : 3 * s.scalarCount = ExplicitSeedBudget.pointwiseCalls := by
    rw [hscalar, seed_pointwise_calls]
  rw [seedWord, PaddingWords.extendedWord_calls _ _ _ _ (seed_address_positive f hf),
    correctedColumnWord_calls _ (seed_address_positive f hf), hpointwise,
    ← ExplicitSeedBudget.padding.1]
  change (f * (s.residualDimension + ∑ i, (sinkEdges i).dimension) +
      2 * ExplicitSeedBudget.pointwiseCalls) * ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) +
      (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * (f * ExplicitSeedBudget.m) *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) +
      ExplicitSeedBudget.roleBits * ExplicitSeedBudget.paddedRoles *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) = _
  calc
    _ = (((s.residualDimension + ∑ i, (sinkEdges i).dimension) +
        (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * ExplicitSeedBudget.m) *
        f + ExplicitSeedBudget.roleBits * ExplicitSeedBudget.paddedRoles +
        2 * ExplicitSeedBudget.pointwiseCalls) * ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) := by
      ring
    _ = _ := by rw [hres]; unfold ExplicitSeedBudget.calls; rw [hf]

theorem seedWord_matrix (f : ℕ) (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m)))
    (endpoint : NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)) →
      NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)))
    (hmaster : ∀ X, (wordMatrix ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges))).mulVec
        (TerminalWords.pack e X) = TerminalWords.pack e (endpoint X))
    (hterminal : ∀ X, NetworkTerminal.correction u (endpoint X) = NetworkTerminal.ordinary X) :
    wordMatrix (seedWord f s sinkEdges e u) = tensorPower C (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.m) :=
  PaddingWords.extendedWord_matrix _ _ _ _ _
    (correctedColumnWord_matrix _ s sinkEdges e u endpoint hmaster hterminal)

/-- Padding preserves the positive saving derived from actual schedule geometry and scalar counts. -/
theorem seedWord_saves (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m)))
    (hsource : labelDimensionSum F = ExplicitSeedBudget.v ^ 3)
    (hsink : labelDimensionSum H + ExplicitSeedBudget.v ^ 3 =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m)
    (hloss : scheduleLoss s + edgesLoss sinkEdges = centralDecreaseTotal ExplicitSeedBudget.h)
    (hscalar : s.scalarCount = invocationScalarTotal ExplicitSeedBudget.h) :
    wordCalls (seedWord f s sinkEdges e u) <
      (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.m) *
        2 ^ (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.m - 1) := by
  have hbalance := seed_residual_balance s sinkEdges hsource hsink
    (hloss.trans seed_central_decrease_total)
  have hmargin : 2 * (3 * s.scalarCount) < ExplicitSeedBudget.margin * f := by
    rw [hscalar, seed_pointwise_calls, hf]
    exact ExplicitSeedBudget.strict_margin
  have hactive := correctedColumnWord_saves _ _ (seed_address_positive f hf) s sinkEdges e u hbalance hmargin
  have hpadded := PaddingWords.fusedWord_saving ExplicitSeedBudget.roles ExplicitSeedBudget.roleBits
    (f * ExplicitSeedBudget.m) 1 seed_padding_bound (seed_address_positive f hf)
    (PaddingWords.canonicalNetworkWord _ _ (correctedColumnWord f s sinkEdges e u))
    (by rw [PaddingWords.canonicalNetworkWord_calls]; omega)
  change wordCalls (seedWord f s sinkEdges e u) + 1 ≤ _ at hpadded
  omega

/-- Conditional assembly: geometry and count come from a concrete Schedule; the complete action
    must be proved separately for the same literal compiled word. -/
theorem finiteWin_of_seed_schedule (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m)))
    (endpoint : NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)) →
      NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)))
    (hsource : labelDimensionSum F = ExplicitSeedBudget.v ^ 3)
    (hsink : labelDimensionSum H + ExplicitSeedBudget.v ^ 3 =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m)
    (hloss : scheduleLoss s + edgesLoss sinkEdges = centralDecreaseTotal ExplicitSeedBudget.h)
    (hscalar : s.scalarCount = invocationScalarTotal ExplicitSeedBudget.h)
    (hmaster : ∀ X, (wordMatrix ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges))).mulVec
        (TerminalWords.pack e X) = TerminalWords.pack e (endpoint X))
    (hterminal : ∀ X, NetworkTerminal.correction u (endpoint X) = NetworkTerminal.ordinary X) :
    FiniteWinStatement :=
  ConstructiveBridge.finiteWin_of_word
    (by rw [seed_bits f hf]; exact ExplicitSeedBudget.bits_at_least_two)
    (seedWord f s sinkEdges e u) (seedWord_matrix f s sinkEdges e u endpoint hmaster hterminal)
    (seedWord_saves f hf s sinkEdges e u hsource hsink hloss hscalar)

theorem main_of_seed_schedule (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i))
    (e : TerminalWords.Role δ β ≃ Fin ExplicitSeedBudget.roles)
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.m)))
    (endpoint : NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)) →
      NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.m)))
    (hsource : labelDimensionSum F = ExplicitSeedBudget.v ^ 3)
    (hsink : labelDimensionSum H + ExplicitSeedBudget.v ^ 3 =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m)
    (hloss : scheduleLoss s + edgesLoss sinkEdges = centralDecreaseTotal ExplicitSeedBudget.h)
    (hscalar : s.scalarCount = invocationScalarTotal ExplicitSeedBudget.h)
    (hmaster : ∀ X, (wordMatrix ((ColumnSchedule.scheduleColumns f s).finishWord
      (ColumnSchedule.edgesColumns f sinkEdges))).mulVec
        (TerminalWords.pack e X) = TerminalWords.pack e (endpoint X))
    (hterminal : ∀ X, NetworkTerminal.correction u (endpoint X) = NetworkTerminal.ordinary X) :
    MainStatement :=
  win_to_fourier (finiteWin_of_seed_schedule f hf s sinkEdges e u endpoint
    hsource hsink hloss hscalar hmaster hterminal)

/-- A physical invocation block carries its actual geometric schedules and embedding.
    It contains neither an action assumption nor a word-call-count certificate. -/
structure InvocationBlock (R m : ℕ) where
  width : ℕ
  first : Labels width m
  last : Labels width m
  sink : Labels width m
  schedule : Schedule first last
  sinkEdges : ∀ i, NestedEdge (last i) (sink i)
  embedding : Fin width ↪ Fin R

def InvocationBlock.residuals (b : InvocationBlock r m) : ℕ :=
  b.schedule.residualDimension + ∑ i, (b.sinkEdges i).dimension

def InvocationBlock.loss (b : InvocationBlock r m) : ℕ :=
  scheduleLoss b.schedule + edgesLoss b.sinkEdges

def InvocationBlock.word (f : ℕ) (b : InvocationBlock r m) : List (WordStep C (r * 2 ^ (f * m))) :=
  TripleSchedule.Global.liftWord b.embedding
    ((ColumnSchedule.scheduleColumns f b.schedule).finishWord (ColumnSchedule.edgesColumns f b.sinkEdges))

theorem InvocationBlock.word_calls (f : ℕ) (hn : 1 ≤ f * m) (b : InvocationBlock r m) :
    wordCalls (b.word f) = (f * b.residuals + 2 * (3 * b.schedule.scalarCount)) * 2 ^ (f * m - 1) := by
  rw [InvocationBlock.word, TripleSchedule.Global.liftWord_calls, column_finish_factored_calls _ hn]
  rfl

theorem InvocationBlock.balance (b : InvocationBlock r m) :
    b.residuals + labelDimensionSum b.first = labelDimensionSum b.sink + 2 * b.loss :=
  finish_balance b.schedule b.sinkEdges

variable {P : Type*} [Fintype P]

def familyResiduals (blocks : P → InvocationBlock r m) : ℕ := ∑ a, (blocks a).residuals
def familyScalars (blocks : P → InvocationBlock r m) : ℕ := ∑ a, (blocks a).schedule.scalarCount
def familySourceDimension (blocks : P → InvocationBlock r m) : ℕ := ∑ a, labelDimensionSum (blocks a).first
def familySinkDimension (blocks : P → InvocationBlock r m) : ℕ := ∑ a, labelDimensionSum (blocks a).sink
def familyLoss (blocks : P → InvocationBlock r m) : ℕ := ∑ a, (blocks a).loss

/-- Literal concatenation of the enlarged embedded local words; no global Schedule is required. -/
def familyWord (f : ℕ) (blocks : P → InvocationBlock r m) : List (WordStep C (r * 2 ^ (f * m))) :=
  (Finset.univ.toList.map (fun a => (blocks a).word f)).flatten

theorem familyWord_calls (f : ℕ) (hn : 1 ≤ f * m) (blocks : P → InvocationBlock r m) :
    wordCalls (familyWord f blocks) =
      (f * familyResiduals blocks + 2 * (3 * familyScalars blocks)) * 2 ^ (f * m - 1) := by
  rw [familyWord, TensorWords.wordCalls_flatten, List.map_map]
  simp_rw [Function.comp_def, InvocationBlock.word_calls _ hn]
  rw [Finset.sum_map_toList]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    familyResiduals, familyScalars]

theorem family_balance (blocks : P → InvocationBlock r m) :
    familyResiduals blocks + familySourceDimension blocks =
      familySinkDimension blocks + 2 * familyLoss blocks := by
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => InvocationBlock.balance (blocks a))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, familyResiduals, familySourceDimension,
    familySinkDimension, familyLoss] using he

/-- Cancellation of actual local boundary dimensions yields the global residual saving.
    The cancellation identity must come from the actual bank stage boundaries and fresh auxiliaries. -/
theorem family_saving_balance (blocks : P → InvocationBlock r m) (N₀ Δ : ℕ)
    (hends : familySinkDimension blocks + 2 * N₀ = familySourceDimension blocks + r * m)
    (hmargin : Δ + 2 * familyLoss blocks = 2 * N₀) :
    familyResiduals blocks + Δ = r * m := by
  have he := family_balance blocks
  omega

/-- The actual forward/reversed schedules, coordinates and physical embeddings for every invocation. -/
def actualBlock (h : ℕ) (hh : 7 ≤ h) (a : Invocation h) :
    InvocationBlock (TripleSchedule.Global.size h) (h ^ 3) :=
  let d := TripleInvocationFrames.invocationData a.1 a.2 hh
  let e := TripleInvocationFrames.invocationAddressCoordinates a.1 h
  if a.1 = 1 then {
    width := TripleSchedule.localSize h
    first := TripleSchedule.ReverseLocal.localLabels d e 0
    last := TripleSchedule.ReverseLocal.localLabels d e 8
    sink := TripleSchedule.ReverseLocal.localFinalLabels d e
    schedule := TripleSchedule.ReverseLocal.localSchedule d e
    sinkEdges := TripleSchedule.ReverseLocal.localSinkEdges d e
    embedding := TripleSchedule.Global.invocationFinEmbedding a.1 a.2 }
  else {
    width := TripleSchedule.localSize h
    first := TripleSchedule.localLabels d e 0
    last := TripleSchedule.localLabels d e 8
    sink := TripleSchedule.localFinalLabels d e
    schedule := TripleSchedule.localSchedule d e
    sinkEdges := TripleSchedule.localSinkEdges d e
    embedding := TripleSchedule.Global.invocationFinEmbedding a.1 a.2 }

theorem actualBlock_scalarCount (h : ℕ) (hh : 7 ≤ h) (a : Invocation h) :
    (actualBlock h hh a).schedule.scalarCount =
      4 * Nat.choose h 3 * TripleCounting.neighborDegree h + 16 * Nat.choose h 3 := by
  by_cases hp : a.1 = 1
  · dsimp only [actualBlock]
    rw [ite_eq_left hp]
    rw [TripleSchedule.ReverseLocal.localSchedule_scalarCount, TripleSchedule.ReverseLocal.local_scalar_count]
  · dsimp only [actualBlock]
    rw [ite_eq_right hp]
    rw [TripleSchedule.localSchedule_scalarCount, TripleSchedule.local_scalar_count]

theorem actualBlocks_scalars (h : ℕ) (hh : 7 ≤ h) :
    familyScalars (actualBlock h hh) = invocationScalarTotal h := by
  simp only [familyScalars, actualBlock_scalarCount, invocationScalarTotal,
    TripleSchedule.local_scalar_count]

/-- Profiles at one fixed physical stage are concatenated in their finite enumeration. -/
def actualStageWord (h f : ℕ) (hh : 7 ≤ h) (p : Fin 3) :
    List (WordStep C (TripleSchedule.Global.size h * 2 ^ (f * h ^ 3))) :=
  familyWord f (fun profile : TripleNetwork.Profile (Fin h) p => actualBlock h hh ⟨p, profile⟩)

/-- The concrete master keeps the explicit physical stage chronology 0,1,2. -/
def actualMasterWord (h f : ℕ) (hh : 7 ≤ h) :
    List (WordStep C (TripleSchedule.Global.size h * 2 ^ (f * h ^ 3))) :=
  actualStageWord h f hh 0 ++ actualStageWord h f hh 1 ++ actualStageWord h f hh 2

theorem actualMasterWord_calls (h f : ℕ) (hh : 7 ≤ h) (hn : 1 ≤ f * h ^ 3) :
    wordCalls (actualMasterWord h f hh) =
      (f * familyResiduals (actualBlock h hh) + 2 * (3 * invocationScalarTotal h)) *
        2 ^ (f * h ^ 3 - 1) := by
  simp only [actualMasterWord, TypedKernelWords.wordCalls_append, actualStageWord,
    familyWord_calls _ hn]
  have hr : familyResiduals (actualBlock h hh) =
      (familyResiduals (fun a => actualBlock h hh ⟨0,a⟩) +
        familyResiduals (fun a => actualBlock h hh ⟨1,a⟩)) +
        familyResiduals (fun a => actualBlock h hh ⟨2,a⟩) := by
    simpa only [familyResiduals] using sum_invocation h (fun a => (actualBlock h hh a).residuals)
  have hs : familyScalars (actualBlock h hh) =
      (familyScalars (fun a => actualBlock h hh ⟨0,a⟩) +
        familyScalars (fun a => actualBlock h hh ⟨1,a⟩)) +
        familyScalars (fun a => actualBlock h hh ⟨2,a⟩) := by
    simpa only [familyScalars] using sum_invocation h (fun a => (actualBlock h hh a).schedule.scalarCount)
  rw [← actualBlocks_scalars h hh, hr, hs]
  ring

private def seedPrefixCard (p : Fin 3) : ℕ := ![1, ExplicitSeedBudget.h, ExplicitSeedBudget.h ^ 2] p
private def seedBeforeDimension (p : Fin 3) : ℕ :=
  ExplicitSeedBudget.v * (seedPrefixCard p + (seedPrefixCard p - 1))
private def seedAfterDimension (p : Fin 3) : ℕ :=
  ExplicitSeedBudget.v * (seedPrefixCard p * ExplicitSeedBudget.h +
      (seedPrefixCard p * ExplicitSeedBudget.h - 1)) +
    (ExplicitSeedBudget.v * ExplicitSeedBudget.degree + ExplicitSeedBudget.h + 1) * ExplicitSeedBudget.m

/-- The actual local residual bases give each invocation's nontruncated dimension equation. -/
theorem seed_invocation_geometry (p : Fin 3)
    (profile : TripleNetwork.Profile (Fin ExplicitSeedBudget.h) p) (hh : 7 ≤ ExplicitSeedBudget.h) :
    TripleSchedule.Global.invocationResidual p profile hh + seedBeforeDimension p =
      seedAfterDimension p + 2 * ((ExplicitSeedBudget.h + 1) * ExplicitSeedBudget.h) := by
  have hb := InvocationBudget.invocation_dimension_formula
    (TripleInvocationFrames.invocationData p profile hh)
    (TripleInvocationFrames.invocationAddressCoordinates p ExplicitSeedBudget.h)
  have hp : Fintype.card (TripleInvocationFrames.Prefix ExplicitSeedBudget.h p) = seedPrefixCard p := by
    fin_cases p <;>
      simp [TripleInvocationFrames.Prefix, seedPrefixCard, StageFrames.EmptyCoordinates, pow_two]
  have hv : Fintype.card (ScalarNetwork.Triple (Fin ExplicitSeedBudget.h)) = ExplicitSeedBudget.v := by
    rw [ScalarNetwork.triple_card, Fintype.card_fin, ← ExplicitSeedBudget.parameter_formulas.1]
  have he : Fintype.card (ScalarNetwork.Edge (Fin ExplicitSeedBudget.h)) =
      ExplicitSeedBudget.v * ExplicitSeedBudget.degree := by
    rw [TripleCounting.edge_card, Fintype.card_fin, ← ExplicitSeedBudget.parameter_formulas.1]
    rw [ExplicitSeedBudget.parameter_formulas.2.1]
    rfl
  change TripleSchedule.Global.invocationResidual p profile hh + _ = _ at hb
  rw [hp, hv, he, ← ExplicitSeedBudget.parameter_formulas.2.2.1] at hb
  exact hb

/-- Closed h=100 residual balance is proved for the actual finite invocation family,
    by summing local geometric identities; no triples or astronomical addresses are enumerated. -/
theorem seed_master_residual_balance (hh : 7 ≤ ExplicitSeedBudget.h) :
    TripleSchedule.Global.masterResidual hh + ExplicitSeedBudget.margin =
      ExplicitSeedBudget.roles * ExplicitSeedBudget.m := by
  have hp (p : Fin 3) := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun profile _ => seed_invocation_geometry p profile hh)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    TripleNetwork.profile_card, Fintype.card_fin, ← ExplicitSeedBudget.parameter_formulas.1] at hp
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun p _ => hp p)
  simp only [Finset.sum_add_distrib] at hs
  change TripleSchedule.Global.masterResidual hh + _ = _ at hs
  norm_num [seedBeforeDimension, seedAfterDimension, seedPrefixCard, Fin.sum_univ_succ,
    ExplicitSeedBudget.h, ExplicitSeedBudget.v, ExplicitSeedBudget.degree, ExplicitSeedBudget.m] at hs
  norm_num [ExplicitSeedBudget.margin, ExplicitSeedBudget.roles, ExplicitSeedBudget.m]
  exact hs

theorem seed_actual_size : TripleSchedule.Global.size ExplicitSeedBudget.h = ExplicitSeedBudget.roles :=
  seed_role_card

theorem seed_actual_padding : TripleSchedule.Global.size ExplicitSeedBudget.h ≤ 2 ^ ExplicitSeedBudget.roleBits := by
  rw [seed_actual_size]
  exact seed_padding_bound

theorem seed_columns_positive (f : ℕ) (hf : f = ExplicitSeedBudget.columns) : 1 ≤ f := by
  rw [hf, ExplicitSeedBudget.columns_value]
  omega

/-- The corrected word uses Global.masterWordColumns's literal stage order. -/
def actualCorrectedWord (f : ℕ) (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3))) :
    List (WordStep C (TripleSchedule.Global.size ExplicitSeedBudget.h * 2 ^ (f * ExplicitSeedBudget.h ^ 3))) :=
  TripleSchedule.Global.masterWordColumns f hh ++ TerminalWords.correctionWord e u

theorem actualCorrectedWord_calls (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3))) :
    wordCalls (actualCorrectedWord f hh e u) =
      (f * TripleSchedule.Global.masterResidual hh + 2 * ExplicitSeedBudget.pointwiseCalls) *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.h ^ 3) := by
  have hn : 1 ≤ f * ExplicitSeedBudget.h ^ 3 := by
    rw [← ExplicitSeedBudget.parameter_formulas.2.2.1]
    exact seed_address_positive f hf
  rw [actualCorrectedWord, TerminalWords.master_terminal_calls,
    TripleSchedule.Global.masterWordColumns_calls _ (seed_columns_positive f hf), pow_address_factor _ hn]
  have hscalar : 3 * (3 * (Nat.choose ExplicitSeedBudget.h 3) ^ 2 *
      TripleSchedule.Global.invocationScalars ExplicitSeedBudget.h) = ExplicitSeedBudget.pointwiseCalls := by
    unfold TripleSchedule.Global.invocationScalars
    rw [← invocation_scalar_total]
    exact seed_pointwise_calls
  rw [hscalar]
  unfold ExplicitSeedBudget.factor
  ring

/-- The concrete h=100 word includes address canonicalization, padding, role axes and tensor fusion. -/
def actualSeedWord (f : ℕ) (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3))) :
    List (WordStep C (2 ^ (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.h ^ 3))) :=
  PaddingWords.extendedWord (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
    (f * ExplicitSeedBudget.h ^ 3) seed_actual_padding (actualCorrectedWord f hh e u)

/-- The exact paper budget is now the count of this actual chronological typed word. -/
theorem actualSeedWord_calls (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3))) :
    wordCalls (actualSeedWord f hh e u) = ExplicitSeedBudget.calls (f * ExplicitSeedBudget.h ^ 3) := by
  have hn : 1 ≤ f * ExplicitSeedBudget.h ^ 3 := by
    rw [← ExplicitSeedBudget.parameter_formulas.2.2.1]
    exact seed_address_positive f hf
  have hres := seed_padding_residuals _ (seed_master_residual_balance hh)
  rw [actualSeedWord, PaddingWords.extendedWord_calls _ _ _ _ hn,
    actualCorrectedWord_calls _ hf, seed_actual_size, ← ExplicitSeedBudget.padding.1]
  rw [← ExplicitSeedBudget.parameter_formulas.2.2.1]
  change (f * TripleSchedule.Global.masterResidual hh + 2 * ExplicitSeedBudget.pointwiseCalls) *
      ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) +
      (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * (f * ExplicitSeedBudget.m) *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) +
      ExplicitSeedBudget.roleBits * ExplicitSeedBudget.paddedRoles *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) = _
  calc
    _ = ((TripleSchedule.Global.masterResidual hh +
        (ExplicitSeedBudget.paddedRoles - ExplicitSeedBudget.roles) * ExplicitSeedBudget.m) * f +
        ExplicitSeedBudget.roleBits * ExplicitSeedBudget.paddedRoles + 2 * ExplicitSeedBudget.pointwiseCalls) *
        ExplicitSeedBudget.factor (f * ExplicitSeedBudget.m) := by ring
    _ = _ := by rw [hres]; unfold ExplicitSeedBudget.calls; rw [hf]

theorem actualSeedWord_saves (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3))) :
    wordCalls (actualSeedWord f hh e u) <
      (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.h ^ 3) *
        2 ^ (ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.h ^ 3 - 1) := by
  rw [actualSeedWord_calls _ hf]
  have he : f * ExplicitSeedBudget.h ^ 3 = ExplicitSeedBudget.m * ExplicitSeedBudget.columns := by
    rw [hf, ← ExplicitSeedBudget.parameter_formulas.2.2.1]
    exact Nat.mul_comm _ _
  simpa only [ExplicitSeedBudget.ordinaryCalls, Nat.add_comm] using
    ExplicitSeedBudget.proposed_count_saves (f * ExplicitSeedBudget.h ^ 3) he

/-- The saving/count is unconditional; the complete action is still an explicit obligation
    for Global.masterWordColumns on every physical dirty-array state. -/
theorem finiteWin_of_actual_master (f : ℕ) (hf : f = ExplicitSeedBudget.columns)
    (hh : 7 ≤ ExplicitSeedBudget.h)
    (e : TerminalWords.Role δ β ≃ Fin (TripleSchedule.Global.size ExplicitSeedBudget.h))
    (u : δ → Vec (Fin (f * ExplicitSeedBudget.h ^ 3)))
    (endpoint : NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.h ^ 3)) →
      NetworkTerminal.State δ β (Fin (f * ExplicitSeedBudget.h ^ 3)))
    (hmaster : ∀ X, (wordMatrix (TripleSchedule.Global.masterWordColumns f hh)).mulVec
        (TerminalWords.pack e X) = TerminalWords.pack e (endpoint X))
    (hterminal : ∀ X, NetworkTerminal.correction u (endpoint X) = NetworkTerminal.ordinary X) :
    FiniteWinStatement := by
  have hcorrected : wordMatrix (actualCorrectedWord f hh e u) =
      PaddingWords.copiesMatrix (TripleSchedule.Global.size ExplicitSeedBudget.h)
        (f * ExplicitSeedBudget.h ^ 3) (wordMatrix (TensorWords.unitAxesWord (f * ExplicitSeedBudget.h ^ 3))) := by
    rw [actualCorrectedWord,
      TerminalWords.master_terminal_bridge_of_endpoint e u _ endpoint hmaster hterminal, ordinaryWord_matrix]
  have hmatrix := PaddingWords.extendedWord_matrix _ _ _ seed_actual_padding _ hcorrected
  have hbits : 2 ≤ ExplicitSeedBudget.roleBits + f * ExplicitSeedBudget.h ^ 3 := by
    rw [← ExplicitSeedBudget.parameter_formulas.2.2.1, seed_bits f hf]
    exact ExplicitSeedBudget.bits_at_least_two
  exact ConstructiveBridge.finiteWin_of_word hbits (actualSeedWord f hh e u) hmatrix
    (actualSeedWord_saves f hf hh e u)

end
end ExactFourierCircuits.MasterBudget
