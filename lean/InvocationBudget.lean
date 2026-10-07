import GateFrames
import ResidualBudget

set_option autoImplicit false
namespace ExactFourierCircuits.InvocationBudget
open BinaryFrames BinaryComplement BinaryTensor BinaryResiduals BinaryProjection StageFrames GateFrames
open FramedScheduleWords ScalarNetwork Module
open scoped BigOperators
noncomputable section

variable {ι η : Type*} [Fintype ι] [Fintype η] {h n : ℕ}

lemma label_dimension (L : Label n) : L.dimension = finrank F2 L.space := by
  simpa only [Fintype.card_fin] using (finrank_eq_card_basis L.basis).symm

lemma label_dimension_eq (A S : Label n) (hAS : A.space = S.space) : A.dimension = S.dimension := by
  rw [label_dimension, label_dimension, hAS]

def edgeLoss {A S : Label n} : NestedEdge A S → ℕ
  | .increasing _ _ _ _ => 0
  | .decreasing _ d _ _ => d

lemma edge_balance {A S : Label n} (e : NestedEdge A S) :
    e.dimension + A.dimension = S.dimension + 2 * edgeLoss e := by
  cases e with
  | increasing hAS d b hb =>
    have hr := ResidualBudget.nested_residual_dimension A.space S.space hAS A.basis b S.basis A.orthonormal hb
    simp only [NestedEdge.dimension, edgeLoss]
    omega
  | decreasing hSA d b hb =>
    have hr := ResidualBudget.nested_residual_dimension S.space A.space hSA S.basis b A.basis S.orthonormal hb
    simp only [NestedEdge.dimension, edgeLoss]
    omega

lemma edge_increasing_dimension {A S : Label n} (e : NestedEdge A S) (hAS : A.space ≤ S.space) :
    e.dimension + A.dimension = S.dimension := by
  cases e with
  | increasing h d b hb =>
    have hr := ResidualBudget.nested_residual_dimension A.space S.space h A.basis b S.basis A.orthonormal hb
    change d + A.dimension = S.dimension
    omega
  | decreasing h d b hb =>
    have heq := label_dimension_eq A S (le_antisymm hAS h)
    have hr := ResidualBudget.nested_residual_dimension S.space A.space h S.basis b A.basis S.orthonormal hb
    change d + A.dimension = S.dimension
    omega

lemma edge_decreasing_dimension {A S : Label n} (e : NestedEdge A S) (hSA : S.space ≤ A.space) :
    e.dimension + S.dimension = A.dimension := by
  cases e with
  | increasing h d b hb =>
    have heq := label_dimension_eq A S (le_antisymm h hSA)
    have hr := ResidualBudget.nested_residual_dimension A.space S.space h A.basis b S.basis A.orthonormal hb
    change d + S.dimension = A.dimension
    omega
  | decreasing h d b hb =>
    have hr := ResidualBudget.nested_residual_dimension S.space A.space h S.basis b A.basis S.orthonormal hb
    change d + S.dimension = A.dimension
    omega

lemma edgeLoss_increasing {A S : Label n} (e : NestedEdge A S) (hAS : A.space ≤ S.space) :
    edgeLoss e = 0 := by
  have hi := edge_increasing_dimension e hAS
  have hb := edge_balance e
  omega

lemma edgeLoss_decreasing {A S : Label n} (e : NestedEdge A S) (hSA : S.space ≤ A.space) :
    edgeLoss e = e.dimension := by
  have hi := edge_decreasing_dimension e hSA
  have hb := edge_balance e
  omega

def centralDecrease (row : Fin 8) : Role h → Bool
  | .center _ => decide (row.val = 4)
  | _ => false

/-- The only geometrically decreasing row is row four on the actual center roles. -/
lemma local_nested (d : Data ι η h) (row : Fin 8) (role : Role h) :
    if centralDecrease row role then d.localAt row.succ role ≤ d.localAt row.castSucc role
      else d.localAt row.castSucc role ≤ d.localAt row.succ role := by
  cases role with
  | x T =>
    fin_cases row <;> simp [centralDecrease, Data.localAt, Data.entry, rowLabel]
    · exact decomposes_nested (residual_X_in_2 _ _ _ d.split (t T) (t_norm T))
    · exact decomposes_nested (residual_X_2_3 _ _ _ d.split (t T) (t_norm T))
  | y S =>
    fin_cases row <;> simp [centralDecrease, Data.localAt, Data.entry, rowLabel]
    · exact decomposes_nested (residual_Y_0_1 _ (t S) (t_norm S))
    · exact decomposes_nested (residual_Y_4_5 _ _ _ d.split (t S))
  | side e =>
    fin_cases row <;> simp [centralDecrease, Data.localAt, Data.entry, rowLabel]
    · exact decomposes_nested (residual_side_0_2 _ _ _ d.split (t e.val.2) (t e.val.1) (t_norm _))
    · exact decomposes_nested
        (residual_side_2_5 _ _ _ d.split (t e.val.2) (t e.val.1) (t_norm _) (edge_orthogonal e))
    · exact decomposes_nested (residual_side_5_7 _ _ _ d.split (t e.val.1) (t_norm _))
  | center i =>
    fin_cases row <;> simp [centralDecrease, Data.localAt, Data.entry, rowLabel]
    all_goals exact decomposes_nested (residual_center_BD_ED _ _ _ d.split)

lemma labels_nested (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (role : Role h) :
    if centralDecrease row role then (d.labels e row.succ role).space ≤ (d.labels e row.castSucc role).space
      else (d.labels e row.castSucc role).space ≤ (d.labels e row.succ role).space := by
  have hl := local_nested d row role
  cases hc : centralDecrease row role
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hl ⊢
    exact Submodule.map_mono (tensorSpace_mono hl le_rfl)
  · simp only [hc, ↓reduceIte] at hl ⊢
    exact Submodule.map_mono (tensorSpace_mono hl le_rfl)

lemma sink_nested (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (role : Role h) :
    (d.labels e 8 role).space ≤ (d.finalLabels e role).space := by
  cases role with
  | x S => exact le_rfl
  | y S => exact le_rfl
  | side edge =>
    change space e (tensorSpace (label3 (η := Fin h) ⊤) (line d.future)) ≤
      space e (tensorSpace (label3 (η := Fin h) ⊤) ⊤)
    exact Submodule.map_mono (tensorSpace_mono le_rfl le_top)
  | center i =>
    change space e (tensorSpace (label3 (η := Fin h) ⊤) (line d.future)) ≤
      space e (tensorSpace (label3 (η := Fin h) ⊤) ⊤)
    exact Submodule.map_mono (tensorSpace_mono le_rfl le_top)

def centralSpace (d : Data ι η h) : Submodule F2 (Vec ((ι × Fin h) × η)) :=
  tensorSpace (tensorSpace (line d.prefixVector) (⊤ : Submodule F2 (Vec (Fin h)))) (line d.future)

lemma central_decomposition (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Option (Fin h)) :
    Decomposes (d.labels e 5 (.center i)).space (space e (centralSpace d)) (d.labels e 4 (.center i)).space := by
  have hr := decomposes_space e
    (tensorSpace_decomposes_left (residual_center_BD_ED d.B d.P ⊤ d.split) (line d.future))
  simpa [Data.at, Data.localAt, rowLabel, centralSpace, Data.P] using hr

lemma centralSpace_basis (d : Data ι η h) : HasONBasis (centralSpace d) :=
  hasONBasis_tensor (hasONBasis_tensor d.P_basis hasONBasis_top) (hasONBasis_line _ d.future_norm)

lemma central_residual_rank (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Option (Fin h)) :
    finrank F2 (residual (d.labels e 5 (.center i)).space (d.labels e 4 (.center i)).space) = h := by
  rw [residual_of_decomposes (central_decomposition d e i) (d.labels e 5 (.center i)).nondegenerate]
  calc
    _ = finrank F2 (centralSpace d) := (subspaceCoordinates e (centralSpace d)).finrank_eq.symm
    _ = h := by
      change finrank F2 (tensorSpace (tensorSpace (line d.prefixVector)
        (⊤ : Submodule F2 (Vec (Fin h)))) (line d.future)) = h
      exact (central_future_residual_dimension (η := Fin h) d.prefixVector d.future
        d.prefix_norm d.future_norm).trans (Fintype.card_fin h)

lemma central_edge_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Option (Fin h)) :
    (d.edges e 4 (.center i)).dimension = h := by
  have hr := central_decomposition d e i
  have hSA := decomposes_nested hr
  have hD := edge_decreasing_dimension (d.edges e 4 (.center i)) hSA
  change (d.edges e 4 (.center i)).dimension + (d.labels e 5 (.center i)).dimension =
    (d.labels e 4 (.center i)).dimension at hD
  obtain ⟨dR, b, hb⟩ := hasONBasis_residual hr
    ⟨(d.labels e 5 (.center i)).dimension, (d.labels e 5 (.center i)).basis,
      (d.labels e 5 (.center i)).orthonormal⟩ (hasONBasis_space e (centralSpace_basis d))
  have hdim := ResidualBudget.nested_residual_dimension _ _ hSA
    (d.labels e 5 (.center i)).basis b (d.labels e 4 (.center i)).basis
    (d.labels e 5 (.center i)).orthonormal hb
  have hR : dR = h := by
    have hcard := finrank_eq_card_basis b
    rw [central_residual_rank d e i] at hcard
    simpa only [Fintype.card_fin] using hcard.symm
  omega

lemma data_edgeLoss (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (role : Role h) :
    edgeLoss (d.edges e row role) = if centralDecrease row role then h else 0 := by
  have hl := labels_nested d e row role
  cases hc : centralDecrease row role
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hl ⊢
    exact edgeLoss_increasing _ hl
  · simp only [hc, ↓reduceIte] at hl ⊢
    rw [edgeLoss_decreasing _ hl]
    cases role <;> simp [centralDecrease] at hc
    rename_i i
    have hr : row = 4 := Fin.ext (by simpa using hc)
    subst row
    exact central_edge_dimension d e i

lemma sink_edgeLoss (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (role : Role h) :
    edgeLoss (d.sinkEdges e role) = 0 := edgeLoss_increasing _ (sink_nested d e role)

/-- A constructor sum equivalence used only to sum actual geometric role data. -/
def roleSum : Role h ≃ Triple (Fin h) ⊕ (Triple (Fin h) ⊕ (Edge (Fin h) ⊕ Option (Fin h))) where
  toFun
    | .x S => .inl S
    | .y S => .inr (.inl S)
    | .side e => .inr (.inr (.inl e))
    | .center i => .inr (.inr (.inr i))
  invFun
    | .inl S => .x S
    | .inr (.inl S) => .y S
    | .inr (.inr (.inl e)) => .side e
    | .inr (.inr (.inr i)) => .center i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with S | S | e | i <;> rfl

lemma sum_roles {A : Type*} [AddCommMonoid A] (f : Role h → A) :
    ∑ role, f role = (∑ S, f (.x S)) + (∑ S, f (.y S)) + (∑ e, f (.side e)) + (∑ i, f (.center i)) := by
  rw [← (roleSum (h := h)).symm.sum_comp]
  simp only [Fintype.sum_sum_type, roleSum, Equiv.coe_fn_symm_mk]
  abel

def centerLoss : Role h → ℕ
  | .center _ => h
  | _ => 0

lemma rowLoss_sum (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (role : Role h) :
    (∑ row : Fin 8, edgeLoss (d.edges e row role)) = centerLoss role := by
  simp only [data_edgeLoss]
  cases role <;> simp [centralDecrease, centerLoss, Fin.sum_univ_succ]

lemma centerLoss_sum : (∑ role : Role h, centerLoss role) = (h + 1) * h := by
  rw [sum_roles]
  simp [centerLoss, Fintype.card_option, Nat.mul_comm]

lemma actual_loss_total (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (∑ row : Fin 8, ∑ role : Role h, edgeLoss (d.edges e row role)) +
      (∑ role : Role h, edgeLoss (d.sinkEdges e role)) = (h + 1) * h := by
  rw [Finset.sum_comm]
  simp only [rowLoss_sum, sink_edgeLoss, Finset.sum_const_zero, add_zero]
  exact centerLoss_sum

lemma rows_role_balance (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (role : Role h) :
    (∑ row : Fin 8, (d.edges e row role).dimension) + (d.labels e 0 role).dimension =
      (d.labels e 8 role).dimension + 2 * centerLoss role := by
  have hb := ResidualBudget.finite_path_accounting (fun j => (d.labels e j role).dimension)
    (fun row => (d.edges e row role).dimension) (fun row => edgeLoss (d.edges e row role))
    (fun row => edge_balance (d.edges e row role))
  rw [rowLoss_sum] at hb
  exact hb

lemma finished_role_balance (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (role : Role h) :
    ((∑ row : Fin 8, (d.edges e row role).dimension) + (d.sinkEdges e role).dimension) +
      (d.labels e 0 role).dimension = (d.finalLabels e role).dimension + 2 * centerLoss role := by
  have hr := rows_role_balance d e role
  have hs := edge_increasing_dimension (d.sinkEdges e role) (sink_nested d e role)
  have hb := ResidualBudget.budget_comp hr
    (show (d.sinkEdges e role).dimension + (d.labels e 8 role).dimension =
      (d.finalLabels e role).dimension + 2 * 0 by simpa using hs)
  simpa using hb

def residualTotal (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) : ℕ :=
  (∑ row : Fin 8, ∑ role : Role h, (d.edges e row role).dimension) +
    ∑ role : Role h, (d.sinkEdges e role).dimension

def sourceDimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) : ℕ :=
  ∑ role : Role h, (d.labels e 0 role).dimension

def sinkDimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) : ℕ :=
  ∑ role : Role h, (d.finalLabels e role).dimension

/-- Nontruncated accounting of the actual eight rows and every auxiliary sink edge. -/
theorem invocation_balance (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    residualTotal d e + sourceDimension d e = sinkDimension d e + 2 * ((h + 1) * h) := by
  have hb := ResidualBudget.role_budget_sum
    (fun role => (∑ row : Fin 8, (d.edges e row role).dimension) + (d.sinkEdges e role).dimension)
    (fun role => (d.labels e 0 role).dimension) (fun role => (d.finalLabels e role).dimension)
    centerLoss (finished_role_balance d e)
  rw [Finset.sum_add_distrib, Finset.sum_comm, centerLoss_sum] at hb
  exact hb

lemma coordinate_rank {κ μ : Type*} [Fintype κ] [Fintype μ]
    (e : κ ≃ μ) (A : Submodule F2 (Vec κ)) : finrank F2 (space e A) = finrank F2 A :=
  (subspaceCoordinates e A).finrank_eq.symm

lemma top_rank {κ : Type*} [Fintype κ] :
    finrank F2 (⊤ : Submodule F2 (Vec κ)) = Fintype.card κ := by
  classical
  exact finrank_eq_card_basis fullBasis

lemma line_rank {κ : Type*} [Fintype κ] (u : Vec κ) (hu : dot u u = 1) :
    finrank F2 (line u) = 1 := by
  rw [finrank_eq_card_basis (lineBasis u hu)]
  simp

lemma perp_rank {κ : Type*} [Fintype κ] (u : Vec κ) (hu : dot u u = 1) (hP : HasONBasis (perp u)) :
    finrank F2 (perp u) = Fintype.card κ - 1 := by
  classical
  obtain ⟨dP, b, hb⟩ := hP
  have hd := finrank_eq_card_basis
    (sumBasis (line u) (perp u) (lineBasis u hu) b (by intro i j; simpa using hu) hb
      (line_decomposes_perp u hu).2)
  rw [(line_decomposes_perp u hu).1, top_rank] at hd
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] at hd
  rw [finrank_eq_card_basis b, Fintype.card_fin]
  omega

lemma tensor_rank {κ μ : Type*} [Fintype κ] [Fintype μ]
    (A : Submodule F2 (Vec κ)) (B : Submodule F2 (Vec μ)) (hA : HasONBasis A) (hB : HasONBasis B) :
    finrank F2 (tensorSpace A B) = finrank F2 A * finrank F2 B := by
  classical
  obtain ⟨dA, a, ha⟩ := hA
  obtain ⟨dB, b, hb⟩ := hB
  rw [finrank_eq_card_basis (tensorBasis A B a b ha hb), finrank_eq_card_basis a, finrank_eq_card_basis b]
  simp

lemma tensor_line_rank {κ μ : Type*} [Fintype κ] [Fintype μ]
    (A : Submodule F2 (Vec κ)) (u : Vec μ) (hu : dot u u = 1) (hA : HasONBasis A) :
    finrank F2 (tensorSpace A (line u)) = finrank F2 A := by
  rw [tensor_rank A (line u) hA (hasONBasis_line u hu), line_rank u hu, mul_one]

lemma source_x_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (S : Triple (Fin h)) :
    (d.labels e 0 (.x S)).dimension = Fintype.card ι := by
  rw [label_dimension, Data.labels_space, coordinate_rank]
  change finrank F2 (tensorSpace (tensorSpace (⊤ : Submodule F2 (Vec ι)) (line (t S))) (line d.future)) = _
  rw [tensor_line_rank _ d.future d.future_norm
      (hasONBasis_tensor hasONBasis_top (hasONBasis_line _ (t_norm S))),
    tensor_line_rank _ (t S) (t_norm S) hasONBasis_top, top_rank]

lemma source_y_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (S : Triple (Fin h)) :
    (d.labels e 0 (.y S)).dimension = Fintype.card ι - 1 := by
  rw [label_dimension, Data.labels_space, coordinate_rank]
  change finrank F2 (tensorSpace (tensorSpace (perp d.prefixVector) (line (t S))) (line d.future)) = _
  rw [tensor_line_rank _ d.future d.future_norm
      (hasONBasis_tensor d.prefix_complement (hasONBasis_line _ (t_norm S))),
    tensor_line_rank _ (t S) (t_norm S) d.prefix_complement,
    perp_rank d.prefixVector d.prefix_norm d.prefix_complement]

lemma source_side_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (side : Edge (Fin h)) :
    (d.labels e 0 (.side side)).dimension = 0 := by
  rw [label_dimension, Data.labels_space]
  change finrank F2 (space e (tensorSpace (⊥ : Submodule F2 (Vec (ι × Fin h))) (line d.future))) = 0
  rw [StageFrames.tensorSpace_bot_left, space_bot]
  simp

lemma source_center_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Option (Fin h)) :
    (d.labels e 0 (.center i)).dimension = 0 := by
  rw [label_dimension, Data.labels_space]
  change finrank F2 (space e (tensorSpace (⊥ : Submodule F2 (Vec (ι × Fin h))) (line d.future))) = 0
  rw [StageFrames.tensorSpace_bot_left, space_bot]
  simp

lemma sink_x_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (S : Triple (Fin h)) :
    (d.finalLabels e (.x S)).dimension = Fintype.card ι * h := by
  rw [label_dimension, Data.finalLabels_space, coordinate_rank, (d.final_bank_spaces S S).1]
  rw [tensor_line_rank _ d.future d.future_norm hasONBasis_top, top_rank]
  simp

lemma sink_y_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (S : Triple (Fin h)) :
    (d.finalLabels e (.y S)).dimension = Fintype.card ι * h - 1 := by
  have heq : d.localAt 8 (.y S) = perp (tensor d.prefixVector (t S)) := by
    change label5 d.B d.P (t S) = _
    exact outgoing_perp d.prefixVector (t S) d.prefix_norm (t_norm S)
  have hP : HasONBasis (perp (tensor d.prefixVector (t S))) := by
    rw [← heq]
    exact d.localAt_basis 8 (.y S)
  have hu : dot (tensor d.prefixVector (t S)) (tensor d.prefixVector (t S)) = 1 := by
    rw [dot_tensor, d.prefix_norm, t_norm]
    simp
  rw [label_dimension, Data.finalLabels_space, coordinate_rank, (d.final_bank_spaces S S).2,
    tensor_line_rank _ d.future d.future_norm hP, perp_rank _ hu hP]
  simp

lemma sink_side_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (side : Edge (Fin h)) :
    (d.finalLabels e (.side side)).dimension = n := by
  rw [label_dimension, (d.final_auxiliary_top e side none).1, top_rank, Fintype.card_fin]

lemma sink_center_dimension (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Option (Fin h)) :
    (d.finalLabels e (.center i)).dimension = n := by
  classical
  rw [label_dimension, Data.finalLabels_space, coordinate_rank]
  change finrank F2 (tensorSpace (label3 (η := Fin h) (⊤ : Submodule F2 (Vec ι))) ⊤) = _
  rw [label3, tensorSpace_top_top, tensorSpace_top_top, top_rank]
  have hc := Fintype.card_congr e
  exact hc.trans (Fintype.card_fin n)

theorem source_dimension_formula (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    sourceDimension d e = Fintype.card (Triple (Fin h)) * (Fintype.card ι + (Fintype.card ι - 1)) := by
  rw [sourceDimension, sum_roles]
  simp only [source_x_dimension, source_y_dimension, source_side_dimension, source_center_dimension]
  simp
  ring

theorem sink_dimension_formula (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    sinkDimension d e = Fintype.card (Triple (Fin h)) * (Fintype.card ι * h + (Fintype.card ι * h - 1)) +
      (Fintype.card (Edge (Fin h)) + h + 1) * n := by
  rw [sinkDimension, sum_roles]
  simp only [sink_x_dimension, sink_y_dimension, sink_side_dimension, sink_center_dimension]
  simp [Fintype.card_option]
  ring

theorem invocation_dimension_formula (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    residualTotal d e + Fintype.card (Triple (Fin h)) * (Fintype.card ι + (Fintype.card ι - 1)) =
      Fintype.card (Triple (Fin h)) * (Fintype.card ι * h + (Fintype.card ι * h - 1)) +
        (Fintype.card (Edge (Fin h)) + h + 1) * n + 2 * ((h + 1) * h) := by
  have hb := invocation_balance d e
  rw [source_dimension_formula, sink_dimension_formula] at hb
  exact hb

end
end ExactFourierCircuits.InvocationBudget
