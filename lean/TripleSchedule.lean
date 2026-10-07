import GateFrames
import RectangularWords
import ScalarSupport
import TripleInvocationFrames
import TripleStageAction
import ColumnSchedule
import TripleColumnAction

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ExactFourierCircuits.TripleSchedule
open OAI.ExactFourier ScalarNetwork GateFrames BinaryFrames BinaryTensor FramedScheduleWords
open scoped BigOperators
noncomputable section
variable {h : ℕ}

/-- The local invocation has exactly the two banks and its actual side/center roles. -/
def localSum : GateFrames.Role h ≃
    (Triple (Fin h) ⊕ (Triple (Fin h) ⊕ (Edge (Fin h) ⊕ Option (Fin h)))) where
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

abbrev localSize (h : ℕ) := Fintype.card (GateFrames.Role h)

def localCoordinates (h : ℕ) : GateFrames.Role h ≃ Fin (localSize h) := Fintype.equivFin _

theorem local_role_card : localSize h =
    2 * Nat.choose h 3 + Nat.choose h 3 * TripleCounting.neighborDegree h + h + 1 := by
  rw [localSize, Fintype.card_congr (localSum (h := h))]
  simp only [Fintype.card_sum, triple_card, TripleCounting.edge_card, Fintype.card_option,
    Fintype.card_fin]
  ring

theorem sum_localRole {A : Type*} [AddCommMonoid A] (f : GateFrames.Role h → A) :
    ∑ role, f role = (∑ S, f (.x S)) + (∑ S, f (.y S)) +
      (∑ e, f (.side e)) + (∑ i, f (.center i)) := by
  rw [← (localSum (h := h)).symm.sum_comp]
  simp only [Fintype.sum_sum_type, localSum, Equiv.coe_fn_symm_mk]
  abel

def localValues (X : GateFrames.Role h → ℂ) : Fin (localSize h) → ℂ :=
  fun i => X ((localCoordinates h).symm i)

@[simp] theorem localValues_at (X : GateFrames.Role h → ℂ) (role : GateFrames.Role h) :
    localValues X (localCoordinates h role) = X role := by simp [localValues]

def dirtyValues
    (s : Projection.DirtyState (Triple (Fin h) → ℂ) (Edge (Fin h) → ℂ) (Option (Fin h) → ℂ)) :
    GateFrames.Role h → ℂ
  | .x S => s.x S
  | .y S => s.y S
  | .side e => s.auxiliaryA e
  | .center i => s.auxiliaryC i

def dirtyState (X : GateFrames.Role h → ℂ) :=
  Projection.DirtyState.mk (fun S => X (.x S)) (fun S => X (.y S))
    (fun e => X (.side e)) (fun i => X (.center i))

@[simp] theorem dirtyValues_dirtyState (X : GateFrames.Role h → ℂ) : dirtyValues (dirtyState X) = X := by
  funext role
  cases role <;> rfl

@[simp] theorem dirtyState_dirtyValues
    (s : Projection.DirtyState (Triple (Fin h) → ℂ) (Edge (Fin h) → ℂ) (Option (Fin h) → ℂ)) :
    dirtyState (dirtyValues s) = s := by cases s; rfl

def roleKind : GateFrames.Role h → Fin 4
  | .x _ => 0
  | .y _ => 1
  | .side _ => 2
  | .center _ => 3

def targetKind (row : Fin 8) : Fin 4 := ![1, 1, 2, 3, 1, 1, 3, 2] row

def sourceKind (row : Fin 8) : Fin 4 := ![2, 3, 0, 0, 3, 2, 0, 0] row

theorem row_kind_support (row : Fin 8) (dest source : GateFrames.Role h)
    (hM : rowCoefficient row dest source ≠ 0) :
    roleKind dest = targetKind row ∧ roleKind source = sourceKind row := by
  cases dest <;> cases source <;> fin_cases row <;> simp [rowCoefficient] at hM
  all_goals exact ⟨rfl, rfl⟩

theorem row_kinds_distinct (row : Fin 8) : targetKind row ≠ sourceKind row := by
  fin_cases row <;> decide

theorem row_roles_distinct (row : Fin 8) (dest source : GateFrames.Role h)
    (hM : rowCoefficient row dest source ≠ 0) : dest ≠ source := by
  intro he
  have hk := row_kind_support row dest source hM
  exact row_kinds_distinct row (hk.1.symm.trans ((congrArg roleKind he).trans hk.2))

def rowMatrix (row : Fin 8) : Matrix (GateFrames.Role h) (GateFrames.Role h) ℂ :=
  Matrix.of (rowCoefficient row)

abbrev RowEntry (row : Fin 8) := ScalarSupport.Support (rowMatrix (h := h) row)

def rowEntryWord (row : Fin 8) (e : RowEntry (h := h) row) :
    List (WordStep C (localSize h)) :=
  RoleWords.roleShearWord (localCoordinates h e.val.1) (localCoordinates h e.val.2)
    ((localCoordinates h).injective.ne (row_roles_distinct row e.val.1 e.val.2 e.property))
    (rowCoefficient row e.val.1 e.val.2) e.property

def rowEntryMatrix (row : Fin 8) (e : RowEntry (h := h) row) :
    Matrix (Fin (localSize h)) (Fin (localSize h)) ℂ :=
  Matrix.single (localCoordinates h e.val.1) (localCoordinates h e.val.2)
    (rowCoefficient row e.val.1 e.val.2)

theorem rowEntryWord_matrix (row : Fin 8) (e : RowEntry (h := h) row) :
    wordMatrix (rowEntryWord row e) = 1 + rowEntryMatrix row e := RoleWords.roleShearWord_matrix _ _ _ _ _

theorem rowEntryWord_calls (row : Fin 8) (e : RowEntry (h := h) row) :
    wordCalls (rowEntryWord row e) = 3 := RoleWords.roleShearWord_calls _ _ _ _ _

theorem rowEntryMatrix_mul_zero (row : Fin 8) (e f : RowEntry (h := h) row) :
    rowEntryMatrix row e * rowEntryMatrix row f = 0 := by
  apply Matrix.single_mul_single_of_ne
  intro he
  have hr := (localCoordinates h).injective he
  have hk1 := row_kind_support row e.val.1 e.val.2 e.property
  have hk2 := row_kind_support row f.val.1 f.val.2 f.property
  exact row_kinds_distinct row (hk2.1.symm.trans ((congrArg roleKind hr.symm).trans hk1.2))

def scalarRowList (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    List (WordStep C (localSize h)) := (L.map (rowEntryWord row)).flatten

theorem rowEntrySum_mul_zero (row : Fin 8) (L : List (RowEntry (h := h) row)) (e : RowEntry (h := h) row) :
    (L.map (rowEntryMatrix row)).sum * rowEntryMatrix row e = 0 := by
  induction L with
  | nil => simp
  | cons f L ih => simp only [List.map_cons, List.sum_cons, Matrix.add_mul,
      rowEntryMatrix_mul_zero, ih, add_zero]

theorem scalarRowList_matrix (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    wordMatrix (scalarRowList row L) = 1 + (L.map (rowEntryMatrix row)).sum := by
  induction L with
  | nil => simp [scalarRowList, wordMatrix]
  | cons e L ih =>
    change wordMatrix (rowEntryWord row e ++ scalarRowList row L) = _
    rw [TypedKernelWords.wordMatrix_append, ih, rowEntryWord_matrix,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, rowEntrySum_mul_zero, add_zero]
    simp only [List.map_cons, List.sum_cons]
    abel

theorem scalarRowList_calls (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    wordCalls (scalarRowList row L) = 3 * L.length := by
  induction L with
  | nil => simp [scalarRowList, wordCalls]
  | cons e L ih =>
    change wordCalls (rowEntryWord row e ++ scalarRowList row L) = _
    rw [TypedKernelWords.wordCalls_append, rowEntryWord_calls, ih, List.length_cons]
    omega

def scalarRowWord (row : Fin 8) : List (WordStep C (localSize h)) :=
  scalarRowList row Finset.univ.toList

theorem scalarRowWord_calls (row : Fin 8) :
    wordCalls (scalarRowWord (h := h) row) = 3 * Fintype.card (RowEntry (h := h) row) := by
  rw [scalarRowWord, scalarRowList_calls]
  simp

theorem scalarRowWord_matrix (row : Fin 8) :
    wordMatrix (scalarRowWord (h := h) row) =
      Matrix.reindex (localCoordinates h) (localCoordinates h)
        (1 + rowMatrix (h := h) row) := by
  rw [scalarRowWord, scalarRowList_matrix, Finset.sum_map_toList]
  have hsum : (∑ e : RowEntry (h := h) row, rowEntryMatrix row e) =
      Matrix.reindex (localCoordinates h) (localCoordinates h) (rowMatrix (h := h) row) := by
    ext i j
    obtain ⟨a, rfl⟩ := (localCoordinates h).surjective i
    obtain ⟨b, rfl⟩ := (localCoordinates h).surjective j
    simp only [Matrix.sum_apply, rowEntryMatrix, Matrix.single_apply,
      (localCoordinates h).injective.eq_iff, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, rowMatrix, Matrix.of_apply]
    by_cases hm : rowCoefficient row a b = 0
    · rw [hm]
      apply Finset.sum_eq_zero
      intro e he
      by_cases heq : e.val.1 = a ∧ e.val.2 = b
      · simp [heq.1, heq.2, hm]
      · simp [heq]
    · let e : RowEntry (h := h) row := ⟨(a, b), hm⟩
      have heq (f : RowEntry (h := h) row) : f.val.1 = a ∧ f.val.2 = b ↔ f = e := by
        constructor
        · intro hf; exact Subtype.ext (Prod.ext hf.1 hf.2)
        · rintro rfl; exact ⟨rfl, rfl⟩
      simp only [heq]
      simp [e]
  rw [hsum]
  change 1 + (Matrix.reindexAlgEquiv ℂ ℂ (localCoordinates h)) (rowMatrix row) =
    (Matrix.reindexAlgEquiv ℂ ℂ (localCoordinates h)) (1 + rowMatrix row)
  rw [map_add, map_one]

theorem scalarRowWord_apply (row : Fin 8) (X : GateFrames.Role h → ℂ) (role : GateFrames.Role h) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) (localCoordinates h role) =
      (1 + rowMatrix row).mulVec X role := by
  rw [scalarRowWord_matrix, reindex_mulVec]
  simp [localValues, Function.comp_def]

/-- The literal eight physical row updates, retaining arbitrary dirty values. -/
def rowAction (row : Fin 8) (X : GateFrames.Role h → ℂ) : GateFrames.Role h → ℂ
  | .y S => match row with
    | 0 => X (.y S) - J.mulVec (fun e => X (.side e)) S
    | 1 => X (.y S) - R.mulVec (fun i => X (.center i)) S
    | 4 => X (.y S) + R.mulVec (fun i => X (.center i)) S
    | 5 => X (.y S) + J.mulVec (fun e => X (.side e)) S
    | _ => X (.y S)
  | .side e => match row with
    | 2 => X (.side e) + V.mulVec (fun S => X (.x S)) e
    | 7 => X (.side e) - V.mulVec (fun S => X (.x S)) e
    | _ => X (.side e)
  | .center i => match row with
    | 3 => X (.center i) + G.mulVec (fun S => X (.x S)) i
    | 6 => X (.center i) - G.mulVec (fun S => X (.x S)) i
    | _ => X (.center i)
  | .x S => X (.x S)

theorem scalarRowWord_rowAction (row : Fin 8) (X : GateFrames.Role h → ℂ) (role : GateFrames.Role h) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) (localCoordinates h role) = rowAction row X role := by
  rw [scalarRowWord_apply, Matrix.add_mulVec, Matrix.one_mulVec]
  change X role + (∑ j, rowCoefficient row role j * X j) = _
  rw [sum_localRole]
  cases role <;> fin_cases row <;>
    simp [rowCoefficient, rowAction, Matrix.mulVec, dotProduct, sub_eq_add_neg,
      Finset.sum_neg_distrib]

theorem scalarRowWord_array (row : Fin 8) (X : GateFrames.Role h → ℂ) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) = localValues (rowAction row X) := by
  funext k
  obtain ⟨role, rfl⟩ := (localCoordinates h).surjective k
  rw [scalarRowWord_rowAction, localValues_at]

def localRowsWord : List (WordStep C (localSize h)) :=
  scalarRowWord 0 ++ scalarRowWord 1 ++ scalarRowWord 2 ++ scalarRowWord 3 ++
  scalarRowWord 4 ++ scalarRowWord 5 ++ scalarRowWord 6 ++ scalarRowWord 7

def localRowsAction (X : GateFrames.Role h → ℂ) :=
  rowAction 7 (rowAction 6 (rowAction 5 (rowAction 4
    (rowAction 3 (rowAction 2 (rowAction 1 (rowAction 0 X)))))))

theorem localRowsAction_eightRows (X : GateFrames.Role h → ℂ) :
    localRowsAction X = dirtyValues
      (Projection.eightRows 1 (Matrix.mulVecLin (V (α := Fin h))) (Matrix.mulVecLin G)
        (Matrix.mulVecLin J) (Matrix.mulVecLin R) (dirtyState X)) := by
  funext role
  cases role with
  | x S => rfl
  | side e => rfl
  | center i => rfl
  | y S =>
    simp [localRowsAction, rowAction, dirtyValues, dirtyState, Projection.eightRows]
    rfl

def bankShear (X : GateFrames.Role h → ℂ) : GateFrames.Role h → ℂ
  | .y S => X (.y S) + X (.x S)
  | role => X role

theorem localRowsAction_identity (X : GateFrames.Role h → ℂ) : localRowsAction X = bankShear X := by
  rw [localRowsAction_eightRows, invocation_dirty_identity]
  funext role
  cases role <;> simp [dirtyValues, dirtyState, bankShear]

theorem localRowsWord_array (X : GateFrames.Role h → ℂ) :
    (wordMatrix (localRowsWord (h := h))).mulVec (localValues X) = localValues (bankShear X) := by
  simp only [localRowsWord, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
    scalarRowWord_array]
  change localValues (localRowsAction X) = _
  rw [localRowsAction_identity]

theorem rowEntry_nonempty (hh : 7 ≤ h) (row : Fin 8) : Nonempty (RowEntry (h := h) row) := by
  have hv : 0 < Nat.choose h 3 := Nat.choose_pos (by omega)
  have hd : 0 < TripleCounting.neighborDegree h := by
    unfold TripleCounting.neighborDegree
    omega
  have ht : Nonempty (Triple (Fin h)) := Fintype.card_pos_iff.mp (by simpa [triple_card] using hv)
  have he : Nonempty (Edge (Fin h)) := Fintype.card_pos_iff.mp
    (by simpa [TripleCounting.edge_card] using Nat.mul_pos hv hd)
  let S := Classical.choice ht
  let edge := Classical.choice he
  fin_cases row
  · exact ⟨⟨(.y edge.val.1, .side edge), by simp [rowMatrix, rowCoefficient, ScalarSupport.J_nonzero]⟩⟩
  · exact ⟨⟨(.y S, .center none), by norm_num [rowMatrix, rowCoefficient, R]⟩⟩
  · exact ⟨⟨(.side edge, .x edge.val.2), by simp [rowMatrix, rowCoefficient, ScalarSupport.V_nonzero]⟩⟩

  · exact ⟨⟨(.center none, .x S), by simp [rowMatrix, rowCoefficient, G]⟩⟩
  · exact ⟨⟨(.y S, .center none), by norm_num [rowMatrix, rowCoefficient, R]⟩⟩
  · exact ⟨⟨(.y edge.val.1, .side edge), by simp [rowMatrix, rowCoefficient, ScalarSupport.J_nonzero]⟩⟩
  · exact ⟨⟨(.center none, .x S), by simp [rowMatrix, rowCoefficient, G]⟩⟩
  · exact ⟨⟨(.side edge, .x edge.val.2), by simp [rowMatrix, rowCoefficient, ScalarSupport.V_nonzero]⟩⟩

def rowZeroSupport : RowEntry (h := h) 0 ≃ ScalarSupport.Support (J (α := Fin h)) where
  toFun p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    exact ⟨(_, _), hp⟩
  invFun p := ⟨(.y p.val.1, .side p.val.2), by simpa [rowMatrix, rowCoefficient] using p.property⟩
  left_inv p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    rfl
  right_inv p := by rcases p with ⟨⟨S, edge⟩, hp⟩; rfl

def rowOneSupport : RowEntry (h := h) 1 ≃ ScalarSupport.Support (R (α := Fin h)) where
  toFun p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    exact ⟨(_, _), hp⟩
  invFun p := ⟨(.y p.val.1, .center p.val.2), by simpa [rowMatrix, rowCoefficient] using p.property⟩
  left_inv p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    rfl
  right_inv p := by rcases p with ⟨⟨S, center⟩, hp⟩; rfl

def rowTwoSupport : RowEntry (h := h) 2 ≃ ScalarSupport.Support (V (α := Fin h)) where
  toFun p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    exact ⟨(_, _), hp⟩
  invFun p := ⟨(.side p.val.1, .x p.val.2), by simpa [rowMatrix, rowCoefficient] using p.property⟩
  left_inv p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    rfl
  right_inv p := by rcases p with ⟨⟨edge, S⟩, hp⟩; rfl

def rowThreeSupport : RowEntry (h := h) 3 ≃ ScalarSupport.Support (G (α := Fin h)) where
  toFun p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    exact ⟨(_, _), hp⟩
  invFun p := ⟨(.center p.val.1, .x p.val.2), by simpa [rowMatrix, rowCoefficient] using p.property⟩
  left_inv p := by
    rcases p with ⟨⟨dest, source⟩, hp⟩
    cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient] at hp
    rfl
  right_inv p := by rcases p with ⟨⟨center, S⟩, hp⟩; rfl

def negSupportEquiv {ρ τ : Type*} (M : Matrix ρ τ ℂ) :
    ScalarSupport.Support (-M) ≃ ScalarSupport.Support M :=
  Equiv.subtypeEquivRight (by intro p; simp)

theorem rowMatrix_four : rowMatrix (h := h) 4 = -rowMatrix 1 := by
  ext dest source
  cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient]
theorem rowMatrix_five : rowMatrix (h := h) 5 = -rowMatrix 0 := by
  ext dest source
  cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient]
theorem rowMatrix_six : rowMatrix (h := h) 6 = -rowMatrix 3 := by
  ext dest source
  cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient]
theorem rowMatrix_seven : rowMatrix (h := h) 7 = -rowMatrix 2 := by
  ext dest source
  cases dest <;> cases source <;> simp [rowMatrix, rowCoefficient]

theorem rowEntry_card (row : Fin 8) : Fintype.card (RowEntry (h := h) row) =
    ![Nat.choose h 3 * TripleCounting.neighborDegree h, 4 * Nat.choose h 3,
      Nat.choose h 3 * TripleCounting.neighborDegree h, 4 * Nat.choose h 3,
      4 * Nat.choose h 3, Nat.choose h 3 * TripleCounting.neighborDegree h,
      4 * Nat.choose h 3, Nat.choose h 3 * TripleCounting.neighborDegree h] row := by
  have h0 : Fintype.card (RowEntry (h := h) 0) = Nat.choose h 3 * TripleCounting.neighborDegree h := by
    rw [Fintype.card_congr (rowZeroSupport (h := h)), ScalarSupport.J_support_card, Fintype.card_fin]
  have h1 : Fintype.card (RowEntry (h := h) 1) = 4 * Nat.choose h 3 := by
    rw [Fintype.card_congr (rowOneSupport (h := h)), ScalarSupport.R_support_card, Fintype.card_fin]
  have h2 : Fintype.card (RowEntry (h := h) 2) = Nat.choose h 3 * TripleCounting.neighborDegree h := by
    rw [Fintype.card_congr (rowTwoSupport (h := h)), ScalarSupport.V_support_card, Fintype.card_fin]
  have h3 : Fintype.card (RowEntry (h := h) 3) = 4 * Nat.choose h 3 := by
    rw [Fintype.card_congr (rowThreeSupport (h := h)), ScalarSupport.G_support_card, Fintype.card_fin]
  fin_cases row
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · change Fintype.card (ScalarSupport.Support (rowMatrix (h := h) 4)) = _
    rw [rowMatrix_four, Fintype.card_congr (negSupportEquiv _)]
    exact h1
  · change Fintype.card (ScalarSupport.Support (rowMatrix (h := h) 5)) = _
    rw [rowMatrix_five, Fintype.card_congr (negSupportEquiv _)]
    exact h0
  · change Fintype.card (ScalarSupport.Support (rowMatrix (h := h) 6)) = _
    rw [rowMatrix_six, Fintype.card_congr (negSupportEquiv _)]
    exact h3
  · change Fintype.card (ScalarSupport.Support (rowMatrix (h := h) 7)) = _
    rw [rowMatrix_seven, Fintype.card_congr (negSupportEquiv _)]
    exact h2

theorem local_scalar_count : (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) =
    4 * Nat.choose h 3 * TripleCounting.neighborDegree h + 16 * Nat.choose h 3 := by
  simp only [rowEntry_card]
  simp [Fin.sum_univ_succ]
  ring

section FramedLocal
variable {ι η : Type*} [Fintype ι] [Fintype η] {n : ℕ}

def localLabels (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (level : Fin 9) :
    Labels (localSize h) n := fun i => d.labels e level ((localCoordinates h).symm i)

def localFinalLabels (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    Labels (localSize h) n := fun i => d.finalLabels e ((localCoordinates h).symm i)

def localEdges (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    ∀ i, NestedEdge (localLabels d e row.castSucc i) (localLabels d e row.succ i) :=
  fun i => d.edges e row ((localCoordinates h).symm i)

def localSinkEdges (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    ∀ i, NestedEdge (localLabels d e 8 i) (localFinalLabels d e i) :=
  fun i => d.sinkEdges e ((localCoordinates h).symm i)

def firstEntryEvent (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (f : RowEntry (h := h) row) :
    Event (localLabels d e row.castSucc) (localLabels d e row.succ) where
  edges := localEdges d e row
  dest := localCoordinates h f.val.1
  source := localCoordinates h f.val.2
  distinct := (localCoordinates h).injective.ne (row_roles_distinct row _ _ f.property)
  coefficient := rowCoefficient row f.val.1 f.val.2
  nonzero := f.property
  compatible := by
    simpa only [localLabels, Equiv.symm_apply_apply] using d.forward_compatible e row _ _ f.property

def constantEntryEvent (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (f : RowEntry (h := h) row) :
    Event (localLabels d e row.succ) (localLabels d e row.succ) where
  edges i := NestedEdge.refl (localLabels d e row.succ i)
  dest := localCoordinates h f.val.1
  source := localCoordinates h f.val.2
  distinct := (localCoordinates h).injective.ne (row_roles_distinct row _ _ f.property)
  coefficient := rowCoefficient row f.val.1 f.val.2
  nonzero := f.property
  compatible := by
    simpa only [localLabels, Equiv.symm_apply_apply] using d.forward_compatible e row _ _ f.property

def constantRowSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : List (RowEntry (h := h) row) →
      Schedule (localLabels d e row.succ) (localLabels d e row.succ)
  | [] => .nil _
  | f :: fs => .cons (constantEntryEvent d e row f) (constantRowSchedule d e row fs)

theorem constantRowSchedule_scalarMatrix (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).scalarMatrix = wordMatrix (scalarRowList row L) := by
  induction L with
  | nil => rfl
  | cons f fs ih =>
    change (constantRowSchedule d e row fs).scalarMatrix *
      (constantEntryEvent d e row f).scalarMatrix = wordMatrix (rowEntryWord row f ++ scalarRowList row fs)
    rw [ih, TypedKernelWords.wordMatrix_append, rowEntryWord_matrix]
    rfl

theorem constantRowSchedule_residualDimension (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).residualDimension = 0 := by
  induction L with
  | nil => rfl
  | cons f fs ih => simp [constantRowSchedule, Schedule.residualDimension,
      Event.residualDimension, constantEntryEvent, ih]

theorem constantRowSchedule_scalarCount (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).scalarCount = L.length := by
  induction L with
  | nil => rfl
  | cons f fs ih => simp [constantRowSchedule, Schedule.scalarCount, ih, Nat.add_comm]

theorem rowSupportList_ne_nil (hh : 7 ≤ h) (row : Fin 8) :
    (Finset.univ : Finset (RowEntry (h := h) row)).toList ≠ [] := by
  rw [List.ne_nil_iff_length_pos]
  simpa using Fintype.card_pos_iff.mpr (rowEntry_nonempty hh row)

def rowSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    Schedule (localLabels d e row.castSucc) (localLabels d e row.succ) :=
  match he : (Finset.univ : Finset (RowEntry (h := h) row)).toList with
  | [] => False.elim (rowSupportList_ne_nil d.large row he)
  | f :: fs => .cons (firstEntryEvent d e row f) (constantRowSchedule d e row fs)

theorem rowSchedule_scalarMatrix (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).scalarMatrix = wordMatrix (scalarRowWord row) := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    change (constantRowSchedule d e row fs).scalarMatrix * (firstEntryEvent d e row f).scalarMatrix = _
    rw [constantRowSchedule_scalarMatrix, scalarRowWord, he]
    change wordMatrix (scalarRowList row fs) * (firstEntryEvent d e row f).scalarMatrix =
      wordMatrix (rowEntryWord row f ++ scalarRowList row fs)
    rw [TypedKernelWords.wordMatrix_append, rowEntryWord_matrix]
    rfl

theorem rowSchedule_residualDimension (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).residualDimension = ∑ i, (localEdges d e row i).dimension := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    rw [Schedule.residualDimension, constantRowSchedule_residualDimension, Nat.add_zero]
    rfl

theorem rowSchedule_scalarCount (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).scalarCount = Fintype.card (RowEntry (h := h) row) := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    rw [Schedule.scalarCount, constantRowSchedule_scalarCount]
    have hl := congrArg List.length he
    simp only [Finset.length_toList, Finset.card_univ, List.length_cons] at hl
    omega

/-- All eight actual physical rows, joined through their shared coordinate labels. -/
def localSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    Schedule (localLabels d e 0) (localLabels d e 8) :=
  (rowSchedule d e 0).append ((rowSchedule d e 1).append
    ((rowSchedule d e 2).append ((rowSchedule d e 3).append
      ((rowSchedule d e 4).append ((rowSchedule d e 5).append
        ((rowSchedule d e 6).append (rowSchedule d e 7)))))))

theorem localSchedule_scalarMatrix (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).scalarMatrix = wordMatrix (localRowsWord (h := h)) := by
  simp only [localSchedule, Schedule.append_scalarMatrix, rowSchedule_scalarMatrix,
    localRowsWord, TypedKernelWords.wordMatrix_append, Matrix.mul_assoc]

theorem localSchedule_scalarCount (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).scalarCount = ∑ row : Fin 8, Fintype.card (RowEntry (h := h) row) := by
  simp [localSchedule, Schedule.append_scalarCount, rowSchedule_scalarCount,
    Fin.sum_univ_succ]

theorem localSchedule_residualDimension (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).residualDimension = ∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension := by
  simp [localSchedule, Schedule.append_residualDimension, rowSchedule_residualDimension,
    Fin.sum_univ_succ]

def localBankShear (X : Values (localSize h) n) : Values (localSize h) n :=
  fun i => match (localCoordinates h).symm i with
    | .y S => X i + X (localCoordinates h (.x S))
    | _ => X i

theorem localRows_scalarAction (X : Values (localSize h) n) :
    scalarAction (wordMatrix (localRowsWord (h := h))) X = localBankShear X := by
  funext i x
  obtain ⟨role, rfl⟩ := (localCoordinates h).surjective i
  have h := congrFun (localRowsWord_array (fun role => X (localCoordinates h role) x)) (localCoordinates h role)
  cases role <;> simpa [scalarAction, FrameCommutation.pointwiseMatrix, Matrix.mulVec,
    dotProduct, localValues, localBankShear, bankShear] using h

/-- The actual typed local word includes all auxiliary sink edges and no dummy scalars. -/
def localWord (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    List (WordStep C (localSize h * 2 ^ n)) :=
  (localSchedule d e).finishWord (localSinkEdges d e)

theorem localWord_array (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (X : Values (localSize h) n) :
    (wordMatrix (localWord d e)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues
        (frames (localFinalLabels d e) (localBankShear (inverseFrames (localLabels d e 0) X))) := by
  rw [localWord, Schedule.finishWord_array, localSchedule_scalarMatrix, localRows_scalarAction]

theorem localWord_calls (hn : 1 ≤ n) (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    wordCalls (localWord d e) =
      ((∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension) +
        ∑ i, (localSinkEdges d e i).dimension) * 2 ^ (n - 1) +
      3 * (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) * 2 ^ n := by
  rw [localWord, Schedule.finishWord_calls hn, localSchedule_residualDimension, localSchedule_scalarCount]

theorem compile_local_invocation (hn : 1 ≤ n) (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    ∃ W : List (WordStep C (localSize h * 2 ^ n)),
      (∀ X : Values (localSize h) n, (wordMatrix W).mulVec (RoleFrameWords.binaryValues X) =
        RoleFrameWords.binaryValues
          (frames (localFinalLabels d e) (localBankShear (inverseFrames (localLabels d e 0) X)))) ∧
      wordCalls W =
        ((∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension) +
          ∑ i, (localSinkEdges d e i).dimension) * 2 ^ (n - 1) +
        3 * (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) * 2 ^ n :=
  ⟨localWord d e, localWord_array d e, localWord_calls hn d e⟩

end FramedLocal

namespace ReverseLocal
set_option maxHeartbeats 1000000

def targetKind (row : Fin 8) : Fin 4 := TripleSchedule.sourceKind row

def sourceKind (row : Fin 8) : Fin 4 := TripleSchedule.targetKind row

theorem row_kind_support (row : Fin 8) (dest source : GateFrames.Role h)
    (hM : reverseRowCoefficient row dest source ≠ 0) :
    roleKind dest = targetKind row ∧ roleKind source = sourceKind row := by
  cases dest <;> cases source <;> fin_cases row <;> simp [reverseRowCoefficient] at hM
  all_goals exact ⟨rfl, rfl⟩

theorem row_kinds_distinct (row : Fin 8) : targetKind row ≠ sourceKind row := by
  fin_cases row <;> decide

theorem row_roles_distinct (row : Fin 8) (dest source : GateFrames.Role h)
    (hM : reverseRowCoefficient row dest source ≠ 0) : dest ≠ source := by
  intro he
  have hk := row_kind_support row dest source hM
  exact row_kinds_distinct row (hk.1.symm.trans ((congrArg roleKind he).trans hk.2))
def rowMatrix (row : Fin 8) : Matrix (GateFrames.Role h) (GateFrames.Role h) ℂ :=
  Matrix.of (reverseRowCoefficient row)

abbrev RowEntry (row : Fin 8) := ScalarSupport.Support (rowMatrix (h := h) row)

def rowEntryWord (row : Fin 8) (e : RowEntry (h := h) row) :
    List (WordStep C (localSize h)) :=
  RoleWords.roleShearWord (localCoordinates h e.val.1) (localCoordinates h e.val.2)
    ((localCoordinates h).injective.ne (row_roles_distinct row e.val.1 e.val.2 e.property))
    (reverseRowCoefficient row e.val.1 e.val.2) e.property

def rowEntryMatrix (row : Fin 8) (e : RowEntry (h := h) row) :
    Matrix (Fin (localSize h)) (Fin (localSize h)) ℂ :=
  Matrix.single (localCoordinates h e.val.1) (localCoordinates h e.val.2)
    (reverseRowCoefficient row e.val.1 e.val.2)

theorem rowEntryWord_matrix (row : Fin 8) (e : RowEntry (h := h) row) :
    wordMatrix (rowEntryWord row e) = 1 + rowEntryMatrix row e := RoleWords.roleShearWord_matrix _ _ _ _ _

theorem rowEntryWord_calls (row : Fin 8) (e : RowEntry (h := h) row) :
    wordCalls (rowEntryWord row e) = 3 := RoleWords.roleShearWord_calls _ _ _ _ _

theorem rowEntryMatrix_mul_zero (row : Fin 8) (e f : RowEntry (h := h) row) :
    rowEntryMatrix row e * rowEntryMatrix row f = 0 := by
  apply Matrix.single_mul_single_of_ne
  intro he
  have hr := (localCoordinates h).injective he
  have hk1 := row_kind_support row e.val.1 e.val.2 e.property
  have hk2 := row_kind_support row f.val.1 f.val.2 f.property
  exact row_kinds_distinct row (hk2.1.symm.trans ((congrArg roleKind hr.symm).trans hk1.2))

def scalarRowList (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    List (WordStep C (localSize h)) := (L.map (rowEntryWord row)).flatten

theorem rowEntrySum_mul_zero (row : Fin 8) (L : List (RowEntry (h := h) row)) (e : RowEntry (h := h) row) :
    (L.map (rowEntryMatrix row)).sum * rowEntryMatrix row e = 0 := by
  induction L with
  | nil => simp
  | cons f L ih => simp only [List.map_cons, List.sum_cons, Matrix.add_mul,
      rowEntryMatrix_mul_zero, ih, add_zero]

theorem scalarRowList_matrix (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    wordMatrix (scalarRowList row L) = 1 + (L.map (rowEntryMatrix row)).sum := by
  induction L with
  | nil => simp [scalarRowList, wordMatrix]
  | cons e L ih =>
    change wordMatrix (rowEntryWord row e ++ scalarRowList row L) = _
    rw [TypedKernelWords.wordMatrix_append, ih, rowEntryWord_matrix,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, rowEntrySum_mul_zero, add_zero]
    simp only [List.map_cons, List.sum_cons]
    abel

theorem scalarRowList_calls (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    wordCalls (scalarRowList row L) = 3 * L.length := by
  induction L with
  | nil => simp [scalarRowList, wordCalls]
  | cons e L ih =>
    change wordCalls (rowEntryWord row e ++ scalarRowList row L) = _
    rw [TypedKernelWords.wordCalls_append, rowEntryWord_calls, ih, List.length_cons]
    omega

def scalarRowWord (row : Fin 8) : List (WordStep C (localSize h)) :=
  scalarRowList row Finset.univ.toList

theorem scalarRowWord_calls (row : Fin 8) :
    wordCalls (scalarRowWord (h := h) row) = 3 * Fintype.card (RowEntry (h := h) row) := by
  rw [scalarRowWord, scalarRowList_calls]
  simp

theorem scalarRowWord_matrix (row : Fin 8) :
    wordMatrix (scalarRowWord (h := h) row) =
      Matrix.reindex (localCoordinates h) (localCoordinates h)
        (1 + rowMatrix (h := h) row) := by
  rw [scalarRowWord, scalarRowList_matrix, Finset.sum_map_toList]
  have hsum : (∑ e : RowEntry (h := h) row, rowEntryMatrix row e) =
      Matrix.reindex (localCoordinates h) (localCoordinates h) (rowMatrix (h := h) row) := by
    ext i j
    obtain ⟨a, rfl⟩ := (localCoordinates h).surjective i
    obtain ⟨b, rfl⟩ := (localCoordinates h).surjective j
    simp only [Matrix.sum_apply, rowEntryMatrix, Matrix.single_apply,
      (localCoordinates h).injective.eq_iff, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, rowMatrix, Matrix.of_apply]
    by_cases hm : reverseRowCoefficient row a b = 0
    · rw [hm]
      apply Finset.sum_eq_zero
      intro e he
      by_cases heq : e.val.1 = a ∧ e.val.2 = b
      · simp [heq.1, heq.2, hm]
      · simp [heq]
    · let e : RowEntry (h := h) row := ⟨(a, b), hm⟩
      have heq (f : RowEntry (h := h) row) : f.val.1 = a ∧ f.val.2 = b ↔ f = e := by
        constructor
        · intro hf; exact Subtype.ext (Prod.ext hf.1 hf.2)
        · rintro rfl; exact ⟨rfl, rfl⟩
      simp only [heq]
      simp [e]
  rw [hsum]
  change 1 + (Matrix.reindexAlgEquiv ℂ ℂ (localCoordinates h)) (rowMatrix row) =
    (Matrix.reindexAlgEquiv ℂ ℂ (localCoordinates h)) (1 + rowMatrix row)
  rw [map_add, map_one]

theorem scalarRowWord_apply (row : Fin 8) (X : GateFrames.Role h → ℂ) (role : GateFrames.Role h) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) (localCoordinates h role) =
      (1 + rowMatrix row).mulVec X role := by
  rw [scalarRowWord_matrix, reindex_mulVec]
  simp [localValues, Function.comp_def]


def reverseV : Matrix (Edge (Fin h)) (Triple (Fin h)) ℂ :=
  Matrix.of (fun e T => V (TripleNetwork.reverseEdge e) T)

def reverseJ : Matrix (Triple (Fin h)) (Edge (Fin h)) ℂ :=
  Matrix.of (fun T e => J T (TripleNetwork.reverseEdge e))

def edgeReversal : Equiv.Perm (Edge (Fin h)) where
  toFun := TripleNetwork.reverseEdge
  invFun := TripleNetwork.reverseEdge
  left_inv := TripleNetwork.reverseEdge_involutive
  right_inv := TripleNetwork.reverseEdge_involutive

theorem reverse_incidence_identity : composeMatrix (R (α := Fin h)) G +
    composeMatrix (reverseJ (h := h)) reverseV = 1 := by
  have hjv : composeMatrix (reverseJ (h := h)) reverseV = composeMatrix J V := by
    ext S T
    unfold composeMatrix
    simp only [Matrix.of_apply, reverseJ, reverseV]
    exact Equiv.sum_comp (edgeReversal (h := h)) (fun e => J S e * V e T)
  rw [hjv]
  exact incidence_identity

theorem reverse_incidence_apply (X : Triple (Fin h) → ℂ) :
    R.mulVec (G.mulVec X) + (reverseJ (h := h)).mulVec (reverseV.mulVec X) = X := by
  rw [← composeMatrix_mulVec, ← composeMatrix_mulVec, ← Matrix.add_mulVec,
    reverse_incidence_identity, Matrix.one_mulVec]

/-- Literal reversed scalar chronology, on the same physical gate-label table. -/
def rowAction (row : Fin 8) (X : GateFrames.Role h → ℂ) : GateFrames.Role h → ℂ
  | .x T => match row with
    | 2 => X (.x T) - reverseJ.mulVec (fun e => X (.side e)) T
    | 3 => X (.x T) - R.mulVec (fun i => X (.center i)) T
    | 6 => X (.x T) + R.mulVec (fun i => X (.center i)) T
    | 7 => X (.x T) + reverseJ.mulVec (fun e => X (.side e)) T
    | _ => X (.x T)
  | .side e => match row with
    | 0 => X (.side e) + reverseV.mulVec (fun S => X (.y S)) e
    | 5 => X (.side e) - reverseV.mulVec (fun S => X (.y S)) e
    | _ => X (.side e)
  | .center i => match row with
    | 1 => X (.center i) + G.mulVec (fun S => X (.y S)) i
    | 4 => X (.center i) - G.mulVec (fun S => X (.y S)) i
    | _ => X (.center i)
  | .y S => X (.y S)

theorem scalarRowWord_rowAction (row : Fin 8) (X : GateFrames.Role h → ℂ) (role : GateFrames.Role h) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) (localCoordinates h role) = rowAction row X role := by
  rw [scalarRowWord_apply, Matrix.add_mulVec, Matrix.one_mulVec]
  change X role + (∑ j, reverseRowCoefficient row role j * X j) = _
  rw [sum_localRole]
  cases role <;> fin_cases row <;>
    simp [reverseRowCoefficient, rowAction, reverseJ, reverseV, Matrix.mulVec, dotProduct,
      sub_eq_add_neg, Finset.sum_neg_distrib]

theorem scalarRowWord_array (row : Fin 8) (X : GateFrames.Role h → ℂ) :
    (wordMatrix (scalarRowWord row)).mulVec (localValues X) = localValues (rowAction row X) := by
  funext k
  obtain ⟨role, rfl⟩ := (localCoordinates h).surjective k
  rw [scalarRowWord_rowAction, localValues_at]

def localRowsWord : List (WordStep C (localSize h)) :=
  scalarRowWord 0 ++ scalarRowWord 1 ++ scalarRowWord 2 ++ scalarRowWord 3 ++
  scalarRowWord 4 ++ scalarRowWord 5 ++ scalarRowWord 6 ++ scalarRowWord 7

def localRowsAction (X : GateFrames.Role h → ℂ) :=
  rowAction 7 (rowAction 6 (rowAction 5 (rowAction 4
    (rowAction 3 (rowAction 2 (rowAction 1 (rowAction 0 X)))))))

def bankShear (X : GateFrames.Role h → ℂ) : GateFrames.Role h → ℂ
  | .x S => X (.x S) - X (.y S)
  | role => X role

theorem localRowsAction_identity (X : GateFrames.Role h → ℂ) : localRowsAction X = bankShear X := by
  have hi := reverse_incidence_apply (fun S => X (.y S))
  funext role
  cases role with
  | y S => rfl
  | side e => simp [localRowsAction, rowAction, bankShear]
  | center i => simp [localRowsAction, rowAction, bankShear]
  | x T =>
    simp only [localRowsAction, rowAction, bankShear, add_sub_cancel_right]
    change X (.x T) - reverseJ.mulVec ((fun e => X (.side e)) + reverseV.mulVec (fun S => X (.y S))) T -
      R.mulVec ((fun i => X (.center i)) + G.mulVec (fun S => X (.y S))) T +
      R.mulVec (fun i => X (.center i)) T + reverseJ.mulVec (fun e => X (.side e)) T = _
    simp only [Matrix.mulVec_add, Pi.add_apply]
    have ht := congrFun hi T
    simp only [Pi.add_apply] at ht
    change _ = X (.x T) - X (.y T)
    linear_combination -ht

theorem localRowsWord_array (X : GateFrames.Role h → ℂ) :
    (wordMatrix (localRowsWord (h := h))).mulVec (localValues X) = localValues (bankShear X) := by
  simp only [localRowsWord, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
    scalarRowWord_array]
  change localValues (localRowsAction X) = _
  rw [localRowsAction_identity]

theorem rowEntry_nonempty (hh : 7 ≤ h) (row : Fin 8) : Nonempty (RowEntry (h := h) row) := by
  have hv : 0 < Nat.choose h 3 := Nat.choose_pos (by omega)
  have hd : 0 < TripleCounting.neighborDegree h := by
    unfold TripleCounting.neighborDegree
    omega
  have ht : Nonempty (Triple (Fin h)) := Fintype.card_pos_iff.mp (by simpa [triple_card] using hv)
  have he : Nonempty (Edge (Fin h)) := Fintype.card_pos_iff.mp
    (by simpa [TripleCounting.edge_card] using Nat.mul_pos hv hd)
  let S := Classical.choice ht
  let edge := Classical.choice he
  fin_cases row
  · exact ⟨⟨(.side edge, .y edge.val.1), by simp [rowMatrix, reverseRowCoefficient,
      ScalarSupport.V_nonzero, TripleNetwork.reverseEdge]⟩⟩
  · exact ⟨⟨(.center none, .y S), by simp [rowMatrix, reverseRowCoefficient, G]⟩⟩
  · exact ⟨⟨(.x edge.val.2, .side edge), by simp [rowMatrix, reverseRowCoefficient,
      ScalarSupport.J_nonzero, TripleNetwork.reverseEdge]⟩⟩
  · exact ⟨⟨(.x S, .center none), by norm_num [rowMatrix, reverseRowCoefficient, R]⟩⟩
  · exact ⟨⟨(.center none, .y S), by simp [rowMatrix, reverseRowCoefficient, G]⟩⟩
  · exact ⟨⟨(.side edge, .y edge.val.1), by simp [rowMatrix, reverseRowCoefficient,
      ScalarSupport.V_nonzero, TripleNetwork.reverseEdge]⟩⟩
  · exact ⟨⟨(.x S, .center none), by norm_num [rowMatrix, reverseRowCoefficient, R]⟩⟩
  · exact ⟨⟨(.x edge.val.2, .side edge), by simp [rowMatrix, reverseRowCoefficient,
      ScalarSupport.J_nonzero, TripleNetwork.reverseEdge]⟩⟩
section FramedLocal
variable {ι η : Type*} [Fintype ι] [Fintype η] {n : ℕ}

def localLabels (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (level : Fin 9) :
    Labels (localSize h) n := fun i => d.labels e level ((localCoordinates h).symm i)

def localFinalLabels (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    Labels (localSize h) n := fun i => d.finalLabels e ((localCoordinates h).symm i)

def localEdges (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    ∀ i, NestedEdge (localLabels d e row.castSucc i) (localLabels d e row.succ i) :=
  fun i => d.edges e row ((localCoordinates h).symm i)

def localSinkEdges (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    ∀ i, NestedEdge (localLabels d e 8 i) (localFinalLabels d e i) :=
  fun i => d.sinkEdges e ((localCoordinates h).symm i)

def firstEntryEvent (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (f : RowEntry (h := h) row) :
    Event (localLabels d e row.castSucc) (localLabels d e row.succ) where
  edges := localEdges d e row
  dest := localCoordinates h f.val.1
  source := localCoordinates h f.val.2
  distinct := (localCoordinates h).injective.ne (row_roles_distinct row _ _ f.property)
  coefficient := reverseRowCoefficient row f.val.1 f.val.2
  nonzero := f.property
  compatible := by
    simpa only [localLabels, Equiv.symm_apply_apply] using d.reverse_compatible e row _ _ f.property

def constantEntryEvent (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (f : RowEntry (h := h) row) :
    Event (localLabels d e row.succ) (localLabels d e row.succ) where
  edges i := NestedEdge.refl (localLabels d e row.succ i)
  dest := localCoordinates h f.val.1
  source := localCoordinates h f.val.2
  distinct := (localCoordinates h).injective.ne (row_roles_distinct row _ _ f.property)
  coefficient := reverseRowCoefficient row f.val.1 f.val.2
  nonzero := f.property
  compatible := by
    simpa only [localLabels, Equiv.symm_apply_apply] using d.reverse_compatible e row _ _ f.property

def constantRowSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : List (RowEntry (h := h) row) →
      Schedule (localLabels d e row.succ) (localLabels d e row.succ)
  | [] => .nil _
  | f :: fs => .cons (constantEntryEvent d e row f) (constantRowSchedule d e row fs)

theorem constantRowSchedule_scalarMatrix (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).scalarMatrix = wordMatrix (scalarRowList row L) := by
  induction L with
  | nil => rfl
  | cons f fs ih =>
    change (constantRowSchedule d e row fs).scalarMatrix *
      (constantEntryEvent d e row f).scalarMatrix = wordMatrix (rowEntryWord row f ++ scalarRowList row fs)
    rw [ih, TypedKernelWords.wordMatrix_append, rowEntryWord_matrix]
    rfl

theorem constantRowSchedule_residualDimension (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).residualDimension = 0 := by
  induction L with
  | nil => rfl
  | cons f fs ih => simp [constantRowSchedule, Schedule.residualDimension,
      Event.residualDimension, constantEntryEvent, ih]

theorem constantRowSchedule_scalarCount (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (L : List (RowEntry (h := h) row)) :
    (constantRowSchedule d e row L).scalarCount = L.length := by
  induction L with
  | nil => rfl
  | cons f fs ih => simp [constantRowSchedule, Schedule.scalarCount, ih, Nat.add_comm]

theorem rowSupportList_ne_nil (hh : 7 ≤ h) (row : Fin 8) :
    (Finset.univ : Finset (RowEntry (h := h) row)).toList ≠ [] := by
  rw [List.ne_nil_iff_length_pos]
  simpa using Fintype.card_pos_iff.mpr (rowEntry_nonempty hh row)

def rowSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    Schedule (localLabels d e row.castSucc) (localLabels d e row.succ) :=
  match he : (Finset.univ : Finset (RowEntry (h := h) row)).toList with
  | [] => False.elim (rowSupportList_ne_nil d.large row he)
  | f :: fs => .cons (firstEntryEvent d e row f) (constantRowSchedule d e row fs)

theorem rowSchedule_scalarMatrix (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).scalarMatrix = wordMatrix (scalarRowWord row) := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    change (constantRowSchedule d e row fs).scalarMatrix * (firstEntryEvent d e row f).scalarMatrix = _
    rw [constantRowSchedule_scalarMatrix, scalarRowWord, he]
    change wordMatrix (scalarRowList row fs) * (firstEntryEvent d e row f).scalarMatrix =
      wordMatrix (rowEntryWord row f ++ scalarRowList row fs)
    rw [TypedKernelWords.wordMatrix_append, rowEntryWord_matrix]
    rfl

theorem rowSchedule_residualDimension (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).residualDimension = ∑ i, (localEdges d e row i).dimension := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    rw [Schedule.residualDimension, constantRowSchedule_residualDimension, Nat.add_zero]
    rfl

theorem rowSchedule_scalarCount (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) : (rowSchedule d e row).scalarCount = Fintype.card (RowEntry (h := h) row) := by
  unfold rowSchedule
  split
  · rename_i he
    exact False.elim (rowSupportList_ne_nil d.large row he)
  · rename_i f fs he
    rw [Schedule.scalarCount, constantRowSchedule_scalarCount]
    have hl := congrArg List.length he
    simp only [Finset.length_toList, Finset.card_univ, List.length_cons] at hl
    omega

/-- All eight actual physical rows, joined through their shared coordinate labels. -/
def localSchedule (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    Schedule (localLabels d e 0) (localLabels d e 8) :=
  (rowSchedule d e 0).append ((rowSchedule d e 1).append
    ((rowSchedule d e 2).append ((rowSchedule d e 3).append
      ((rowSchedule d e 4).append ((rowSchedule d e 5).append
        ((rowSchedule d e 6).append (rowSchedule d e 7)))))))

theorem localSchedule_scalarMatrix (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).scalarMatrix = wordMatrix (localRowsWord (h := h)) := by
  simp only [localSchedule, Schedule.append_scalarMatrix, rowSchedule_scalarMatrix,
    localRowsWord, TypedKernelWords.wordMatrix_append, Matrix.mul_assoc]

theorem localSchedule_scalarCount (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).scalarCount = ∑ row : Fin 8, Fintype.card (RowEntry (h := h) row) := by
  simp [localSchedule, Schedule.append_scalarCount, rowSchedule_scalarCount,
    Fin.sum_univ_succ]

theorem localSchedule_residualDimension (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (localSchedule d e).residualDimension = ∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension := by
  simp [localSchedule, Schedule.append_residualDimension, rowSchedule_residualDimension,
    Fin.sum_univ_succ]

def localBankShear (X : Values (localSize h) n) : Values (localSize h) n :=
  fun i => match (localCoordinates h).symm i with
    | .x S => X i - X (localCoordinates h (.y S))
    | _ => X i

theorem localRows_scalarAction (X : Values (localSize h) n) :
    scalarAction (wordMatrix (localRowsWord (h := h))) X = localBankShear X := by
  funext i x
  obtain ⟨role, rfl⟩ := (localCoordinates h).surjective i
  have h := congrFun (localRowsWord_array (fun role => X (localCoordinates h role) x)) (localCoordinates h role)
  cases role <;> simpa [scalarAction, FrameCommutation.pointwiseMatrix, Matrix.mulVec,
    dotProduct, localValues, localBankShear, bankShear] using h

/-- The actual typed local word includes all auxiliary sink edges and no dummy scalars. -/
def localWord (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    List (WordStep C (localSize h * 2 ^ n)) :=
  (localSchedule d e).finishWord (localSinkEdges d e)

theorem localWord_array (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (X : Values (localSize h) n) :
    (wordMatrix (localWord d e)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues
        (frames (localFinalLabels d e) (localBankShear (inverseFrames (localLabels d e 0) X))) := by
  rw [localWord, Schedule.finishWord_array, localSchedule_scalarMatrix, localRows_scalarAction]

theorem localWord_calls (hn : 1 ≤ n) (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    wordCalls (localWord d e) =
      ((∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension) +
        ∑ i, (localSinkEdges d e i).dimension) * 2 ^ (n - 1) +
      3 * (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) * 2 ^ n := by
  rw [localWord, Schedule.finishWord_calls hn, localSchedule_residualDimension, localSchedule_scalarCount]

theorem compile_local_invocation (hn : 1 ≤ n) (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    ∃ W : List (WordStep C (localSize h * 2 ^ n)),
      (∀ X : Values (localSize h) n, (wordMatrix W).mulVec (RoleFrameWords.binaryValues X) =
        RoleFrameWords.binaryValues
          (frames (localFinalLabels d e) (localBankShear (inverseFrames (localLabels d e 0) X)))) ∧
      wordCalls W =
        ((∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension) +
          ∑ i, (localSinkEdges d e i).dimension) * 2 ^ (n - 1) +
        3 * (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) * 2 ^ n :=
  ⟨localWord d e, localWord_array d e, localWord_calls hn d e⟩

end FramedLocal
/-- Reversal acts on the actual ordered edge and exchanges the physical bank names. -/
def reflectedRole : GateFrames.Role h → GateFrames.Role h
  | .x T => .y T
  | .y T => .x T
  | .side e => .side (TripleNetwork.reverseEdge e)
  | .center i => .center i

lemma reflectedRole_involutive : Function.Involutive (reflectedRole (h := h)) := by
  intro r
  cases r <;> simp [reflectedRole, TripleNetwork.reverseEdge_involutive]

def rowReflection : Equiv.Perm (Fin 8) where
  toFun row := ⟨7-row.val,by omega⟩
  invFun row := ⟨7-row.val,by omega⟩
  left_inv row := by apply Fin.ext; dsimp; omega
  right_inv row := by apply Fin.ext; dsimp; omega

lemma reversed_coefficient (row : Fin 8) (a b : GateFrames.Role h) :
    reverseRowCoefficient row a b = - rowCoefficient (rowReflection row) (reflectedRole a) (reflectedRole b) := by
  fin_cases row <;> cases a <;> cases b <;>
    simp [rowReflection, reverseRowCoefficient, rowCoefficient, reflectedRole]

def rowSupportReflection (row : Fin 8) : RowEntry (h := h) row ≃
    TripleSchedule.RowEntry (h := h) (rowReflection row) where
  toFun f := ⟨(reflectedRole f.val.1, reflectedRole f.val.2), by
    have hc := f.property
    change reverseRowCoefficient row f.val.1 f.val.2 ≠ 0 at hc
    rw [reversed_coefficient] at hc
    change rowCoefficient (rowReflection row) (reflectedRole f.val.1) (reflectedRole f.val.2) ≠ 0
    simpa only [neg_ne_zero] using hc⟩
  invFun f := ⟨(reflectedRole f.val.1, reflectedRole f.val.2), by
    change reverseRowCoefficient row (reflectedRole f.val.1) (reflectedRole f.val.2) ≠ 0
    rw [reversed_coefficient, reflectedRole_involutive, reflectedRole_involutive]
    exact neg_ne_zero.mpr f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact Prod.ext (reflectedRole_involutive _) (reflectedRole_involutive _)
  right_inv f := by
    apply Subtype.ext
    exact Prod.ext (reflectedRole_involutive _) (reflectedRole_involutive _)

lemma local_scalar_count : (∑ row : Fin 8, Fintype.card (RowEntry (h := h) row)) =
    4 * Nat.choose h 3 * TripleCounting.neighborDegree h + 16 * Nat.choose h 3 := by
  simp_rw [Fintype.card_congr (rowSupportReflection _)]
  have hs := Equiv.sum_comp rowReflection (fun row => Fintype.card (TripleSchedule.RowEntry (h := h) row))
  exact hs.trans TripleSchedule.local_scalar_count

end ReverseLocal

namespace Global
open TripleNetwork

abbrev PhysicalRole (h : ℕ) := TripleCounting.Role (Fin h)
abbrev size (h : ℕ) := Fintype.card (PhysicalRole h)
def coordinates (h : ℕ) : PhysicalRole h ≃ Fin (size h) := Fintype.equivFin _

def invocationRoleMap (p : Fin 3) (profile : Profile (Fin h) p) :
    GateFrames.Role h → PhysicalRole h
  | .x T => .inl (0, (axisCoordinates p).symm (T, profile))
  | .y T => .inl (1, (axisCoordinates p).symm (T, profile))
  | .side e => .inr ⟨p, profile, .inl e⟩
  | .center i => .inr ⟨p, profile, .inr i⟩

theorem invocationRoleMap_injective (p : Fin 3) (profile : Profile (Fin h) p) :
    Function.Injective (invocationRoleMap p profile) := by
  intro a b hab
  cases a <;> cases b <;> simp only [invocationRoleMap, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq] at hab
  all_goals try { cases hab }
  all_goals try { apply congrArg GateFrames.Role.x; exact congrArg Prod.fst ((axisCoordinates p).symm.injective hab.2) }
  all_goals try { apply congrArg GateFrames.Role.y; exact congrArg Prod.fst ((axisCoordinates p).symm.injective hab.2) }
  all_goals try { simp_all }

def invocationRoleEmbedding (p : Fin 3) (profile : Profile (Fin h) p) :
    GateFrames.Role h ↪ PhysicalRole h :=
  ⟨invocationRoleMap p profile, invocationRoleMap_injective p profile⟩

def invocationFinEmbedding (p : Fin 3) (profile : Profile (Fin h) p) :
    Fin (localSize h) ↪ Fin (size h) :=
  (localCoordinates h).symm.toEmbedding.trans
    ((invocationRoleEmbedding p profile).trans (coordinates h).toEmbedding)

/-- Role outermost and binary address innermost, unchanged by the physical-role embedding. -/
def addressEmbedding {r R n : ℕ} (e : Fin r ↪ Fin R) :
    Fin (r * 2 ^ n) ↪ Fin (R * 2 ^ n) where
  toFun i := RoleWords.roleAddresses R n
    (e ((RoleWords.roleAddresses r n).symm i).1, ((RoleWords.roleAddresses r n).symm i).2)
  inj' := by
    intro i j hij
    have ht := (RoleWords.roleAddresses R n).injective hij
    apply (RoleWords.roleAddresses r n).symm.injective
    apply Prod.ext
    · exact e.injective (congrArg (fun z : Fin R × Fin (2 ^ n) => z.1) ht)
    · exact congrArg (fun z : Fin R × Fin (2 ^ n) => z.2) ht

@[simp] theorem addressEmbedding_at {r R n : ℕ} (e : Fin r ↪ Fin R)
    (i : Fin r) (a : Fin (2 ^ n)) :
    addressEmbedding (n := n) e (RoleWords.roleAddresses r n (i, a)) =
      RoleWords.roleAddresses R n (e i, a) := by
  change RoleWords.roleAddresses R n
    (e ((RoleWords.roleAddresses r n).symm (RoleWords.roleAddresses r n (i,a))).1,
      ((RoleWords.roleAddresses r n).symm (RoleWords.roleAddresses r n (i,a))).2) = _
  simp only [Equiv.symm_apply_apply]

theorem embedded_selected {w v : ℕ} (e : Fin w ↪ Fin v)
    (M : Matrix (Fin w) (Fin w) ℂ) (X : Fin v → ℂ) (i : Fin w) :
    (Embedded.matrix e M).mulVec X (e i) = M.mulVec (fun j => X (e j)) i := by
  unfold Matrix.mulVec dotProduct
  rw [← (Embedded.coordinates e).sum_comp, Fintype.sum_sum_type]
  simp only [Embedded.coordinates_inl, Embedded.coordinates_inr, Embedded.matrix_on]
  have hz (a : Embedded.complement e) : Embedded.matrix e M (e i) a.val = 0 := by
    rw [Embedded.matrix_off_col e M _ _ a.property]
    simp only [ite_eq_right (fun h => a.property ⟨i,h⟩)]
  simp_rw [hz]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]

theorem embedded_untouched {w v : ℕ} (e : Fin w ↪ Fin v)
    (M : Matrix (Fin w) (Fin w) ℂ) (X : Fin v → ℂ) (i : Fin v)
    (hi : i ∉ Set.range e) : (Embedded.matrix e M).mulVec X i = X i := by
  unfold Matrix.mulVec dotProduct
  simp_rw [Embedded.matrix_off_row e M i _ hi]
  simp

theorem binaryValues_restrict {r R n : ℕ} (e : Fin r ↪ Fin R) (X : Values R n) :
    (fun i => RoleFrameWords.binaryValues X (addressEmbedding e i)) =
      RoleFrameWords.binaryValues (fun i => X (e i)) := by
  funext i
  obtain ⟨⟨j,a⟩,rfl⟩ := (RoleWords.roleAddresses r n).surjective i
  obtain ⟨x,rfl⟩ := (DirectionalWords.addresses n).surjective a
  simp

/-- A literal word restricted to exactly the physical roles of one invocation. -/
def liftWord {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) : List (WordStep C (R * 2 ^ n)) :=
  TensorWords.embeddedWord (addressEmbedding e) W

theorem liftWord_calls {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) : wordCalls (liftWord e W) = wordCalls W :=
  TensorWords.embeddedWord_calls _ _

theorem liftWord_selected {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) (X : Values R n) (i : Fin r) (x : Vec (Fin n)) :
    (wordMatrix (liftWord e W)).mulVec (RoleFrameWords.binaryValues X)
      (RoleWords.roleAddresses R n (e i, DirectionalWords.addresses n x)) =
    (wordMatrix W).mulVec (RoleFrameWords.binaryValues (fun j => X (e j)))
      (RoleWords.roleAddresses r n (i, DirectionalWords.addresses n x)) := by
  rw [liftWord, TensorWords.embeddedWord_matrix, ← addressEmbedding_at,
    embedded_selected, binaryValues_restrict]

theorem addressEmbedding_not_mem {r R n : ℕ} (e : Fin r ↪ Fin R)
    (i : Fin R) (hi : i ∉ Set.range e) (a : Fin (2 ^ n)) :
    RoleWords.roleAddresses R n (i,a) ∉ Set.range (addressEmbedding (n := n) e) := by
  rintro ⟨k,hk⟩
  apply hi
  refine ⟨((RoleWords.roleAddresses r n).symm k).1, ?_⟩
  exact congrArg Prod.fst ((RoleWords.roleAddresses R n).injective hk)

theorem liftWord_untouched {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) (X : Values R n) (i : Fin R)
    (hi : i ∉ Set.range e) (x : Vec (Fin n)) :
    (wordMatrix (liftWord e W)).mulVec (RoleFrameWords.binaryValues X)
      (RoleWords.roleAddresses R n (i, DirectionalWords.addresses n x)) = X i x := by
  rw [liftWord, TensorWords.embeddedWord_matrix,
    embedded_untouched _ _ _ _ (addressEmbedding_not_mem e i hi _)]
  exact RoleFrameWords.binaryValues_at _ _ _

theorem invocation_profiles_distinct (p : Fin 3) (a b : Profile (Fin h) p)
    (u v : GateFrames.Role h)
    (he : invocationRoleMap p a u = invocationRoleMap p b v) : a = b := by
  cases u <;> cases v <;> simp only [invocationRoleMap, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq] at he
  all_goals try { cases he }
  all_goals try { exact congrArg Prod.snd ((axisCoordinates p).symm.injective he.2) }
  all_goals { simp_all }

theorem invocationFin_disjoint (p : Fin 3) (a b : Profile (Fin h) p) (hab : a ≠ b)
    (u v : Fin (localSize h)) : invocationFinEmbedding p a u ≠ invocationFinEmbedding p b v := by
  intro he
  apply hab
  apply invocation_profiles_distinct p a b ((localCoordinates h).symm u) ((localCoordinates h).symm v)
  exact (coordinates h).injective he

/-- Exact array action of a literal global word. -/
def wordAction {R n : ℕ} (W : List (WordStep C (R * 2 ^ n))) (X : Values R n) : Values R n :=
  fun i x => (wordMatrix W).mulVec (RoleFrameWords.binaryValues X)
    (RoleWords.roleAddresses R n (i, DirectionalWords.addresses n x))

theorem binaryValues_wordAction {R n : ℕ} (W : List (WordStep C (R * 2 ^ n))) (X : Values R n) :
    RoleFrameWords.binaryValues (wordAction W X) = (wordMatrix W).mulVec (RoleFrameWords.binaryValues X) := by
  funext k
  obtain ⟨⟨i,a⟩,rfl⟩ := (RoleWords.roleAddresses R n).surjective k
  obtain ⟨x,rfl⟩ := (DirectionalWords.addresses n).surjective a
  exact RoleFrameWords.binaryValues_at _ _ _

@[simp] theorem wordAction_nil {R n : ℕ} (X : Values R n) : wordAction ([] : List (WordStep C (R*2^n))) X = X := by
  funext i x
  simp [wordAction, wordMatrix]

theorem wordAction_append {R n : ℕ} (W V : List (WordStep C (R * 2 ^ n))) (X : Values R n) :
    wordAction (W ++ V) X = wordAction V (wordAction W X) := by
  funext i x
  rw [wordAction, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
    ← binaryValues_wordAction]
  rfl

theorem liftWord_action_selected {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) (X : Values R n) (i : Fin r) :
    wordAction (liftWord e W) X (e i) = wordAction W (fun j => X (e j)) i := by
  funext x
  exact liftWord_selected e W X i x

theorem liftWord_action_untouched {r R n : ℕ} (e : Fin r ↪ Fin R)
    (W : List (WordStep C (r * 2 ^ n))) (X : Values R n) (i : Fin R)
    (hi : i ∉ Set.range e) : wordAction (liftWord e W) X i = X i := by
  funext x
  exact liftWord_untouched e W X i hi x

section ProfileAssembly
variable {P : Type*} [Fintype P] [DecidableEq P] {r R n : ℕ}
variable (e : P → (Fin r ↪ Fin R))
variable (he : ∀ a b, a ≠ b → ∀ u v, e a u ≠ e b v)
variable (words : P → List (WordStep C (r * 2 ^ n)))

def profileWords (L : List P) : List (WordStep C (R * 2 ^ n)) :=
  (L.map (fun p => liftWord (e p) (words p))).flatten

omit [Fintype P] [DecidableEq P] in
theorem profileWords_calls (L : List P) : wordCalls (profileWords e words L) =
    (L.map (fun p => wordCalls (words p))).sum := by
  rw [profileWords, TensorWords.wordCalls_flatten]
  simp only [List.map_map, Function.comp_def, liftWord_calls]

omit [Fintype P] [DecidableEq P] in
include he in
theorem profileWords_untouched (L : List P) (p : P) (hp : p ∉ L)
    (X : Values R n) (i : Fin r) : wordAction (profileWords e words L) X (e p i) = X (e p i) := by
  induction L generalizing X with
  | nil => simp [profileWords]
  | cons q L ih =>
    have hpq : p ≠ q := fun h => hp (by simp [h])
    have hpt : p ∉ L := fun h => hp (by simp [h])
    have hi : e p i ∉ Set.range (e q) := by
      rintro ⟨j,hj⟩
      exact he p q hpq i j hj.symm
    simp only [profileWords, List.map_cons, List.flatten_cons]
    rw [wordAction_append, ← profileWords, ih hpt,
      liftWord_action_untouched _ _ _ _ hi]

omit [Fintype P] in
include he in
theorem profileWords_selected (L : List P) (hL : L.Nodup) (p : P) (hp : p ∈ L)
    (X : Values R n) (i : Fin r) :
    wordAction (profileWords e words L) X (e p i) = wordAction (words p) (fun j => X (e p j)) i := by
  induction L generalizing X with
  | nil => simp at hp
  | cons q L ih =>
    have hn := List.nodup_cons.mp hL
    simp only [profileWords, List.map_cons, List.flatten_cons]
    rw [wordAction_append, ← profileWords]
    by_cases hpq : p = q
    · subst q
      rw [profileWords_untouched e he words L p hn.1,
        liftWord_action_selected]
    · have hpt : p ∈ L := (List.mem_cons.mp hp).resolve_left hpq
      rw [ih hn.2 hpt]
      have hrestrict : (fun j => wordAction (liftWord (e q) (words q)) X (e p j)) =
          (fun j => X (e p j)) := by
        funext j
        apply liftWord_action_untouched
        rintro ⟨k,hk⟩
        exact he p q hpq j k hk.symm
      rw [hrestrict]

omit [Fintype P] [DecidableEq P] in
theorem profileWords_outside (L : List P) (X : Values R n) (i : Fin R)
    (hi : ∀ p ∈ L, i ∉ Set.range (e p)) : wordAction (profileWords e words L) X i = X i := by
  induction L generalizing X with
  | nil => simp [profileWords]
  | cons p L ih =>
    simp only [profileWords, List.map_cons, List.flatten_cons]
    rw [wordAction_append, ← profileWords, ih _ (fun q hq => hi q (by simp [hq])),
      liftWord_action_untouched _ _ _ _ (hi p (by simp))]

end ProfileAssembly

/-- These are the actual data, coordinates, physical roles and row chronology of each stage. -/
def invocationWord (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    List (WordStep C (localSize h * 2 ^ (h ^ 3))) :=
  if p = 1 then
    ReverseLocal.localWord (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h)
  else
    localWord (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h)

def stageWord (p : Fin 3) (hh : 7 ≤ h) : List (WordStep C (size h * 2 ^ (h ^ 3))) :=
  profileWords (invocationFinEmbedding p) (fun profile => invocationWord p profile hh) Finset.univ.toList

theorem stageWord_selected (p : Fin 3) (hh : 7 ≤ h) (profile : Profile (Fin h) p)
    (X : Values (size h) (h ^ 3)) (i : Fin (localSize h)) :
    wordAction (stageWord p hh) X (invocationFinEmbedding p profile i) =
      wordAction (invocationWord p profile hh) (fun j => X (invocationFinEmbedding p profile j)) i :=
  profileWords_selected _ (invocationFin_disjoint p) _ _ (Finset.nodup_toList _) _ (by simp) _ _

theorem stageWord_calls (p : Fin 3) (hh : 7 ≤ h) : wordCalls (stageWord p hh) =
    ∑ profile : Profile (Fin h) p, wordCalls (invocationWord p profile hh) := by
  rw [stageWord, profileWords_calls]
  simpa only [Finset.toList_toFinset] using
    (List.sum_toFinset (fun profile => wordCalls (invocationWord p profile hh))
      (Finset.nodup_toList (Finset.univ : Finset (Profile (Fin h) p)))).symm

def initialLabels (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    Labels (localSize h) (h ^ 3) :=
  localLabels (TripleInvocationFrames.invocationData p profile hh)
    (TripleInvocationFrames.invocationAddressCoordinates p h) 0

def finalLabels (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    Labels (localSize h) (h ^ 3) :=
  localFinalLabels (TripleInvocationFrames.invocationData p profile hh)
    (TripleInvocationFrames.invocationAddressCoordinates p h)

def physicalShear (p : Fin 3) (X : Values (localSize h) (h ^ 3)) : Values (localSize h) (h ^ 3) :=
  if p = 1 then ReverseLocal.localBankShear X else localBankShear X

theorem invocationWord_action (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (X : Values (localSize h) (h ^ 3)) :
    wordAction (invocationWord p profile hh) X =
      frames (finalLabels p profile hh) (physicalShear p (inverseFrames (initialLabels p profile hh) X)) := by
  by_cases hp : p = 1
  · simp only [invocationWord, physicalShear, hp, ↓reduceIte]
    funext i x
    unfold wordAction
    rw [ReverseLocal.localWord_array]
    exact RoleFrameWords.binaryValues_at _ _ _
  · simp only [invocationWord, physicalShear, hp, ↓reduceIte]
    funext i x
    unfold wordAction
    rw [localWord_array]
    exact RoleFrameWords.binaryValues_at _ _ _

theorem stageWord_selected_frames (p : Fin 3) (hh : 7 ≤ h) (profile : Profile (Fin h) p)
    (X : Values (size h) (h ^ 3)) (i : Fin (localSize h)) :
    wordAction (stageWord p hh) X (invocationFinEmbedding p profile i) =
      frames (finalLabels p profile hh)
        (physicalShear p (inverseFrames (initialLabels p profile hh)
          (fun j => X (invocationFinEmbedding p profile j)))) i := by
  rw [stageWord_selected, invocationWord_action]

theorem invocationFinEmbedding_at (p : Fin 3) (profile : Profile (Fin h) p)
    (r : GateFrames.Role h) : invocationFinEmbedding p profile (localCoordinates h r) =
      coordinates h (invocationRoleMap p profile r) := by
  simp [invocationFinEmbedding, invocationRoleEmbedding]

theorem stageWord_selected_role (p : Fin 3) (hh : 7 ≤ h) (profile : Profile (Fin h) p)
    (X : Values (size h) (h ^ 3)) (r : GateFrames.Role h) :
    wordAction (stageWord p hh) X (coordinates h (invocationRoleMap p profile r)) =
      frames (finalLabels p profile hh)
        (physicalShear p (inverseFrames (initialLabels p profile hh)
          (fun j => X (invocationFinEmbedding p profile j)))) (localCoordinates h r) := by
  rw [← invocationFinEmbedding_at]
  exact stageWord_selected_frames p hh profile X _

theorem invocationRoleMap_inactive (p q : Fin 3) (hq : q ≠ p) (profile : Profile (Fin h) q)
    (a : Edge (Fin h) ⊕ Option (Fin h)) (b : Profile (Fin h) p) (r : GateFrames.Role h) :
    invocationRoleMap p b r ≠ .inr ⟨q,profile,a⟩ := by
  intro he
  cases r <;> simp only [invocationRoleMap] at he
  all_goals try { cases he }
  all_goals { apply hq; exact (congrArg Sigma.fst (Sum.inr.inj he)).symm }

theorem stageWord_inactive (p q : Fin 3) (hh : 7 ≤ h) (hq : q ≠ p)
    (profile : Profile (Fin h) q) (a : Edge (Fin h) ⊕ Option (Fin h))
    (X : Values (size h) (h ^ 3)) :
    wordAction (stageWord p hh) X (coordinates h (.inr ⟨q,profile,a⟩)) =
      X (coordinates h (.inr ⟨q,profile,a⟩)) := by
  apply profileWords_outside
  intro b _
  rintro ⟨r,he⟩
  exact invocationRoleMap_inactive p q hq profile a b ((localCoordinates h).symm r)
    ((coordinates h).injective he)

/-- The three actual physical stages, including the reversed middle chronology. -/
def masterWord (hh : 7 ≤ h) : List (WordStep C (size h * 2 ^ (h ^ 3))) :=
  stageWord 0 hh ++ stageWord 1 hh ++ stageWord 2 hh

theorem masterWord_action (hh : 7 ≤ h) (X : Values (size h) (h ^ 3)) :
    wordAction (masterWord hh) X =
      wordAction (stageWord 2 hh) (wordAction (stageWord 1 hh) (wordAction (stageWord 0 hh) X)) := by
  simp only [masterWord, wordAction_append]

theorem masterWord_calls (hh : 7 ≤ h) : wordCalls (masterWord hh) =
    ∑ p : Fin 3, ∑ profile : Profile (Fin h) p, wordCalls (invocationWord p profile hh) := by
  simp only [masterWord, TypedKernelWords.wordCalls_append, stageWord_calls]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change ((∑ profile : Profile (Fin h) 0, wordCalls (invocationWord 0 profile hh)) +
    (∑ profile : Profile (Fin h) 1, wordCalls (invocationWord 1 profile hh))) +
    (∑ profile : Profile (Fin h) 2, wordCalls (invocationWord 2 profile hh)) =
    (∑ profile : Profile (Fin h) 0, wordCalls (invocationWord 0 profile hh)) +
    ((∑ profile : Profile (Fin h) 1, wordCalls (invocationWord 1 profile hh)) +
    ((∑ profile : Profile (Fin h) 2, wordCalls (invocationWord 2 profile hh)) + 0))
  simp only [Nat.add_zero, Nat.add_assoc]

lemma bank_axis (p : Fin 3) (profile : Profile (Fin h) p) (T : Triple (Fin h)) :
    ((axisCoordinates p).symm (T,profile)) p = T := by
  exact congrArg Prod.fst ((axisCoordinates p).apply_symm_apply (T,profile))

lemma bank_profile (p : Fin 3) (profile : Profile (Fin h) p) (T : Triple (Fin h)) :
    TripleInvocationFrames.bankProfile p ((axisCoordinates p).symm (T,profile)) = profile := by
  exact congrArg Prod.snd ((axisCoordinates p).apply_symm_apply (T,profile))

lemma selected_initial_space (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (r : GateFrames.Role h) :
    (TripleStageAction.incoming hh p (invocationRoleMap p profile r)).space =
      ((TripleInvocationFrames.invocationData p profile hh).labels
        (TripleInvocationFrames.invocationAddressCoordinates p h) 0 r).space := by
  classical
  cases r with
  | x T => simp only [TripleStageAction.incoming, invocationRoleMap, bank_axis, bank_profile, ↓reduceIte]
  | y T => simp only [TripleStageAction.incoming, invocationRoleMap, bank_axis, bank_profile,
      show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
  | side edge =>
    simp only [TripleStageAction.incoming, invocationRoleMap, lt_self_iff_false, ↓reduceIte,
      TripleStageAction.zeroLabel]
    exact ((TripleInvocationFrames.invocationData p profile hh).entry_auxiliary_zero
      (TripleInvocationFrames.invocationAddressCoordinates p h) edge none).1.symm
  | center i =>
    simp only [TripleStageAction.incoming, invocationRoleMap, lt_self_iff_false, ↓reduceIte,
      TripleStageAction.zeroLabel]
    simp [Data.labels, labelOfBasis, Data.at, Data.localAt, Data.entry, StageFrames.tensorSpace_bot_left, StageFrames.space_bot]

lemma selected_final_space (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (r : GateFrames.Role h) :
    (TripleStageAction.outgoing hh p (invocationRoleMap p profile r)).space =
      ((TripleInvocationFrames.invocationData p profile hh).finalLabels
        (TripleInvocationFrames.invocationAddressCoordinates p h) r).space := by
  classical
  cases r with
  | x T => simp only [TripleStageAction.outgoing, invocationRoleMap, bank_axis, bank_profile, ↓reduceIte]
  | y T => simp only [TripleStageAction.outgoing, invocationRoleMap, bank_axis, bank_profile,
      show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
  | side edge =>
    simp only [TripleStageAction.outgoing, invocationRoleMap, le_refl, ↓reduceIte,
      TripleStageAction.fullLabel]
    exact ((TripleInvocationFrames.invocationData p profile hh).final_auxiliary_top
      (TripleInvocationFrames.invocationAddressCoordinates p h) edge none).1.symm
  | center i =>
    simp only [TripleStageAction.outgoing, invocationRoleMap, le_refl, ↓reduceIte,
      TripleStageAction.fullLabel]
    simp only [Data.finalLabels, labelOfBasis_space, Data.finalSpace, BinaryResiduals.label3]
    rw [BinaryResiduals.tensorSpace_top_top, BinaryResiduals.tensorSpace_top_top, StageFrames.space_top]

lemma selected_initial_exponent (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (r : GateFrames.Role h) :
    (initialLabels p profile hh (localCoordinates h r)).exponent =
      (TripleStageAction.incoming hh p (invocationRoleMap p profile r)).exponent := by
  apply Label.exponent_eq
  simpa only [initialLabels, localLabels, Equiv.symm_apply_apply] using
    (selected_initial_space p profile hh r).symm

lemma selected_final_exponent (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (r : GateFrames.Role h) :
    (finalLabels p profile hh (localCoordinates h r)).exponent =
      (TripleStageAction.outgoing hh p (invocationRoleMap p profile r)).exponent := by
  apply Label.exponent_eq
  simpa only [finalLabels, localFinalLabels, Equiv.symm_apply_apply] using
    (selected_final_space p profile hh r).symm

def unpack (X : Values (size h) (h ^ 3)) : TripleStageAction.Arrays h :=
  fun r => X (coordinates h r)

def pack (X : TripleStageAction.Arrays h) : Values (size h) (h ^ 3) :=
  fun i => X ((coordinates h).symm i)

@[simp] lemma unpack_pack (X : TripleStageAction.Arrays h) : unpack (pack X) = X := by
  funext r; simp only [unpack, pack, Equiv.symm_apply_apply]
@[simp] lemma pack_unpack (X : Values (size h) (h ^ 3)) : pack (unpack X) = X := by
  funext i; simp only [unpack, pack, Equiv.apply_symm_apply]

lemma selected_inverse (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (X : Values (size h) (h ^ 3)) :
    inverseFrames (initialLabels p profile hh) (fun j => X (invocationFinEmbedding p profile j)) =
      fun j => TripleStageAction.inverseFrames (TripleStageAction.incoming hh p) (unpack X)
        (invocationRoleMap p profile ((localCoordinates h).symm j)) := by
  funext j
  obtain ⟨r,rfl⟩ := (localCoordinates h).surjective j
  simp only [inverseFrames, TripleStageAction.inverseFrames, Equiv.symm_apply_apply,
    selected_initial_exponent, invocationFinEmbedding_at, unpack]

lemma selected_scalar (p : Fin 3) (profile : Profile (Fin h) p)
    (Y : TripleStageAction.Arrays h) (r : GateFrames.Role h) :
    physicalShear p (fun j => Y (invocationRoleMap p profile ((localCoordinates h).symm j)))
      (localCoordinates h r) = TripleStageAction.scalarStage p Y (invocationRoleMap p profile r) := by
  cases r <;> by_cases hp : p = 1 <;>
    simp [physicalShear, hp, localBankShear, ReverseLocal.localBankShear,
      TripleStageAction.scalarStage, invocationRoleMap]

lemma stageWord_active (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (X : Values (size h) (h ^ 3)) (r : GateFrames.Role h) :
    wordAction (stageWord p hh) X (coordinates h (invocationRoleMap p profile r)) =
      TripleStageAction.framedStage hh p (unpack X) (invocationRoleMap p profile r) := by
  rw [stageWord_selected_role]
  unfold frames
  rw [selected_final_exponent, selected_inverse, selected_scalar]
  rfl

lemma frame_cancel {n : ℕ} (q : Vec (Fin n) → ZMod 4) (Y : FrameSpectrum.Array (ι := Fin n)) :
    FrameSpectrum.frameMap q (FrameSpectrum.frameMap (fun x => -q x) Y) = Y :=
  congrArg (fun T : FrameSpectrum.Operator (ι := Fin n) => T Y) (FrameSpectrum.frameMap_inverse q).1

lemma inactive_labels (p q : Fin 3) (hh : 7 ≤ h) (hq : q ≠ p)
    (profile : Profile (Fin h) q) (t : Edge (Fin h) ⊕ Option (Fin h)) :
    TripleStageAction.outgoing hh p (.inr ⟨q,profile,t⟩) =
      TripleStageAction.incoming hh p (.inr ⟨q,profile,t⟩) := by
  have he : q ≤ p ↔ q < p := by simp only [Fin.le_iff_val_le_val,Fin.lt_def] at *; omega
  simp only [TripleStageAction.outgoing,TripleStageAction.incoming,he]

/-- The literal profile word realizes the actual physical framed stage on every dirty input. -/
theorem stageWord_action (p : Fin 3) (hh : 7 ≤ h) (X : Values (size h) (h ^ 3)) :
    wordAction (stageWord p hh) X = pack (TripleStageAction.framedStage hh p (unpack X)) := by
  funext i
  obtain ⟨r,rfl⟩ := (coordinates h).surjective i
  simp only [pack, Equiv.symm_apply_apply]
  cases r with
  | inl rd =>
    rcases rd with ⟨b,d⟩
    have hbvalue : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hbvalue with rfl | rfl
    · have hb : (axisCoordinates p).symm (d p,TripleInvocationFrames.bankProfile p d) = d :=
        TripleInvocationFrames.bank_reassemble p d
      simpa only [invocationRoleMap, hb] using
        stageWord_active p (TripleInvocationFrames.bankProfile p d) hh X (.x (d p))
    · have hb : (axisCoordinates p).symm (d p,TripleInvocationFrames.bankProfile p d) = d :=
        TripleInvocationFrames.bank_reassemble p d
      simpa only [invocationRoleMap, hb] using
        stageWord_active p (TripleInvocationFrames.bankProfile p d) hh X (.y (d p))
  | inr a =>
    rcases a with ⟨q,profile,t⟩
    by_cases hq : q = p
    · subst q
      cases t with
      | inl edge => exact stageWord_active p profile hh X (.side edge)
      | inr center => exact stageWord_active p profile hh X (.center center)
    · rw [stageWord_inactive p q hh hq profile t X]
      unfold TripleStageAction.framedStage TripleStageAction.frames TripleStageAction.scalarStage
      change unpack X (.inr ⟨q,profile,t⟩) =
        FrameSpectrum.frameMap (TripleStageAction.outgoing hh p (.inr ⟨q,profile,t⟩)).exponent
          (TripleStageAction.inverseFrames (TripleStageAction.incoming hh p) (unpack X) (.inr ⟨q,profile,t⟩))
      unfold TripleStageAction.inverseFrames
      rw [inactive_labels p q hh hq profile t]
      exact (frame_cancel _ _).symm

/-- Universal full three-stage action of the actual finite typed word, with all auxiliaries dirty. -/
theorem masterWord_endpoint (hh : 7 ≤ h) (X : Values (size h) (h ^ 3)) :
    wordAction (masterWord hh) X =
      pack (TripleStageAction.frames (TripleStageAction.outgoing hh 2)
        (TripleStageAction.exchanged (TripleStageAction.inverseFrames (TripleStageAction.incoming hh 0) (unpack X)))) := by
  rw [masterWord_action, stageWord_action, stageWord_action, unpack_pack,
    stageWord_action, unpack_pack, TripleStageAction.framed_stages]

def invocationResidual (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) : ℕ :=
  let d := TripleInvocationFrames.invocationData p profile hh
  let e := TripleInvocationFrames.invocationAddressCoordinates p h
  (∑ row : Fin 8, ∑ r : GateFrames.Role h, (d.edges e row r).dimension) +
    ∑ r : GateFrames.Role h, (d.sinkEdges e r).dimension

def masterResidual (hh : 7 ≤ h) : ℕ :=
  ∑ p : Fin 3, ∑ profile : Profile (Fin h) p, invocationResidual p profile hh

def invocationScalars (h : ℕ) : ℕ :=
  4 * Nat.choose h 3 * TripleCounting.neighborDegree h + 16 * Nat.choose h 3

lemma localEdges_dimension {ι η : Type*} [Fintype ι] [Fintype η] {n : ℕ}
    (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) (i : Fin (localSize h)) :
    (localEdges d e row i).dimension = (d.edges e row ((localCoordinates h).symm i)).dimension := rfl
lemma localSinkEdges_dimension {ι η : Type*} [Fintype ι] [Fintype η] {n : ℕ}
    (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) (i : Fin (localSize h)) :
    (localSinkEdges d e i).dimension = (d.sinkEdges e ((localCoordinates h).symm i)).dimension := rfl

lemma local_residual_reindex {ι η : Type*} [Fintype ι] [Fintype η] {n : ℕ}
    (d : GateFrames.Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n) :
    (∑ row : Fin 8, ∑ i, (localEdges d e row i).dimension) +
        ∑ i, (localSinkEdges d e i).dimension =
      (∑ row : Fin 8, ∑ r : GateFrames.Role h, (d.edges e row r).dimension) +
        ∑ r : GateFrames.Role h, (d.sinkEdges e r).dimension := by
  apply congrArg₂ Nat.add
  · apply Finset.sum_congr rfl
    intro row _
    calc
      (∑ i, (localEdges d e row i).dimension) =
          ∑ i, (d.edges e row ((localCoordinates h).symm i)).dimension :=
        Finset.sum_congr rfl (fun i _ => localEdges_dimension d e row i)
      _ = ∑ r : GateFrames.Role h, (d.edges e row r).dimension :=
        (localCoordinates h).symm.sum_comp (fun r => (d.edges e row r).dimension)
  · calc
      (∑ i, (localSinkEdges d e i).dimension) =
          ∑ i, (d.sinkEdges e ((localCoordinates h).symm i)).dimension :=
        Finset.sum_congr rfl (fun i _ => localSinkEdges_dimension d e i)
      _ = ∑ r : GateFrames.Role h, (d.sinkEdges e r).dimension :=
        (localCoordinates h).symm.sum_comp (fun r => (d.sinkEdges e r).dimension)

lemma invocationWord_calls (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    wordCalls (invocationWord p profile hh) =
      invocationResidual p profile hh * 2 ^ (h ^ 3 - 1) + 3 * invocationScalars h * 2 ^ (h ^ 3) := by
  have hn : 1 ≤ h ^ 3 := Nat.succ_le_iff.mpr (pow_pos (by omega) 3)
  by_cases hp : p = 1
  · rw [invocationWord, ite_eq_left hp, ReverseLocal.localWord_calls hn,
      ReverseLocal.local_scalar_count]
    rw [show (∑ row : Fin 8, ∑ i, (ReverseLocal.localEdges
      (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h) row i).dimension) +
      (∑ i, (ReverseLocal.localSinkEdges (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h) i).dimension) =
      invocationResidual p profile hh from local_residual_reindex _ _]
    rfl
  · rw [invocationWord, ite_eq_right hp, localWord_calls hn, local_scalar_count,
      local_residual_reindex]
    rfl

/-- Columns lift the actual residual directions; pointwise scalar gates occur once. -/
def invocationWordColumns (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    List (WordStep C (localSize h * 2 ^ (f * h ^ 3))) :=
  let d := TripleInvocationFrames.invocationData p profile hh
  let e := TripleInvocationFrames.invocationAddressCoordinates p h
  if p = 1 then
    (ColumnSchedule.scheduleColumns f (ReverseLocal.localSchedule d e)).finishWord
      (ColumnSchedule.edgesColumns f (ReverseLocal.localSinkEdges d e))
  else
    (ColumnSchedule.scheduleColumns f (localSchedule d e)).finishWord
      (ColumnSchedule.edgesColumns f (localSinkEdges d e))

def stageWordColumns (f : ℕ) (p : Fin 3) (hh : 7 ≤ h) :
    List (WordStep C (size h * 2 ^ (f * h ^ 3))) :=
  profileWords (invocationFinEmbedding p) (fun profile => invocationWordColumns f p profile hh) Finset.univ.toList

def masterWordColumns (f : ℕ) (hh : 7 ≤ h) : List (WordStep C (size h * 2 ^ (f * h ^ 3))) :=
  stageWordColumns f 0 hh ++ stageWordColumns f 1 hh ++ stageWordColumns f 2 hh

lemma invocationWordColumns_calls (f : ℕ) (hf : 1 ≤ f) (p : Fin 3)
    (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    wordCalls (invocationWordColumns f p profile hh) =
      f * invocationResidual p profile hh * 2 ^ (f * h ^ 3 - 1) +
        3 * invocationScalars h * 2 ^ (f * h ^ 3) := by
  have hn : 1 ≤ f * h ^ 3 := Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (pow_pos (by omega) 3))
  unfold invocationWordColumns
  dsimp only
  by_cases hp : p = 1
  · rw [ite_eq_left hp, ColumnSchedule.finishColumns_word_calls f hn,
      ReverseLocal.localSchedule_residualDimension, ReverseLocal.localSchedule_scalarCount,
      ReverseLocal.local_scalar_count]
    rw [show (∑ row : Fin 8, ∑ i, (ReverseLocal.localEdges
      (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h) row i).dimension) +
      (∑ i, (ReverseLocal.localSinkEdges (TripleInvocationFrames.invocationData p profile hh)
      (TripleInvocationFrames.invocationAddressCoordinates p h) i).dimension) =
      invocationResidual p profile hh from local_residual_reindex _ _]
    rfl
  · rw [ite_eq_right hp, ColumnSchedule.finishColumns_word_calls f hn,
      localSchedule_residualDimension, localSchedule_scalarCount, local_scalar_count,
      local_residual_reindex]
    rfl

lemma stageWordColumns_calls (f : ℕ) (hf : 1 ≤ f) (p : Fin 3) (hh : 7 ≤ h) :
    wordCalls (stageWordColumns f p hh) =
      f * (∑ profile : Profile (Fin h) p, invocationResidual p profile hh) * 2 ^ (f * h ^ 3 - 1) +
        3 * ((Nat.choose h 3) ^ 2 * invocationScalars h) * 2 ^ (f * h ^ 3) := by
  rw [stageWordColumns, profileWords_calls]
  have hs := (List.sum_toFinset (fun profile => wordCalls (invocationWordColumns f p profile hh))
      (Finset.nodup_toList (Finset.univ : Finset (Profile (Fin h) p)))).symm
  simp only [Finset.toList_toFinset] at hs
  rw [hs]
  simp_rw [invocationWordColumns_calls f hf _ _ hh]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    TripleNetwork.profile_card, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

lemma masterWordColumns_calls (f : ℕ) (hf : 1 ≤ f) (hh : 7 ≤ h) :
    wordCalls (masterWordColumns f hh) =
      f * masterResidual hh * 2 ^ (f * h ^ 3 - 1) +
        3 * (3 * (Nat.choose h 3) ^ 2 * invocationScalars h) * 2 ^ (f * h ^ 3) := by
  simp only [masterWordColumns, TypedKernelWords.wordCalls_append, stageWordColumns_calls f hf]
  unfold masterResidual
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change _ = f * ((∑ profile : Profile (Fin h) 0, invocationResidual 0 profile hh) +
      ((∑ profile : Profile (Fin h) 1, invocationResidual 1 profile hh) +
      ((∑ profile : Profile (Fin h) 2, invocationResidual 2 profile hh) + 0))) * _ + _
  ring

def initialLabelsColumns (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    Labels (localSize h) (f * h ^ 3) := ColumnSchedule.labelsColumns f (initialLabels p profile hh)
def finalLabelsColumns (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h) :
    Labels (localSize h) (f * h ^ 3) := ColumnSchedule.labelsColumns f (finalLabels p profile hh)
def physicalShearColumns (f : ℕ) (p : Fin 3) (X : Values (localSize h) (f * h ^ 3)) :
    Values (localSize h) (f * h ^ 3) :=
  if p = 1 then ReverseLocal.localBankShear X else localBankShear X

theorem invocationWordColumns_action (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p)
    (hh : 7 ≤ h) (X : Values (localSize h) (f * h ^ 3)) :
    wordAction (invocationWordColumns f p profile hh) X =
      frames (finalLabelsColumns f p profile hh)
        (physicalShearColumns f p (inverseFrames (initialLabelsColumns f p profile hh) X)) := by
  by_cases hp : p = 1
  · simp only [invocationWordColumns, physicalShearColumns, hp, ↓reduceIte]
    funext i x
    unfold wordAction
    rw [ColumnSchedule.finishColumns_word_array, ReverseLocal.localSchedule_scalarMatrix,
      ReverseLocal.localRows_scalarAction]
    exact RoleFrameWords.binaryValues_at _ _ _
  · simp only [invocationWordColumns, physicalShearColumns, hp, ↓reduceIte]
    funext i x
    unfold wordAction
    rw [ColumnSchedule.finishColumns_word_array, localSchedule_scalarMatrix, localRows_scalarAction]
    exact RoleFrameWords.binaryValues_at _ _ _

lemma selected_initialColumns_exponent (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p)
    (hh : 7 ≤ h) (r : GateFrames.Role h) :
    (initialLabelsColumns f p profile hh (localCoordinates h r)).exponent =
      (TripleColumnAction.incoming hh f p (invocationRoleMap p profile r)).exponent := by
  apply Label.exponent_eq
  change ColumnSchedule.columnSpace f (initialLabels p profile hh (localCoordinates h r)).space =
    ColumnSchedule.columnSpace f (TripleStageAction.incoming hh p (invocationRoleMap p profile r)).space
  congr 1
  simpa only [initialLabels, localLabels, Equiv.symm_apply_apply] using
    (selected_initial_space p profile hh r).symm

lemma selected_finalColumns_exponent (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p)
    (hh : 7 ≤ h) (r : GateFrames.Role h) :
    (finalLabelsColumns f p profile hh (localCoordinates h r)).exponent =
      (TripleColumnAction.outgoing hh f p (invocationRoleMap p profile r)).exponent := by
  apply Label.exponent_eq
  change ColumnSchedule.columnSpace f (finalLabels p profile hh (localCoordinates h r)).space =
    ColumnSchedule.columnSpace f (TripleStageAction.outgoing hh p (invocationRoleMap p profile r)).space
  congr 1
  simpa only [finalLabels, localFinalLabels, Equiv.symm_apply_apply] using
    (selected_final_space p profile hh r).symm

def unpackColumns (f : ℕ) (X : Values (size h) (f * h ^ 3)) : TripleColumnAction.Arrays h f :=
  fun r => X (coordinates h r)
def packColumns (f : ℕ) (X : TripleColumnAction.Arrays h f) : Values (size h) (f * h ^ 3) :=
  fun i => X ((coordinates h).symm i)
@[simp] lemma unpackColumns_pack (f : ℕ) (X : TripleColumnAction.Arrays h f) :
    unpackColumns f (packColumns f X) = X := by funext r; simp only [unpackColumns,packColumns,Equiv.symm_apply_apply]
@[simp] lemma packColumns_unpack (f : ℕ) (X : Values (size h) (f * h ^ 3)) :
    packColumns f (unpackColumns f X) = X := by funext i; simp only [unpackColumns,packColumns,Equiv.apply_symm_apply]

lemma selectedColumns_inverse (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (X : Values (size h) (f * h ^ 3)) :
    inverseFrames (initialLabelsColumns f p profile hh) (fun j => X (invocationFinEmbedding p profile j)) =
      fun j => TripleColumnAction.inverseFrames (TripleColumnAction.incoming hh f p) (unpackColumns f X)
        (invocationRoleMap p profile ((localCoordinates h).symm j)) := by
  funext j
  obtain ⟨r,rfl⟩ := (localCoordinates h).surjective j
  simp only [inverseFrames, TripleColumnAction.inverseFrames, Equiv.symm_apply_apply,
    selected_initialColumns_exponent, invocationFinEmbedding_at, unpackColumns]

lemma selectedColumns_scalar (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p)
    (Y : TripleColumnAction.Arrays h f) (r : GateFrames.Role h) :
    physicalShearColumns f p (fun j => Y (invocationRoleMap p profile ((localCoordinates h).symm j)))
      (localCoordinates h r) = TripleColumnAction.scalarStage p Y (invocationRoleMap p profile r) := by
  cases r <;> by_cases hp : p = 1 <;>
    simp [physicalShearColumns, hp, localBankShear, ReverseLocal.localBankShear,
      TripleColumnAction.scalarStage, invocationRoleMap]

lemma stageWordColumns_active (f : ℕ) (p : Fin 3) (profile : Profile (Fin h) p) (hh : 7 ≤ h)
    (X : Values (size h) (f * h ^ 3)) (r : GateFrames.Role h) :
    wordAction (stageWordColumns f p hh) X (coordinates h (invocationRoleMap p profile r)) =
      TripleColumnAction.framedStage hh f p (unpackColumns f X) (invocationRoleMap p profile r) := by
  rw [← invocationFinEmbedding_at]
  rw [show wordAction (stageWordColumns f p hh) X (invocationFinEmbedding p profile (localCoordinates h r)) =
      wordAction (invocationWordColumns f p profile hh) (fun j => X (invocationFinEmbedding p profile j))
        (localCoordinates h r) from
    profileWords_selected _ (invocationFin_disjoint p) _ _ (Finset.nodup_toList _) _ (by simp) _ _]
  rw [invocationWordColumns_action]
  unfold frames
  rw [selected_finalColumns_exponent, selectedColumns_inverse, selectedColumns_scalar]
  rfl

lemma stageWordColumns_inactive (f : ℕ) (p q : Fin 3) (hh : 7 ≤ h) (hq : q ≠ p)
    (profile : Profile (Fin h) q) (a : Edge (Fin h) ⊕ Option (Fin h))
    (X : Values (size h) (f * h ^ 3)) :
    wordAction (stageWordColumns f p hh) X (coordinates h (.inr ⟨q,profile,a⟩)) =
      X (coordinates h (.inr ⟨q,profile,a⟩)) := by
  apply profileWords_outside
  intro b _
  rintro ⟨r,he⟩
  exact invocationRoleMap_inactive p q hq profile a b ((localCoordinates h).symm r)
    ((coordinates h).injective he)

/-- The copied literal stage acts on all columns together and preserves unrelated dirty roles. -/
theorem stageWordColumns_action (f : ℕ) (p : Fin 3) (hh : 7 ≤ h)
    (X : Values (size h) (f * h ^ 3)) :
    wordAction (stageWordColumns f p hh) X =
      packColumns f (TripleColumnAction.framedStage hh f p (unpackColumns f X)) := by
  funext i
  obtain ⟨r,rfl⟩ := (coordinates h).surjective i
  simp only [packColumns, Equiv.symm_apply_apply]
  cases r with
  | inl rd =>
    rcases rd with ⟨b,d⟩
    have hbvalue : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hbvalue with rfl | rfl
    · have hb : (axisCoordinates p).symm (d p,TripleInvocationFrames.bankProfile p d) = d :=
        TripleInvocationFrames.bank_reassemble p d
      simpa only [invocationRoleMap,hb] using
        stageWordColumns_active f p (TripleInvocationFrames.bankProfile p d) hh X (.x (d p))
    · have hb : (axisCoordinates p).symm (d p,TripleInvocationFrames.bankProfile p d) = d :=
        TripleInvocationFrames.bank_reassemble p d
      simpa only [invocationRoleMap,hb] using
        stageWordColumns_active f p (TripleInvocationFrames.bankProfile p d) hh X (.y (d p))
  | inr a =>
    rcases a with ⟨q,profile,t⟩
    by_cases hq : q = p
    · subst q
      cases t with
      | inl edge => exact stageWordColumns_active f p profile hh X (.side edge)
      | inr center => exact stageWordColumns_active f p profile hh X (.center center)
    · rw [stageWordColumns_inactive f p q hh hq profile t X]
      unfold TripleColumnAction.framedStage TripleColumnAction.frames TripleColumnAction.scalarStage
      change unpackColumns f X (.inr ⟨q,profile,t⟩) =
        FrameSpectrum.frameMap (TripleColumnAction.outgoing hh f p (.inr ⟨q,profile,t⟩)).exponent
          (TripleColumnAction.inverseFrames (TripleColumnAction.incoming hh f p) (unpackColumns f X) (.inr ⟨q,profile,t⟩))
      unfold TripleColumnAction.inverseFrames
      have he : TripleColumnAction.outgoing hh f p (.inr ⟨q,profile,t⟩) =
          TripleColumnAction.incoming hh f p (.inr ⟨q,profile,t⟩) := by
        change ColumnSchedule.columns f (TripleStageAction.outgoing hh p (.inr ⟨q,profile,t⟩)) =
          ColumnSchedule.columns f (TripleStageAction.incoming hh p (.inr ⟨q,profile,t⟩))
        rw [inactive_labels p q hh hq profile t]
      rw [he]
      exact (frame_cancel _ _).symm

/-- All three copied literal stages realize the concrete framed scalar exchange. -/
theorem masterWordColumns_endpoint (f : ℕ) (hh : 7 ≤ h) (X : Values (size h) (f * h ^ 3)) :
    wordAction (masterWordColumns f hh) X =
      packColumns f (TripleColumnAction.frames (TripleColumnAction.outgoing hh f 2)
        (TripleColumnAction.exchanged (TripleColumnAction.inverseFrames (TripleColumnAction.incoming hh f 0) (unpackColumns f X)))) := by
  simp only [masterWordColumns,wordAction_append]
  rw [stageWordColumns_action,stageWordColumns_action,unpackColumns_pack,
    stageWordColumns_action,unpackColumns_pack,TripleColumnAction.framed_stages]

lemma columnsStateArrays_eq (f : ℕ) (s : TripleColumnAction.State h f) :
    TerminalWords.stateArrays (coordinates h) s = packColumns f (TripleColumnAction.stateArrays s) := by
  funext i
  change (fun x => TerminalWords.values s ((coordinates h).symm i,x)) =
    TripleColumnAction.stateArrays s ((coordinates h).symm i)
  generalize (coordinates h).symm i = r
  cases r with
  | inl rd => rcases rd with ⟨b,d⟩; fin_cases b <;> rfl
  | inr a => rfl

/-- Packed universal endpoint for the actual entire network, at every finite column count. -/
theorem masterWordColumns_packed_endpoint (f : ℕ) (hh : 7 ≤ h) (s : TripleColumnAction.State h f) :
    (wordMatrix (masterWordColumns f hh)).mulVec (TerminalWords.pack (coordinates h) s) =
      TerminalWords.pack (coordinates h)
        (TripleColumnAction.sinkFrames f (NetworkTerminal.exchange (TripleColumnAction.sourceInverse f s))) := by
  rw [TerminalWords.pack_binaryValues,columnsStateArrays_eq,← binaryValues_wordAction,
    masterWordColumns_endpoint,unpackColumns_pack,TripleColumnAction.source_inverse_arrays,
    TripleColumnAction.exchanged_arrays,TripleColumnAction.sink_frames_arrays,
    ← columnsStateArrays_eq,← TerminalWords.pack_binaryValues]

end Global

end
end ExactFourierCircuits.TripleSchedule
