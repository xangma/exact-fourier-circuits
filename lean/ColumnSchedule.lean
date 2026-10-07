import GateFrames
import ResidualBudget
import BinaryColumns

set_option autoImplicit false
namespace ExactFourierCircuits.ColumnSchedule
open OAI.ExactFourier BinaryFrames BinaryTensor BinaryResiduals BinaryProjection
open FramedScheduleWords Module
open scoped BigOperators
noncomputable section

variable {m r : ℕ}

/-- Physical columns are the outer factor of the global binary address. -/
def columnSpace (f : ℕ) (A : Submodule F2 (Vec (Fin m))) :
    Submodule F2 (Vec (Fin (f * m))) :=
  StageFrames.space finProdFinEquiv (tensorSpace (⊤ : Submodule F2 (Vec (Fin f))) A)

def columnBasis (f : ℕ) {d : ℕ} (A : Submodule F2 (Vec (Fin m)))
    (b : Basis (Fin d) F2 A) (hb : Orthonormal (fun k => (b k : Vec (Fin m)))) :
    Basis (Fin (f * d)) F2 (columnSpace f A) :=
  ((tensorBasis (⊤ : Submodule F2 (Vec (Fin f))) A fullBasis b fullBasis_orthonormal hb).reindex
    finProdFinEquiv).map (GateFrames.subspaceCoordinates finProdFinEquiv _)

lemma columnBasis_vector (f : ℕ) {d : ℕ} (A : Submodule F2 (Vec (Fin m)))
    (b : Basis (Fin d) F2 A) (hb : Orthonormal (fun k => (b k : Vec (Fin m))))
    (c : Fin f) (k : Fin d) :
    (columnBasis f A b hb (finProdFinEquiv (c, k)) : Vec (Fin (f * m))) =
      StageFrames.coordinates finProdFinEquiv (tensor (unit c) (b k : Vec (Fin m))) := by
  unfold columnBasis columnSpace
  unfold BinaryProjection.Orthonormal at hb
  rw [Basis.map_apply, Basis.reindex_apply]
  simp only [Equiv.symm_apply_apply]
  change StageFrames.coordinates finProdFinEquiv
    (tensorBasis (⊤ : Submodule F2 (Vec (Fin f))) A fullBasis b fullBasis_orthonormal hb (c, k)
      : Vec (Fin f × Fin m)) = _
  rw [tensorBasis_apply, fullBasis_apply]

lemma columnBasis_orthonormal (f : ℕ) {d : ℕ} (A : Submodule F2 (Vec (Fin m)))
    (b : Basis (Fin d) F2 A) (hb : Orthonormal (fun k => (b k : Vec (Fin m)))) :
    Orthonormal (fun k => (columnBasis f A b hb k : Vec (Fin (f * m)))) := by
  intro i j
  obtain ⟨⟨c, k⟩, rfl⟩ := (finProdFinEquiv : Fin f × Fin d ≃ Fin (f * d)).surjective i
  obtain ⟨⟨c', k'⟩, rfl⟩ := (finProdFinEquiv : Fin f × Fin d ≃ Fin (f * d)).surjective j
  change dot (columnBasis f A b hb (finProdFinEquiv (c, k)) : Vec (Fin (f * m)))
    (columnBasis f A b hb (finProdFinEquiv (c', k')) : Vec (Fin (f * m))) = _
  rw [columnBasis_vector, columnBasis_vector, StageFrames.coordinates_dot]
  exact (BinaryColumns.columnFamily_orthonormal (fun k => (b k : Vec (Fin m))) hb (c, k) (c', k')).trans
    (by simp)

/-- An actual orthonormal basis of the copied subspace, with literal dimension f*d. -/
def columns (f : ℕ) (L : Label m) : Label (f * m) where
  space := columnSpace f L.space
  dimension := f * L.dimension
  basis := columnBasis f L.space L.basis L.orthonormal
  orthonormal := columnBasis_orthonormal f L.space L.basis L.orthonormal

@[simp] lemma columns_space (f : ℕ) (L : Label m) : (columns f L).space = columnSpace f L.space := rfl
@[simp] lemma columns_dimension (f : ℕ) (L : Label m) : (columns f L).dimension = f * L.dimension := rfl

lemma columnSpace_mono (f : ℕ) {A S : Submodule F2 (Vec (Fin m))} (h : A ≤ S) :
    columnSpace f A ≤ columnSpace f S :=
  Submodule.map_mono (tensorSpace_mono le_rfl h)

lemma columns_decomposes (f : ℕ) (A S : Label m) (h : A.space ≤ S.space) :
    Decomposes (columns f A).space (columnSpace f (residual A.space S.space)) (columns f S).space :=
  GateFrames.decomposes_space finProdFinEquiv
    (tensorSpace_decomposes_right (⊤ : Submodule F2 (Vec (Fin f)))
      (ResidualBudget.nested_decomposes A.space S.space h A.basis A.orthonormal))

lemma columns_residual (f : ℕ) (A S : Label m) (h : A.space ≤ S.space) :
    residual (columns f A).space (columns f S).space = columnSpace f (residual A.space S.space) :=
  residual_of_decomposes (columns_decomposes f A S h) (columns f A).nondegenerate

def columnResidualBasis (f : ℕ) (A S : Label m) (h : A.space ≤ S.space) {d : ℕ}
    (b : Basis (Fin d) F2 (residual A.space S.space))
    (hb : Orthonormal (fun k => (b k : Vec (Fin m)))) :
    Basis (Fin (f * d)) F2 (residual (columns f A).space (columns f S).space) :=
  residualBasis _ _ _ (columns_decomposes f A S h) (columns f A).nondegenerate
    (columnBasis f _ b hb)

lemma columnResidualBasis_orthonormal (f : ℕ) (A S : Label m) (h : A.space ≤ S.space) {d : ℕ}
    (b : Basis (Fin d) F2 (residual A.space S.space))
    (hb : Orthonormal (fun k => (b k : Vec (Fin m)))) :
    Orthonormal (fun k => (columnResidualBasis f A S h b hb k : Vec (Fin (f * m)))) :=
  residualBasis_orthonormal _ _ _ (columns_decomposes f A S h) (columns f A).nondegenerate
    (columnBasis f _ b hb) (columnBasis_orthonormal f _ b hb)

def edgeColumns (f : ℕ) {A S : Label m} : NestedEdge A S → NestedEdge (columns f A) (columns f S)
  | .increasing h d b hb => .increasing (columnSpace_mono f h) (f * d)
      (columnResidualBasis f A S h b hb) (columnResidualBasis_orthonormal f A S h b hb)
  | .decreasing h d b hb => .decreasing (columnSpace_mono f h) (f * d)
      (columnResidualBasis f S A h b hb) (columnResidualBasis_orthonormal f S A h b hb)

@[simp] lemma edgeColumns_dimension (f : ℕ) {A S : Label m} (e : NestedEdge A S) :
    (edgeColumns f e).dimension = f * e.dimension := by cases e <;> rfl

def labelsColumns (f : ℕ) (F : Labels r m) : Labels r (f * m) := fun i => columns f (F i)

def edgesColumns (f : ℕ) {F G : Labels r m} (edges : ∀ i, NestedEdge (F i) (G i)) :
    ∀ i, NestedEdge (labelsColumns f F i) (labelsColumns f G i) := fun i => edgeColumns f (edges i)

lemma edgesColumns_dimension (f : ℕ) {F G : Labels r m} (edges : ∀ i, NestedEdge (F i) (G i)) :
    (∑ i, (edgesColumns f edges i).dimension) = f * ∑ i, (edges i).dimension := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact edgeColumns_dimension f (edges i)

/-- Scalar role indices and coefficients are unchanged; only address frames are copied. -/
def eventColumns (f : ℕ) {F G : Labels r m} (e : Event F G) :
    Event (labelsColumns f F) (labelsColumns f G) where
  edges := edgesColumns f e.edges
  dest := e.dest
  source := e.source
  distinct := e.distinct
  coefficient := e.coefficient
  nonzero := e.nonzero
  compatible := by
    change columnSpace f (G e.dest).space = columnSpace f (G e.source).space
    rw [e.compatible]

@[simp] lemma eventColumns_scalarMatrix (f : ℕ) {F G : Labels r m} (e : Event F G) :
    (eventColumns f e).scalarMatrix = e.scalarMatrix := rfl

lemma eventColumns_residualDimension (f : ℕ) {F G : Labels r m} (e : Event F G) :
    (eventColumns f e).residualDimension = f * e.residualDimension :=
  edgesColumns_dimension f e.edges

def scheduleColumns (f : ℕ) : ∀ {F G : Labels r m}, Schedule F G →
    Schedule (labelsColumns f F) (labelsColumns f G)
  | _, _, .nil F => .nil (labelsColumns f F)
  | _, _, .cons e s => .cons (eventColumns f e) (scheduleColumns f s)

@[simp] lemma scheduleColumns_scalarMatrix (f : ℕ) {F G : Labels r m} (s : Schedule F G) :
    (scheduleColumns f s).scalarMatrix = s.scalarMatrix := by
  induction s with
  | nil F => rfl
  | cons e s ih => simp only [scheduleColumns, Schedule.scalarMatrix, ih, eventColumns_scalarMatrix]

@[simp] lemma scheduleColumns_scalarCount (f : ℕ) {F G : Labels r m} (s : Schedule F G) :
    (scheduleColumns f s).scalarCount = s.scalarCount := by
  induction s with
  | nil F => rfl
  | cons e s ih => simp only [scheduleColumns, Schedule.scalarCount, ih]

lemma scheduleColumns_residualDimension (f : ℕ) {F G : Labels r m} (s : Schedule F G) :
    (scheduleColumns f s).residualDimension = f * s.residualDimension := by
  induction s with
  | nil F => simp [scheduleColumns, Schedule.residualDimension]
  | cons e s ih =>
    simp only [scheduleColumns, Schedule.residualDimension, ih, eventColumns_residualDimension]
    ring

theorem scheduleColumns_word_array (f : ℕ) {F G : Labels r m} (s : Schedule F G)
    (X : Values r (f * m)) :
    (wordMatrix (scheduleColumns f s).word).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues
        (frames (labelsColumns f G) (scalarAction s.scalarMatrix (inverseFrames (labelsColumns f F) X))) := by
  rw [Schedule.word_array, scheduleColumns_scalarMatrix]

theorem scheduleColumns_word_calls (f : ℕ) (hn : 1 ≤ f * m) {F G : Labels r m} (s : Schedule F G) :
    wordCalls (scheduleColumns f s).word =
      f * s.residualDimension * 2 ^ (f * m - 1) + 3 * s.scalarCount * 2 ^ (f * m) := by
  rw [Schedule.word_calls hn, scheduleColumns_residualDimension, scheduleColumns_scalarCount]

theorem finishColumns_word_calls (f : ℕ) (hn : 1 ≤ f * m) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i)) :
    wordCalls ((scheduleColumns f s).finishWord (edgesColumns f sinkEdges)) =
      f * (s.residualDimension + ∑ i, (sinkEdges i).dimension) * 2 ^ (f * m - 1) +
        3 * s.scalarCount * 2 ^ (f * m) := by
  rw [Schedule.finishWord_calls hn, scheduleColumns_residualDimension, edgesColumns_dimension,
    scheduleColumns_scalarCount]
  ring

theorem finishColumns_word_array (f : ℕ) {F G H : Labels r m}
    (s : Schedule F G) (sinkEdges : ∀ i, NestedEdge (G i) (H i)) (X : Values r (f * m)) :
    (wordMatrix ((scheduleColumns f s).finishWord (edgesColumns f sinkEdges))).mulVec
      (RoleFrameWords.binaryValues X) = RoleFrameWords.binaryValues
        (frames (labelsColumns f H) (scalarAction s.scalarMatrix (inverseFrames (labelsColumns f F) X))) := by
  rw [Schedule.finishWord_array, scheduleColumns_scalarMatrix]

/-- Reindexing the finite basis family does not change its projection. -/
lemma projection_index_equiv {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (e : κ ≃ ν) (z : κ → Vec ι) (ξ : Vec ι) :
    frameProjection (fun i => z (e.symm i)) ξ = frameProjection z ξ := by
  unfold frameProjection
  exact e.symm.sum_comp (fun i => dot (z i) ξ • z i)

lemma projection_coordinates {ι η κ : Type*} [Fintype ι] [Fintype η] [Fintype κ]
    (e : ι ≃ η) (z : κ → Vec ι) (ξ : Vec ι) :
    frameProjection (fun i => StageFrames.coordinates e (z i)) (StageFrames.coordinates e ξ) =
      StageFrames.coordinates e (frameProjection z ξ) := by
  simp [frameProjection, StageFrames.coordinates_dot]

lemma coordinates_weightModFour {ι η : Type*} [Fintype ι] [Fintype η]
    (e : ι ≃ η) (ξ : Vec ι) :
    weightModFour (StageFrames.coordinates e ξ) = weightModFour ξ := by
  unfold weightModFour
  rw [StageFrames.coordinates_weight]

lemma columns_vectors_eq (f : ℕ) (L : Label m) :
    (columns f L).vectors = fun i => StageFrames.coordinates finProdFinEquiv
      (BinaryColumns.columnFamily L.vectors
        ((finProdFinEquiv : Fin f × Fin L.dimension ≃ Fin (f * L.dimension)).symm i)) := by
  funext i
  obtain ⟨⟨c, k⟩, rfl⟩ :=
    (finProdFinEquiv : Fin f × Fin L.dimension ≃ Fin (f * L.dimension)).surjective i
  simp only [Equiv.symm_apply_apply]
  change (columnBasis f L.space L.basis L.orthonormal (finProdFinEquiv (c, k)) : Vec (Fin (f * m))) =
    StageFrames.coordinates finProdFinEquiv (tensor (unit c) (L.basis k : Vec (Fin m)))
  exact columnBasis_vector f L.space L.basis L.orthonormal c k

/-- The actual copied-label projection is the coordinate transport of the block projection. -/
lemma columns_projection (f : ℕ) (L : Label m) (ξ : Vec (Fin f × Fin m)) :
    frameProjection (columns f L).vectors (StageFrames.coordinates finProdFinEquiv ξ) =
      StageFrames.coordinates finProdFinEquiv (frameProjection (BinaryColumns.columnFamily L.vectors) ξ) := by
  change frameProjection (fun i : Fin (f * L.dimension) =>
    (columnBasis f L.space L.basis L.orthonormal i : Vec (Fin (f * m)))) _ = _
  have hv : (fun i : Fin (f * L.dimension) =>
      (columnBasis f L.space L.basis L.orthonormal i : Vec (Fin (f * m)))) =
      fun i => StageFrames.coordinates finProdFinEquiv
        (BinaryColumns.columnFamily L.vectors (finProdFinEquiv.symm i)) := columns_vectors_eq f L
  rw [hv]
  exact (projection_index_equiv
    (finProdFinEquiv : Fin f × Fin L.dimension ≃ Fin (f * L.dimension))
    (fun i => StageFrames.coordinates finProdFinEquiv (BinaryColumns.columnFamily L.vectors i))
    (StageFrames.coordinates finProdFinEquiv ξ)).trans (projection_coordinates _ _ _)

/-- The copied label's exponent is the sum of the original exponents in the physical columns. -/
theorem columns_exponent (f : ℕ) (L : Label m) (ξ : Vec (Fin f × Fin m)) :
    (columns f L).exponent (StageFrames.coordinates finProdFinEquiv ξ) =
      ∑ c, L.exponent (BinaryColumns.column ξ c) := by
  change weightModFour (frameProjection (columns f L).vectors
    (StageFrames.coordinates finProdFinEquiv ξ)) = _
  rw [columns_projection, coordinates_weightModFour]
  exact BinaryColumns.columnFamily_projection_weightModFour L.vectors ξ

def column (f m : ℕ) (ξ : Vec (Fin (f * m))) (c : Fin f) : Vec (Fin m) :=
  fun i => ξ (finProdFinEquiv (c, i))

theorem columns_exponent_flat (f : ℕ) (L : Label m) (ξ : Vec (Fin (f * m))) :
    (columns f L).exponent ξ = ∑ c, L.exponent (column f m ξ c) := by
  have h := columns_exponent f L ((StageFrames.coordinates finProdFinEquiv).symm ξ)
  calc
    _ = ∑ c, L.exponent (BinaryColumns.column ((StageFrames.coordinates finProdFinEquiv).symm ξ) c) := by
      simpa only [LinearEquiv.apply_symm_apply] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      congr 1

lemma zero_columns_exponent (L : Label m) (ξ : Vec (Fin (0 * m))) :
    (columns 0 L).exponent ξ = 0 := by
  rw [columns_exponent_flat]
  simp

end
end ExactFourierCircuits.ColumnSchedule
