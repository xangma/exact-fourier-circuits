import BinaryResiduals

set_option autoImplicit false

/- Concrete stage boundaries with proved binary-coordinate transports.
   Gate chronology and the complete macro sequence remain separate. -/
namespace ExactFourierCircuits.StageFrames
open BinaryFrames BinaryComplement BinaryTensor BinaryResiduals Module
open scoped BigOperators
noncomputable section

variable {ι η κ : Type*} [Fintype ι] [Fintype η] [Fintype κ]

def coordinates (e : ι ≃ η) : Vec ι ≃ₗ[F2] Vec η where
  toFun x := fun j => x (e.symm j)
  invFun y := fun i => y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  map_add' x y := rfl
  map_smul' c x := rfl

omit [Fintype ι] [Fintype η] in
@[simp] lemma coordinates_apply (e : ι ≃ η) (x : Vec ι) (j : η) :
    coordinates e x j = x (e.symm j) := rfl
omit [Fintype ι] [Fintype η] in
@[simp] lemma coordinates_symm_apply (e : ι ≃ η) (y : Vec η) (i : ι) :
    (coordinates e).symm y i = y (e i) := rfl

lemma coordinates_dot (e : ι ≃ η) (x y : Vec ι) :
    dot (coordinates e x) (coordinates e y) = dot x y := by
  unfold dot
  exact e.symm.sum_comp (fun i => x i * y i)

lemma coordinates_weight (e : ι ≃ η) (x : Vec ι) :
    weight (coordinates e x) = weight x := by
  unfold weight
  exact e.symm.sum_comp (fun i => bit (x i))

def space (e : ι ≃ η) (A : Submodule F2 (Vec ι)) : Submodule F2 (Vec η) :=
  A.map (coordinates e).toLinearMap

omit [Fintype ι] [Fintype η] in
lemma mem_space (e : ι ≃ η) (A : Submodule F2 (Vec ι)) (y : Vec η) :
    y ∈ space e A ↔ (coordinates e).symm y ∈ A := by
  constructor
  · rintro ⟨x, hx, he⟩
    rw [← he]
    simpa using hx
  · intro hy
    exact ⟨(coordinates e).symm y, hy, (coordinates e).apply_symm_apply y⟩

omit [Fintype ι] [Fintype η] in
@[simp] lemma space_top (e : ι ≃ η) : space e (⊤ : Submodule F2 (Vec ι)) = ⊤ := by
  ext y; simp [mem_space]
omit [Fintype ι] [Fintype η] in
@[simp] lemma space_bot (e : ι ≃ η) : space e (⊥ : Submodule F2 (Vec ι)) = ⊥ := by
  ext y; simp [mem_space]

omit [Fintype ι] [Fintype η] in
lemma space_line (e : ι ≃ η) (u : Vec ι) :
    space e (line u) = line (coordinates e u) := by
  ext y
  rw [mem_space, mem_line, mem_line]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa using congrArg (coordinates e) hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa using congrArg (coordinates e).symm hc⟩

lemma space_perp (e : ι ≃ η) (u : Vec ι) :
    space e (perp u) = perp (coordinates e u) := by
  ext y
  rw [mem_space]
  change dot u ((coordinates e).symm y) = 0 ↔ dot (coordinates e u) y = 0
  rw [← coordinates_dot e u ((coordinates e).symm y)]
  simp

omit [Fintype ι] [Fintype η] in
lemma space_trans {μ : Type*} (e : ι ≃ η) (f : η ≃ μ)
    (A : Submodule F2 (Vec ι)) : space f (space e A) = space (e.trans f) A := by
  ext y
  simp only [mem_space]
  rfl

omit [Fintype ι] [Fintype η] in
lemma tensorSpace_bot_left (C : Submodule F2 (Vec η)) :
    tensorSpace (⊥ : Submodule F2 (Vec ι)) C = ⊥ := by
  apply le_antisymm
  swap
  · exact bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨xy, rfl⟩
  have ha : (xy.1 : Vec ι) = 0 := (Submodule.mem_bot F2).mp xy.1.property
  simp [ha]

def tensorRight (q : Vec η) : Vec ι →ₗ[F2] Vec (ι × η) where
  toFun x := tensor x q
  map_add' := fun x y => tensor_add_left x y q
  map_smul' := fun c x => tensor_smul_left c x q

omit [Fintype ι] [Fintype η] in
lemma tensorSpace_line_right (A : Submodule F2 (Vec ι)) (q : Vec η) :
    tensorSpace A (line q) = A.map (tensorRight q) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, c⟩, rfl⟩
    obtain ⟨t, ht⟩ := (mem_line q c).mp c.property
    change tensor (a : Vec ι) (c : Vec η) ∈ _
    rw [← ht, tensor_smul_right, ← tensor_smul_left]
    exact ⟨t • (a : Vec ι), A.smul_mem t a.property, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    exact tensor_mem A (line q) a ha q ((mem_line q q).mpr ⟨1, by simp⟩)

omit [Fintype ι] [Fintype η] in
lemma mem_tensorSpace_line (A : Submodule F2 (Vec ι)) (q : Vec η) (x : Vec (ι × η)) :
    x ∈ tensorSpace A (line q) ↔ ∃ a ∈ A, tensor a q = x := by
  rw [tensorSpace_line_right]
  rfl

omit [Fintype ι] [Fintype η] in
lemma tensorSpace_line_line (p : Vec ι) (q : Vec η) :
    tensorSpace (line p) (line q) = line (tensor p q) := by
  ext x
  rw [mem_tensorSpace_line, mem_line]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨c, rfl⟩ := (mem_line p a).mp ha
    exact ⟨c, by simpa using hx⟩
  · rintro ⟨c, hc⟩
    exact ⟨c • p, (mem_line p _).mpr ⟨c, rfl⟩, by simpa using hc⟩

lemma orth_line (u : Vec ι) : orth (line u) = perp u := by
  ext x
  constructor
  · intro hx
    exact hx u ((mem_line u u).mpr ⟨1, by simp⟩)
  · intro hx a ha
    obtain ⟨c, rfl⟩ := (mem_line u a).mp ha
    rw [dot_smul_left, hx, mul_zero]

/-- The local outgoing Y sum is the perpendicular in the enlarged prefix. -/
theorem outgoing_perp (p : Vec ι) (t : Vec η)
    (hp : dot p p = 1) (ht : dot t t = 1) :
    label5 (perp p) (line p) t = perp (tensor p t) := by
  classical
  have he := stage_Y_outgoing_relative_perp (perp p) (line p) ⊤
    (decomposes_symm (line_decomposes_perp p hp)) (lineBasis p hp)
    (by intro i j; simpa using hp) t ht
  rw [tensorSpace_line_line, label3, tensorSpace_top_top, BinaryResiduals.residual,
    top_inf_eq, orth_line] at he
  exact he.symm

omit [Fintype ι] [Fintype η] [Fintype κ] in
lemma coordinates_tensor_product (e : ι ≃ η) (x : Vec ι) (q : Vec κ) :
    coordinates (e.prodCongr (Equiv.refl κ)) (tensor x q) = tensor (coordinates e x) q := by
  ext ij
  rfl

omit [Fintype ι] [Fintype η] [Fintype κ] in
lemma coordinates_tensor_assoc (x : Vec ι) (q : Vec η) (r : Vec κ) :
    coordinates (Equiv.prodAssoc ι η κ) (tensor (tensor x q) r) = tensor x (tensor q r) := by
  ext ijk
  simp [coordinates, tensor, mul_assoc]

omit [Fintype ι] [Fintype η] [Fintype κ] in
lemma space_tensor_line (e : ι ≃ η) (A : Submodule F2 (Vec ι)) (q : Vec κ) :
    space (e.prodCongr (Equiv.refl κ)) (tensorSpace A (line q)) =
      tensorSpace (space e A) (line q) := by
  ext x
  rw [mem_space, mem_tensorSpace_line, mem_tensorSpace_line]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨coordinates e a, ⟨a, ha, rfl⟩, ?_⟩
    have hh := congrArg (coordinates (e.prodCongr (Equiv.refl κ))) he
    simpa only [LinearEquiv.apply_symm_apply, coordinates_tensor_product] using hh
  · rintro ⟨a, ha, he⟩
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨b, hb, ?_⟩
    rw [← he]
    ext ij
    simp [coordinates, tensor]

omit [Fintype ι] [Fintype η] [Fintype κ] in
lemma space_assoc_line (A : Submodule F2 (Vec ι)) (q : Vec η) (r : Vec κ) :
    space (Equiv.prodAssoc ι η κ)
      (tensorSpace (tensorSpace A (line q)) (line r)) =
      tensorSpace A (line (tensor q r)) := by
  ext x
  rw [mem_space, mem_tensorSpace_line, mem_tensorSpace_line]
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨b, hb, rfl⟩ := (mem_tensorSpace_line A q a).mp ha
    refine ⟨b, hb, ?_⟩
    have hh := congrArg (coordinates (Equiv.prodAssoc ι η κ)) he
    simpa only [LinearEquiv.apply_symm_apply, coordinates_tensor_assoc] using hh
  · rintro ⟨a, ha, he⟩
    refine ⟨tensor a q, tensor_mem A (line q) a ha q
      ((mem_line q q).mpr ⟨1, by simp⟩), ?_⟩
    rw [← he]
    ext ijk
    simp [coordinates, tensor, mul_assoc]

omit [Fintype ι] [Fintype η] in
lemma space_symm_cancel (e : ι ≃ η) (A : Submodule F2 (Vec ι)) :
    space e.symm (space e A) = A := by
  ext x
  simp only [mem_space]
  change ((coordinates e).symm (coordinates e x) ∈ A) ↔ x ∈ A
  simp

omit [Fintype ι] [Fintype η] in
lemma space_unit_right [Unique η] (A : Submodule F2 (Vec ι)) :
    space (Equiv.prodUnique ι η) (tensorSpace A (line (characteristic : Vec η))) = A := by
  ext y
  rw [mem_space, mem_tensorSpace_line]
  constructor
  · rintro ⟨a, ha, he⟩
    have h : a = y := by
      funext i
      have hh := congrFun he (i, default)
      simpa [tensor, characteristic, coordinates] using hh
    simpa [h] using ha
  · intro hy
    refine ⟨y, hy, ?_⟩
    ext ij
    simp [tensor, characteristic, coordinates]

omit [Fintype ι] [Fintype η] in
lemma coordinates_unit_left [Unique ι] (t : Vec η) :
    coordinates (Equiv.uniqueProd η ι) (tensor (characteristic : Vec ι) t) = t := by
  ext i
  simp [coordinates, tensor, characteristic]

/-- Append the active coordinate to the prefix; the inverse is `Fin.init` and last. -/
def appendCoordinates (k h : ℕ) : ((Fin k → Fin h) × Fin h) ≃ (Fin (k + 1) → Fin h) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin h))

/-- Factor the next active coordinate from the future; the inverse is head and `Fin.tail`. -/
def prependCoordinates (k h : ℕ) : (Fin h × (Fin k → Fin h)) ≃ (Fin (k + 1) → Fin h) :=
  Fin.consEquiv (fun _ : Fin (k + 1) => Fin h)

lemma append_tripleTensor (k h : ℕ) (s : Fin (k + 1) → Finset (Fin h)) :
    coordinates (appendCoordinates k h)
      (tensor (tripleTensor k h (fun i => s i.castSucc)) (indicator (s (Fin.last k)))) =
      tripleTensor (k + 1) h s := by
  ext x
  simp [coordinates, appendCoordinates, tensor, tripleTensor, tensorFamily,
    Fin.prod_univ_castSucc, Fin.init]

lemma prepend_tripleTensor (k h : ℕ) (s : Fin (k + 1) → Finset (Fin h)) :
    coordinates (prependCoordinates k h)
      (tensor (indicator (s 0)) (tripleTensor k h (fun i => s i.succ))) =
      tripleTensor (k + 1) h s := by
  ext x
  simp [coordinates, prependCoordinates, tensor, tripleTensor, tensorFamily,
    Fin.prod_univ_succ, Fin.tail]

/-- The prefix outgoing label becomes the exact successor prefix perpendicular. -/
theorem prefix_outgoing_perp (k h : ℕ) (s : Fin (k + 1) → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) :
    space (appendCoordinates k h)
      (label5 (perp (tripleTensor k h (fun i => s i.castSucc)))
        (line (tripleTensor k h (fun i => s i.castSucc))) (indicator (s (Fin.last k)))) =
      perp (tripleTensor (k + 1) h s) := by
  rw [outgoing_perp _ _ (tripleTensor_norm k h _ (fun i => hs i.castSucc))
    (triple_indicator_norm _ (hs (Fin.last k))), space_perp, append_tripleTensor]

/-- The future unit line factors into the next active triple and remaining future. -/
theorem future_line_factor (k h : ℕ) (s : Fin (k + 1) → Finset (Fin h)) :
    space (prependCoordinates k h)
      (tensorSpace (line (indicator (s 0))) (line (tripleTensor k h (fun i => s i.succ)))) =
      line (tripleTensor (k + 1) h s) := by
  rw [tensorSpace_line_line, space_line, prepend_tripleTensor]

section ThreeStages
variable {h : ℕ}

abbrev Axis (h : ℕ) := Fin h
abbrev EmptyCoordinates (h : ℕ) := Fin 0 → Fin h
abbrev Cube (h : ℕ) := (Axis h × Axis h) × Axis h
abbrev PhysicalCoordinates (h : ℕ) := Fin 3 → Fin h

def emptyVector (h : ℕ) : Vec (EmptyCoordinates h) :=
  tripleTensor 0 h (fun i => Fin.elim0 i)

@[simp] lemma emptyVector_characteristic : emptyVector h = characteristic :=
  tripleTensor_zero_characteristic h _
@[simp] lemma emptyVector_norm : dot (emptyVector h) (emptyVector h) = 1 :=
  tripleTensor_norm 0 h _ (by intro i; exact Fin.elim0 i)
@[simp] lemma emptyVector_line : line (emptyVector h) = ⊤ := tripleTensor_zero_line h _
@[simp] lemma emptyVector_perp : perp (emptyVector h) = ⊥ := tripleTensor_zero_perp h _

/-- Literal empty-prefix/current/future coordinates at the first stage. -/
def firstCoordinates (h : ℕ) :
    ((EmptyCoordinates h × Axis h) × (Axis h × Axis h)) ≃ Cube h :=
  ((Equiv.uniqueProd (Axis h) (EmptyCoordinates h)).prodCongr
    (Equiv.refl (Axis h × Axis h))).trans (Equiv.prodAssoc (Axis h) (Axis h) (Axis h)).symm

/-- Literal prefix/current/empty-future coordinates at the last stage. -/
def lastCoordinates (h : ℕ) : Cube h × EmptyCoordinates h ≃ Cube h :=
  Equiv.prodUnique (Cube h) (EmptyCoordinates h)

def tripleCoordinates (h : ℕ) : Cube h ≃ PhysicalCoordinates h where
  toFun xyz := ![xyz.1.1, xyz.1.2, xyz.2]
  invFun x := ((x 0, x 1), x 2)
  left_inv xyz := by cases xyz; rfl
  right_inv x := by funext i; fin_cases i <;> rfl

def fullVector (t : Fin 3 → Vec (Axis h)) : Vec (Cube h) := tensor (tensor (t 0) (t 1)) (t 2)

/-- The three incoming physical X labels before transport to function coordinates. -/
def incomingX (t : Fin 3 → Vec (Axis h)) : Fin 3 → Submodule F2 (Vec (Cube h))
  | 0 => space (firstCoordinates h)
      (tensorSpace (tensorSpace ⊤ (line (t 0))) (line (tensor (t 1) (t 2))))
  | 1 => tensorSpace (tensorSpace ⊤ (line (t 1))) (line (t 2))
  | 2 => space (lastCoordinates h)
      (tensorSpace (tensorSpace ⊤ (line (t 2))) (line (emptyVector h)))

def incomingY (t : Fin 3 → Vec (Axis h)) : Fin 3 → Submodule F2 (Vec (Cube h))
  | 0 => space (firstCoordinates h)
      (tensorSpace (tensorSpace (perp (emptyVector h)) (line (t 0)))
        (line (tensor (t 1) (t 2))))
  | 1 => tensorSpace (tensorSpace (perp (t 0)) (line (t 1))) (line (t 2))
  | 2 => space (lastCoordinates h)
      (tensorSpace (tensorSpace (perp (tensor (t 0) (t 1))) (line (t 2)))
        (line (emptyVector h)))

/-- The three outgoing X labels, retaining the actual current and future factors. -/
def outgoingX (t : Fin 3 → Vec (Axis h)) : Fin 3 → Submodule F2 (Vec (Cube h))
  | 0 => space (firstCoordinates h)
      (tensorSpace (label3 (η := Axis h) (⊤ : Submodule F2 (Vec (EmptyCoordinates h))))
        (line (tensor (t 1) (t 2))))
  | 1 => tensorSpace (label3 (η := Axis h) (⊤ : Submodule F2 (Vec (Axis h)))) (line (t 2))
  | 2 => space (lastCoordinates h)
      (tensorSpace (label3 (η := Axis h) (⊤ : Submodule F2 (Vec (Axis h × Axis h))))
        (line (emptyVector h)))

def outgoingY (t : Fin 3 → Vec (Axis h)) : Fin 3 → Submodule F2 (Vec (Cube h))
  | 0 => space (firstCoordinates h)
      (tensorSpace (label5 (perp (emptyVector h)) (line (emptyVector h)) (t 0))
        (line (tensor (t 1) (t 2))))
  | 1 => tensorSpace (label5 (perp (t 0)) (line (t 0)) (t 1)) (line (t 2))
  | 2 => space (lastCoordinates h)
      (tensorSpace (label5 (perp (tensor (t 0) (t 1))) (line (tensor (t 0) (t 1))) (t 2))
        (line (emptyVector h)))

lemma first_space_tensor (A : Submodule F2 (Vec (EmptyCoordinates h × Axis h)))
    (q : Vec (Axis h × Axis h)) :
    space (firstCoordinates h) (tensorSpace A (line q)) =
      space (Equiv.prodAssoc (Axis h) (Axis h) (Axis h)).symm
        (tensorSpace (space (Equiv.uniqueProd (Axis h) (EmptyCoordinates h)) A) (line q)) := by
  rw [firstCoordinates, ← space_trans, space_tensor_line]

theorem source_X (t : Fin 3 → Vec (Axis h)) : incomingX t 0 = line (fullVector t) := by
  classical
  change space (firstCoordinates h) (tensorSpace (tensorSpace ⊤ (line (t 0)))
    (line (tensor (t 1) (t 2)))) = _
  rw [← emptyVector_line (h := h), tensorSpace_line_line, first_space_tensor, space_line,
    emptyVector_characteristic, coordinates_unit_left, tensorSpace_line_line, space_line]
  congr 1
  ext xyz
  simp [coordinates, tensor, fullVector, mul_assoc]

theorem source_Y (t : Fin 3 → Vec (Axis h)) : incomingY t 0 = ⊥ := by
  simp only [incomingY, emptyVector_perp, tensorSpace_bot_left, space_bot]

theorem boundary_0_X (t : Fin 3 → Vec (Axis h)) : outgoingX t 0 = incomingX t 1 := by
  classical
  change space (firstCoordinates h) (tensorSpace (label3 ⊤)
    (line (tensor (t 1) (t 2)))) = _
  rw [label3, tensorSpace_top_top, first_space_tensor, space_top]
  have he := space_assoc_line (⊤ : Submodule F2 (Vec (Axis h))) (t 1) (t 2)
  have hh := congrArg (space (Equiv.prodAssoc (Axis h) (Axis h) (Axis h)).symm) he
  simpa only [space_symm_cancel, incomingX] using hh.symm

theorem boundary_0_Y (t : Fin 3 → Vec (Axis h)) (ht : ∀ i, dot (t i) (t i) = 1) :
    outgoingY t 0 = incomingY t 1 := by
  classical
  change space (firstCoordinates h) (tensorSpace
    (label5 (perp (emptyVector h)) (line (emptyVector h)) (t 0))
    (line (tensor (t 1) (t 2)))) = _
  rw [outgoing_perp _ _ emptyVector_norm (ht 0), first_space_tensor,
    space_perp, emptyVector_characteristic, coordinates_unit_left]
  have he := space_assoc_line (perp (t 0)) (t 1) (t 2)
  have hh := congrArg (space (Equiv.prodAssoc (Axis h) (Axis h) (Axis h)).symm) he
  simpa only [space_symm_cancel, incomingY] using hh.symm

theorem boundary_1_X (t : Fin 3 → Vec (Axis h)) : outgoingX t 1 = incomingX t 2 := by
  classical
  simp only [outgoingX, incomingX, label3, tensorSpace_top_top, emptyVector_characteristic,
    lastCoordinates, space_unit_right]

theorem boundary_1_Y (t : Fin 3 → Vec (Axis h)) (ht : ∀ i, dot (t i) (t i) = 1) :
    outgoingY t 1 = incomingY t 2 := by
  classical
  simp only [outgoingY, incomingY, outgoing_perp _ _ (ht 0) (ht 1),
    emptyVector_characteristic, lastCoordinates, space_unit_right]

theorem sink_X (t : Fin 3 → Vec (Axis h)) : outgoingX t 2 = ⊤ := by
  classical
  simp only [outgoingX, label3, tensorSpace_top_top, emptyVector_characteristic,
    lastCoordinates, space_unit_right]

theorem sink_Y (t : Fin 3 → Vec (Axis h)) (ht : ∀ i, dot (t i) (t i) = 1) :
    outgoingY t 2 = perp (fullVector t) := by
  classical
  have hp : dot (tensor (t 0) (t 1)) (tensor (t 0) (t 1)) = 1 := by
    rw [dot_tensor, ht 0, ht 1, one_mul]
  simp only [outgoingY, outgoing_perp _ _ hp (ht 2), emptyVector_characteristic,
    lastCoordinates, space_unit_right, fullVector]

def physicalIncomingX (t : Fin 3 → Vec (Axis h)) (j : Fin 3) :=
  space (tripleCoordinates h) (incomingX t j)
def physicalIncomingY (t : Fin 3 → Vec (Axis h)) (j : Fin 3) :=
  space (tripleCoordinates h) (incomingY t j)
def physicalOutgoingX (t : Fin 3 → Vec (Axis h)) (j : Fin 3) :=
  space (tripleCoordinates h) (outgoingX t j)
def physicalOutgoingY (t : Fin 3 → Vec (Axis h)) (j : Fin 3) :=
  space (tripleCoordinates h) (outgoingY t j)

/-- Both bank labels match between consecutive stages in one fixed coordinate space. -/
theorem consecutive_boundaries (t : Fin 3 → Vec (Axis h))
    (ht : ∀ i, dot (t i) (t i) = 1) (j : Fin 2) :
    physicalOutgoingX t j.castSucc = physicalIncomingX t j.succ ∧
    physicalOutgoingY t j.castSucc = physicalIncomingY t j.succ := by
  fin_cases j
  · exact ⟨congrArg (space (tripleCoordinates h)) (boundary_0_X t),
      congrArg (space (tripleCoordinates h)) (boundary_0_Y t ht)⟩
  · exact ⟨congrArg (space (tripleCoordinates h)) (boundary_1_X t),
      congrArg (space (tripleCoordinates h)) (boundary_1_Y t ht)⟩

def directions (s : Fin 3 → Finset (Fin h)) : Fin 3 → Vec (Axis h) := fun i => indicator (s i)

/-- The displayed product coordinates and the finite-function tensor are proved equal. -/
lemma physical_full_tripleTensor (s : Fin 3 → Finset (Fin h)) :
    coordinates (tripleCoordinates h) (fullVector (directions s)) = tripleTensor 3 h s := by
  ext x
  simp [coordinates, tripleCoordinates, fullVector, directions, tensor,
    tripleTensor, tensorFamily, Fin.prod_univ_succ, mul_assoc]

lemma directions_norm (s : Fin 3 → Finset (Fin h)) (hs : ∀ i, (s i).card = 3) :
    ∀ i, dot (directions s i) (directions s i) = 1 :=
  fun i => triple_indicator_norm (s i) (hs i)

theorem physical_source (s : Fin 3 → Finset (Fin h)) :
    physicalIncomingX (directions s) 0 = line (tripleTensor 3 h s) ∧
    physicalIncomingY (directions s) 0 = ⊥ := by
  constructor
  · rw [physicalIncomingX, source_X, space_line, physical_full_tripleTensor]
  · rw [physicalIncomingY, source_Y, space_bot]

theorem physical_sink (s : Fin 3 → Finset (Fin h)) (hs : ∀ i, (s i).card = 3) :
    physicalOutgoingX (directions s) 2 = ⊤ ∧
    physicalOutgoingY (directions s) 2 = perp (tripleTensor 3 h s) := by
  constructor
  · rw [physicalOutgoingX, sink_X, space_top]
  · rw [physicalOutgoingY, sink_Y _ (directions_norm s hs), space_perp,
      physical_full_tripleTensor]

/-- Complete bank-boundary certificate for one actual triple profile. -/
theorem triple_stage_boundaries (s : Fin 3 → Finset (Fin h)) (hs : ∀ i, (s i).card = 3) :
    (physicalIncomingX (directions s) 0 = line (tripleTensor 3 h s) ∧
      physicalIncomingY (directions s) 0 = ⊥) ∧
    (∀ j : Fin 2,
      physicalOutgoingX (directions s) j.castSucc = physicalIncomingX (directions s) j.succ ∧
      physicalOutgoingY (directions s) j.castSucc = physicalIncomingY (directions s) j.succ) ∧
    (physicalOutgoingX (directions s) 2 = ⊤ ∧
      physicalOutgoingY (directions s) 2 = perp (tripleTensor 3 h s)) :=
  ⟨physical_source s, fun j => consecutive_boundaries _ (directions_norm s hs) j,
    physical_sink s hs⟩

/-- Any positive prefix/future tensor factor has the concrete residual basis already proved.
    The zero-length case has the explicit empty basis in `emptyTripleComplementBasis`. -/
theorem factor_complement_basis (k : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) (hk : 1 ≤ k) (hh : 7 ≤ h) :
    ∃ p, ∃ b : Basis (OneIndex p) F2 (perp (tripleTensor k h s)),
      (∀ j, (b j : Vec (Fin k → Fin h)) =
        transvection (unit p + tripleTensor k h s) (unit j.val)) ∧
      (∀ i j, dot (b i : Vec (Fin k → Fin h)) (b j : Vec (Fin k → Fin h)) =
        if i = j then 1 else 0) :=
  tripleTensor_complement_basis k h s hs hk hh

/-- Column and three-factor binary coordinates have exactly the claimed ambient dimension. -/
lemma column_coordinate_card (f h : ℕ) :
    Fintype.card (Fin f × PhysicalCoordinates h) = f * h ^ 3 := by simp [PhysicalCoordinates]

/-- A fixed finite coordinate identification; no external row-major ordering is assumed. -/
def columnCoordinates (f h : ℕ) : (Fin f × PhysicalCoordinates h) ≃ Fin (f * h ^ 3) :=
  (Fintype.equivFin _).trans (finCongr (column_coordinate_card f h))

def addressCoordinates (f h : ℕ) : (Fin f × PhysicalCoordinates h) ≃ Fin (h ^ 3 * f) :=
  (columnCoordinates f h).trans (finCongr (Nat.mul_comm f (h ^ 3)))

end ThreeStages

end
end ExactFourierCircuits.StageFrames
