import BinaryComplement
import BinaryTensor

set_option autoImplicit false

/- Concrete coordinate-space versions of the orthogonal residual decompositions
   in network.tex. The gate chronology and complete network remain separate. -/
namespace ExactFourierCircuits.BinaryResiduals
open BinaryFrames BinaryComplement BinaryTensor Module
open scoped BigOperators
noncomputable section

variable {ι η κ α : Type*} [Fintype ι] [Fintype η]

/-- Orthogonality between two actual coordinate subspaces. -/
def Orthogonal (A B : Submodule F2 (Vec ι)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, dot x y = 0

/-- A subspace has no radical for the restricted dot product. -/
def Nondegenerate (A : Submodule F2 (Vec ι)) : Prop :=
  ∀ x ∈ A, (∀ a ∈ A, dot a x = 0) → x = 0

def orth (A : Submodule F2 (Vec ι)) : Submodule F2 (Vec ι) where
  carrier := {x | ∀ a ∈ A, dot a x = 0}
  zero_mem' := by intro a ha; simp [dot]
  add_mem' := by
    intro x y hx hy a ha
    rw [dot_add_right, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro c x hx a ha
    rw [dot_smul_right, hx a ha, mul_zero]

/-- The orthogonal residual of the smaller label inside the larger one. -/
def residual (A S : Submodule F2 (Vec ι)) := S ⊓ orth A

def Decomposes (A B S : Submodule F2 (Vec ι)) : Prop :=
  A ⊔ B = S ∧ Orthogonal A B

lemma orthogonal_symm {A B : Submodule F2 (Vec ι)} (h : Orthogonal A B) :
    Orthogonal B A := by
  intro y hy x hx
  rw [dot_comm]
  exact h x hx y hy

lemma orthogonal_mono {A B C D : Submodule F2 (Vec ι)}
    (h : Orthogonal A B) (hCA : C ≤ A) (hDB : D ≤ B) : Orthogonal C D := by
  intro x hx y hy
  exact h x (hCA hx) y (hDB hy)

lemma orthogonal_sup_left {A B C : Submodule F2 (Vec ι)}
    (hA : Orthogonal A C) (hB : Orthogonal B C) : Orthogonal (A ⊔ B) C := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [dot_add_left, hA a ha y hy, hB b hb y hy, add_zero]

lemma orthogonal_sup_right {A B C : Submodule F2 (Vec ι)}
    (hB : Orthogonal A B) (hC : Orthogonal A C) : Orthogonal A (B ⊔ C) :=
  orthogonal_symm (orthogonal_sup_left (orthogonal_symm hB) (orthogonal_symm hC))

lemma decomposes_symm {A B S : Submodule F2 (Vec ι)} (h : Decomposes A B S) :
    Decomposes B A S := ⟨sup_comm A B ▸ h.1, orthogonal_symm h.2⟩

lemma decomposes_nested {A B S : Submodule F2 (Vec ι)} (h : Decomposes A B S) : A ≤ S :=
  h.1 ▸ le_sup_left

/-- Orthogonal sums give the claimed residual whenever the smaller label is nondegenerate. -/
theorem residual_of_decomposes {A B S : Submodule F2 (Vec ι)}
    (h : Decomposes A B S) (hA : Nondegenerate A) : residual A S = B := by
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ A ⊔ B := h.1 ▸ hx.1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxS
    have ha0 : a = 0 := hA a ha (by
      intro z hz
      have hz0 := hx.2 z hz
      rw [← hab, dot_add_right, h.2 z hz b hb, add_zero] at hz0
      exact hz0)
    rw [ha0, zero_add] at hab
    exact hab ▸ hb
  · intro x hx
    have hxAB : x ∈ A ⊔ B := (show B ≤ A ⊔ B from le_sup_right) hx
    refine ⟨h.1 ▸ hxAB, ?_⟩
    exact fun a ha => h.2 a ha x hx

lemma orthogonal_span {s t : Set (Vec ι)}
    (h : ∀ x ∈ s, ∀ y ∈ t, dot x y = 0) :
    Orthogonal (Submodule.span F2 s) (Submodule.span F2 t) := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [dot]
    | add y z hy hz iy iz => rw [dot_add_right, iy, iz, add_zero]
    | smul c y hy iy => rw [dot_smul_right, iy, mul_zero]
  | zero => simp [dot]
  | add x z hx hz ix iz => rw [dot_add_left, ix, iz, add_zero]
  | smul c x hx ix => rw [dot_smul_left, ix, mul_zero]


lemma nondegenerate_bot : Nondegenerate (⊥ : Submodule F2 (Vec ι)) := by
  intro x hx hzero
  simpa using hx

lemma nondegenerate_sup {A B : Submodule F2 (Vec ι)}
    (hA : Nondegenerate A) (hB : Nondegenerate B) (hAB : Orthogonal A B) :
    Nondegenerate (A ⊔ B) := by
  intro x hx hzero
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hx
  have ha0 : a = 0 := hA a ha (by
    intro z hz
    have hz0 := hzero z (Submodule.mem_sup_left hz)
    rw [← he, dot_add_right, hAB z hz b hb, add_zero] at hz0
    exact hz0)
  rw [ha0, zero_add] at he
  have hb0 : b = 0 := hB b hb (by
    intro z hz
    rw [he]
    exact hzero z (Submodule.mem_sup_right hz))
  exact he.symm.trans hb0

section ResidualBases
variable [Fintype κ] [DecidableEq κ]

/-- Transporting the displayed residual basis gives a basis of the actual orthogonal residual. -/
def residualBasis (A B S : Submodule F2 (Vec ι)) (h : Decomposes A B S)
    (hA : Nondegenerate A) (b : Basis κ F2 B) : Basis κ F2 (residual A S) :=
  b.map (LinearEquiv.ofEq _ _ (residual_of_decomposes h hA).symm)

omit [Fintype κ] [DecidableEq κ] in
@[simp] lemma residualBasis_apply (A B S : Submodule F2 (Vec ι)) (h : Decomposes A B S)
    (hA : Nondegenerate A) (b : Basis κ F2 B) (i : κ) :
    (residualBasis A B S h hA b i : Vec ι) = (b i : Vec ι) := by simp [residualBasis]

omit [Fintype κ] in
lemma residualBasis_orthonormal (A B S : Submodule F2 (Vec ι)) (h : Decomposes A B S)
    (hA : Nondegenerate A) (b : Basis κ F2 B)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0) (i j : κ) :
    dot (residualBasis A B S h hA b i : Vec ι)
      (residualBasis A B S h hA b j : Vec ι) = if i = j then 1 else 0 := by
  rw [residualBasis_apply, residualBasis_apply]
  exact hb i j

end ResidualBases

section Frames
variable [Fintype κ] [DecidableEq κ]

lemma dot_frame_coeff (z : κ → Vec ι)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0)
    (c : κ → F2) (j : κ) : dot (z j) (∑ i, c i • z i) = c j := by
  rw [dot_finset_sum_right]
  simp only [dot_smul_right, hz]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Ne.symm hij]
  · simp

lemma orthonormal_linearIndependent (z : κ → Vec ι)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) :
    LinearIndependent F2 z := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := dot_frame_coeff z hz c j
  rw [hc] at h
  simpa [dot] using h.symm

def frameBasis (z : κ → Vec ι)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) :
    Basis κ F2 (Submodule.span F2 (Set.range z)) :=
  Basis.span (orthonormal_linearIndependent z hz)

@[simp] lemma frameBasis_apply (z : κ → Vec ι)
    (hz : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) (i : κ) :
    (frameBasis z hz i : Vec ι) = z i := by simp [frameBasis]

theorem basis_nondegenerate (A : Submodule F2 (Vec ι)) (b : Basis κ F2 A)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0) :
    Nondegenerate A := by
  intro x hx hzero
  have he : (∑ i, b.repr ⟨x, hx⟩ i • (b i : Vec ι)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun a : A => (a : Vec ι)) (b.sum_repr ⟨x, hx⟩)
  have hc (j : κ) : b.repr ⟨x, hx⟩ j = 0 := by
    have h := dot_frame_coeff (fun i => (b i : Vec ι)) hb (b.repr ⟨x, hx⟩) j
    rw [he, hzero _ (b j).property] at h
    exact h.symm
  rw [← he]
  simp [hc]

end Frames


omit [Fintype ι] in
lemma vec_add_self (x : Vec ι) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)


section FiniteBases
variable [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]

omit [Fintype ι] [DecidableEq κ] in
lemma basis_span_coe (A : Submodule F2 (Vec ι)) (b : Basis κ F2 A) :
    Submodule.span F2 (Set.range (fun i => (b i : Vec ι))) = A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (b i).property
  · intro x hx
    have he : (∑ i, b.repr ⟨x, hx⟩ i • (b i : Vec ι)) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun a : A => (a : Vec ι)) (b.sum_repr ⟨x, hx⟩)
    rw [← he]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩

omit [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] in
lemma sumFamily_span (a : κ → Vec ι) (b : α → Vec ι) :
    Submodule.span F2 (Set.range (Sum.elim a b)) =
      Submodule.span F2 (Set.range a) ⊔ Submodule.span F2 (Set.range b) := by
  have hr : Set.range (Sum.elim a b) = Set.range a ∪ Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  rw [hr, Submodule.span_union]

omit [Fintype κ] [Fintype α] in
lemma sumFamily_orthonormal (a : κ → Vec ι) (b : α → Vec ι)
    (ha : ∀ i j, dot (a i) (a j) = if i = j then 1 else 0)
    (hb : ∀ i j, dot (b i) (b j) = if i = j then 1 else 0)
    (hab : ∀ i j, dot (a i) (b j) = 0) (i j : κ ⊕ α) :
    dot (Sum.elim a b i) (Sum.elim a b j) = if i = j then 1 else 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa using ha i j
    | inr j => simpa using hab i j
  | inr i =>
    cases j with
    | inl j => simpa [dot_comm] using hab j i
    | inr j => simpa using hb i j

/-- Joining two orthogonal frames gives an actual orthonormal basis of their sum. -/
def sumBasis (A B : Submodule F2 (Vec ι)) (a : Basis κ F2 A) (b : Basis α F2 B)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0)
    (hab : Orthogonal A B) : Basis (κ ⊕ α) F2 ↥(A ⊔ B) :=
  (frameBasis (Sum.elim (fun i => (a i : Vec ι)) (fun j => (b j : Vec ι)))
    (sumFamily_orthonormal (fun i => (a i : Vec ι)) (fun j => (b j : Vec ι)) ha hb (fun i j => hab _ (a i).property _ (b j).property))).map
    (LinearEquiv.ofEq _ _ (by rw [sumFamily_span, basis_span_coe, basis_span_coe]))

@[simp] lemma sumBasis_apply (A B : Submodule F2 (Vec ι)) (a : Basis κ F2 A) (b : Basis α F2 B)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0)
    (hab : Orthogonal A B) (i : κ ⊕ α) :
    (sumBasis A B a b ha hb hab i : Vec ι) =
      Sum.elim (fun i => (a i : Vec ι)) (fun j => (b j : Vec ι)) i := by simp [sumBasis]

lemma sumBasis_orthonormal (A B : Submodule F2 (Vec ι)) (a : Basis κ F2 A) (b : Basis α F2 B)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0)
    (hab : Orthogonal A B) (i j : κ ⊕ α) :
    dot (sumBasis A B a b ha hb hab i : Vec ι) (sumBasis A B a b ha hb hab j : Vec ι) =
      if i = j then 1 else 0 := by
  rw [sumBasis_apply, sumBasis_apply]
  exact sumFamily_orthonormal (fun i => (a i : Vec ι)) (fun j => (b j : Vec ι)) ha hb (fun i j => hab _ (a i).property _ (b j).property) i j

end FiniteBases


section FullBases
variable [DecidableEq ι]

def fullBasis : Basis ι F2 (↥(⊤ : Submodule F2 (Vec ι))) :=
  (Pi.basisFun F2 ι).map (Submodule.topEquiv).symm

@[simp] lemma fullBasis_apply (i : ι) : (fullBasis i : Vec ι) = unit i := by
  simp only [fullBasis, Basis.map_apply, Submodule.topEquiv,
    Pi.basisFun_apply]
  change Pi.single i (1 : F2) = unit i
  ext j
  simp [Pi.single_apply, unit, eq_comm]

lemma fullBasis_orthonormal (i j : ι) :
    dot (fullBasis i : Vec ι) (fullBasis j : Vec ι) = if i = j then 1 else 0 := by
  rw [fullBasis_apply, fullBasis_apply, dot_units]

lemma full_nondegenerate : Nondegenerate (⊤ : Submodule F2 (Vec ι)) :=
  basis_nondegenerate _ fullBasis fullBasis_orthonormal

end FullBases

section Lines
variable [DecidableEq ι]

def line (u : Vec ι) : Submodule F2 (Vec ι) := Submodule.span F2 {u}

omit [Fintype ι] [DecidableEq ι] in
lemma mem_line (u x : Vec ι) : x ∈ line u ↔ ∃ c : F2, c • u = x :=
  Submodule.mem_span_singleton

omit [DecidableEq ι] in
lemma line_perp_orthogonal (u : Vec ι) : Orthogonal (line u) (perp u) := by
  intro a ha x hx
  obtain ⟨c, rfl⟩ := (mem_line u a).mp ha
  rw [dot_smul_left, hx, mul_zero]

omit [DecidableEq ι] in
/-- Every unit line has its exact orthogonal-complement decomposition. -/
theorem line_decomposes_perp (u : Vec ι) (hu : dot u u = 1) :
    Decomposes (line u) (perp u) ⊤ := by
  refine ⟨?_, line_perp_orthogonal u⟩
  apply top_unique
  intro x hx
  let c := dot u x
  have hr : x + c • u ∈ perp u := by
    change dot u (x + c • u) = 0
    rw [dot_add_right, dot_smul_right, hu, mul_one]
    exact CharTwo.add_self_eq_zero c
  apply Submodule.mem_sup.mpr
  refine ⟨c • u, (mem_line u _).mpr ⟨c, rfl⟩, x + c • u, hr, ?_⟩
  calc
    _ = x + (c • u + c • u) := by abel
    _ = x := by rw [vec_add_self, add_zero]

omit [DecidableEq ι] in
/-- This is the neighboring-triple split used specifically on side edge 2→5. -/
theorem pair_decomposes_perp (u y : Vec ι) (hu : dot u u = 1)
    (huy : dot u y = 0) : Decomposes (line u) (pairPerp u y) (perp y) := by
  refine ⟨?_, orthogonal_mono (line_perp_orthogonal u) le_rfl inf_le_left⟩
  apply le_antisymm
  · apply sup_le
    · intro a ha
      obtain ⟨c, rfl⟩ := (mem_line u a).mp ha
      change dot y (c • u) = 0
      rw [dot_smul_right, dot_comm y u, huy, mul_zero]
    · exact inf_le_right
  · intro x hx
    let c := dot u x
    have hr : x + c • u ∈ pairPerp u y := by
      constructor
      · change dot u (x + c • u) = 0
        rw [dot_add_right, dot_smul_right, hu, mul_one]
        exact CharTwo.add_self_eq_zero c
      · change dot y (x + c • u) = 0
        rw [dot_add_right, dot_smul_right, dot_comm y u, huy, mul_zero, hx, add_zero]
    apply Submodule.mem_sup.mpr
    refine ⟨c • u, (mem_line u _).mpr ⟨c, rfl⟩, x + c • u, hr, ?_⟩
    calc
      _ = x + (c • u + c • u) := by abel
      _ = x := by rw [vec_add_self, add_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma constant_span (u : Vec ι) :
    Submodule.span F2 (Set.range (fun _ : Unit => u)) = line u := by
  congr 1
  ext x
  simp

def lineBasis (u : Vec ι) (hu : dot u u = 1) : Basis Unit F2 (line u) :=
  (frameBasis (fun _ : Unit => u) (by intro i j; simpa using hu)).map
    (LinearEquiv.ofEq _ _ (constant_span u))

omit [DecidableEq ι] in
@[simp] lemma lineBasis_apply (u : Vec ι) (hu : dot u u = 1) (i : Unit) :
    (lineBasis u hu i : Vec ι) = u := by simp [lineBasis]

omit [DecidableEq ι] in
lemma line_nondegenerate (u : Vec ι) (hu : dot u u = 1) : Nondegenerate (line u) := by
  apply basis_nondegenerate _ (lineBasis u hu)
  intro i j
  simpa using hu

lemma perp_nondegenerate (u : Vec ι) (p : ι) (hu : dot u u = 1) (hp : u p = 0) :
    Nondegenerate (perp u) :=
  basis_nondegenerate _ (oneComplementBasis u p hu hp)
    (oneComplementBasis_orthonormal u p hu hp)

lemma pairPerp_nondegenerate (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0) :
    Nondegenerate (pairPerp u y) :=
  basis_nondegenerate _ (twoComplementBasis u y p q hu hy huy hp hqp hq)
    (twoComplementBasis_orthonormal u y p q hu hy huy hp hqp hq)

end Lines

section Tensors
variable [DecidableEq ι] [DecidableEq η]

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_add_left (x x' : Vec ι) (y : Vec η) :
    tensor (x + x') y = tensor x y + tensor x' y := by ext ij; simp [tensor, add_mul]
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_add_right (x : Vec ι) (y y' : Vec η) :
    tensor x (y + y') = tensor x y + tensor x y' := by ext ij; simp [tensor, mul_add]
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_smul_left (c : F2) (x : Vec ι) (y : Vec η) :
    tensor (c • x) y = c • tensor x y := by ext ij; simp [tensor, mul_assoc]
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_smul_right (c : F2) (x : Vec ι) (y : Vec η) :
    tensor x (c • y) = c • tensor x y := by ext ij; simp [tensor]; ring
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_zero_left (y : Vec η) : tensor (0 : Vec ι) y = 0 := by ext ij; simp [tensor]
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensor_zero_right (x : Vec ι) : tensor x (0 : Vec η) = 0 := by ext ij; simp [tensor]

/-- The concrete tensor subspace inside the product coordinate space. -/
def tensorSpace (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η)) :
    Submodule F2 (Vec (ι × η)) :=
  Submodule.span F2 (Set.range (fun xy : A × C => tensor (xy.1 : Vec ι) (xy.2 : Vec η)))

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensor_mem (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (x : Vec ι) (hx : x ∈ A) (y : Vec η) (hy : y ∈ C) : tensor x y ∈ tensorSpace A C :=
  Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_mono {A B : Submodule F2 (Vec ι)} {C D : Submodule F2 (Vec η)}
    (hAB : A ≤ B) (hCD : C ≤ D) : tensorSpace A C ≤ tensorSpace B D := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨a, c⟩, rfl⟩
  exact tensor_mem B D a (hAB a.property) c (hCD c.property)

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_sup_left (A B : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η)) :
    tensorSpace (A ⊔ B) C = tensorSpace A C ⊔ tensorSpace B C := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, c⟩, rfl⟩
    obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp a.property
    change tensor (a : Vec ι) (c : Vec η) ∈ _
    rw [← he, tensor_add_left]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (tensor_mem A C x hx c c.property))
      (Submodule.mem_sup_right (tensor_mem B C y hy c c.property))
  · exact sup_le (tensorSpace_mono le_sup_left le_rfl)
      (tensorSpace_mono le_sup_right le_rfl)

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_sup_right (A : Submodule F2 (Vec ι)) (C D : Submodule F2 (Vec η)) :
    tensorSpace A (C ⊔ D) = tensorSpace A C ⊔ tensorSpace A D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, c⟩, rfl⟩
    obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp c.property
    change tensor (a : Vec ι) (c : Vec η) ∈ _
    rw [← he, tensor_add_right]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (tensor_mem A C a a.property x hx))
      (Submodule.mem_sup_right (tensor_mem A D a a.property y hy))
  · exact sup_le (tensorSpace_mono le_rfl le_sup_left)
      (tensorSpace_mono le_rfl le_sup_right)

omit [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_orthogonal_left {A B : Submodule F2 (Vec ι)}
    (hAB : Orthogonal A B) (C D : Submodule F2 (Vec η)) :
    Orthogonal (tensorSpace A C) (tensorSpace B D) := by
  apply orthogonal_span
  rintro x ⟨⟨a, c⟩, rfl⟩ y ⟨⟨b, d⟩, rfl⟩
  rw [dot_tensor, hAB a a.property b b.property, zero_mul]

omit [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_orthogonal_right (A B : Submodule F2 (Vec ι))
    {C D : Submodule F2 (Vec η)} (hCD : Orthogonal C D) :
    Orthogonal (tensorSpace A C) (tensorSpace B D) := by
  apply orthogonal_span
  rintro x ⟨⟨a, c⟩, rfl⟩ y ⟨⟨b, d⟩, rfl⟩
  rw [dot_tensor, hCD c c.property d d.property, mul_zero]

omit [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_decomposes_left {A B S : Submodule F2 (Vec ι)}
    (h : Decomposes A B S) (C : Submodule F2 (Vec η)) :
    Decomposes (tensorSpace A C) (tensorSpace B C) (tensorSpace S C) :=
  ⟨by rw [← tensorSpace_sup_left, h.1], tensorSpace_orthogonal_left h.2 C C⟩

omit [DecidableEq ι] [DecidableEq η] in
lemma tensorSpace_decomposes_right (A : Submodule F2 (Vec ι))
    {C D S : Submodule F2 (Vec η)} (h : Decomposes C D S) :
    Decomposes (tensorSpace A C) (tensorSpace A D) (tensorSpace A S) :=
  ⟨by rw [← tensorSpace_sup_right, h.1], tensorSpace_orthogonal_right A A h.2⟩

omit [Fintype ι] [Fintype η] in
lemma tensor_unit (i : ι) (j : η) : tensor (unit i) (unit j) = unit (i, j) := by
  ext ij
  by_cases hi : ij.1 = i <;> by_cases hj : ij.2 = j <;>
    simp [tensor, unit, hi, hj, Prod.ext_iff]

lemma tensorSpace_top_top : tensorSpace (⊤ : Submodule F2 (Vec ι)) (⊤ : Submodule F2 (Vec η)) = ⊤ := by
  apply top_unique
  intro x hx
  rw [← unit_decomposition x]
  apply Submodule.sum_mem
  intro ij hij
  apply Submodule.smul_mem
  rw [← tensor_unit ij.1 ij.2]
  exact tensor_mem _ _ _ (Submodule.mem_top) _ (Submodule.mem_top)


omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensor_finset_sum_left (s : Finset κ) (x : κ → Vec ι) (y : Vec η) :
    tensor (∑ i ∈ s, x i) y = ∑ i ∈ s, tensor (x i) y := by
  ext ij
  simp [tensor, Finset.sum_apply, Finset.sum_mul]

omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensor_finset_sum_right (x : Vec ι) (s : Finset α) (y : α → Vec η) :
    tensor x (∑ j ∈ s, y j) = ∑ j ∈ s, tensor x (y j) := by
  ext ij
  simp [tensor, Finset.sum_apply, Finset.mul_sum]

section TensorBases
variable [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]

omit [DecidableEq κ] [DecidableEq α] in
omit [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η] in
lemma tensorBasis_span (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (a : Basis κ F2 A) (c : Basis α F2 C) :
    Submodule.span F2 (Set.range (fun ij : κ × α => tensor (a ij.1 : Vec ι) (c ij.2 : Vec η))) =
      tensorSpace A C := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨i,j⟩, rfl⟩
    exact tensor_mem A C _ (a i).property _ (c j).property
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨av, cv⟩, rfl⟩
    have heA : (∑ i, a.repr av i • (a i : Vec ι)) = av := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun x : A => (x : Vec ι)) (a.sum_repr av)
    have heC : (∑ j, c.repr cv j • (c j : Vec η)) = cv := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun x : C => (x : Vec η)) (c.sum_repr cv)
    change tensor (av : Vec ι) (cv : Vec η) ∈ _
    rw [← heA, tensor_finset_sum_left]
    apply Submodule.sum_mem
    intro i hi
    rw [tensor_smul_left]
    apply Submodule.smul_mem
    rw [← heC, tensor_finset_sum_right]
    apply Submodule.sum_mem
    intro j hj
    rw [tensor_smul_right]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(i,j), rfl⟩

/-- Tensor basis and spanning, with the right coordinate inside as in Python. -/
def tensorBasis (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (a : Basis κ F2 A) (c : Basis α F2 C)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hc : ∀ i j, dot (c i : Vec η) (c j : Vec η) = if i = j then 1 else 0) :
    Basis (κ × α) F2 (tensorSpace A C) :=
  (frameBasis (fun ij : κ × α => tensor (a ij.1 : Vec ι) (c ij.2 : Vec η))
    (tensor_orthonormal (fun i => (a i : Vec ι)) (fun j => (c j : Vec η)) ha hc)).map
    (LinearEquiv.ofEq _ _ (tensorBasis_span A C a c))

omit [DecidableEq ι] [DecidableEq η] in
@[simp] lemma tensorBasis_apply (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (a : Basis κ F2 A) (c : Basis α F2 C)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hc : ∀ i j, dot (c i : Vec η) (c j : Vec η) = if i = j then 1 else 0) (i : κ × α) :
    (tensorBasis A C a c ha hc i : Vec (ι × η)) = tensor (a i.1 : Vec ι) (c i.2 : Vec η) := by
  simp [tensorBasis]

omit [DecidableEq ι] [DecidableEq η] in
lemma tensorBasis_orthonormal (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (a : Basis κ F2 A) (c : Basis α F2 C)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hc : ∀ i j, dot (c i : Vec η) (c j : Vec η) = if i = j then 1 else 0) (i j : κ × α) :
    dot (tensorBasis A C a c ha hc i : Vec (ι × η))
      (tensorBasis A C a c ha hc j : Vec (ι × η)) = if i = j then 1 else 0 := by
  rw [tensorBasis_apply, tensorBasis_apply]
  exact tensor_orthonormal (fun i => (a i : Vec ι)) (fun j => (c j : Vec η)) ha hc i j


omit [DecidableEq ι] [DecidableEq η] in
lemma tensor_nondegenerate (A : Submodule F2 (Vec ι)) (C : Submodule F2 (Vec η))
    (a : Basis κ F2 A) (c : Basis α F2 C)
    (ha : ∀ i j, dot (a i : Vec ι) (a j : Vec ι) = if i = j then 1 else 0)
    (hc : ∀ i j, dot (c i : Vec η) (c j : Vec η) = if i = j then 1 else 0) :
    Nondegenerate (tensorSpace A C) :=
  basis_nondegenerate _ (tensorBasis A C a c ha hc)
    (tensorBasis_orthonormal A C a c ha hc)

end TensorBases

end Tensors


section Table
variable [DecidableEq ι] [DecidableEq η]

def label0 (B : Submodule F2 (Vec ι)) (t : Vec η) := tensorSpace B (line t)
def label1 (B : Submodule F2 (Vec ι)) := tensorSpace B (⊤ : Submodule F2 (Vec η))
def label2 (B P : Submodule F2 (Vec ι)) (t : Vec η) :=
  label1 (η := η) B ⊔ tensorSpace P (line t)
def label3 (E : Submodule F2 (Vec ι)) := tensorSpace E (⊤ : Submodule F2 (Vec η))
def label5 (B P : Submodule F2 (Vec ι)) (t : Vec η) :=
  label1 (η := η) B ⊔ tensorSpace P (perp t)

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- X: incoming label → row 2. -/
theorem residual_X_in_2 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (t : Vec η) (ht : dot t t = 1) :
    Decomposes (tensorSpace E (line t)) (tensorSpace B (perp t)) (label2 B P t) := by
  refine ⟨?_, tensorSpace_orthogonal_right E B (line_perp_orthogonal t)⟩
  rw [← hE.1, tensorSpace_sup_left]
  have hB := tensorSpace_decomposes_right B (line_decomposes_perp t ht)
  calc
    _ = (tensorSpace B (line t) ⊔ tensorSpace B (perp t)) ⊔ tensorSpace P (line t) := by ac_rfl
    _ = _ := by rw [hB.1]; rfl

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- X: row 2 → row 3. -/
theorem residual_X_2_3 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (t : Vec η) (ht : dot t t = 1) :
    Decomposes (label2 B P t) (tensorSpace P (perp t)) (label3 (η := η) E) := by
  refine ⟨?_, orthogonal_sup_left
    (tensorSpace_orthogonal_left hE.2 _ _) (tensorSpace_orthogonal_right P P (line_perp_orthogonal t))⟩
  change (tensorSpace B ⊤ ⊔ tensorSpace P (line t)) ⊔ tensorSpace P (perp t) = tensorSpace E ⊤
  rw [sup_assoc, ← tensorSpace_sup_right, (line_decomposes_perp t ht).1,
    ← tensorSpace_sup_left, hE.1]

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- Y: row 0 → row 1. -/
theorem residual_Y_0_1 (B : Submodule F2 (Vec ι)) (t : Vec η) (ht : dot t t = 1) :
    Decomposes (label0 B t) (tensorSpace B (perp t)) (label1 (η := η) B) :=
  tensorSpace_decomposes_right B (line_decomposes_perp t ht)

omit [DecidableEq ι] [DecidableEq η] in
/-- Y: row 4 (=row 1 label) → row 5. -/
theorem residual_Y_4_5 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (t : Vec η) : Decomposes (label1 (η := η) B) (tensorSpace P (perp t)) (label5 B P t) :=
  ⟨rfl, tensorSpace_orthogonal_left hE.2 _ _⟩

omit [DecidableEq ι] in
lemma zero_decomposes (S : Submodule F2 (Vec ι)) : Decomposes ⊥ S S := by
  refine ⟨bot_sup_eq S, ?_⟩
  intro x hx y hy
  have hx0 : x = 0 := by simpa using hx
  rw [hx0]
  simp [dot]

omit [DecidableEq ι] [DecidableEq η] in
/-- Center: source → row 1. -/
theorem residual_center_source_1 (B : Submodule F2 (Vec ι)) :
    Decomposes ⊥ (label1 (η := η) B) (label1 (η := η) B) := zero_decomposes _

omit [DecidableEq ι] [DecidableEq η] in
/-- Center: rows 1→3, 3→4 (a decrease), and 4→6 all have the same complement P⊗D. -/
theorem residual_center_BD_ED (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E) :
    Decomposes (label1 (η := η) B) (tensorSpace P (⊤ : Submodule F2 (Vec η))) (label3 (η := η) E) :=
  tensorSpace_decomposes_left hE _

omit [DecidableEq ι] [DecidableEq η] in
/-- Side: source → row 0. -/
theorem residual_side_source_0 (B : Submodule F2 (Vec ι)) (t : Vec η) :
    Decomposes ⊥ (label0 B t) (label0 B t) := zero_decomposes _

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- Side: row 0 → row 2, including the actual direct sum of two residual factors. -/
theorem residual_side_0_2 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (tx ty : Vec η) (hy : dot ty ty = 1) :
    Decomposes (label0 B ty) (tensorSpace B (perp ty) ⊔ tensorSpace P (line tx))
      (label2 B P tx) := by
  refine ⟨?_, orthogonal_sup_right
    (tensorSpace_orthogonal_right B B (line_perp_orthogonal ty))
    (tensorSpace_orthogonal_left hE.2 _ _)⟩
  change tensorSpace B (line ty) ⊔ (tensorSpace B (perp ty) ⊔ tensorSpace P (line tx)) = _
  rw [← sup_assoc, ← tensorSpace_sup_right, (line_decomposes_perp ty hy).1]
  rfl

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- Side: row 2 → row 5, using the neighboring-pair orthogonality. -/
theorem residual_side_2_5 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (tx ty : Vec η) (hx : dot tx tx = 1) (hxy : dot tx ty = 0) :
    Decomposes (label2 B P tx) (tensorSpace P (pairPerp tx ty)) (label5 B P ty) := by
  refine ⟨?_, orthogonal_sup_left
    (tensorSpace_orthogonal_left hE.2 _ _)
    (tensorSpace_orthogonal_right P P (pair_decomposes_perp tx ty hx hxy).2)⟩
  change (tensorSpace B ⊤ ⊔ tensorSpace P (line tx)) ⊔ tensorSpace P (pairPerp tx ty) = _
  rw [sup_assoc, ← tensorSpace_sup_right, (pair_decomposes_perp tx ty hx hxy).1]
  rfl

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- Side: row 5 → row 7. -/
theorem residual_side_5_7 (B P E : Submodule F2 (Vec ι)) (hE : Decomposes B P E)
    (ty : Vec η) (hy : dot ty ty = 1) :
    Decomposes (label5 B P ty) (tensorSpace P (line ty)) (label3 (η := η) E) := by
  refine ⟨?_, orthogonal_sup_left
    (tensorSpace_orthogonal_left hE.2 _ _)
    (tensorSpace_orthogonal_right P P (orthogonal_symm (line_perp_orthogonal ty)))⟩
  change (tensorSpace B ⊤ ⊔ tensorSpace P (perp ty)) ⊔ tensorSpace P (line ty) = tensorSpace E ⊤
  rw [sup_assoc, ← tensorSpace_sup_right, (decomposes_symm (line_decomposes_perp ty hy)).1,
    ← tensorSpace_sup_left, hE.1]

omit [DecidableEq ι] in
omit [DecidableEq η] in
/-- Auxiliary: last → sink, in the full future coordinate space. -/
theorem residual_auxiliary_last_sink (S : Submodule F2 (Vec ι)) (q : Vec η)
    (hq : dot q q = 1) :
    Decomposes (tensorSpace S (line q)) (tensorSpace S (perp q)) (tensorSpace S ⊤) :=
  tensorSpace_decomposes_right S (line_decomposes_perp q hq)

end Table



section StageInterfaces
variable [DecidableEq ι] [DecidableEq η] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq η] in
/-- The outgoing Y label is exactly the relative perpendicular to the active triple line. -/
theorem stage_Y_outgoing_relative_perp (B P E : Submodule F2 (Vec ι))
    (hE : Decomposes B P E) (bP : Basis κ F2 P)
    (hP : ∀ i j, dot (bP i : Vec ι) (bP j : Vec ι) = if i = j then 1 else 0)
    (t : Vec η) (ht : dot t t = 1) :
    residual (tensorSpace P (line t)) (label3 (η := η) E) = label5 B P t := by
  apply residual_of_decomposes (decomposes_symm (residual_side_5_7 B P E hE t ht))
  exact tensor_nondegenerate P (line t) bP (lineBasis t ht) hP
    (by intro i j; simpa using ht)

omit [DecidableEq ι] in
/-- The central complement P⊗D has exactly h dimensions when P is a unit line. -/
theorem central_residual_dimension (p : Vec ι) (hp : dot p p = 1) :
    Module.finrank F2 (tensorSpace (line p) (⊤ : Submodule F2 (Vec η))) = Fintype.card η := by
  have b := tensorBasis (line p) (⊤ : Submodule F2 (Vec η))
    (lineBasis p hp) fullBasis (by intro i j; simpa using hp) fullBasis_orthonormal
  rw [Module.finrank_eq_card_basis b]
  simp

omit [DecidableEq ι] in
/-- This counts the actual orthogonal residual of the central row-3→row-4 decrease. -/
theorem central_decrease_dimension (B E : Submodule F2 (Vec ι)) (p : Vec ι)
    (hE : Decomposes B (line p) E) (hp : dot p p = 1)
    (hBD : Nondegenerate (label1 (η := η) B)) :
    Module.finrank F2 (residual (label1 (η := η) B) (label3 (η := η) E)) = Fintype.card η := by
  rw [residual_of_decomposes (residual_center_BD_ED B (line p) E hE) hBD]
  exact central_residual_dimension p hp

end StageInterfaces


section FutureCentral
variable {ζ : Type*} [Fintype ζ] [DecidableEq ι] [DecidableEq η] [DecidableEq ζ]

omit [DecidableEq ι] [DecidableEq ζ] in
/-- Tensoring the central residual with its future unit line still leaves exactly h dimensions. -/
theorem central_future_residual_dimension (p : Vec ι) (q : Vec ζ)
    (hp : dot p p = 1) (hq : dot q q = 1) :
    Module.finrank F2 (tensorSpace
      (tensorSpace (line p) (⊤ : Submodule F2 (Vec η))) (line q)) = Fintype.card η := by
  let b := tensorBasis (line p) (⊤ : Submodule F2 (Vec η))
    (lineBasis p hp) fullBasis (by intro i j; simpa using hp) fullBasis_orthonormal
  have hb := tensorBasis_orthonormal (line p) (⊤ : Submodule F2 (Vec η))
    (lineBasis p hp) fullBasis (by intro i j; simpa using hp) fullBasis_orthonormal
  have bq := tensorBasis _ (line q) b (lineBasis q hq) hb (by intro i j; simpa using hq)
  rw [Module.finrank_eq_card_basis bq]
  simp

omit [DecidableEq ι] [DecidableEq ζ] in
theorem central_future_decrease_dimension (B E : Submodule F2 (Vec ι)) (p : Vec ι) (q : Vec ζ)
    (hE : Decomposes B (line p) E) (hp : dot p p = 1) (hq : dot q q = 1)
    (hsmall : Nondegenerate (tensorSpace (label1 (η := η) B) (line q))) :
    Module.finrank F2 (residual (tensorSpace (label1 (η := η) B) (line q))
      (tensorSpace (label3 (η := η) E) (line q))) = Fintype.card η := by
  rw [residual_of_decomposes
    (tensorSpace_decomposes_left (residual_center_BD_ED B (line p) E hE) (line q)) hsmall]
  exact central_future_residual_dimension p q hp hq

end FutureCentral

section TripleTensors

lemma weight_indicator (s : Finset ι) [DecidableEq ι] : weight (indicator s) = s.card := by
  rw [weight_eq_support_card]
  congr 1
  ext i
  simp [indicator]

lemma weight_characteristic : weight (characteristic : Vec ι) = Fintype.card ι := by
  simp [weight, characteristic]

/-- The exact prefix/future line vector; the coordinate order is the finite function order. -/
def tripleTensor (k h : ℕ) (s : Fin k → Finset (Fin h)) : Vec (Fin k → Fin h) :=
  tensorFamily (fun i => indicator (s i))

lemma tripleTensor_norm (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) : dot (tripleTensor k h s) (tripleTensor k h s) = 1 :=
  tensorFamily_norm_one _ (fun i => triple_indicator_norm _ (hs i))

lemma tripleTensor_weight (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) : weight (tripleTensor k h s) = 3 ^ k := by
  rw [tripleTensor, weight_tensorFamily]
  simp [weight_indicator, hs]

lemma tripleTensor_ambient_card (k h : ℕ) : Fintype.card (Fin k → Fin h) = h ^ k := by
  simp

lemma tripleTensor_not_characteristic (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) (hk : 1 ≤ k) (hh : 7 ≤ h) :
    tripleTensor k h s ≠ characteristic := by
  intro he
  have hw := congrArg weight he
  rw [tripleTensor_weight k h s hs, weight_characteristic, tripleTensor_ambient_card] at hw
  have hlt : 3 ^ k < h ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- Positive-length tensor-triple complements use the proved coordinate construction. -/
theorem tripleTensor_complement_basis (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) (hk : 1 ≤ k) (hh : 7 ≤ h) :
    ∃ p, ∃ b : Basis (OneIndex p) F2 (perp (tripleTensor k h s)),
      (∀ j, (b j : Vec (Fin k → Fin h)) =
        transvection (unit p + tripleTensor k h s) (unit j.val)) ∧
      (∀ i j, dot (b i : Vec (Fin k → Fin h)) (b j : Vec (Fin k → Fin h)) =
        if i = j then 1 else 0) := by
  obtain ⟨p, hp⟩ := (exists_zero_iff_not_characteristic _).mpr
    (tripleTensor_not_characteristic k h s hs hk hh)
  refine ⟨p, oneComplementBasis _ p (tripleTensor_norm k h s hs) hp, ?_, ?_⟩
  · exact oneComplementBasis_apply _ _ _ _
  · exact oneComplementBasis_orthonormal _ _ _ _

/-- In a one-coordinate space the unit line exhausts the full space. -/
lemma perp_characteristic_of_unique [Unique ι] : perp (characteristic : Vec ι) = ⊥ := by
  ext x
  constructor
  · intro hx
    have hd : dot (characteristic : Vec ι) x = x default := by simp [dot, characteristic]
    have hx0 : x = 0 := by
      ext i
      have hi : i = default := Subsingleton.elim _ _
      rw [hi]
      exact hd.symm.trans hx
    simpa using hx0
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    rw [hx0]
    simp

@[simp] lemma tripleTensor_zero_characteristic (h : ℕ) (s : Fin 0 → Finset (Fin h)) :
    tripleTensor 0 h s = characteristic := by ext p; simp [tripleTensor, tensorFamily, characteristic]

lemma tripleTensor_zero_perp (h : ℕ) (s : Fin 0 → Finset (Fin h)) :
    perp (tripleTensor 0 h s) = ⊥ := by
  rw [tripleTensor_zero_characteristic]
  exact perp_characteristic_of_unique

/-- Empty prefix/future factors have a genuine empty complement basis. -/
def emptyTripleComplementBasis (h : ℕ) (s : Fin 0 → Finset (Fin h)) :
    Basis Empty F2 (perp (tripleTensor 0 h s)) :=
  (Basis.empty (↥(⊥ : Submodule F2 (Vec (Fin 0 → Fin h))))).map
    (LinearEquiv.ofEq _ _ (tripleTensor_zero_perp h s).symm)


lemma tripleTensor_prefix_split (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) :
    Decomposes (perp (tripleTensor k h s)) (line (tripleTensor k h s)) ⊤ :=
  decomposes_symm (line_decomposes_perp _ (tripleTensor_norm k h s hs))

lemma tripleTensor_zero_line (h : ℕ) (s : Fin 0 → Finset (Fin h)) :
    line (tripleTensor 0 h s) = ⊤ := by
  have he := (line_decomposes_perp (tripleTensor 0 h s)
    (tripleTensor_norm 0 h s (by intro i; exact Fin.elim0 i))).1
  simpa only [tripleTensor_zero_perp, sup_bot_eq] using he


/-- All prefix/future complements are nondegenerate, including the empty-factor case. -/
lemma tripleTensor_perp_nondegenerate (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) (hh : 7 ≤ h) : Nondegenerate (perp (tripleTensor k h s)) := by
  cases k with
  | zero => rw [tripleTensor_zero_perp]; exact nondegenerate_bot
  | succ k =>
    obtain ⟨p, b, hi, hb⟩ := tripleTensor_complement_basis (k + 1) h s hs (by omega) hh
    exact basis_nondegenerate _ b hb

end TripleTensors

end
end ExactFourierCircuits.BinaryResiduals
