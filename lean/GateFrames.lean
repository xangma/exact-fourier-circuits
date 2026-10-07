import StageFrames
import TripleNetwork
import FramedScheduleWords

set_option autoImplicit false

/- The actual physical-row support, coordinate subspace labels, and their
   finite orthonormal bases. No macro schedule is assumed by these facts. -/
namespace ExactFourierCircuits.GateFrames
open BinaryFrames BinaryComplement BinaryTensor BinaryResiduals StageFrames ScalarNetwork Module
open scoped BigOperators
noncomputable section

variable {ι η κ : Type*} [Fintype ι] [Fintype η]

/-- A basis indexed by a literal finite coordinate count. -/
def HasONBasis (A : Submodule F2 (Vec ι)) : Prop :=
  ∃ d, ∃ b : Basis (Fin d) F2 A,
    ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0

lemma hasONBasis_of_basis [Fintype κ] [DecidableEq κ]
    (A : Submodule F2 (Vec ι)) (b : Basis κ F2 A)
    (hb : ∀ i j, dot (b i : Vec ι) (b j : Vec ι) = if i = j then 1 else 0) : HasONBasis A := by
  classical
  refine ⟨Fintype.card κ, b.reindex (Fintype.equivFin κ), ?_⟩
  intro i j
  simp only [Basis.reindex_apply, hb]
  simp

lemma hasONBasis_bot : HasONBasis (⊥ : Submodule F2 (Vec ι)) := by
  classical
  apply hasONBasis_of_basis _ (Basis.empty (ι := Empty) (↥(⊥ : Submodule F2 (Vec ι))))
  intro i
  exact i.elim

lemma hasONBasis_top : HasONBasis (⊤ : Submodule F2 (Vec ι)) := by
  classical
  exact hasONBasis_of_basis _ fullBasis fullBasis_orthonormal

lemma hasONBasis_line (u : Vec ι) (hu : dot u u = 1) : HasONBasis (line u) := by
  exact hasONBasis_of_basis _ (lineBasis u hu) (by intro i j; simpa using hu)

lemma hasONBasis_nondegenerate {A : Submodule F2 (Vec ι)} (hA : HasONBasis A) : Nondegenerate A := by
  obtain ⟨d, b, hb⟩ := hA
  exact basis_nondegenerate A b hb

lemma hasONBasis_tensor {A : Submodule F2 (Vec ι)} {B : Submodule F2 (Vec η)}
    (hA : HasONBasis A) (hB : HasONBasis B) : HasONBasis (tensorSpace A B) := by
  classical
  obtain ⟨d, a, ha⟩ := hA
  obtain ⟨e, b, hb⟩ := hB
  exact hasONBasis_of_basis _ (tensorBasis A B a b ha hb)
    (tensorBasis_orthonormal A B a b ha hb)

lemma hasONBasis_sum {A B : Submodule F2 (Vec ι)}
    (hA : HasONBasis A) (hB : HasONBasis B) (hAB : Orthogonal A B) : HasONBasis (A ⊔ B) := by
  classical
  obtain ⟨d, a, ha⟩ := hA
  obtain ⟨e, b, hb⟩ := hB
  exact hasONBasis_of_basis _ (sumBasis A B a b ha hb hAB)
    (sumBasis_orthonormal A B a b ha hb hAB)

lemma hasONBasis_residual {A B S : Submodule F2 (Vec ι)}
    (h : Decomposes A B S) (hA : HasONBasis A) (hB : HasONBasis B) :
    HasONBasis (BinaryResiduals.residual A S) := by
  rw [residual_of_decomposes h (hasONBasis_nondegenerate hA)]
  exact hB

/-- Restriction of the proved coordinate permutation to an actual subspace. -/
def subspaceCoordinates (e : ι ≃ η) (A : Submodule F2 (Vec ι)) : A ≃ₗ[F2] space e A where
  toFun x := ⟨coordinates e x, ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨(coordinates e).symm y, (mem_space e A y).mp y.property⟩
  left_inv x := by apply Subtype.ext; exact (coordinates e).symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact (coordinates e).apply_symm_apply y
  map_add' x y := by apply Subtype.ext; exact (coordinates e).map_add x y
  map_smul' c x := by apply Subtype.ext; exact (coordinates e).map_smul c x

lemma hasONBasis_space (e : ι ≃ η) {A : Submodule F2 (Vec ι)} (hA : HasONBasis A) :
    HasONBasis (space e A) := by
  obtain ⟨d, b, hb⟩ := hA
  refine ⟨d, b.map (subspaceCoordinates e A), ?_⟩
  intro i j
  simp only [Basis.map_apply]
  change dot (coordinates e (b i)) (coordinates e (b j)) = _
  rw [coordinates_dot, hb]

/-- The existential basis can be used directly by the actual word schedule. -/
def labelOfBasis {n : ℕ} {A : Submodule F2 (Vec (Fin n))} (hA : HasONBasis A) :
    FramedScheduleWords.Label n where
  space := A
  dimension := Classical.choose hA
  basis := Classical.choose (Classical.choose_spec hA)
  orthonormal := Classical.choose_spec (Classical.choose_spec hA)

@[simp] lemma labelOfBasis_space {n : ℕ} {A : Submodule F2 (Vec (Fin n))}
    (hA : HasONBasis A) : (labelOfBasis hA).space = A := rfl

section TripleBases
variable {h : ℕ}

def t (S : Triple (Fin h)) : Vec (Fin h) := indicator S.val

lemma t_norm (S : Triple (Fin h)) : dot (t S) (t S) = 1 := triple_indicator_norm _ S.property

lemma edge_orthogonal (e : Edge (Fin h)) : dot (t e.val.2) (t e.val.1) = 0 := by
  rw [dot_comm]
  exact even_intersection_orthogonal _ _ (neighboring_even _ _ e.property)

lemma hasONBasis_triple_perp (S : Triple (Fin h)) (hh : 7 ≤ h) : HasONBasis (perp (t S)) := by
  obtain ⟨p, hp⟩ := triple_indicator_valid_pivot S.val S.property (by simpa using hh)
  exact hasONBasis_of_basis _ (oneComplementBasis _ p (t_norm S) hp)
    (oneComplementBasis_orthonormal _ p (t_norm S) hp)

lemma hasONBasis_pair_perp (e : Edge (Fin h)) (hh : 7 ≤ h) :
    HasONBasis (pairPerp (t e.val.2) (t e.val.1)) := by
  have he : Even (e.val.2.val ∩ e.val.1.val).card := by
    simpa [Finset.inter_comm] using neighboring_even _ _ e.property
  obtain ⟨p, q, hp, hqp, hq⟩ := triple_pair_valid_pivots e.val.2.val e.val.1.val
    e.val.2.property e.val.1.property he (by simpa using hh)
  exact hasONBasis_of_basis _
    (twoComplementBasis _ _ p q (t_norm _) (t_norm _) (edge_orthogonal e) hp hqp hq)
    (twoComplementBasis_orthonormal _ _ p q (t_norm _) (t_norm _) (edge_orthogonal e) hp hqp hq)

/-- Actual prefix/future complements, including their zero-factor case. -/
lemma hasONBasis_tripleTensor_perp (k h : ℕ) (s : Fin k → Finset (Fin h))
    (hs : ∀ i, (s i).card = 3) (hh : 7 ≤ h) : HasONBasis (perp (tripleTensor k h s)) := by
  cases k with
  | zero => rw [tripleTensor_zero_perp]; exact hasONBasis_bot
  | succ k =>
    obtain ⟨p, b, hvec, hb⟩ := tripleTensor_complement_basis (k + 1) h s hs (by omega) hh
    exact hasONBasis_of_basis _ b hb

end TripleBases

section PhysicalRows
variable {h : ℕ}

/-- Actual roles of a single scalar invocation, with physically ordered side pairs. -/
inductive Role (h : ℕ) where
  | x : Triple (Fin h) → Role h
  | y : Triple (Fin h) → Role h
  | side : Edge (Fin h) → Role h
  | center : Option (Fin h) → Role h
  deriving DecidableEq, Fintype

def rowCoefficient : Fin 8 → Role h → Role h → ℂ
  | 0, .y S, .side e => -J S e
  | 1, .y S, .center i => -R S i
  | 2, .side e, .x T => V e T
  | 3, .center i, .x T => G i T
  | 4, .y S, .center i => R S i
  | 5, .y S, .side e => J S e
  | 6, .center i, .x T => -G i T
  | 7, .side e, .x T => -V e T
  | _, _, _ => 0

/-- Reversal uses the reversed logical ordered edge, preserving its physical pair. -/
def reverseRowCoefficient : Fin 8 → Role h → Role h → ℂ
  | 0, .side e, .y S => V (TripleNetwork.reverseEdge e) S
  | 1, .center i, .y S => G i S
  | 2, .x T, .side e => -J T (TripleNetwork.reverseEdge e)
  | 3, .x T, .center i => -R T i
  | 4, .center i, .y S => -G i S
  | 5, .side e, .y S => -V (TripleNetwork.reverseEdge e) S
  | 6, .x T, .center i => R T i
  | 7, .x T, .side e => J T (TripleNetwork.reverseEdge e)
  | _, _, _ => 0

/-- Every role retains its last touched label; both roles of each row share that row's label. -/
def rowLabel (B P E : Submodule F2 (Vec ι)) (row : Fin 8) :
    Role h → Submodule F2 (Vec (ι × Fin h))
  | .x T => if row.val < 2 then tensorSpace E (line (t T))
      else if row.val = 2 then label2 B P (t T) else label3 E
  | .y S => if row.val = 0 then label0 B (t S)
      else if row.val < 5 then label1 B else label5 B P (t S)
  | .side e => if row.val < 2 then label0 B (t e.val.1)
      else if row.val < 5 then label2 B P (t e.val.2)
      else if row.val < 7 then label5 B P (t e.val.1) else label3 E
  | .center _ => if row.val = 0 then ⊥
      else if row.val = 1 ∨ row.val = 2 ∨ row.val = 4 ∨ row.val = 5 then label1 B else label3 E

lemma V_support (e : Edge (Fin h)) (T : Triple (Fin h)) (hV : V e T ≠ 0) : e.val.2 = T := by
  by_contra hn
  simp [V, hn] at hV

lemma J_support (S : Triple (Fin h)) (e : Edge (Fin h)) (hJ : J S e ≠ 0) : e.val.1 = S := by
  by_contra hn
  simp [J, hn] at hJ

omit [Fintype ι] in
set_option maxHeartbeats 1000000 in
theorem row_support_common_label (B P E : Submodule F2 (Vec ι))
    (row : Fin 8) (dest source : Role h) (hn : rowCoefficient row dest source ≠ 0) :
    rowLabel B P E row dest = rowLabel B P E row source := by
  cases dest <;> cases source <;> fin_cases row <;> simp [rowCoefficient] at hn
  all_goals simp [rowLabel]
  all_goals first | rfl | rw [J_support _ _ hn] | rw [V_support _ _ hn]

omit [Fintype ι] in
set_option maxHeartbeats 1000000 in
theorem reverse_row_support_common_label (B P E : Submodule F2 (Vec ι))
    (row : Fin 8) (dest source : Role h) (hn : reverseRowCoefficient row dest source ≠ 0) :
    rowLabel B P E row dest = rowLabel B P E row source := by
  cases dest <;> cases source <;> fin_cases row <;> simp [reverseRowCoefficient] at hn
  all_goals simp [rowLabel]
  all_goals first
    | rfl
    | have hs := V_support _ _ hn
      dsimp [TripleNetwork.reverseEdge] at hs
      rw [hs]
    | have hs := J_support _ _ hn
      dsimp [TripleNetwork.reverseEdge] at hs
      rw [hs]

def gateLabel (B P E : Submodule F2 (Vec ι)) (q : Vec η) (row : Fin 8) (role : Role h) :=
  tensorSpace (rowLabel B P E row role) (line q)

omit [Fintype ι] [Fintype η] in
theorem row_support_common_gateLabel (B P E : Submodule F2 (Vec ι)) (q : Vec η)
    (row : Fin 8) (dest source : Role h) (hn : rowCoefficient row dest source ≠ 0) :
    gateLabel B P E q row dest = gateLabel B P E q row source := by
  rw [gateLabel, gateLabel, row_support_common_label B P E row dest source hn]

omit [Fintype ι] [Fintype η] in
theorem reverse_row_support_common_gateLabel (B P E : Submodule F2 (Vec ι)) (q : Vec η)
    (row : Fin 8) (dest source : Role h) (hn : reverseRowCoefficient row dest source ≠ 0) :
    gateLabel B P E q row dest = gateLabel B P E q row source := by
  rw [gateLabel, gateLabel, reverse_row_support_common_label B P E row dest source hn]

end PhysicalRows

section LabelBases
variable {h : ℕ}

lemma hasONBasis_label0 {B : Submodule F2 (Vec ι)} (hB : HasONBasis B) (S : Triple (Fin h)) :
    HasONBasis (label0 B (t S)) := hasONBasis_tensor hB (hasONBasis_line _ (t_norm S))

lemma hasONBasis_label1 {B : Submodule F2 (Vec ι)} (hB : HasONBasis B) :
    HasONBasis (label1 (η := Fin h) B) := hasONBasis_tensor hB hasONBasis_top

lemma hasONBasis_label2 {B P E : Submodule F2 (Vec ι)} (hE : Decomposes B P E)
    (hB : HasONBasis B) (hP : HasONBasis P) (S : Triple (Fin h)) :
    HasONBasis (label2 B P (t S)) :=
  hasONBasis_sum (hasONBasis_label1 hB) (hasONBasis_tensor hP (hasONBasis_line _ (t_norm S)))
    (tensorSpace_orthogonal_left hE.2 _ _)

lemma hasONBasis_label5 {B P E : Submodule F2 (Vec ι)} (hE : Decomposes B P E)
    (hB : HasONBasis B) (hP : HasONBasis P) (S : Triple (Fin h)) (hh : 7 ≤ h) :
    HasONBasis (label5 B P (t S)) :=
  hasONBasis_sum (hasONBasis_label1 hB) (hasONBasis_tensor hP (hasONBasis_triple_perp S hh))
    (tensorSpace_orthogonal_left hE.2 _ _)

theorem rowLabel_hasONBasis {B P E : Submodule F2 (Vec ι)} (hE : Decomposes B P E)
    (hB : HasONBasis B) (hP : HasONBasis P) (hFull : HasONBasis E) (hh : 7 ≤ h)
    (row : Fin 8) (role : Role h) : HasONBasis (rowLabel B P E row role) := by
  cases role with
  | x T =>
    simp only [rowLabel]
    split
    · exact hasONBasis_label0 hFull T
    · split
      · exact hasONBasis_label2 hE hB hP T
      · exact hasONBasis_label1 hFull
  | y S =>
    simp only [rowLabel]
    split
    · exact hasONBasis_label0 hB S
    · split
      · exact hasONBasis_label1 hB
      · exact hasONBasis_label5 hE hB hP S hh
  | side e =>
    simp only [rowLabel]
    split
    · exact hasONBasis_label0 hB e.val.1
    · split
      · exact hasONBasis_label2 hE hB hP e.val.2
      · split
        · exact hasONBasis_label5 hE hB hP e.val.1 hh
        · exact hasONBasis_label1 hFull
  | center i =>
    simp only [rowLabel]
    split
    · exact hasONBasis_bot
    · split
      · exact hasONBasis_label1 hB
      · exact hasONBasis_label1 hFull

theorem gateLabel_hasONBasis {B P E : Submodule F2 (Vec ι)} (hE : Decomposes B P E)
    (hB : HasONBasis B) (hP : HasONBasis P) (hFull : HasONBasis E)
    (q : Vec η) (hq : dot q q = 1) (hh : 7 ≤ h) (row : Fin 8) (role : Role h) :
    HasONBasis (gateLabel B P E q row role) :=
  hasONBasis_tensor (rowLabel_hasONBasis hE hB hP hFull hh row role) (hasONBasis_line q hq)

/-- An oriented table edge with an actual orthonormal complement, before any basis choice. -/
def Transition (A B : Submodule F2 (Vec ι)) : Prop :=
  (∃ R, Decomposes A R B ∧ HasONBasis R) ∨ (∃ R, Decomposes B R A ∧ HasONBasis R)

lemma transition_increasing {A R B : Submodule F2 (Vec ι)} (h : Decomposes A R B)
    (hR : HasONBasis R) : Transition A B := Or.inl ⟨R, h, hR⟩

lemma transition_refl (A : Submodule F2 (Vec ι)) : Transition A A :=
  transition_increasing (decomposes_symm (zero_decomposes A)) hasONBasis_bot

lemma transition_symm {A B : Submodule F2 (Vec ι)} (h : Transition A B) : Transition B A :=
  h.symm

lemma transition_tensor_line {A B : Submodule F2 (Vec ι)} (h : Transition A B)
    (q : Vec η) (hq : dot q q = 1) : Transition (tensorSpace A (line q)) (tensorSpace B (line q)) := by
  rcases h with ⟨R, hr, hR⟩ | ⟨R, hr, hR⟩
  · exact Or.inl ⟨tensorSpace R (line q), tensorSpace_decomposes_left hr (line q),
      hasONBasis_tensor hR (hasONBasis_line q hq)⟩
  · exact Or.inr ⟨tensorSpace R (line q), tensorSpace_decomposes_left hr (line q),
      hasONBasis_tensor hR (hasONBasis_line q hq)⟩

lemma transition_tensor_left {A B : Submodule F2 (Vec η)} (h : Transition A B)
    (C : Submodule F2 (Vec ι)) (hC : HasONBasis C) :
    Transition (tensorSpace C A) (tensorSpace C B) := by
  rcases h with ⟨R, hr, hR⟩ | ⟨R, hr, hR⟩
  · exact Or.inl ⟨tensorSpace C R, tensorSpace_decomposes_right C hr, hasONBasis_tensor hC hR⟩
  · exact Or.inr ⟨tensorSpace C R, tensorSpace_decomposes_right C hr, hasONBasis_tensor hC hR⟩

lemma decomposes_space (e : ι ≃ η) {A R B : Submodule F2 (Vec ι)} (h : Decomposes A R B) :
    Decomposes (space e A) (space e R) (space e B) := by
  constructor
  · simpa only [space, Submodule.map_sup] using congrArg (space e) h.1
  · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    exact (coordinates_dot e a b).trans (h.2 a ha b hb)

lemma transition_space (e : ι ≃ η) {A B : Submodule F2 (Vec ι)} (h : Transition A B) :
    Transition (space e A) (space e B) := by
  rcases h with ⟨R, hr, hR⟩ | ⟨R, hr, hR⟩
  · exact Or.inl ⟨space e R, decomposes_space e hr, hasONBasis_space e hR⟩
  · exact Or.inr ⟨space e R, decomposes_space e hr, hasONBasis_space e hR⟩

/-- Converts the actual geometric table complement into the word compiler's nested edge. -/
def transitionToEdge {n : ℕ} (old new : FramedScheduleWords.Label n)
    (h : Transition old.space new.space) : FramedScheduleWords.NestedEdge old new := by
  classical
  by_cases hi : ∃ R, Decomposes old.space R new.space ∧ HasONBasis R
  · let R := Classical.choose hi
    have hr := (Classical.choose_spec hi).1
    have hR := (Classical.choose_spec hi).2
    have hb := hasONBasis_residual hr ⟨old.dimension, old.basis, old.orthonormal⟩ hR
    exact .increasing (decomposes_nested hr) (Classical.choose hb)
      (Classical.choose (Classical.choose_spec hb))
      (Classical.choose_spec (Classical.choose_spec hb))
  · have hd : ∃ R, Decomposes new.space R old.space ∧ HasONBasis R := h.resolve_left hi
    have hr := (Classical.choose_spec hd).1
    have hR := (Classical.choose_spec hd).2
    have hb := hasONBasis_residual hr ⟨new.dimension, new.basis, new.orthonormal⟩ hR
    exact .decreasing (decomposes_nested hr) (Classical.choose hb)
      (Classical.choose (Classical.choose_spec hb))
      (Classical.choose_spec (Classical.choose_spec hb))

end LabelBases

section InvocationFrames
variable {h : ℕ}

/-- Prefix and future data of an actual invocation; only their proved bases are inputs. -/
structure Data (ι η : Type*) [Fintype ι] [Fintype η] (h : ℕ) where
  prefixVector : Vec ι
  prefix_norm : dot prefixVector prefixVector = 1
  prefix_complement : HasONBasis (perp prefixVector)
  future : Vec η
  future_norm : dot future future = 1
  future_complement : HasONBasis (perp future)
  large : 7 ≤ h

def tensorData (k l h : ℕ) (prefixTriples : Fin k → Triple (Fin h))
    (future : Fin l → Triple (Fin h)) (hh : 7 ≤ h) : Data (Fin k → Fin h) (Fin l → Fin h) h where
  prefixVector := tripleTensor k h (fun i => (prefixTriples i).val)
  prefix_norm := tripleTensor_norm k h _ (fun i => (prefixTriples i).property)
  prefix_complement := hasONBasis_tripleTensor_perp k h _ (fun i => (prefixTriples i).property) hh
  future := tripleTensor l h (fun i => (future i).val)
  future_norm := tripleTensor_norm l h _ (fun i => (future i).property)
  future_complement := hasONBasis_tripleTensor_perp l h _ (fun i => (future i).property) hh
  large := hh

/-- An explicit finite-function join, preserving the prefix-then-future factor order. -/
def joinCoordinates (k l h : ℕ) : ((Fin k → Fin h) × (Fin l → Fin h)) ≃ (Fin (k + l) → Fin h) :=
  (Equiv.sumArrowEquivProdArrow (Fin k) (Fin l) (Fin h)).symm.trans
    (finSumFinEquiv.arrowCongr (Equiv.refl (Fin h)))

/-- Literal prefix/current/future factor coordinates for each of the three physical axes. -/
def invocationCoordinates (axis : Fin 3) (h : ℕ) :
    (((Fin axis.val → Fin h) × Fin h) × (Fin (2 - axis.val) → Fin h)) ≃ (Fin 3 → Fin h) :=
  ((appendCoordinates axis.val h).prodCongr (Equiv.refl (Fin (2 - axis.val) → Fin h))).trans
    ((joinCoordinates (axis.val + 1) (2 - axis.val) h).trans
      ((finCongr (show axis.val + 1 + (2 - axis.val) = 3 by have := axis.isLt; omega)).arrowCongr
        (Equiv.refl (Fin h))))

def Data.B (d : Data ι η h) := perp d.prefixVector
def Data.P (d : Data ι η h) := line d.prefixVector

lemma Data.split (d : Data ι η h) : Decomposes d.B d.P ⊤ :=
  decomposes_symm (line_decomposes_perp d.prefixVector d.prefix_norm)

lemma Data.P_basis (d : Data ι η h) : HasONBasis d.P := hasONBasis_line _ d.prefix_norm

def Data.entry (d : Data ι η h) : Role h → Submodule F2 (Vec (ι × Fin h))
  | .x T => tensorSpace ⊤ (line (t T))
  | .y S => label0 d.B (t S)
  | .side _ => ⊥
  | .center _ => ⊥

/-- Level zero is entry; level k+1 is the common gate frame at row k. -/
def Data.localAt (d : Data ι η h) (level : Fin 9) (role : Role h) :
    Submodule F2 (Vec (ι × Fin h)) :=
  if h0 : level.val = 0 then d.entry role
    else rowLabel d.B d.P ⊤ ⟨level.val - 1, by omega⟩ role

def Data.at (d : Data ι η h) (level : Fin 9) (role : Role h) :
    Submodule F2 (Vec ((ι × Fin h) × η)) := tensorSpace (d.localAt level role) (line d.future)

lemma Data.entry_basis (d : Data ι η h) (role : Role h) : HasONBasis (d.entry role) := by
  cases role with
  | x T => exact hasONBasis_label0 hasONBasis_top T
  | y S => exact hasONBasis_label0 d.prefix_complement S
  | side e => exact hasONBasis_bot
  | center i => exact hasONBasis_bot

lemma Data.localAt_basis (d : Data ι η h) (level : Fin 9) (role : Role h) :
    HasONBasis (d.localAt level role) := by
  unfold Data.localAt
  split
  · exact d.entry_basis role
  · exact rowLabel_hasONBasis d.split d.prefix_complement d.P_basis hasONBasis_top d.large _ role

lemma Data.at_basis (d : Data ι η h) (level : Fin 9) (role : Role h) : HasONBasis (d.at level role) :=
  hasONBasis_tensor (d.localAt_basis level role) (hasONBasis_line _ d.future_norm)

lemma Data.B_perp_basis (d : Data ι η h) (S : Triple (Fin h)) :
    HasONBasis (tensorSpace d.B (perp (t S))) :=
  hasONBasis_tensor d.prefix_complement (hasONBasis_triple_perp S d.large)

lemma Data.P_perp_basis (d : Data ι η h) (S : Triple (Fin h)) :
    HasONBasis (tensorSpace d.P (perp (t S))) :=
  hasONBasis_tensor d.P_basis (hasONBasis_triple_perp S d.large)

lemma Data.side_first_basis (d : Data ι η h) (e : Edge (Fin h)) :
    HasONBasis (tensorSpace d.B (perp (t e.val.1)) ⊔ tensorSpace d.P (line (t e.val.2))) :=
  hasONBasis_sum (d.B_perp_basis e.val.1)
    (hasONBasis_tensor d.P_basis (hasONBasis_line _ (t_norm _)))
    (tensorSpace_orthogonal_left d.split.2 _ _)

/-- Every physical role path has the exact table residual, including the central decrease. -/
theorem Data.local_transition (d : Data ι η h) (row : Fin 8) (role : Role h) :
    Transition (d.localAt row.castSucc role) (rowLabel d.B d.P ⊤ row role) := by
  cases role with
  | x T =>
    fin_cases row <;> simp [Data.localAt, Data.entry, rowLabel]
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_increasing (residual_X_in_2 _ _ _ d.split (t T) (t_norm T)) (d.B_perp_basis T)
    · exact transition_increasing (residual_X_2_3 _ _ _ d.split (t T) (t_norm T)) (d.P_perp_basis T)
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_refl _
  | y S =>
    fin_cases row <;> simp [Data.localAt, Data.entry, rowLabel]
    · exact transition_refl _
    · exact transition_increasing (residual_Y_0_1 _ (t S) (t_norm S)) (d.B_perp_basis S)
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_increasing (residual_Y_4_5 _ _ _ d.split (t S)) (d.P_perp_basis S)
    · exact transition_refl _
    · exact transition_refl _
  | side e =>
    fin_cases row <;> simp [Data.localAt, Data.entry, rowLabel]
    · exact transition_increasing (residual_side_source_0 _ (t e.val.1))
        (hasONBasis_label0 d.prefix_complement _)
    · exact transition_refl _
    · exact transition_increasing (residual_side_0_2 _ _ _ d.split (t e.val.2) (t e.val.1) (t_norm _))
        (d.side_first_basis e)
    · exact transition_refl _
    · exact transition_refl _
    · exact transition_increasing
        (residual_side_2_5 _ _ _ d.split (t e.val.2) (t e.val.1) (t_norm _) (edge_orthogonal e))
        (hasONBasis_tensor d.P_basis (hasONBasis_pair_perp e d.large))
    · exact transition_refl _
    · exact transition_increasing (residual_side_5_7 _ _ _ d.split (t e.val.1) (t_norm _))
        (hasONBasis_tensor d.P_basis (hasONBasis_line _ (t_norm _)))
  | center i =>
    fin_cases row <;> simp [Data.localAt, Data.entry, rowLabel]
    · exact transition_refl _
    · exact transition_increasing (residual_center_source_1 _)
        (hasONBasis_label1 d.prefix_complement)
    · exact transition_refl _
    · exact transition_increasing (residual_center_BD_ED _ _ _ d.split)
        (hasONBasis_tensor d.P_basis hasONBasis_top)
    · exact transition_symm (transition_increasing (residual_center_BD_ED _ _ _ d.split)
        (hasONBasis_tensor d.P_basis hasONBasis_top))
    · exact transition_refl _
    · exact transition_increasing (residual_center_BD_ED _ _ _ d.split)
        (hasONBasis_tensor d.P_basis hasONBasis_top)
    · exact transition_refl _

lemma Data.at_transition (d : Data ι η h) (row : Fin 8) (role : Role h) :
    Transition (d.at row.castSucc role) (d.at row.succ role) := by
  have hh := transition_tensor_line (d.local_transition row role) d.future d.future_norm
  simpa [Data.at, Data.localAt] using hh

/-- Auxiliary sink labels fill the whole future factor; bank endpoints remain their last labels. -/
def Data.finalSpace (d : Data ι η h) : Role h → Submodule F2 (Vec ((ι × Fin h) × η))
  | .x T => d.at 8 (.x T)
  | .y S => d.at 8 (.y S)
  | .side _ => tensorSpace (label3 (η := Fin h) (⊤ : Submodule F2 (Vec ι))) ⊤
  | .center _ => tensorSpace (label3 (η := Fin h) (⊤ : Submodule F2 (Vec ι))) ⊤

lemma Data.finalSpace_basis (d : Data ι η h) (role : Role h) : HasONBasis (d.finalSpace role) := by
  cases role with
  | x T => exact d.at_basis 8 (.x T)
  | y S => exact d.at_basis 8 (.y S)
  | side e => exact hasONBasis_tensor (hasONBasis_label1 hasONBasis_top) hasONBasis_top
  | center i => exact hasONBasis_tensor (hasONBasis_label1 hasONBasis_top) hasONBasis_top

lemma Data.sink_transition (d : Data ι η h) (role : Role h) :
    Transition (d.at 8 role) (d.finalSpace role) := by
  cases role with
  | x T => exact transition_refl _
  | y S => exact transition_refl _
  | side e =>
    change Transition (tensorSpace (label3 (η := Fin h) ⊤) (line d.future))
      (tensorSpace (label3 (η := Fin h) ⊤) ⊤)
    exact transition_increasing (residual_auxiliary_last_sink _ d.future d.future_norm)
      (hasONBasis_tensor (hasONBasis_label1 hasONBasis_top) d.future_complement)
  | center i =>
    change Transition (tensorSpace (label3 (η := Fin h) ⊤) (line d.future))
      (tensorSpace (label3 (η := Fin h) ⊤) ⊤)
    exact transition_increasing (residual_auxiliary_last_sink _ d.future d.future_norm)
      (hasONBasis_tensor (hasONBasis_label1 hasONBasis_top) d.future_complement)

/-- One fixed family of Label objects, shared definitionally by consecutive row blocks. -/
def Data.labels {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (level : Fin 9) (role : Role h) : FramedScheduleWords.Label n :=
  labelOfBasis (hasONBasis_space e (d.at_basis level role))

def Data.edges {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (role : Role h) :
    FramedScheduleWords.NestedEdge (d.labels e row.castSucc role) (d.labels e row.succ role) :=
  transitionToEdge _ _ (transition_space e (d.at_transition row role))

def Data.finalLabels {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (role : Role h) : FramedScheduleWords.Label n :=
  labelOfBasis (hasONBasis_space e (d.finalSpace_basis role))

def Data.sinkEdges {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (role : Role h) : FramedScheduleWords.NestedEdge (d.labels e 8 role) (d.finalLabels e role) :=
  transitionToEdge _ _ (transition_space e (d.sink_transition role))

@[simp] lemma Data.labels_space {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (level : Fin 9) (role : Role h) : (d.labels e level role).space = space e (d.at level role) := rfl

@[simp] lemma Data.finalLabels_space {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (role : Role h) : (d.finalLabels e role).space = space e (d.finalSpace role) := rfl

lemma Data.after_space {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (role : Role h) :
    (d.labels e row.succ role).space = space e (gateLabel d.B d.P ⊤ d.future row role) := by
  simp [Data.at, Data.localAt, gateLabel]

theorem Data.forward_compatible {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (dest source : Role h) (hn : rowCoefficient row dest source ≠ 0) :
    (d.labels e row.succ dest).space = (d.labels e row.succ source).space := by
  rw [d.after_space, d.after_space, row_support_common_gateLabel _ _ _ _ row dest source hn]

theorem Data.reverse_compatible {n : ℕ} (d : Data ι η h) (e : ((ι × Fin h) × η) ≃ Fin n)
    (row : Fin 8) (dest source : Role h) (hn : reverseRowCoefficient row dest source ≠ 0) :
    (d.labels e row.succ dest).space = (d.labels e row.succ source).space := by
  rw [d.after_space, d.after_space, reverse_row_support_common_gateLabel _ _ _ _ row dest source hn]

theorem Data.entry_auxiliary_zero {n : ℕ} (d : Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (side : Edge (Fin h)) (center : Option (Fin h)) :
    (d.labels e 0 (.side side)).space = ⊥ ∧ (d.labels e 0 (.center center)).space = ⊥ := by
  simp [Data.at, Data.localAt, Data.entry, tensorSpace_bot_left]

theorem Data.final_auxiliary_top {n : ℕ} (d : Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (side : Edge (Fin h)) (center : Option (Fin h)) :
    (d.finalLabels e (.side side)).space = ⊤ ∧ (d.finalLabels e (.center center)).space = ⊤ := by
  classical
  simp [Data.finalSpace, label3, tensorSpace_top_top]

theorem Data.final_bank_spaces (d : Data ι η h) (T S : Triple (Fin h)) :
    d.finalSpace (.x T) = tensorSpace (⊤ : Submodule F2 (Vec (ι × Fin h))) (line d.future) ∧
    d.finalSpace (.y S) = tensorSpace (perp (tensor d.prefixVector (t S))) (line d.future) := by
  classical
  simp [Data.finalSpace, Data.at, Data.localAt, rowLabel, label3, tensorSpace_top_top,
    Data.B, Data.P, outgoing_perp _ _ d.prefix_norm (t_norm S)]

end InvocationFrames

end
end ExactFourierCircuits.GateFrames
