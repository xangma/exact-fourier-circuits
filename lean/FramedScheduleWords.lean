import RoleFrameWords
import FrameCommutation

set_option autoImplicit false
namespace ExactFourierCircuits.FramedScheduleWords
open OAI.ExactFourier BinaryFrames BinaryTensor FrameSpectrum BinaryProjection Module
open scoped BigOperators
noncomputable section
variable {r n : ℕ}

/-- An actual binary subspace with a finite orthonormal basis. -/
structure Label (n : ℕ) where
  space : Submodule F2 (Vec (Fin n))
  dimension : ℕ
  basis : Basis (Fin dimension) F2 space
  orthonormal : Orthonormal (fun i => (basis i : Vec (Fin n)))

def Label.vectors (L : Label n) : Fin L.dimension → Vec (Fin n) := fun i => L.basis i

def Label.exponent (L : Label n) : Vec (Fin n) → ZMod 4 := frameExponent L.vectors

theorem Label.span (L : Label n) : frameSpan L.vectors = L.space :=
  BinaryResiduals.basis_span_coe L.space L.basis

theorem Label.exponent_eq (A B : Label n) (h : A.space = B.space) :
    A.exponent = B.exponent := by
  funext x
  unfold Label.exponent frameExponent
  rw [frameProjection_eq_of_span_eq A.vectors B.vectors A.orthonormal B.orthonormal
    (by rw [Label.span, Label.span, h])]

theorem Label.nondegenerate (L : Label n) : BinaryResiduals.Nondegenerate L.space := by
  rw [← Label.span L]
  exact frameSpan_nondegenerate L.vectors L.orthonormal

theorem Label.selfResidual_eq_bot (L : Label n) :
    BinaryResiduals.residual L.space L.space = ⊥ := by
  apply BinaryResiduals.residual_of_decomposes _ L.nondegenerate
  constructor
  · exact sup_bot_eq _
  · intro x hx y hy
    have hy0 : y = 0 := hy
    rw [hy0]
    simp [dot]

def Label.emptyResidualBasis (L : Label n) :
    Basis (Fin 0) F2 (BinaryResiduals.residual L.space L.space) :=
  (Basis.empty (↥(⊥ : Submodule F2 (Vec (Fin n))))).map
    (LinearEquiv.ofEq _ _ L.selfResidual_eq_bot.symm)

abbrev Labels (r n : ℕ) := Fin r → Label n
abbrev Values (r n : ℕ) := Fin r → Array (ι := Fin n)

def frames (F : Labels r n) (X : Values r n) : Values r n :=
  fun i => frameMap (F i).exponent (X i)

def inverseFrames (F : Labels r n) (X : Values r n) : Values r n :=
  fun i => frameMap (fun x => -(F i).exponent x) (X i)

theorem frames_inverse (F : Labels r n) (X : Values r n) :
    frames F (inverseFrames F X) = X := by
  funext i
  exact congrArg (fun T : Operator (ι := Fin n) => T (X i)) (frameMap_inverse (F i).exponent).1

theorem inverseFrames_frames (F : Labels r n) (X : Values r n) :
    inverseFrames F (frames F X) = X := by
  funext i
  exact congrArg (fun T : Operator (ι := Fin n) => T (X i)) (frameMap_inverse (F i).exponent).2

def scalarAction (M : Matrix (Fin r) (Fin r) ℂ) (X : Values r n) : Values r n :=
  FrameCommutation.pointwiseMatrix M X

theorem scalarAction_one (X : Values r n) : scalarAction (1 : Matrix (Fin r) (Fin r) ℂ) X = X := by
  funext i x
  simp [scalarAction, FrameCommutation.pointwiseMatrix, Matrix.one_apply]

theorem scalarAction_mul (M N : Matrix (Fin r) (Fin r) ℂ) (X : Values r n) :
    scalarAction (M * N) X = scalarAction M (scalarAction N X) := by
  funext i x
  exact congrFun (Matrix.mulVec_mulVec (fun j => X j x) M N).symm i

/-- The residual is geometric; its basis and orientation are the only edge data. -/
inductive NestedEdge (old new : Label n) where
  | increasing (nested : old.space ≤ new.space) (dimension : ℕ)
      (basis : Basis (Fin dimension) F2 (BinaryResiduals.residual old.space new.space))
      (orthonormal : Orthonormal (fun i => (basis i : Vec (Fin n))))
  | decreasing (nested : new.space ≤ old.space) (dimension : ℕ)
      (basis : Basis (Fin dimension) F2 (BinaryResiduals.residual new.space old.space))
      (orthonormal : Orthonormal (fun i => (basis i : Vec (Fin n))))

variable {old new : Label n}

def NestedEdge.dimension : NestedEdge old new → ℕ
  | .increasing _ d _ _ => d
  | .decreasing _ d _ _ => d

/-- An untouched role requires no calls and no dummy scalar event. -/
def NestedEdge.refl (L : Label n) : NestedEdge L L :=
  .increasing le_rfl 0 L.emptyResidualBasis (by intro i; exact Fin.elim0 i)

@[simp] theorem NestedEdge.refl_dimension (L : Label n) : (NestedEdge.refl L).dimension = 0 := rfl

def NestedEdge.word (role : Fin r) : NestedEdge old new → List (WordStep C (r * 2 ^ n))
  | .increasing _ _ b hb =>
    RoleFrameWords.roleFrameList role (fun i => (b i : Vec (Fin n))) (frame_unit _ hb) false
  | .decreasing _ _ b hb =>
    RoleFrameWords.roleFrameList role (fun i => (b i : Vec (Fin n))) (frame_unit _ hb) true

def edgeOperator (old new : Label n) : Operator (ι := Fin n) :=
  (frameMap new.exponent).comp (frameMap (fun x => -old.exponent x))

theorem NestedEdge.word_array (role : Fin r) (e : NestedEdge old new) (X : Values r n) :
    (wordMatrix (e.word role)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (Function.update X role (edgeOperator old new (X role))) := by
  cases e with
  | increasing h d b hb =>
    exact RoleFrameWords.roleFrameList_nested_array role old.space new.space h old.basis b new.basis
      old.orthonormal hb new.orthonormal false X
  | decreasing h d b hb =>
    exact RoleFrameWords.roleFrameList_nested_array role new.space old.space h new.basis b old.basis
      new.orthonormal hb old.orthonormal true X

theorem NestedEdge.word_calls (hn : 1 ≤ n) (role : Fin r) (e : NestedEdge old new) :
    wordCalls (e.word role) = e.dimension * 2 ^ (n - 1) := by
  cases e <;> simp only [NestedEdge.word, NestedEdge.dimension,
    RoleFrameWords.roleFrameList_calls hn, Fintype.card_fin]

variable {before after : Labels r n}

def edgesWord (edges : ∀ i, NestedEdge (before i) (after i)) (roles : List (Fin r)) :
    List (WordStep C (r * 2 ^ n)) := (roles.map (fun i => (edges i).word i)).flatten

theorem edgesWord_array (edges : ∀ i, NestedEdge (before i) (after i))
    (roles : List (Fin r)) (hroles : roles.Nodup) (X : Values r n) :
    (wordMatrix (edgesWord edges roles)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (fun i => if i ∈ roles then edgeOperator (before i) (after i) (X i) else X i) := by
  induction roles generalizing X with
  | nil => simp [edgesWord, wordMatrix]
  | cons i roles ih =>
    simp only [List.nodup_cons] at hroles
    simp only [edgesWord, List.map_cons, List.flatten_cons, TypedKernelWords.wordMatrix_append]
    rw [← edgesWord, ← Matrix.mulVec_mulVec, NestedEdge.word_array, ih hroles.2]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [hroles.1]
    · simp [hji]

theorem allEdgesWord_array (edges : ∀ i, NestedEdge (before i) (after i)) (X : Values r n) :
    (wordMatrix (edgesWord edges Finset.univ.toList)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (frames after (inverseFrames before X)) := by
  rw [edgesWord_array edges _ (Finset.nodup_toList _)]
  simp only [Finset.mem_toList, Finset.mem_univ, ↓reduceIte]
  rfl

theorem edgesWord_calls (hn : 1 ≤ n) (edges : ∀ i, NestedEdge (before i) (after i))
    (roles : List (Fin r)) :
    wordCalls (edgesWord edges roles) =
      (roles.map (fun i => (edges i).dimension)).sum * 2 ^ (n - 1) := by
  induction roles with
  | nil => simp [edgesWord, wordCalls]
  | cons i roles ih =>
    simp only [edgesWord, List.map_cons, List.flatten_cons, TypedKernelWords.wordCalls_append,
      NestedEdge.word_calls hn, List.sum_cons]
    rw [← edgesWord, ih]
    ring

theorem allEdgesWord_calls (hn : 1 ≤ n) (edges : ∀ i, NestedEdge (before i) (after i)) :
    wordCalls (edgesWord edges Finset.univ.toList) = (∑ i, (edges i).dimension) * 2 ^ (n - 1) := by
  rw [edgesWord_calls hn]
  congr 1
  exact Finset.sum_map_toList _ _

theorem pointwiseWord_binary_array (W : List (WordStep C r)) (X : Values r n) :
    (wordMatrix (RoleWords.pointwiseWord n W)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (scalarAction (wordMatrix W) X) := by
  unfold RoleFrameWords.binaryValues
  rw [RoleWords.pointwiseWord_array]
  rfl

/-- One certified frame transition in every role followed by a literal nonzero shear. -/
structure Event (before after : Labels r n) where
  edges : ∀ i, NestedEdge (before i) (after i)
  dest : Fin r
  source : Fin r
  distinct : dest ≠ source
  coefficient : ℂ
  nonzero : coefficient ≠ 0
  compatible : (after dest).space = (after source).space

def Event.scalarMatrix (e : Event before after) : Matrix (Fin r) (Fin r) ℂ :=
  1 + Matrix.single e.dest e.source e.coefficient

def Event.word (e : Event before after) : List (WordStep C (r * 2 ^ n)) :=
  edgesWord e.edges Finset.univ.toList ++
    RoleWords.pointwiseShearWord n e.dest e.source e.distinct e.coefficient e.nonzero

def Event.residualDimension (e : Event before after) : ℕ := ∑ i, (e.edges i).dimension

theorem Event.frames_commute (e : Event before after) (X : Values r n) :
    frames after (scalarAction e.scalarMatrix X) = scalarAction e.scalarMatrix (frames after X) := by
  apply FrameCommutation.compatible_frames_commute
  intro i j hij
  by_cases heq : i = j
  · subst j; rfl
  by_cases hi : i = e.dest
  · subst i
    by_cases hj : j = e.source
    · subst j
      exact Label.exponent_eq _ _ e.compatible
    · simp [Event.scalarMatrix, heq, Ne.symm hj] at hij
  · simp [Event.scalarMatrix, heq, Ne.symm hi] at hij

theorem Event.word_array (e : Event before after) (X : Values r n) :
    (wordMatrix e.word).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (frames after (scalarAction e.scalarMatrix (inverseFrames before X))) := by
  rw [Event.word, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
    allEdgesWord_array]
  change (wordMatrix (RoleWords.pointwiseWord n
    (RoleWords.roleShearWord e.dest e.source e.distinct e.coefficient e.nonzero))).mulVec _ = _
  rw [pointwiseWord_binary_array, RoleWords.roleShearWord_matrix]
  change RoleFrameWords.binaryValues (scalarAction e.scalarMatrix (frames after (inverseFrames before X))) = _
  rw [← Event.frames_commute]

theorem Event.word_calls (hn : 1 ≤ n) (e : Event before after) :
    wordCalls e.word = e.residualDimension * 2 ^ (n - 1) + 3 * 2 ^ n := by
  rw [Event.word, TypedKernelWords.wordCalls_append, allEdgesWord_calls hn,
    RoleWords.pointwiseShearWord_calls]
  rfl

/-- The indices enforce matching frame endpoints for every adjacent event. -/
inductive Schedule : Labels r n → Labels r n → Type
  | nil (F : Labels r n) : Schedule F F
  | cons {F G H : Labels r n} (event : Event F G) (tail : Schedule G H) : Schedule F H

variable {first last : Labels r n}

def Schedule.word : ∀ {F G : Labels r n}, Schedule F G → List (WordStep C (r * 2 ^ n))
  | _, _, .nil _ => []
  | _, _, .cons e s => e.word ++ s.word

def Schedule.scalarMatrix : ∀ {F G : Labels r n}, Schedule F G → Matrix (Fin r) (Fin r) ℂ
  | _, _, .nil _ => 1
  | _, _, .cons e s => s.scalarMatrix * e.scalarMatrix

def Schedule.residualDimension : ∀ {F G : Labels r n}, Schedule F G → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons e s => e.residualDimension + s.residualDimension

def Schedule.scalarCount : ∀ {F G : Labels r n}, Schedule F G → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ s => 1 + s.scalarCount

theorem Schedule.word_array (s : Schedule first last) (X : Values r n) :
    (wordMatrix s.word).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (frames last (scalarAction s.scalarMatrix (inverseFrames first X))) := by
  induction s generalizing X with
  | nil F => simp [Schedule.word, wordMatrix, Schedule.scalarMatrix, scalarAction_one, frames_inverse]
  | @cons F G H e s ih =>
    rw [Schedule.word, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
      Event.word_array, ih, inverseFrames_frames, ← scalarAction_mul]
    rfl

theorem Schedule.word_calls (hn : 1 ≤ n) (s : Schedule first last) :
    wordCalls s.word = s.residualDimension * 2 ^ (n - 1) + 3 * s.scalarCount * 2 ^ n := by
  induction s with
  | nil F => simp [Schedule.word, wordCalls, Schedule.residualDimension, Schedule.scalarCount]
  | cons e s ih =>
    rw [Schedule.word, TypedKernelWords.wordCalls_append, Event.word_calls hn, ih,
      Schedule.residualDimension, Schedule.scalarCount]
    ring

def Schedule.append : ∀ {F G H : Labels r n}, Schedule F G → Schedule G H → Schedule F H
  | _, _, _, .nil _, t => t
  | _, _, _, .cons e s, t => .cons e (s.append t)

theorem Schedule.append_word {middle : Labels r n} (s : Schedule first middle)
    (t : Schedule middle last) : (s.append t).word = s.word ++ t.word := by
  induction s with
  | nil F => rfl
  | cons e s ih => simp only [Schedule.append, Schedule.word, ih, List.append_assoc]

theorem Schedule.append_scalarMatrix {middle : Labels r n} (s : Schedule first middle)
    (t : Schedule middle last) : (s.append t).scalarMatrix = t.scalarMatrix * s.scalarMatrix := by
  induction s with
  | nil F => simp [Schedule.append, Schedule.scalarMatrix]
  | cons e s ih => simp only [Schedule.append, Schedule.scalarMatrix, ih, Matrix.mul_assoc]

theorem Schedule.append_residualDimension {middle : Labels r n} (s : Schedule first middle)
    (t : Schedule middle last) : (s.append t).residualDimension = s.residualDimension + t.residualDimension := by
  induction s with
  | nil F => simp [Schedule.append, Schedule.residualDimension]
  | cons e s ih => simp only [Schedule.append, Schedule.residualDimension, ih, Nat.add_assoc]

theorem Schedule.append_scalarCount {middle : Labels r n} (s : Schedule first middle)
    (t : Schedule middle last) : (s.append t).scalarCount = s.scalarCount + t.scalarCount := by
  induction s with
  | nil F => simp [Schedule.append, Schedule.scalarCount]
  | cons e s ih => simp only [Schedule.append, Schedule.scalarCount, ih, Nat.add_assoc]

/-- Instantiation requires only the scalar schedule identity, not compiled word actions. -/
theorem compile_schedule (hn : 1 ≤ n) (s : Schedule first last)
    (M : Matrix (Fin r) (Fin r) ℂ) (hscalar : s.scalarMatrix = M) :
    ∃ W : List (WordStep C (r * 2 ^ n)),
      (∀ X : Values r n, (wordMatrix W).mulVec (RoleFrameWords.binaryValues X) =
        RoleFrameWords.binaryValues (frames last (scalarAction M (inverseFrames first X)))) ∧
      wordCalls W = s.residualDimension * 2 ^ (n - 1) + 3 * s.scalarCount * 2 ^ n := by
  refine ⟨s.word, ?_, Schedule.word_calls hn s⟩
  intro X
  rw [Schedule.word_array, hscalar]

/-- Final sink edges carry no scalar shear and add no dummy scalar calls. -/
def Schedule.finishWord {middle : Labels r n} (s : Schedule first middle)
    (edges : ∀ i, NestedEdge (middle i) (last i)) : List (WordStep C (r * 2 ^ n)) :=
  s.word ++ edgesWord edges Finset.univ.toList

theorem Schedule.finishWord_array {middle : Labels r n} (s : Schedule first middle)
    (edges : ∀ i, NestedEdge (middle i) (last i)) (X : Values r n) :
    (wordMatrix (s.finishWord edges)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (frames last (scalarAction s.scalarMatrix (inverseFrames first X))) := by
  rw [Schedule.finishWord, TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec,
    Schedule.word_array, allEdgesWord_array, inverseFrames_frames]

theorem Schedule.finishWord_calls (hn : 1 ≤ n) {middle : Labels r n} (s : Schedule first middle)
    (edges : ∀ i, NestedEdge (middle i) (last i)) :
    wordCalls (s.finishWord edges) =
      (s.residualDimension + ∑ i, (edges i).dimension) * 2 ^ (n - 1) +
        3 * s.scalarCount * 2 ^ n := by
  rw [Schedule.finishWord, TypedKernelWords.wordCalls_append, Schedule.word_calls hn,
    allEdgesWord_calls hn]
  ring

theorem compile_finish_edges (hn : 1 ≤ n) {middle : Labels r n} (s : Schedule first middle)
    (edges : ∀ i, NestedEdge (middle i) (last i))
    (M : Matrix (Fin r) (Fin r) ℂ) (hscalar : s.scalarMatrix = M) :
    ∃ W : List (WordStep C (r * 2 ^ n)),
      (∀ X : Values r n, (wordMatrix W).mulVec (RoleFrameWords.binaryValues X) =
        RoleFrameWords.binaryValues (frames last (scalarAction M (inverseFrames first X)))) ∧
      wordCalls W = (s.residualDimension + ∑ i, (edges i).dimension) * 2 ^ (n - 1) +
        3 * s.scalarCount * 2 ^ n := by
  refine ⟨s.finishWord edges, ?_, Schedule.finishWord_calls hn s edges⟩
  intro X
  rw [Schedule.finishWord_array, hscalar]

end
end ExactFourierCircuits.FramedScheduleWords
