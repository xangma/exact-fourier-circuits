import NetworkTerminal
import RoleFrameWords
import StageFrames
import OAI.Computability.FourierCircuit.MonomialTools

set_option autoImplicit false

/- Literal free terminal words on all packed role/address coordinates. -/
namespace ExactFourierCircuits.TerminalWords
open OAI.ExactFourier BinaryFrames BinaryTensor FrameSpectrum NetworkTerminal
open scoped BigOperators
noncomputable section

variable {δ β : Type*}
variable {w n : ℕ}

abbrev Role (δ β : Type*) := (Fin 2 × δ) ⊕ β
abbrev Point (δ β : Type*) (n : ℕ) := Role δ β × Vec (Fin n)

/-- Literal role outer/address inner coordinates, with an explicitly supplied role equivalence. -/
def points (e : Role δ β ≃ Fin w) (n : ℕ) : Point δ β n ≃ Fin (w * 2 ^ n) :=
  (e.prodCongr (DirectionalWords.addresses n)).trans (RoleWords.roleAddresses w n)

def values (s : State δ β (Fin n)) : Point δ β n → ℂ
  | (.inl (bank, d), x) => if bank = 0 then s.x d x else s.y d x
  | (.inr b, x) => s.auxiliary b x

def pack (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) : Fin (w * 2 ^ n) → ℂ :=
  fun i => values s ((points e n).symm i)

@[simp] lemma pack_at (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) (p : Point δ β n) :
    pack e s (points e n p) = values s p := by simp [pack]

theorem pack_surjective (e : Role δ β ≃ Fin w) : Function.Surjective (pack (n := n) e) := by
  intro f
  let s : State δ β (Fin n) :=
    ⟨fun d x => f (points e n (.inl (0, d), x)),
     fun d x => f (points e n (.inl (1, d), x)),
     fun b x => f (points e n (.inr b, x))⟩
  refine ⟨s, ?_⟩
  funext i
  obtain ⟨⟨r, x⟩, rfl⟩ := (points e n).surjective i
  rw [pack_at]
  cases r with
  | inl rd => rcases rd with ⟨bank, d⟩; fin_cases bank <;> simp [values, s]
  | inr b => rfl

def translateY (u : δ → Vec (Fin n)) : Point δ β n → Point δ β n
  | (.inl (bank, d), x) => (.inl (bank, d), if bank = 0 then x else x + u d)
  | (.inr b, x) => (.inr b, x)

lemma translateY_involutive (u : δ → Vec (Fin n)) : Function.Involutive (translateY (β := β) u) := by
  rintro ⟨r, x⟩
  cases r with
  | inl rd =>
    rcases rd with ⟨bank, d⟩
    fin_cases bank <;> simp [translateY, add_assoc]
  | inr b => rfl

def translateYEquiv (u : δ → Vec (Fin n)) : Equiv.Perm (Point δ β n) :=
  { toFun := translateY u
    invFun := translateY u
    left_inv := translateY_involutive u
    right_inv := translateY_involutive u }

@[simp] lemma translateYEquiv_apply (u : δ → Vec (Fin n)) (p : Point δ β n) :
    translateYEquiv u p = translateY u p := rfl

def exchangePoint : Point δ β n → Point δ β n
  | (.inl (bank, d), x) => (.inl ((Equiv.swap 0 1) bank, d), x)
  | (.inr b, x) => (.inr b, x)

lemma exchangePoint_involutive : Function.Involutive (exchangePoint (δ := δ) (β := β) (n := n)) := by
  rintro ⟨r, x⟩
  cases r with
  | inl rd => rcases rd with ⟨bank, d⟩; simp [exchangePoint]
  | inr b => rfl

def exchangeEquiv : Equiv.Perm (Point δ β n) :=
  { toFun := exchangePoint
    invFun := exchangePoint
    left_inv := exchangePoint_involutive
    right_inv := exchangePoint_involutive }

@[simp] lemma exchangeEquiv_apply (p : Point δ β n) : exchangeEquiv p = exchangePoint p := rfl

def exchangeSign : Point δ β n → ℂ
  | (.inl (bank, _), _) => if bank = 0 then 1 else -1
  | (.inr _, _) => 1

lemma exchangeSign_nonzero (p : Point δ β n) : exchangeSign p ≠ 0 := by
  rcases p with ⟨r, x⟩
  cases r with
  | inl rd => rcases rd with ⟨bank, d⟩; fin_cases bank <;> norm_num [exchangeSign]
  | inr b => norm_num [exchangeSign]

def packedPerm (e : Role δ β ≃ Fin w) (σ : Equiv.Perm (Point δ β n)) :
    Equiv.Perm (Fin (w * 2 ^ n)) := (points e n).symm.trans (σ.trans (points e n))

/-- A pullback permutation followed by nonzero output scaling. -/
def monomial (σ : Equiv.Perm (Fin (w * 2 ^ n))) (c : Fin (w * 2 ^ n) → ℂ) :
    Matrix (Fin (w * 2 ^ n)) (Fin (w * 2 ^ n)) ℂ := fun i j => if j = σ i then c i else 0

lemma monomial_isMonomial (σ : Equiv.Perm (Fin (w * 2 ^ n)))
    (c : Fin (w * 2 ^ n) → ℂ) (hc : ∀ i, c i ≠ 0) : IsMonomial (monomial σ c) := by
  classical
  refine ⟨σ.symm, fun j => c (σ.symm j), fun j => hc _, ?_⟩
  intro i j
  have he : j = σ i ↔ i = σ.symm j := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  simp only [monomial, he]
  split_ifs with hi
  · rw [hi]
  · rfl

lemma monomial_apply (σ : Equiv.Perm (Fin (w * 2 ^ n))) (c : Fin (w * 2 ^ n) → ℂ)
    (f : Fin (w * 2 ^ n) → ℂ) (i : Fin (w * 2 ^ n)) :
    (monomial σ c).mulVec f i = c i * f (σ i) := by
  classical
  simp [monomial, Matrix.mulVec, dotProduct, ite_mul]

def translationMatrix (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :=
  monomial (packedPerm e (translateYEquiv u)) (fun _ => 1)

def exchangeMatrix (e : Role δ β ≃ Fin w) (n : ℕ) :=
  monomial (packedPerm e (exchangeEquiv (n := n))) (fun i => exchangeSign ((points e n).symm i))

lemma translationMatrix_monomial (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    IsMonomial (translationMatrix e u) := monomial_isMonomial _ _ (fun _ => one_ne_zero)

lemma exchangeMatrix_monomial (e : Role δ β ≃ Fin w) (n : ℕ) :
    IsMonomial (exchangeMatrix e n) := monomial_isMonomial _ _ (fun _ => exchangeSign_nonzero _)

/-- Translation of physical Y is chronologically first, then the signed bank exchange. -/
def correctionWord (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    List (WordStep C (w * 2 ^ n)) :=
  [.monomial (translationMatrix e u) (translationMatrix_monomial e u),
   .monomial (exchangeMatrix e n) (exchangeMatrix_monomial e n)]

theorem correctionWord_calls (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    wordCalls (correctionWord e u) = 0 := by simp [correctionWord, wordCalls, WordStep.calls]

theorem correctionWord_matrix (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    wordMatrix (correctionWord e u) = exchangeMatrix e n * translationMatrix e u := by
  simp [correctionWord, wordMatrix, WordStep.matrix]

theorem correctionWord_monomial (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    IsMonomial (wordMatrix (correctionWord e u)) := by
  rw [correctionWord_matrix]
  exact MonomialMatrix.mul (exchangeMatrix_monomial e n) (translationMatrix_monomial e u)

theorem correctionWord_unit (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n)) :
    IsUnit (wordMatrix (correctionWord e u)) := MonomialMatrix.unit _ (correctionWord_monomial e u)

def translatedY (u : δ → Vec (Fin n)) (s : State δ β (Fin n)) : State δ β (Fin n) :=
  ⟨s.x, fun d => translateMap (u d) (s.y d), s.auxiliary⟩

def signedExchange (s : State δ β (Fin n)) : State δ β (Fin n) := ⟨s.y, -s.x, s.auxiliary⟩

theorem translationMatrix_action (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (s : State δ β (Fin n)) : (translationMatrix e u).mulVec (pack e s) = pack e (translatedY u s) := by
  funext i
  obtain ⟨⟨r, x⟩, rfl⟩ := (points e n).surjective i
  rw [translationMatrix, monomial_apply, one_mul, pack_at]
  simp only [packedPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [pack_at]
  cases r with
  | inl rd =>
    rcases rd with ⟨bank, d⟩
    fin_cases bank <;> simp [translateY, values, translatedY, translateMap, Projection.translate]
  | inr b => rfl

theorem exchangeMatrix_action (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) :
    (exchangeMatrix e n).mulVec (pack e s) = pack e (signedExchange s) := by
  funext i
  obtain ⟨⟨r, x⟩, rfl⟩ := (points e n).surjective i
  rw [exchangeMatrix, monomial_apply, pack_at]
  simp only [packedPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [pack_at]
  cases r with
  | inl rd =>
    rcases rd with ⟨bank, d⟩
    fin_cases bank <;> simp [exchangePoint, exchangeSign, values, signedExchange]
  | inr b => simp [exchangeSign, exchangePoint, values, signedExchange]

/-- Exact whole-state action, with arbitrary dirty auxiliary arrays. -/
theorem correctionWord_action (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (s : State δ β (Fin n)) :
    (wordMatrix (correctionWord e u)).mulVec (pack e s) = pack e (correction u s) := by
  rw [correctionWord_matrix, ← Matrix.mulVec_mulVec, translationMatrix_action, exchangeMatrix_action]
  rfl

theorem corrected_endpoint_word (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (hu : ∀ d, dot (u d) (u d) = 1) (s : State δ β (Fin n)) :
    (wordMatrix (correctionWord e u)).mulVec
      (pack e (sinkFrames u (exchange (sourceInverse u s)))) = pack e (ordinary s) := by
  rw [correctionWord_action, corrected_source_sink_exchange u hu]

def coordinateWord (n : ℕ) : List (WordStep C (2 ^ n)) :=
  FrameWords.signedFrameList (unit : Fin n → Vec (Fin n))
    (fun i => by rw [dot_units]; simp) false Finset.univ.toList

theorem coordinateWord_action (n : ℕ) :
    FrameWords.binaryAction (wordMatrix (coordinateWord n)) = frameMap weightModFour := by
  rw [coordinateWord, FrameWords.signedFrameList_action, coordinate_word_standard]

theorem coordinateWord_calls (n : ℕ) (hn : 1 ≤ n) :
    wordCalls (coordinateWord n) = n * 2 ^ (n - 1) := by
  rw [coordinateWord, FrameWords.signedFrameList_calls hn]
  simp

def copyCoordinates (w n : ℕ) : (Σ _ : Fin w, Fin (2 ^ n)) ≃ Fin (w * 2 ^ n) :=
  (Equiv.sigmaEquivProd (Fin w) (Fin (2 ^ n))).trans (RoleWords.roleAddresses w n)

/-- A literal ordinary address word on each physical role. -/
def ordinaryWord (w n : ℕ) : List (WordStep C (w * 2 ^ n)) :=
  TensorWords.parallelWord (copyCoordinates w n) (coordinateWord n)

def ordinaryMatrix (w n : ℕ) : Matrix (Fin (w * 2 ^ n)) (Fin (w * 2 ^ n)) ℂ :=
  Matrix.reindex (RoleWords.roleAddresses w n) (RoleWords.roleAddresses w n)
    (Matrix.kronecker (1 : Matrix (Fin w) (Fin w) ℂ) (wordMatrix (coordinateWord n)))

theorem ordinaryWord_matrix (w n : ℕ) : wordMatrix (ordinaryWord w n) = ordinaryMatrix w n := by
  rw [ordinaryWord, TensorWords.parallelWord_matrix]
  ext i j
  obtain ⟨⟨r, a⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective i
  obtain ⟨⟨s, b⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective j
  simp [ordinaryMatrix, copyCoordinates, Matrix.reindex_apply, Matrix.blockDiagonal'_apply,
    Matrix.one_apply]

theorem ordinaryWord_calls (w n : ℕ) (hn : 1 ≤ n) :
    wordCalls (ordinaryWord w n) = w * (n * 2 ^ (n - 1)) := by
  rw [ordinaryWord, TensorWords.parallelWord_calls, coordinateWord_calls n hn]

theorem ordinaryMatrix_role_apply (w n : ℕ) (X : Fin w → Fin (2 ^ n) → ℂ)
    (r : Fin w) (a : Fin (2 ^ n)) :
    (ordinaryMatrix w n).mulVec (RoleWords.arrayValues n X) (RoleWords.roleAddresses w n (r, a)) =
      (wordMatrix (coordinateWord n)).mulVec (X r) a := by
  rw [ordinaryMatrix, reindex_mulVec]
  simp [RoleWords.arrayValues, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

theorem ordinaryWord_binary_action (X : Fin w → Array (ι := Fin n)) :
    (wordMatrix (ordinaryWord w n)).mulVec (RoleFrameWords.binaryValues X) =
      RoleFrameWords.binaryValues (fun r => frameMap weightModFour (X r)) := by
  rw [ordinaryWord_matrix]
  funext i
  obtain ⟨⟨r, a⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective i
  obtain ⟨x, rfl⟩ := (DirectionalWords.addresses n).surjective a
  rw [RoleFrameWords.binaryValues_at, RoleFrameWords.binaryValues, ordinaryMatrix_role_apply]
  have h := congrArg (fun T : Operator (ι := Fin n) => T (X r) x) (coordinateWord_action n)
  simpa only [RoleFrameWords.binaryAction_apply] using h

def stateArrays (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) : Fin w → Array (ι := Fin n) :=
  fun r x => values s (e.symm r, x)

lemma pack_binaryValues (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) :
    pack e s = RoleFrameWords.binaryValues (stateArrays e s) := by
  funext i
  obtain ⟨⟨r, x⟩, rfl⟩ := (points e n).surjective i
  rw [pack_at]
  change values s (r, x) = RoleFrameWords.binaryValues (stateArrays e s)
    (RoleWords.roleAddresses w n (e r, DirectionalWords.addresses n x))
  simp [stateArrays]

lemma stateArrays_ordinary (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) :
    stateArrays e (ordinary s) = fun r => frameMap weightModFour (stateArrays e s r) := by
  funext r
  change (fun x => values (ordinary s) (e.symm r, x)) =
    frameMap weightModFour (fun x => values s (e.symm r, x))
  generalize e.symm r = r'
  cases r' with
  | inl rd => rcases rd with ⟨bank, d⟩; fin_cases bank <;> rfl
  | inr b => rfl

theorem ordinaryWord_action (e : Role δ β ≃ Fin w) (s : State δ β (Fin n)) :
    (wordMatrix (ordinaryWord w n)).mulVec (pack e s) = pack e (ordinary s) := by
  rw [pack_binaryValues, ordinaryWord_binary_action, pack_binaryValues, stateArrays_ordinary]

lemma matrix_eq_of_mulVec {a : ℕ} (M N : Matrix (Fin a) (Fin a) ℂ)
    (h : ∀ f, M.mulVec f = N.mulVec f) : M = N := by
  ext i j
  have hh := congrFun (h (fun k => if k = j then 1 else 0)) i
  simpa [Matrix.mulVec, dotProduct, mul_ite] using hh

/-- This variant also applies to column endpoints: the combined translation need not have odd norm. -/
theorem master_terminal_bridge_of_endpoint (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (W : List (WordStep C (w * 2 ^ n))) (endpoint : State δ β (Fin n) → State δ β (Fin n))
    (hW : ∀ s, (wordMatrix W).mulVec (pack e s) = pack e (endpoint s))
    (hEnd : ∀ s, correction u (endpoint s) = ordinary s) :
    wordMatrix (W ++ correctionWord e u) = wordMatrix (ordinaryWord w n) := by
  apply matrix_eq_of_mulVec
  intro f
  obtain ⟨s, rfl⟩ := pack_surjective e f
  rw [TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec, hW,
    correctionWord_action, hEnd, ordinaryWord_action]

/-- Once the actual framed master word is supplied, terminal correction gives the ordinary word matrix. -/
theorem master_terminal_bridge (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (hu : ∀ d, dot (u d) (u d) = 1) (W : List (WordStep C (w * 2 ^ n)))
    (hW : ∀ s : State δ β (Fin n), (wordMatrix W).mulVec (pack e s) =
      pack e (sinkFrames u (exchange (sourceInverse u s)))) :
    wordMatrix (W ++ correctionWord e u) = wordMatrix (ordinaryWord w n) := by
  apply matrix_eq_of_mulVec
  intro f
  obtain ⟨s, rfl⟩ := pack_surjective e f
  rw [TypedKernelWords.wordMatrix_append, ← Matrix.mulVec_mulVec, hW,
    corrected_endpoint_word e u hu, ordinaryWord_action]

theorem master_terminal_calls (e : Role δ β ≃ Fin w) (u : δ → Vec (Fin n))
    (W : List (WordStep C (w * 2 ^ n))) : wordCalls (W ++ correctionWord e u) = wordCalls W := by
  rw [TypedKernelWords.wordCalls_append, correctionWord_calls, add_zero]

/-- A fixed exact identification of the actual three-factor bank coordinates. -/
def bankCoordinates (h : ℕ) : (Fin 3 → Fin h) ≃ Fin (h ^ 3) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

def finiteBankDirection (h : ℕ) (d : TripleNetwork.Bank (Fin h)) : Vec (Fin (h ^ 3)) :=
  StageFrames.coordinates (bankCoordinates h) (bankDirection h d)

lemma finiteBankDirection_norm (h : ℕ) (d : TripleNetwork.Bank (Fin h)) :
    dot (finiteBankDirection h d) (finiteBankDirection h d) = 1 := by
  rw [finiteBankDirection, StageFrames.coordinates_dot, bankDirection_norm]

theorem triple_corrected_endpoint_word (h : ℕ)
    (e : Role (TripleNetwork.Bank (Fin h)) β ≃ Fin w)
    (s : State (TripleNetwork.Bank (Fin h)) β (Fin (h ^ 3))) :
    (wordMatrix (correctionWord e (finiteBankDirection h))).mulVec
      (pack e (sinkFrames (finiteBankDirection h)
        (exchange (sourceInverse (finiteBankDirection h) s)))) = pack e (ordinary s) :=
  corrected_endpoint_word e _ (finiteBankDirection_norm h) s

theorem triple_master_terminal_bridge (h : ℕ)
    (e : Role (TripleNetwork.Bank (Fin h)) β ≃ Fin w)
    (W : List (WordStep C (w * 2 ^ (h ^ 3))))
    (hW : ∀ s : State (TripleNetwork.Bank (Fin h)) β (Fin (h ^ 3)),
      (wordMatrix W).mulVec (pack e s) = pack e (sinkFrames (finiteBankDirection h)
        (exchange (sourceInverse (finiteBankDirection h) s)))) :
    wordMatrix (W ++ correctionWord e (finiteBankDirection h)) = wordMatrix (ordinaryWord w (h ^ 3)) :=
  master_terminal_bridge e _ (finiteBankDirection_norm h) W hW

end
end ExactFourierCircuits.TerminalWords
