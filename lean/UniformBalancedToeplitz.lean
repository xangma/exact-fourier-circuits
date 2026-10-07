import UniformToeplitzChunkWord
import OAI.Computability.FourierCircuit.ToeplitzCross

set_option autoImplicit false

/-! Constructive balanced Toeplitz words. Integer partition/address construction
is separate from semantic complex coefficients and from fixed RAM production. -/
namespace ExactFourierCircuits.UniformBalancedToeplitz
open OAI.ExactFourier TypedKernelWords
open UniformWorkspacePlanner UniformToeplitzChunkWord
open scoped BigOperators

/-- Actual ragged block size, in the planner's exact order. -/
def size (n b : ℕ) (i : Fin (chunkCount n b)) : ℕ := min b (n-i.val*b)

theorem size_mem (n b : ℕ) (i : Fin (chunkCount n b)) : size n b i∈chunkSizes n b := by
  exact List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩

theorem size_pos (n b : ℕ) (hb : 0<b) (i : Fin (chunkCount n b)) : 0<size n b i :=
  chunk_pos hb (size_mem n b i)

theorem offset_lt (n b : ℕ) (hb : 0<b) (i : Fin (chunkCount n b)) : i.val*b<n := by
  have h := size_pos n b hb i
  dsimp [size] at h
  omega

/-- Every literal chunk coordinate is inside the original axis. -/
def blockEmbedding (n b : ℕ) (hb : 0<b) (i : Fin (chunkCount n b)) : Fin (size n b i) ↪ Fin n where
  toFun j := ⟨i.val*b+j.val,by
    have hj := j.isLt
    dsimp [size] at hj
    have hi := offset_lt n b hb i
    omega⟩
  inj' j k h := Fin.ext (by have := congrArg Fin.val h;dsimp at this;omega)

theorem ceiling_cover (n b : ℕ) (hb : 0<b) : n ≤ chunkCount n b*b := by
  have hrem := Nat.mod_lt (n+b-1) hb
  have hdiv := Nat.mod_add_div (n+b-1) b
  dsimp [chunkCount]
  have he : b*((n+b-1)/b)=((n+b-1)/b)*b := Nat.mul_comm _ _
  omega

def blockIndex (n b : ℕ) (hb : 0<b) (q : Fin n) : Fin (chunkCount n b) :=
  ⟨q.val/b,(Nat.div_lt_iff_lt_mul hb).mpr (q.isLt.trans_le (ceiling_cover n b hb))⟩

def localIndex (n b : ℕ) (hb : 0<b) (q : Fin n) : Fin (size n b (blockIndex n b hb q)) :=
  ⟨q.val%b,by
    have hm := Nat.mod_lt q.val hb
    have he := Nat.mod_add_div q.val b
    have hi := q.isLt
    dsimp [size,blockIndex]
    have hc : b*(q.val/b)=(q.val/b)*b := Nat.mul_comm _ _
    omega⟩

theorem fin_heq {n m : ℕ} {i : Fin n} {j : Fin m} (h : n=m) (hv : i.val=j.val) : HEq i j := by
  subst m
  exact heq_of_eq (Fin.ext hv)

/-- Quotient/remainder are the inverse of the actual offset enumeration. -/
def blocks (n b : ℕ) (hb : 0<b) : (Σ i : Fin (chunkCount n b), Fin (size n b i)) ≃ Fin n where
  toFun q := blockEmbedding n b hb q.1 q.2
  invFun q := ⟨blockIndex n b hb q,localIndex n b hb q⟩
  left_inv := by
    rintro ⟨i,j⟩
    have hj : j.val<b := j.isLt.trans_le (min_le_left _ _)
    have hdiv : (i.val*b+j.val)/b=i.val := by
      rw [Nat.mul_comm i.val b,Nat.mul_add_div hb,Nat.div_eq_of_lt hj,Nat.add_zero]
    have hmod : (i.val*b+j.val)%b=j.val := by
      rw [Nat.mul_comm i.val b,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
    have hi : blockIndex n b hb (blockEmbedding n b hb i j)=i := Fin.ext hdiv
    exact Sigma.ext hi (fin_heq (congrArg (size n b) hi) hmod)
  right_inv q := Fin.ext (by
    change q.val/b*b+q.val%b=q.val
    have he := Nat.mod_add_div q.val b
    have hc := Nat.mul_comm b (q.val/b)
    omega)

@[simp] theorem blocks_apply (n b : ℕ) (hb : 0<b)
    (i : Fin (chunkCount n b)) (j : Fin (size n b i)) :
    blocks n b hb ⟨i,j⟩=blockEmbedding n b hb i j := rfl

theorem chunkCount_le (n b : ℕ) (hb : 0<b) : chunkCount n b ≤ n := by
  change (n+b-1)/b ≤ n
  apply (Nat.div_le_iff_le_mul_add_pred hb).mpr
  have hm : n*b=n+n*(b-1) := by
    have he : b=1+(b-1) := by omega
    conv_lhs => rw [he]
    ring
  have hc := Nat.mul_comm b n
  omega

noncomputable section
variable {v e a : ℕ}

def rectangle (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ) : Matrix (Fin v) (Fin v) ℂ :=
  ∑ i, ∑ j, Matrix.single (target i) (source j) (M i j)

theorem rectangle_row (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ) (i : Fin a) (p : Fin v) :
    rectangle source target M (target i) p=∑ j, if source j=p then M i j else 0 := by
  classical
  simp only [rectangle,Matrix.single,Matrix.sum_apply,Matrix.of_apply,target.injective.eq_iff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji;simp [hji]
  · simp

theorem rectangle_off (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ) (q p : Fin v) (hq : q∉Set.range target) :
    rectangle source target M q p=0 := by
  classical
  have hn (i : Fin a) : target i≠q := fun hi=>hq ⟨i,hi⟩
  simp [rectangle,Matrix.single,Matrix.sum_apply,Matrix.of_apply,hn]

theorem rectangle_action (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ) (X : Fin v → ℂ) (i : Fin a) :
    (rectangle source target M).mulVec X (target i)=M.mulVec (X ∘ source) i := by
  classical
  simp only [Matrix.mulVec,dotProduct,rectangle_row,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

theorem update_eq {W : List (WordStep C v)} (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ)
    (hon : ∀ X i, (wordMatrix W).mulVec X (target i)=X (target i)+M.mulVec (X ∘ source) i)
    (hoff : ∀ X q, q∉Set.range target → (wordMatrix W).mulVec X q=X q) :
    wordMatrix W=1+rectangle source target M := by
  classical
  ext q p
  have hact : ∀ X, (wordMatrix W).mulVec X q=(1+rectangle source target M).mulVec X q := by
    intro X
    rw [Matrix.add_mulVec,Matrix.one_mulVec]
    by_cases hq : q∈Set.range target
    · obtain ⟨i,rfl⟩ := hq
      simpa only [Pi.add_apply,rectangle_action] using hon X i
    · rw [hoff X q hq]
      have hz : (rectangle source target M).mulVec X q=0 := by
        simp only [Matrix.mulVec,dotProduct,rectangle_off source target M q _ hq,zero_mul,Finset.sum_const_zero]
      simp [hz]
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using hact (Pi.single p 1)

/-- Canonical contiguous lower/upper halves; no padding coordinate is introduced. -/
def coordinates (n : ℕ) : (Fin (n/2) ⊕ Fin (n-n/2)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

def left (n : ℕ) : Fin (n/2) ↪ Fin n :=
  (⟨Sum.inl,fun _ _ h=>Sum.inl.inj h⟩ : Fin (n/2) ↪ Fin (n/2) ⊕ Fin (n-n/2)).trans (coordinates n).toEmbedding

def right (n : ℕ) : Fin (n-n/2) ↪ Fin n :=
  (⟨Sum.inr,fun _ _ h=>Sum.inr.inj h⟩ : Fin (n-n/2) ↪ Fin (n/2) ⊕ Fin (n-n/2)).trans (coordinates n).toEmbedding

theorem left_right (n : ℕ) (i : Fin (n/2)) (j : Fin (n-n/2)) : left n i≠right n j := by
  intro h
  have hh : Sum.inl i=Sum.inr j := (coordinates n).injective h
  cases hh

theorem size_end (n b : ℕ) (hb : 0<b) (i : Fin (chunkCount n b)) : i.val*b+size n b i ≤ n := by
  have ho := offset_lt n b hb i
  have hs : size n b i ≤ n-i.val*b := min_le_right _ _
  omega

def pairSource (n : ℕ) (hv : 0<selected n) (j : Fin (chunkCount (n/2) (selected n))) :
    Fin (size (n/2) (selected n) j) ↪ Fin n :=
  (blockEmbedding (n/2) (selected n) hv j).trans (left n)

def pairTarget (n : ℕ) (hv : 0<selected n) (i : Fin (chunkCount (n-n/2) (selected n))) :
    Fin (size (n-n/2) (selected n) i) ↪ Fin n :=
  (blockEmbedding (n-n/2) (selected n) hv i).trans (right n)

def pairs (n : ℕ) : List (Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :=
  (List.finRange (chunkCount (n-n/2) (selected n))).flatMap fun i =>
    (List.finRange (chunkCount (n/2) (selected n))).map fun j => (i,j)

def pairWord (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) : List (WordStep C n) :=
  let a := size (n-n/2) (selected n) q.1
  let e := size (n/2) (selected n) q.2
  let i₀ := n/2+q.1.val*selected n
  let j₀ := q.2.val*selected n
  let M := fun i j => ToeplitzLayers.cross (n/2) (PowerSeries.coeff · f)
    (PowerSeries.coeff · f⁻¹) (i₀+i) (j₀+j)
  let v₀ := fun i => -PowerSeries.coeff (i₀+i-n/2) f
  let w₀ := fun j => PowerSeries.coeff (n/2-(j₀+j)) f⁻¹
  selectedWord hv (size_mem (n-n/2) (selected n) q.1) (size_mem (n/2) (selected n) q.2)
    (pairSource n hv q.2) (pairTarget n hv q.1)
    (fun _ _=>left_right n _ _) (UniformToeplitzCrossDAG.sharedBank (exponent a e)
      (UniformToeplitzCrossDAG.rankKernels (exponent a e) a e M v₀ w₀))

def correctionWord (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) : List (WordStep C n) :=
  ((pairs n).map (pairWord n hv f)).flatten

/-- Actual measured recursion, with the finite direct fallback and balanced halves. -/
inductive Plan : ℕ → Type
  | direct (n : ℕ) (cap : n<196) : Plan n
  | split (n : ℕ) (hn : 2 ≤ n) (hv : 0<selected n) (L : Plan (n/2)) (R : Plan (n-n/2)) : Plan n

def plan (n : ℕ) : Plan n :=
  if hb : n<2 ∨ selected n=0 then
    .direct n (by rcases hb with h|h;omega;exact fallback_below_196 h)
  else
    .split n (by omega) (by omega) (plan (n/2)) (plan (n-n/2))
termination_by n
decreasing_by all_goals omega

/-- Literal diagonal words precede the cross correction. -/
def render {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    List (WordStep C n) :=
  match P with
  | .direct n _ => if hn : 0<n then
      UniformDirectToeplitz.word (fun i=>PowerSeries.coeff i.val f) hn
        (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf)
    else []
  | .split n _ hv L R =>
      TensorWords.embeddedWord (left n) (render L f hf) ++
      TensorWords.embeddedWord (right n) (render R f hf) ++ correctionWord n hv f

def word (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (WordStep C n) :=
  render (plan n) f hf

theorem rectangle_mul_zero {e' a' : ℕ} (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (M : Matrix (Fin a) (Fin e) ℂ) (source' : Fin e' ↪ Fin v) (target' : Fin a' ↪ Fin v)
    (N : Matrix (Fin a') (Fin e') ℂ) (h : ∀ i j, source i≠target' j) :
    rectangle source target M * rectangle source' target' N=0 := by
  classical
  simp only [rectangle,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  apply Matrix.single_mul_single_of_ne
  exact h l i

theorem update_prod {ι : Type} (F : ι → Matrix (Fin v) (Fin v) ℂ)
    (hF : ∀ i j, F i*F j=0) (L : List ι) :
    (L.map (fun i=>1+F i)).prod=1+(L.map F).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hz : F i*(L.map F).sum=0 := by
      clear ih
      induction L with
      | nil => simp
      | cons j L ih => simp [mul_add,hF,ih]
    simp only [List.map_cons,List.prod_cons,List.sum_cons,ih]
    simp only [add_mul,mul_add,one_mul,mul_one,hz,add_zero]
    abel

theorem wordList_updates {ι : Type} (W : ι → List (WordStep C v))
    (F : ι → Matrix (Fin v) (Fin v) ℂ) (hW : ∀ i, wordMatrix (W i)=1+F i)
    (hF : ∀ i j, F i*F j=0) (L : List ι) :
    wordMatrix ((L.map W).flatten)=1+(L.map F).sum := by
  rw [TensorWords.wordMatrix_flatten,List.map_map]
  simp only [Function.comp_def,hW]
  rw [←List.map_reverse,update_prod F hF,List.map_reverse,List.sum_reverse]

def pairMatrix (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) : Matrix (Fin n) (Fin n) ℂ :=
  rectangle (pairSource n hv q.2) (pairTarget n hv q.1)
    (fun i j=>ToeplitzLayers.cross (n/2) (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹)
      (n/2+q.1.val*selected n+i.val) (q.2.val*selected n+j.val))

theorem pairWord_matrix (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    wordMatrix (pairWord n hv f q)=1+pairMatrix n hv f q := by
  apply update_eq (pairSource n hv q.2) (pairTarget n hv q.1)
  · intro X i
    exact congrFun (selectedToeplitzWord_spec hv (size_mem _ _ q.1) (size_mem _ _ q.2)
      (pairSource n hv q.2) (pairTarget n hv q.1) (fun _ _=>left_right n _ _)
      (n/2) (n/2+q.1.val*selected n) (q.2.val*selected n)
      (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (by omega)
      (size_end (n/2) (selected n) hv q.2) X) (Sum.inr i)
  · intro X i hi
    exact selectedWord_other hv (size_mem _ _ q.1) (size_mem _ _ q.2)
      (pairSource n hv q.2) (pairTarget n hv q.1) (fun _ _=>left_right n _ _) _ X i hi

theorem pairMatrix_mul (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (p q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    pairMatrix n hv f p*pairMatrix n hv f q=0 :=
  rectangle_mul_zero _ _ _ _ _ _ (fun _ _=>left_right n _ _)

theorem correctionWord_matrix_sum (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    wordMatrix (correctionWord n hv f)=1+((pairs n).map (pairMatrix n hv f)).sum :=
  wordList_updates _ _ (pairWord_matrix n hv f) (pairMatrix_mul n hv f) _

theorem pairs_sum {M : Type} [AddCommMonoid M] (n : ℕ)
    (F : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n)) → M) :
    ((pairs n).map F).sum=∑ i,∑ j,F (i,j) := by
  unfold pairs
  rw [List.map_flatMap,List.flatMap_def,List.sum_flatten]
  simp only [List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def]

def crossMatrix (n : ℕ) (f : PowerSeries ℂ) : Matrix (Fin (n-n/2)) (Fin (n/2)) ℂ :=
  fun i j=>ToeplitzLayers.cross (n/2) (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (n/2+i.val) j.val

def entrySingle (n : ℕ) (f : PowerSeries ℂ) (i : Fin (n-n/2)) (j : Fin (n/2)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single (right n i) (left n j) (crossMatrix n f i j)

theorem pairMatrix_eq_sum (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (i : Fin (chunkCount (n-n/2) (selected n))) (j : Fin (chunkCount (n/2) (selected n))) :
    pairMatrix n hv f (i,j)=∑ p : Fin (size (n-n/2) (selected n) i),
      ∑ q : Fin (size (n/2) (selected n) j),
        entrySingle n f (blocks (n-n/2) (selected n) hv ⟨i,p⟩) (blocks (n/2) (selected n) hv ⟨j,q⟩) := by
  unfold pairMatrix rectangle
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change Matrix.single _ _ (ToeplitzLayers.cross _ _ _ (n/2+i.val*selected n+p.val) (j.val*selected n+q.val))=
    Matrix.single _ _ (ToeplitzLayers.cross _ _ _ (n/2+(i.val*selected n+p.val)) (j.val*selected n+q.val))
  rw [Nat.add_assoc]
  rfl

theorem pairMatrix_total (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    ((pairs n).map (pairMatrix n hv f)).sum=rectangle (left n) (right n) (crossMatrix n f) := by
  classical
  rw [pairs_sum]
  simp_rw [pairMatrix_eq_sum]
  calc
    _ = ∑ i,∑ p : Fin (size (n-n/2) (selected n) i),∑ j,∑ q : Fin (size (n/2) (selected n) j),
        entrySingle n f (blocks (n-n/2) (selected n) hv ⟨i,p⟩) (blocks (n/2) (selected n) hv ⟨j,q⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : (Σ j : Fin (chunkCount (n-n/2) (selected n)),Fin (size (n-n/2) (selected n) j)),
        ∑ j : (Σ k : Fin (chunkCount (n/2) (selected n)),Fin (size (n/2) (selected n) k)),
        entrySingle n f (blocks (n-n/2) (selected n) hv i) (blocks (n/2) (selected n) hv j) := by
      simp only [Fintype.sum_sigma]
    _ = rectangle (left n) (right n) (crossMatrix n f) := by
      unfold rectangle
      apply Fintype.sum_equiv (blocks (n-n/2) (selected n) hv)
      intro i
      exact (blocks (n/2) (selected n) hv).sum_comp (entrySingle n f (blocks (n-n/2) (selected n) hv i))

theorem correctionWord_matrix (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    wordMatrix (correctionWord n hv f)=1+rectangle (left n) (right n) (crossMatrix n f) := by
  rw [correctionWord_matrix_sum,pairMatrix_total]

theorem right_not_left (n : ℕ) (j : Fin (n-n/2)) : right n j∉Set.range (left n) := by
  rintro ⟨i,h⟩
  exact left_right n i j h

theorem left_not_right (n : ℕ) (i : Fin (n/2)) : left n i∉Set.range (right n) := by
  rintro ⟨j,h⟩
  exact left_right n i j h.symm

theorem rectangle_blocks (n : ℕ) (E : Matrix (Fin (n-n/2)) (Fin (n/2)) ℂ) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm (rectangle (left n) (right n) E)=
      Matrix.fromBlocks 0 0 E 0 := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · change rectangle (left n) (right n) E (left n i) (left n j)=0
    exact rectangle_off _ _ _ _ _ (left_not_right n i)
  · change rectangle (left n) (right n) E (left n i) (right n j)=0
    exact rectangle_off _ _ _ _ _ (left_not_right n i)
  · change rectangle (left n) (right n) E (right n i) (left n j)=E i j
    rw [rectangle_row]
    simp [(left n).injective.eq_iff]
  · change rectangle (left n) (right n) E (right n i) (right n j)=0
    rw [rectangle_row]
    simp [left_right]

theorem correctionWord_blocks (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm (wordMatrix (correctionWord n hv f))=
      Matrix.fromBlocks 1 0 (crossMatrix n f) 1 := by
  rw [correctionWord_matrix]
  change (Matrix.reindexAlgEquiv ℂ ℂ (coordinates n).symm) (1+rectangle (left n) (right n) (crossMatrix n f))=_
  rw [map_add,map_one]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [rectangle_blocks,←Matrix.fromBlocks_one,Matrix.fromBlocks_add]
  simp

theorem embeddedLeft_blocks (n : ℕ) (L : Matrix (Fin (n/2)) (Fin (n/2)) ℂ) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm (Embedded.matrix (left n) L)=
      Matrix.fromBlocks L 0 0 1 := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · exact Embedded.matrix_on (left n) L i j
  · change Embedded.matrix (left n) L (left n i) (right n j)=0
    rw [Embedded.matrix_off_col _ _ _ _ (right_not_left n j)]
    simp [left_right]
  · change Embedded.matrix (left n) L (right n i) (left n j)=0
    rw [Embedded.matrix_off_row _ _ _ _ (right_not_left n i)]
    simp [Ne.symm (left_right n j i)]
  · change Embedded.matrix (left n) L (right n i) (right n j)=_
    rw [Embedded.matrix_off_row _ _ _ _ (right_not_left n i)]
    simp [(right n).injective.eq_iff]
    exact Matrix.one_apply.symm

theorem embeddedRight_blocks (n : ℕ) (R : Matrix (Fin (n-n/2)) (Fin (n-n/2)) ℂ) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm (Embedded.matrix (right n) R)=
      Matrix.fromBlocks 1 0 0 R := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · change Embedded.matrix (right n) R (left n i) (left n j)=_
    rw [Embedded.matrix_off_row _ _ _ _ (left_not_right n i)]
    simp [(left n).injective.eq_iff]
    exact Matrix.one_apply.symm
  · change Embedded.matrix (right n) R (left n i) (right n j)=0
    rw [Embedded.matrix_off_row _ _ _ _ (left_not_right n i)]
    simp [left_right]
  · change Embedded.matrix (right n) R (right n i) (left n j)=0
    rw [Embedded.matrix_off_col _ _ _ _ (left_not_right n j)]
    simp [Ne.symm (left_right n j i)]
  · exact Embedded.matrix_on (right n) R i j

theorem diagonalWord_blocks (n : ℕ) (L : List (WordStep C (n/2))) (R : List (WordStep C (n-n/2))) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm
      (wordMatrix (TensorWords.embeddedWord (left n) L ++ TensorWords.embeddedWord (right n) R))=
      Matrix.fromBlocks (wordMatrix L) 0 0 (wordMatrix R) := by
  rw [wordMatrix_append,TensorWords.embeddedWord_matrix,TensorWords.embeddedWord_matrix]
  change (Matrix.reindexAlgEquiv ℂ ℂ (coordinates n).symm) (Embedded.matrix (right n) _*Embedded.matrix (left n) _)=_
  rw [map_mul]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [embeddedRight_blocks,embeddedLeft_blocks,Matrix.fromBlocks_multiply]
  simp

theorem crossMatrix_mul (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    crossMatrix n f*CoefficientTime.truncMatrix (n/2) f=
      ToeplitzLayers.lowerCross (n/2) (n-n/2) (PowerSeries.coeff · f) := by
  unfold crossMatrix
  rw [←ToeplitzLayers.cross_mul,Matrix.mul_assoc,←CoefficientTime.truncMatrix_mul,
    mul_comm f⁻¹ f,PowerSeries.mul_inv_cancel _ hf,CoefficientTime.truncMatrix_one,Matrix.mul_one]

theorem trunc_blocks (n : ℕ) (f : PowerSeries ℂ) :
    Matrix.reindex (coordinates n).symm (coordinates n).symm (CoefficientTime.truncMatrix n f)=
      Matrix.fromBlocks (CoefficientTime.truncMatrix (n/2) f) 0
        (ToeplitzLayers.lowerCross (n/2) (n-n/2) (PowerSeries.coeff · f))
        (CoefficientTime.truncMatrix (n-n/2) f) := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · change (if n/2+j.val ≤ i.val then PowerSeries.coeff (i.val-(n/2+j.val)) f else 0)=0
    rw [ite_eq_right (by have := i.isLt;omega)]
  · change (if j.val ≤ n/2+i.val then PowerSeries.coeff (n/2+i.val-j.val) f else 0)=_
    rw [ite_eq_left (by have := j.isLt;omega)]
    rfl
  · change (if n/2+j.val ≤ n/2+i.val then PowerSeries.coeff ((n/2+i.val)-(n/2+j.val)) f else 0)=_
    simp only [Nat.add_le_add_iff_left,Nat.add_sub_add_left]
    rfl

theorem render_matrix {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordMatrix (render P f hf)=CoefficientTime.truncMatrix n f := by
  induction P with
  | direct n cap =>
    dsimp only [render]
    split_ifs with hn
    · rw [UniformDirectToeplitz.word_matrix]
      rfl
    · have hzero : n=0 := by omega
      subst n
      ext i j
      exact Fin.elim0 i
  | split n hn hv L R ihL ihR =>
    change wordMatrix (TensorWords.embeddedWord (left n) (render L f hf) ++
      TensorWords.embeddedWord (right n) (render R f hf) ++ correctionWord n hv f)=_
    apply (Matrix.reindexAlgEquiv ℂ ℂ (coordinates n).symm).injective
    rw [wordMatrix_append,map_mul]
    simp only [Matrix.coe_reindexAlgEquiv]
    rw [correctionWord_blocks,diagonalWord_blocks,ihL,ihR,Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero,Matrix.zero_mul,Matrix.one_mul,zero_add,add_zero]
    rw [crossMatrix_mul n f hf,trunc_blocks]

theorem word_matrix (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordMatrix (word n f hf)=CoefficientTime.truncMatrix n f := render_matrix (plan n) f hf

theorem word_action (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) (X : Fin n → ℂ) :
    (wordMatrix (word n f hf)).mulVec X=(CoefficientTime.truncMatrix n f).mulVec X := by
  rw [word_matrix]

theorem pairWord_call_bound (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    wordCalls (pairWord n hv f q) ≤ 48*n :=
  selectedWord_call_bound hv (size_mem _ _ q.1) (size_mem _ _ q.2)
    (pairSource n hv q.2) (pairTarget n hv q.1) (fun _ _=>left_right n _ _) _

theorem pairWord_depth (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    Layered (wordMatrix (pairWord n hv f q)) (1848*(8*Nat.clog 2 n+23)) :=
  selectedWord_depth hv (size_mem _ _ q.1) (size_mem _ _ q.2)
    (pairSource n hv q.2) (pairTarget n hv q.1) (fun _ _=>left_right n _ _) _

theorem pairs_length (n : ℕ) : (pairs n).length=chunkCount (n-n/2) (selected n)*chunkCount (n/2) (selected n) := by
  simp [pairs,List.length_flatMap]

theorem correctionWord_call_bound (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    wordCalls (correctionWord n hv f) ≤ 48*n*((n-n/2)*(n/2)) := by
  rw [correctionWord,TensorWords.wordCalls_flatten,List.map_map]
  simp only [Function.comp_def]
  rw [pairs_sum]
  have h : (∑ i,∑ j,wordCalls (pairWord n hv f (i,j))) ≤
      ∑ _i : Fin (chunkCount (n-n/2) (selected n)),∑ _j : Fin (chunkCount (n/2) (selected n)),48*n := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact pairWord_call_bound n hv f (i,j)
  have ha := chunkCount_le (n-n/2) (selected n) hv
  have hs := chunkCount_le (n/2) (selected n) hv
  have hh := Nat.mul_le_mul_left (48*n) (Nat.mul_le_mul ha hs)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  calc
    _ ≤ 48*n*(chunkCount (n-n/2) (selected n)*chunkCount (n/2) (selected n)) := by
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
    _ ≤ _ := hh

theorem wordList_depth {ι : Type} (W : ι → List (WordStep C v)) (d : ℕ)
    (hW : ∀ i, Layered (wordMatrix (W i)) d) (L : List ι) :
    Layered (wordMatrix ((L.map W).flatten)) (L.length*d) := by
  induction L with
  | nil => simpa [wordMatrix] using (Layered.identity : Layered (1 : Matrix (Fin v) (Fin v) ℂ) 0)
  | cons i L ih =>
    change Layered (wordMatrix (W i++(L.map W).flatten)) ((L.length+1)*d)
    rw [wordMatrix_append]
    simpa only [Nat.add_mul,Nat.one_mul] using ih.mul (hW i)

theorem correctionWord_depth_exact (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    Layered (wordMatrix (correctionWord n hv f))
      (chunkCount (n-n/2) (selected n)*chunkCount (n/2) (selected n)*(1848*(8*Nat.clog 2 n+23))) := by
  have h := wordList_depth (pairWord n hv f) _ (pairWord_depth n hv f) (pairs n)
  rwa [pairs_length] at h

def crossUnit : ℕ := 42504*131072^2
def depthUnit : ℕ := crossUnit+532545

theorem chunkCount_log_bound (n s : ℕ) (hv : 0<selected n) (hs : s ≤ n) :
    chunkCount s (selected n) ≤ 131072*(Nat.clog 2 n+1) := by
  by_cases hn : 2^17 ≤ n
  · have h := large_chunkCount hn hs
    rw [chunkSizes_length] at h
    omega
  · have h := (chunkCount_le s (selected n) hv).trans hs
    norm_num at hn
    omega

theorem correctionWord_depth (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    Layered (wordMatrix (correctionWord n hv f)) (crossUnit*(Nat.clog 2 n+1)^3) := by
  apply (correctionWord_depth_exact n hv f).weaken
  have ha := chunkCount_log_bound n (n-n/2) hv (Nat.sub_le _ _)
  have hs := chunkCount_log_bound n (n/2) hv (Nat.div_le_self _ _)
  have hlocal : 1848*(8*Nat.clog 2 n+23) ≤ 42504*(Nat.clog 2 n+1) := by omega
  calc
    _ ≤ (131072*(Nat.clog 2 n+1))*(131072*(Nat.clog 2 n+1))*(42504*(Nat.clog 2 n+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hs) hlocal
    _ = _ := by unfold crossUnit;ring

theorem half_clog (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n/2)+1 ≤ Nat.clog 2 n ∧ Nat.clog 2 (n-n/2)+1 ≤ Nat.clog 2 n := by
  have h := Nat.clog_of_two_le (by decide : 1<2) hn
  have he : (n+2-1)/2=n-n/2 := by omega
  rw [he] at h
  have hmono := Nat.clog_mono_right 2 (show n/2 ≤ n-n/2 by omega)
  omega

theorem diagonalWord_depth (n : ℕ) (L : List (WordStep C (n/2))) (R : List (WordStep C (n-n/2)))
    (d e : ℕ) (hL : Layered (wordMatrix L) d) (hR : Layered (wordMatrix R) e) :
    Layered (wordMatrix (TensorWords.embeddedWord (left n) L++TensorWords.embeddedWord (right n) R)) (max d e) := by
  have h := (hL.parallel hR).reindex (coordinates n)
  have he : Matrix.reindex (coordinates n) (coordinates n)
      (Matrix.fromBlocks (wordMatrix L) 0 0 (wordMatrix R))=
      wordMatrix (TensorWords.embeddedWord (left n) L++TensorWords.embeddedWord (right n) R) := by
    rw [←diagonalWord_blocks]
    ext i j
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  rwa [he] at h

theorem fourth_increment (k : ℕ) : k^4+(k+1)^3 ≤ (k+1)^4 := by
  have he : k^4+(k+1)^3+(3*k^3+3*k^2+k)=(k+1)^4 := by ring
  omega

theorem render_depth {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    Layered (wordMatrix (render P f hf)) (depthUnit*(Nat.clog 2 n+1)^4) := by
  induction P with
  | direct n cap =>
    rw [render_matrix]
    by_cases hn : 0<n
    · have h := (UniformDirectToeplitz.finite_fallback_bounds
        (fun i : Fin n=>PowerSeries.coeff i.val f) hn
        (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf) (by omega)).2
      have hm : UniformDirectToeplitz.matrix (fun i : Fin n=>PowerSeries.coeff i.val f)=CoefficientTime.truncMatrix n f := rfl
      rw [hm] at h
      apply h.weaken
      have hp : 1 ≤ (Nat.clog 2 n+1)^4 := by
        have hpos : 0<(Nat.clog 2 n+1)^4 := pow_pos (by omega) _
        omega
      have hb : 532545 ≤ depthUnit := by unfold depthUnit;omega
      exact hb.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left depthUnit hp)
    · have hzero : n=0 := by omega
      subst n
      have he : CoefficientTime.truncMatrix 0 f=1 := by ext i j;exact Fin.elim0 i
      rw [he]
      exact Layered.identity.weaken (Nat.zero_le _)
  | split n hn hv L R ihL ihR =>
    have hhalf := half_clog n hn
    have hl := ihL.weaken (Nat.mul_le_mul_left depthUnit (Nat.pow_le_pow_left hhalf.1 4))
    have hr := ihR.weaken (Nat.mul_le_mul_left depthUnit (Nat.pow_le_pow_left hhalf.2 4))
    have hd := diagonalWord_depth n (render L f hf) (render R f hf) _ _ hl hr
    rw [max_self] at hd
    have hc := correctionWord_depth n hv f
    have h := hc.mul hd
    rw [←wordMatrix_append] at h
    apply h.weaken
    have hunit : crossUnit ≤ depthUnit := by unfold depthUnit;omega
    have hstep := Nat.mul_le_mul_left depthUnit (fourth_increment (Nat.clog 2 n))
    have hcoef := Nat.mul_le_mul_right ((Nat.clog 2 n+1)^3) hunit
    rw [Nat.mul_add] at hstep
    omega

theorem word_depth (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    Layered (wordMatrix (word n f hf)) (depthUnit*(Nat.clog 2 n+1)^4) := render_depth (plan n) f hf

theorem render_call_bound {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordCalls (render P f hf) ≤ 16*n^3 := by
  induction P with
  | direct n cap =>
    dsimp only [render]
    split_ifs with hn
    · rw [UniformDirectToeplitz.word_calls]
      have hm := Nat.mul_le_mul_left (3*n) (Nat.sub_le n 1)
      have hp : n*n ≤ n*n*n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n*n) (show 1 ≤ n by omega)
      nlinarith
    · simp [wordCalls]
  | split n hn hv L R ihL ihR =>
    change wordCalls (TensorWords.embeddedWord (left n) (render L f hf)++
      TensorWords.embeddedWord (right n) (render R f hf)++correctionWord n hv f) ≤ _
    rw [wordCalls_append,wordCalls_append,TensorWords.embeddedWord_calls,TensorWords.embeddedWord_calls]
    have hc := correctionWord_call_bound n hv f
    have he : 16*(n/2)^3+16*(n-n/2)^3+48*n*((n-n/2)*(n/2))=16*n^3 := by
      have hs : n=n/2+(n-n/2) := by omega
      conv_rhs => rw [hs]
      conv_lhs => arg 2;arg 1;arg 2;rw [hs]
      ring
    omega

theorem word_call_bound (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordCalls (word n f hf) ≤ 16*n^3 := render_call_bound (plan n) f hf

theorem layersWord_length_calls {r : ℕ} (bank : Fin r → ℂ) (L : List (List (UniformReplayPrint.ShearCode (Fin v) r))) :
    6*(layersWord bank L).length=28*wordCalls (layersWord bank L) := by
  rw [layersWord_eq,listWord_length,listWord_calls]
  omega

theorem pairWord_length_bound (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    (pairWord n hv f q).length ≤ 224*n := by
  have he : 6*(pairWord n hv f q).length=28*wordCalls (pairWord n hv f q) := by
    dsimp only [pairWord,selectedWord,chunkWord]
    exact layersWord_length_calls _ _
  have hc := pairWord_call_bound n hv f q
  omega

theorem correctionWord_length_bound (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    (correctionWord n hv f).length ≤ 224*n*((n-n/2)*(n/2)) := by
  rw [correctionWord,List.length_flatten,List.map_map]
  simp only [Function.comp_def]
  rw [pairs_sum]
  have h : (∑ i,∑ j,(pairWord n hv f (i,j)).length) ≤
      ∑ _i : Fin (chunkCount (n-n/2) (selected n)),∑ _j : Fin (chunkCount (n/2) (selected n)),224*n := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact pairWord_length_bound n hv f (i,j)
  have ha := chunkCount_le (n-n/2) (selected n) hv
  have hs := chunkCount_le (n/2) (selected n) hv
  have hh := Nat.mul_le_mul_left (224*n) (Nat.mul_le_mul ha hs)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  calc
    _ ≤ 224*n*(chunkCount (n-n/2) (selected n)*chunkCount (n/2) (selected n)) := by
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
    _ ≤ _ := hh

theorem render_length_bound {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (render P f hf).length ≤ 75*n^3 := by
  induction P with
  | direct n cap =>
    dsimp only [render]
    split_ifs with hn
    · rw [UniformDirectToeplitz.word_length]
      have hm := Nat.mul_le_mul_left (14*n) (Nat.sub_le n 1)
      have hp : n*n ≤ n*n*n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n*n) (show 1 ≤ n by omega)
      have hq : n ≤ n*n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
      nlinarith
    · simp
  | split n hn hv L R ihL ihR =>
    change (TensorWords.embeddedWord (left n) (render L f hf)++
      TensorWords.embeddedWord (right n) (render R f hf)++correctionWord n hv f).length ≤ _
    simp only [List.length_append,TensorWords.embeddedWord,List.length_map]
    have hc := correctionWord_length_bound n hv f
    have he : 75*(n/2)^3+75*(n-n/2)^3+225*n*((n-n/2)*(n/2))=75*n^3 := by
      have hs : n=n/2+(n-n/2) := by omega
      conv_rhs => rw [hs]
      conv_lhs => arg 2;arg 1;arg 2;rw [hs]
      ring
    have hcoef := Nat.mul_le_mul_right ((n-n/2)*(n/2))
      (Nat.mul_le_mul_right n (by decide : 224 ≤ 225))
    omega

theorem word_length_bound (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (word n f hf).length ≤ 75*n^3 := render_length_bound (plan n) f hf

/-- Computable recursion diagnostics, without evaluating any complex coefficient. -/
def Plan.height {n : ℕ} : Plan n → ℕ
  | .direct _ _ => 0
  | .split _ _ _ L R => 1+max L.height R.height

def Plan.leaves {n : ℕ} : Plan n → List ℕ
  | .direct n _ => [n]
  | .split _ _ _ L R => L.leaves++R.leaves

theorem Plan.leaves_sum {n : ℕ} (P : Plan n) : P.leaves.sum=n := by
  induction P with
  | direct n cap => simp [Plan.leaves]
  | split n hn hv L R ihL ihR => simp only [Plan.leaves,List.sum_append,ihL,ihR];omega

end

end ExactFourierCircuits.UniformBalancedToeplitz
