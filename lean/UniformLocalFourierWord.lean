import UniformBalancedToeplitz
import UniformNewton
import UniformNewtonTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFourierWord
open OAI.ExactFourier TypedKernelWords
open NewtonFourier CoefficientTime
noncomputable section

theorem isMonomial_transpose {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsMonomial M) : IsMonomial M.transpose := by
  classical
  obtain ⟨sigma,d,hd,h⟩:=hM
  refine ⟨sigma.symm,fun j=>d (sigma.symm j),fun j=>hd _,?_⟩
  intro i j
  by_cases hij:i=sigma.symm j
  · subst i
    simp [Matrix.transpose_apply,h]
  · have hji:j≠sigma i:=by
      intro he
      apply hij
      rw [he,Equiv.symm_apply_apply]
    simp [Matrix.transpose_apply,h,hij,hji]

theorem embeddedCall_transpose {q n : ℕ} (M : Matrix (Fin q) (Fin q) ℂ)
    (e : Fin q ↪ Fin n) : embeddedCall M.transpose e=(embeddedCall M e).transpose := by
  classical
  ext u v
  simp only [embeddedCall,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:e i=u <;> by_cases hj:e j=v <;> simp [hi,hj]
  · by_cases huv:u=v
    · subst v;rfl
    · simp [huv,Ne.symm huv]

theorem C_transpose : C.transpose=C := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Transpose changes only the monomial matrix. Every forward C call survives. -/
def transposeStep {n : ℕ} : WordStep C n → WordStep C n
  | .monomial M hM => .monomial M.transpose (isMonomial_transpose hM)
  | .call e => .call e

theorem transposeStep_matrix {n : ℕ} (s : WordStep C n) :
    (transposeStep s).matrix=s.matrix.transpose := by
  cases s with
  | monomial M hM => rfl
  | call e =>
    change embeddedCall C e=(embeddedCall C e).transpose
    simpa only [C_transpose] using embeddedCall_transpose C e

theorem transposeStep_calls {n : ℕ} (s : WordStep C n) :
    (transposeStep s).calls=s.calls := by cases s <;> rfl

/-- Reversal is required because words are stored in execution order. -/
def transposeWord {n : ℕ} (W : List (WordStep C n)) : List (WordStep C n) :=
  (W.map transposeStep).reverse

theorem wordMatrix_cons {n : ℕ} (s : WordStep C n) (W : List (WordStep C n)) :
    wordMatrix (s::W)=wordMatrix W*s.matrix := by
  change wordMatrix ([s]++W)=_
  rw [wordMatrix_append,wordMatrix_singleton]

theorem transposeWord_matrix {n : ℕ} (W : List (WordStep C n)) :
    wordMatrix (transposeWord W)=(wordMatrix W).transpose := by
  induction W with
  | nil => simp [transposeWord,wordMatrix]
  | cons s W ih =>
    change wordMatrix ((List.map transposeStep (s::W)).reverse)=_
    rw [List.map_cons,List.reverse_cons]
    change wordMatrix (transposeWord W++[transposeStep s])=_
    rw [wordMatrix_append,wordMatrix_singleton,transposeStep_matrix,ih,
      wordMatrix_cons,Matrix.transpose_mul]

theorem transposeWord_calls {n : ℕ} (W : List (WordStep C n)) :
    wordCalls (transposeWord W)=wordCalls W := by
  simp [transposeWord,wordCalls,List.map_map,Function.comp_def,transposeStep_calls]

theorem transposeWord_length {n : ℕ} (W : List (WordStep C n)) :
    (transposeWord W).length=W.length := by simp [transposeWord]

theorem transposeWord_depth {n d : ℕ} (W : List (WordStep C n))
    (hW : Layered (wordMatrix W) d) : Layered (wordMatrix (transposeWord W)) d := by
  rw [transposeWord_matrix]
  exact hW.transpose

theorem diagonal_isMonomial {n : ℕ} (d : Fin n → ℂ) (hd : ∀j,d j≠0) :
    IsMonomial (Matrix.diagonal d) := by
  classical
  refine ⟨Equiv.refl _,d,hd,?_⟩
  intro i j
  by_cases hij:i=j
  · subst j;simp
  · simp [hij]

def diagonalStep {n : ℕ} (d : Fin n → ℂ) (hd : ∀j,d j≠0) : WordStep C n :=
  .monomial (Matrix.diagonal d) (diagonal_isMonomial d hd)

theorem diagonalStep_matrix {n : ℕ} (d : Fin n → ℂ) (hd : ∀j,d j≠0) :
    (diagonalStep d hd).matrix=Matrix.diagonal d := rfl

theorem diagonalStep_calls {n : ℕ} (d : Fin n → ℂ) (hd : ∀j,d j≠0) :
    (diagonalStep d hd).calls=0 := rfl

/-- Two literal diagonal rounds surrounding the constructive Toeplitz word. -/
def sandwich {n : ℕ} (left right : Fin n → ℂ) (hl : ∀j,left j≠0) (hr : ∀j,right j≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (WordStep C n) :=
  [diagonalStep right hr]++UniformBalancedToeplitz.word n f hf++[diagonalStep left hl]

theorem sandwich_matrix {n : ℕ} (left right : Fin n → ℂ) (hl : ∀j,left j≠0)
    (hr : ∀j,right j≠0) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordMatrix (sandwich left right hl hr f hf)=
      Matrix.diagonal left*truncMatrix n f*Matrix.diagonal right := by
  simp only [sandwich,wordMatrix_append,wordMatrix_singleton,diagonalStep_matrix,
    UniformBalancedToeplitz.word_matrix,Matrix.mul_assoc]

theorem sandwich_calls {n : ℕ} (left right : Fin n → ℂ) (hl : ∀j,left j≠0)
    (hr : ∀j,right j≠0) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    wordCalls (sandwich left right hl hr f hf)=wordCalls (UniformBalancedToeplitz.word n f hf) := by
  simp [sandwich,wordCalls,diagonalStep_calls]

theorem sandwich_length {n : ℕ} (left right : Fin n → ℂ) (hl : ∀j,left j≠0)
    (hr : ∀j,right j≠0) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (sandwich left right hl hr f hf).length=(UniformBalancedToeplitz.word n f hf).length+2 := by
  simp [sandwich]

theorem sandwich_depth {n : ℕ} (left right : Fin n → ℂ) (hl : ∀j,left j≠0)
    (hr : ∀j,right j≠0) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    Layered (wordMatrix (sandwich left right hl hr f hf))
      (UniformBalancedToeplitz.depthUnit*(Nat.clog 2 n+1)^4+2) := by
  rw [sandwich_matrix]
  have hL:=Layered.mono _ (MonomialMatrix.diagonal left hl)
  have hR:=Layered.mono _ (MonomialMatrix.diagonal right hr)
  have hT:=UniformBalancedToeplitz.word_depth n f hf
  rw [UniformBalancedToeplitz.word_matrix] at hT
  convert (hL.mul hT).mul hR using 1
  omega

def NWord {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    List (WordStep C n) :=
  sandwich (fun j=>NewtonFourier.H omega j.val) (fun j=>scale omega j.val)
    (UniformNewton.Hvalue_ne_zero hroot) (UniformNewton.scaleValue_ne_zero hn hroot)
    (invH omega) (by simp)

theorem NWord_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    wordMatrix (NWord hn hroot)=N n omega := by
  rw [NWord,sandwich_matrix]
  exact (UniformNewton.N_toeplitz_factorization hroot).symm

/-- Literal transposed N, inverse diagonal, then N: no existential local circuit. -/
def symmetricWord {n : ℕ} (W : List (WordStep C n)) (d : Fin n → ℂ) (hd : ∀j,d j≠0) :
    List (WordStep C n) := transposeWord W++[diagonalStep d hd]++W

theorem symmetricWord_matrix {n : ℕ} (W : List (WordStep C n))
    (d : Fin n → ℂ) (hd : ∀j,d j≠0) :
    wordMatrix (symmetricWord W d hd)=wordMatrix W*Matrix.diagonal d*(wordMatrix W).transpose := by
  simp only [symmetricWord,wordMatrix_append,wordMatrix_singleton,diagonalStep_matrix,
    transposeWord_matrix,Matrix.mul_assoc]

theorem symmetricWord_calls {n : ℕ} (W : List (WordStep C n))
    (d : Fin n → ℂ) (hd : ∀j,d j≠0) : wordCalls (symmetricWord W d hd)=2*wordCalls W := by
  simp only [symmetricWord,wordCalls_append,transposeWord_calls]
  have h:wordCalls [diagonalStep d hd]=0:=rfl
  rw [h]
  omega

theorem symmetricWord_length {n : ℕ} (W : List (WordStep C n))
    (d : Fin n → ℂ) (hd : ∀j,d j≠0) : (symmetricWord W d hd).length=2*W.length+1 := by
  simp [symmetricWord,transposeWord_length];omega

theorem symmetricWord_depth {n D : ℕ} (W : List (WordStep C n))
    (d : Fin n → ℂ) (hd : ∀j,d j≠0) (hW : Layered (wordMatrix W) D) :
    Layered (wordMatrix (symmetricWord W d hd)) (2*D+1) := by
  rw [symmetricWord_matrix]
  have hD:=Layered.mono _ (MonomialMatrix.diagonal d hd)
  simpa only [two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (hW.mul hD).mul hW.transpose

def word {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) : List (WordStep C n) :=
  symmetricWord (NWord hn hroot) (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j))

theorem word_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    wordMatrix (word hn hroot)=RadixTwo.dft n omega := by
  rw [word,symmetricWord_matrix,NWord_matrix]
  rw [←UniformNewton.Preparation.diagonal_inverse hn hroot]
  exact (UniformNewton.fourier_factorization hn hroot).symm

theorem word_action {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (x : Fin n → ℂ) : (wordMatrix (word hn hroot)).mulVec x=(RadixTwo.dft n omega).mulVec x := by
  rw [word_matrix]

def sufficientSlots (n : ℕ) : ℕ := 2*(UniformBalancedToeplitz.depthUnit*(Nat.clog 2 n+1)^4+2)+1
def depthUnit : ℕ := 2*UniformBalancedToeplitz.depthUnit+5

theorem word_depth {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    Layered (wordMatrix (word hn hroot)) (sufficientSlots n) := by
  exact symmetricWord_depth _ _ _ (sandwich_depth ..)

theorem sufficientSlots_bound (n : ℕ) : sufficientSlots n≤depthUnit*(Nat.clog 2 n+1)^4 := by
  have hp:1≤(Nat.clog 2 n+1)^4:=by
    have hp:0<(Nat.clog 2 n+1)^4:=by positivity
    omega
  unfold sufficientSlots depthUnit
  nlinarith

theorem word_depth_bound {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    Layered (wordMatrix (word hn hroot)) (depthUnit*(Nat.clog 2 n+1)^4) :=
  (word_depth hn hroot).weaken (sufficientSlots_bound n)

theorem word_calls_exact {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    wordCalls (word hn hroot)=2*wordCalls (UniformBalancedToeplitz.word n (invH omega) (by simp)) := by
  rw [word,symmetricWord_calls,NWord,sandwich_calls]

theorem word_call_bound {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    wordCalls (word hn hroot)≤32*n^3 := by
  rw [word_calls_exact]
  have h:=UniformBalancedToeplitz.word_call_bound n (invH omega) (by simp)
  omega

theorem word_length_exact {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    (word hn hroot).length=2*(UniformBalancedToeplitz.word n (invH omega) (by simp)).length+5 := by
  rw [word,symmetricWord_length,NWord,sandwich_length]
  omega

theorem word_length_bound {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    (word hn hroot).length≤155*n^3 := by
  rw [word_length_exact]
  have h:=UniformBalancedToeplitz.word_length_bound n (invH omega) (by simp)
  have hp:1≤n^3:=by have hp:=pow_pos hn 3;omega
  omega

/-- Canonical positive-exponent word, including the empty width. -/
def specifiedWord (n : ℕ) : List (WordStep C n) :=
  if hn:0<n then word hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) else []

theorem specifiedWord_matrix (n : ℕ) : wordMatrix (specifiedWord n)=fourierMatrix n := by
  by_cases hn:0<n
  · simp only [specifiedWord,dite_eq_left hn,word_matrix]
    rfl
  · have hz:n=0:=by omega
    subst n
    ext i j
    exact Fin.elim0 i

theorem specifiedWord_action (n : ℕ) (x : Fin n → ℂ) :
    (wordMatrix (specifiedWord n)).mulVec x=(fourierMatrix n).mulVec x := by
  rw [specifiedWord_matrix]

theorem specifiedWord_depth (n : ℕ) :
    Layered (wordMatrix (specifiedWord n)) (sufficientSlots n) := by
  by_cases hn:0<n
  · simpa only [specifiedWord,dite_eq_left hn] using word_depth hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))
  · simp only [specifiedWord,dite_eq_right hn,wordMatrix,List.map_nil,List.reverse_nil,List.prod_nil]
    exact Layered.identity.weaken (Nat.zero_le _)

theorem specifiedWord_calls (n : ℕ) : wordCalls (specifiedWord n)≤32*n^3 := by
  by_cases hn:0<n
  · simpa only [specifiedWord,dite_eq_left hn] using word_call_bound hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))
  · simp [specifiedWord,hn,wordCalls]

theorem specifiedWord_length (n : ℕ) : (specifiedWord n).length≤155*n^3 := by
  by_cases hn:0<n
  · simpa only [specifiedWord,dite_eq_left hn] using word_length_bound hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))
  · simp [specifiedWord,hn]

/-- Read an actual output reference of the shared Newton preparation table.
The correctness premise below is its proved machine postcondition. -/
def preparedValue {n : ℕ} (a : ℕ) (s : UniformMachine.State) (j : Fin n) (q : Fin 5) : ℂ :=
  ((s.scalarHeap (a+((UniformNewton.Preparation.table n).output
    (finProdFinEquiv (j,q))).val)).getD UniformMachine.Scalar.zero).value

theorem preparedValue_eq {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) (j : Fin n) (q : Fin 5) :
    preparedValue a s j q=UniformNewton.Preparation.expected omega j.val q := by
  unfold preparedValue
  rw [hp j q]
  rfl

theorem preparedH_value {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) (j : Fin n) :
    preparedValue a s j 0=NewtonFourier.H omega j.val := by
  simpa [UniformNewton.Preparation.expected] using preparedValue_eq hp j 0

theorem preparedScale_value {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) (j : Fin n) :
    preparedValue a s j 1=scale omega j.val := by
  simpa [UniformNewton.Preparation.expected] using preparedValue_eq hp j 1

theorem preparedInvH_value {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) (j : Fin n) :
    preparedValue a s j 2=(NewtonFourier.H omega j.val)⁻¹ := by
  simpa [UniformNewton.Preparation.expected] using preparedValue_eq hp j 2

theorem preparedInvD_value {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) (j : Fin n) :
    preparedValue a s j 4=(UniformNewton.diagonalValue omega j.val)⁻¹ := by
  simpa [UniformNewton.Preparation.expected] using preparedValue_eq hp j 4

/-- Only the actually written finite inverse-H bank is used as the seed series;
the tail is literal zero. Recursive reciprocal preparation remains separate. -/
def preparedSeries (n a : ℕ) (s : UniformMachine.State) : PowerSeries ℂ :=
  PowerSeries.mk (fun j=>if hj:j<n then preparedValue a s ⟨j,hj⟩ 2 else 0)

theorem preparedSeries_constant {n a : ℕ} (hn : 0<n) {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    PowerSeries.constantCoeff (preparedSeries n a s)=1 := by
  simp only [preparedSeries,PowerSeries.constantCoeff_mk,dite_eq_left hn]
  rw [preparedInvH_value hp]
  simp

theorem preparedSeries_trunc {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    truncMatrix n (preparedSeries n a s)=truncMatrix n (invH omega) := by
  ext i j
  unfold truncMatrix
  split_ifs with hij
  · have hk:i.val-j.val<n:=lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    simp only [preparedSeries,PowerSeries.coeff_mk,dite_eq_left hk]
    rw [preparedInvH_value hp]
    simp [invH,PowerSeries.coeff_mk]
  · rfl

theorem preparedH_nonzero {n a : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hroot : IsPrimitiveRoot omega n) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s)
    (j : Fin n) : preparedValue a s j 0≠0 := by
  rw [preparedH_value hp]
  exact UniformNewton.Hvalue_ne_zero hroot j

theorem preparedScale_nonzero {n a : ℕ} (hn : 0<n) {omega : ℂ} {s : UniformMachine.State}
    (hroot : IsPrimitiveRoot omega n) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s)
    (j : Fin n) : preparedValue a s j 1≠0 := by
  rw [preparedScale_value hp]
  exact UniformNewton.scaleValue_ne_zero hn hroot j

theorem preparedInvD_nonzero {n a : ℕ} (hn : 0<n) {omega : ℂ} {s : UniformMachine.State}
    (hroot : IsPrimitiveRoot omega n) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s)
    (j : Fin n) : preparedValue a s j 4≠0 := by
  rw [preparedInvD_value hp]
  exact inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j)

def preparedNWord {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    List (WordStep C n) :=
  sandwich (fun j=>preparedValue a s j 0) (fun j=>preparedValue a s j 1)
    (preparedH_nonzero hroot hp) (preparedScale_nonzero hn hroot hp)
    (preparedSeries n a s) (by rw [preparedSeries_constant hn hp];exact one_ne_zero)

theorem preparedNWord_matrix {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    wordMatrix (preparedNWord hn hroot s hp)=N n omega := by
  have hH:(fun j : Fin n=>preparedValue a s j 0)=(fun j=>NewtonFourier.H omega j.val):=
    funext (preparedH_value hp)
  have hs:(fun j : Fin n=>preparedValue a s j 1)=(fun j=>scale omega j.val):=
    funext (preparedScale_value hp)
  rw [preparedNWord,sandwich_matrix,hH,hs,preparedSeries_trunc hp]
  exact (UniformNewton.N_toeplitz_factorization hroot).symm

def preparedWord {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    List (WordStep C n) :=
  symmetricWord (preparedNWord hn hroot s hp) (fun j=>preparedValue a s j 4)
    (preparedInvD_nonzero hn hroot hp)

theorem preparedWord_matrix {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    wordMatrix (preparedWord hn hroot s hp)=RadixTwo.dft n omega := by
  have hd:(fun j : Fin n=>preparedValue a s j 4)=
      (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹):=funext (preparedInvD_value hp)
  rw [preparedWord,symmetricWord_matrix,preparedNWord_matrix,hd,
    ←UniformNewton.Preparation.diagonal_inverse hn hroot]
  exact (UniformNewton.fourier_factorization hn hroot).symm

theorem preparedWord_depth {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    Layered (wordMatrix (preparedWord hn hroot s hp)) (sufficientSlots n) :=
  symmetricWord_depth _ _ _ (sandwich_depth ..)

theorem preparedWord_calls {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    wordCalls (preparedWord hn hroot s hp)≤32*n^3 := by
  rw [preparedWord,symmetricWord_calls,preparedNWord,sandwich_calls]
  have h:=UniformBalancedToeplitz.word_call_bound n (preparedSeries n a s)
    (by rw [preparedSeries_constant hn hp];exact one_ne_zero)
  omega

theorem preparedWord_length {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    (preparedWord hn hroot s hp).length≤155*n^3 := by
  rw [preparedWord,symmetricWord_length,preparedNWord,sandwich_length]
  have h:=UniformBalancedToeplitz.word_length_bound n (preparedSeries n a s)
    (by rw [preparedSeries_constant hn hp];exact one_ne_zero)
  have hp:1≤n^3:=by have h:=pow_pos hn 3;omega
  omega

theorem prepared_specified_matrix (n a : ℕ) (hn : 0<n) (s : UniformMachine.State)
    (hp : UniformNewtonTableMachine.PreparedOutputs n (zeta n) a s) :
    wordMatrix (preparedWord hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) s hp)=
      fourierMatrix n :=
  preparedWord_matrix hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) s hp

end
end ExactFourierCircuits.UniformLocalFourierWord
