import UniformLocalFourierWord
import OAI.Computability.FourierCircuit.PairFamilies

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3, Proposition 3.1, PDF p. 12; §3.3–3.4, Lemmas 3.4–3.5 and equations (3.12)–(3.14), pp. 15–18.
Mixed rounds preserve exact width; disjoint ordered pairs carry the fixed six-C replacement. Layer semantics is distinct from scalar-table preparation and physical RAM execution.
-/

set_option autoImplicit false
/-! Explicit mixed-layer data, preserving every forward C call.
Parallel nodes contain their disjoint coordinate maps. RAM printing is separate. -/
namespace ExactFourierCircuits.UniformLocalFourierLayers
open OAI.ExactFourier TypedKernelWords
open scoped BigOperators
noncomputable section

/- Paper: Proposition 3.1, p. 12 and Lemma 3.4, p. 17: mixed rounds on disjoint coordinate regions, with identity padding of shorter children. -/
inductive Layer : ℕ → Type
  | step {n : ℕ} (s : WordStep C n) : Layer n
  | parallel {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : Layer a) (R : Layer b) : Layer n
  | embed {a n : ℕ} (e : Fin a ↪ Fin n) (L : Layer a) : Layer n
  | batch {s n : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
      (steps : Fin s → WordStep C 2) : Layer n

namespace Layer

def idle (n : ℕ) : Layer n := .step (.monomial 1 MonomialMatrix.one)
def word {n : ℕ} : Layer n → List (WordStep C n)
  | .step s => [s]
  | .parallel e L R =>
      TensorWords.embeddedWord ((Function.Embedding.inl : Fin _ ↪ Fin _ ⊕ Fin _).trans e.toEmbedding) L.word ++
      TensorWords.embeddedWord (Function.Embedding.inr.trans e.toEmbedding) R.word
  | .embed e L => TensorWords.embeddedWord e L.word
  | @Layer.batch s _ position steps =>
      (Finset.univ.toList.map (fun i : Fin s => TensorWords.embeddedWord
        ((Embedded.sigmaIn i).trans position) [steps i])).reverse.flatten

def matrix {n : ℕ} (L : Layer n) : Matrix (Fin n) (Fin n) ℂ := wordMatrix L.word
def calls {n : ℕ} (L : Layer n) : ℕ := wordCalls L.word
@[simp] theorem step_matrix {n : ℕ} (s : WordStep C n) : (Layer.step s).matrix=s.matrix := wordMatrix_singleton s
@[simp] theorem step_calls {n : ℕ} (s : WordStep C n) : (Layer.step s).calls=s.calls := by rfl
@[simp] theorem idle_matrix (n : ℕ) : (idle n).matrix=1 := by simp only [idle,step_matrix,WordStep.matrix]
@[simp] theorem idle_calls (n : ℕ) : (idle n).calls=0 := rfl
@[simp] theorem embed_matrix {a n : ℕ} (e : Fin a ↪ Fin n) (L : Layer a) :
    (Layer.embed e L).matrix=Embedded.matrix e L.matrix := TensorWords.embeddedWord_matrix e L.word
@[simp] theorem embed_calls {a n : ℕ} (e : Fin a ↪ Fin n) (L : Layer a) :
    (Layer.embed e L).calls=L.calls := TensorWords.embeddedWord_calls e L.word
@[simp] theorem parallel_matrix {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : Layer a) (R : Layer b) :
    (Layer.parallel e L R).matrix=Matrix.reindex e e (Matrix.fromBlocks L.matrix 0 0 R.matrix) := by
  change wordMatrix (_++_)=_
  rw [wordMatrix_append,TensorWords.embeddedWord_matrix,TensorWords.embeddedWord_matrix,
    ←Embedded.matrix_comp,←Embedded.matrix_comp,Embedded.matrix_inl,Embedded.matrix_inr,
    ←Embedded.matrix_mul,Embedded.matrix_equiv]
  simp [matrix,Matrix.fromBlocks_multiply]
@[simp] theorem parallel_calls {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : Layer a) (R : Layer b) :
    (Layer.parallel e L R).calls=L.calls+R.calls := by
  simp only [calls,word,wordCalls_append,TensorWords.embeddedWord_calls]

def embedHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ↪ b) : Matrix a a ℂ →* Matrix b b ℂ where
  toFun := Embedded.matrix e
  map_one' := Embedded.matrix_one e
  map_mul' := Embedded.matrix_mul e

@[simp] theorem batch_matrix {s n : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n) (steps : Fin s → WordStep C 2) :
    (Layer.batch position steps).matrix=Embedded.matrix position (Matrix.blockDiagonal' (fun i => (steps i).matrix)) := by
  change wordMatrix _=_
  simp only [word,TensorWords.wordMatrix_flatten,List.map_reverse,List.reverse_reverse,
    List.map_map,Function.comp_def,TensorWords.embeddedWord_matrix,wordMatrix_singleton,
    ←Embedded.matrix_comp]
  rw [show Finset.univ.toList.map (fun i : Fin s =>
      Embedded.matrix position (Embedded.matrix (Embedded.sigmaIn i) (steps i).matrix)) =
      (Finset.univ.toList.map (fun i : Fin s => Embedded.matrix (Embedded.sigmaIn i) (steps i).matrix)).map
        (embedHom position) from by simpa only [embedHom,MonoidHom.coe_mk,OneHom.coe_mk,Function.comp_def] using (List.map_map ..).symm]
  rw [←map_list_prod,Embedded.blockDiagonal'_product]
  rfl
@[simp] theorem batch_calls {s n : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n) (steps : Fin s → WordStep C 2) :
    (Layer.batch position steps).calls=∑ i, (steps i).calls := by
  simp only [calls,word,TensorWords.wordCalls_flatten,List.map_reverse,List.sum_reverse,
    List.map_map,Function.comp_def,TensorWords.embeddedWord_calls]
  simp [wordCalls]
end Layer

def serialize {n : ℕ} (L : List (Layer n)) : List (WordStep C n) := (L.map Layer.word).flatten
def matrix {n : ℕ} (L : List (Layer n)) : Matrix (Fin n) (Fin n) ℂ := (L.map Layer.matrix).reverse.prod
def calls {n : ℕ} (L : List (Layer n)) : ℕ := (L.map Layer.calls).sum
@[simp] theorem serialize_matrix {n : ℕ} (L : List (Layer n)) : wordMatrix (serialize L)=matrix L := by
  change wordMatrix (L.map Layer.word).flatten = (L.map (fun l => wordMatrix l.word)).reverse.prod
  simpa only [List.map_map,Function.comp_def] using TensorWords.wordMatrix_flatten (L.map Layer.word)
@[simp] theorem serialize_calls {n : ℕ} (L : List (Layer n)) : wordCalls (serialize L)=calls L := by
  change wordCalls (L.map Layer.word).flatten = (L.map (fun l => wordCalls l.word)).sum
  simpa only [List.map_map,Function.comp_def] using TensorWords.wordCalls_flatten (L.map Layer.word)
@[simp] theorem matrix_nil (n : ℕ) : matrix ([] : List (Layer n))=1 := rfl
@[simp] theorem calls_nil (n : ℕ) : calls ([] : List (Layer n))=0 := rfl
@[simp] theorem matrix_cons {n : ℕ} (l : Layer n) (L : List (Layer n)) : matrix (l::L)=matrix L*l.matrix := by simp [matrix]
@[simp] theorem calls_cons {n : ℕ} (l : Layer n) (L : List (Layer n)) : calls (l::L)=l.calls+calls L := rfl
@[simp] theorem matrix_append {n : ℕ} (L R : List (Layer n)) : matrix (L++R)=matrix R*matrix L := by simp [matrix]
@[simp] theorem calls_append {n : ℕ} (L R : List (Layer n)) : calls (L++R)=calls L+calls R := by simp [calls]

@[simp] theorem matrix_singleton {n : ℕ} (L : Layer n) : matrix [L]=L.matrix := by simp [matrix]
@[simp] theorem calls_singleton {n : ℕ} (L : Layer n) : calls [L]=L.calls := rfl

def serial {n : ℕ} (W : List (WordStep C n)) : List (Layer n) := W.map Layer.step
@[simp] theorem serial_matrix {n : ℕ} (W : List (WordStep C n)) : matrix (serial W)=wordMatrix W := by
  simp [matrix,serial,wordMatrix,List.map_map,Function.comp_def]
@[simp] theorem serial_calls {n : ℕ} (W : List (WordStep C n)) : calls (serial W)=wordCalls W := by
  simp [calls,serial,wordCalls,List.map_map,Function.comp_def]
@[simp] theorem serial_length {n : ℕ} (W : List (WordStep C n)) : (serial W).length=W.length := by simp [serial]

/-- Identity-pad the shorter child and zip actual disjoint layers. -/
def parallel {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) : List (Layer a) → List (Layer b) → List (Layer n)
  | [], [] => []
  | l::L, [] => Layer.parallel e l (Layer.idle b)::parallel e L []
  | [], r::R => Layer.parallel e (Layer.idle a) r::parallel e [] R
  | l::L, r::R => Layer.parallel e l r::parallel e L R
@[simp] theorem parallel_length {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : List (Layer a)) (R : List (Layer b)) :
    (parallel e L R).length=max L.length R.length := by
  induction L generalizing R with
  | nil => induction R with
    | nil => simp [parallel]
    | cons r R ih => simp [parallel,ih]
  | cons l L ih => cases R with
    | nil => simp [parallel,ih]
    | cons r R => simp [parallel,ih,max_add_add_right]
@[simp] theorem parallel_calls {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : List (Layer a)) (R : List (Layer b)) :
    calls (parallel e L R)=calls L+calls R := by
  induction L generalizing R with
  | nil => induction R with
    | nil => simp [parallel]
    | cons r R ih => simp [parallel,ih]
  | cons l L ih => cases R with
    | nil => simp [parallel,ih]
    | cons r R => simp [parallel,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
@[simp] theorem parallel_matrix {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n) (L : List (Layer a)) (R : List (Layer b)) :
    matrix (parallel e L R)=Matrix.reindex e e (Matrix.fromBlocks (matrix L) 0 0 (matrix R)) := by
  induction L generalizing R with
  | nil => induction R with
    | nil => simp [parallel]
    | cons r R ih =>
      simp only [parallel,matrix_cons,ih,Layer.parallel_matrix,Layer.idle_matrix,matrix_nil]
      change (Matrix.reindexAlgEquiv ℂ ℂ e) _ * (Matrix.reindexAlgEquiv ℂ ℂ e) _ = (Matrix.reindexAlgEquiv ℂ ℂ e) _
      rw [←map_mul]
      simp [Matrix.fromBlocks_multiply]
  | cons l L ih => cases R with
    | nil =>
      simp only [parallel,matrix_cons,ih,Layer.parallel_matrix,Layer.idle_matrix,matrix_nil]
      change (Matrix.reindexAlgEquiv ℂ ℂ e) _ * (Matrix.reindexAlgEquiv ℂ ℂ e) _ = (Matrix.reindexAlgEquiv ℂ ℂ e) _
      rw [←map_mul]
      simp [Matrix.fromBlocks_multiply]
    | cons r R =>
      simp only [parallel,matrix_cons,ih,Layer.parallel_matrix]
      change (Matrix.reindexAlgEquiv ℂ ℂ e) _ * (Matrix.reindexAlgEquiv ℂ ℂ e) _ = (Matrix.reindexAlgEquiv ℂ ℂ e) _
      rw [←map_mul]
      simp [Matrix.fromBlocks_multiply]


/-- Equal-length local words are transposed into simultaneous disjoint batches. -/
def batchWords {s n : ℕ} (T : ℕ) (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
    (W : Fin s → List (WordStep C 2)) (hW : ∀ i, (W i).length=T) : List (Layer n) :=
  List.ofFn (fun t : Fin T => Layer.batch position
    (fun i => (W i).get (Fin.cast (hW i).symm t)))

theorem ofFn_cast_get {α : Type} (W : List α) {T : ℕ} (hW : W.length=T) :
    List.ofFn (fun t : Fin T => W.get (Fin.cast hW.symm t))=W := by
  subst T
  exact List.ofFn_get W

@[simp] theorem batchWords_length {s n T : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
    (W : Fin s → List (WordStep C 2)) (hW : ∀ i, (W i).length=T) :
    (batchWords T position W hW).length=T := by simp [batchWords]

theorem batchWords_matrix {s n T : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
    (W : Fin s → List (WordStep C 2)) (hW : ∀ i, (W i).length=T) :
    matrix (batchWords T position W hW)=
      Embedded.matrix position (Matrix.blockDiagonal' (fun i => wordMatrix (W i))) := by
  let f : Fin T → (Fin s → Matrix (Fin 2) (Fin 2) ℂ) :=
    fun t i => ((W i).get (Fin.cast (hW i).symm t)).matrix
  let phi := (Layer.embedHom position).comp
    (Matrix.blockDiagonal'RingHom (fun _ : Fin s => Fin 2) ℂ).toMonoidHom
  have he : (batchWords T position W hW).map Layer.matrix = (List.ofFn f).map phi := by
    simp only [batchWords,List.map_ofFn,Function.comp_def,Layer.batch_matrix]
    rfl
  unfold matrix
  rw [he,←List.map_reverse,←map_list_prod]
  change Embedded.matrix position (Matrix.blockDiagonal' ((List.ofFn f).reverse.prod))=_
  congr 2
  funext i
  have hi := map_list_prod (Pi.evalMonoidHom (fun _ : Fin s => Matrix (Fin 2) (Fin 2) ℂ) i)
    (List.ofFn f).reverse
  change ((List.ofFn f).reverse.prod) i = ((List.ofFn f).reverse.map (fun g => g i)).prod at hi
  rw [hi]
  simp only [List.map_reverse,List.map_ofFn]
  simpa only [wordMatrix,List.map_ofFn,Function.comp_def,f] using
    congrArg (fun V : List (WordStep C 2) => wordMatrix V) (ofFn_cast_get (W i) (hW i))

theorem batchWords_calls {s n T : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
    (W : Fin s → List (WordStep C 2)) (hW : ∀ i, (W i).length=T) :
    calls (batchWords T position W hW)=∑ i,wordCalls (W i) := by
  simp only [calls,batchWords,List.map_ofFn,List.sum_ofFn,Function.comp_def,Layer.batch_calls]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrArg (fun V : List (WordStep C 2) => wordCalls V) (ofFn_cast_get (W i) (hW i))
  simpa only [wordCalls,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hi

open UniformToeplitzChunkWord UniformReplayPrint

theorem localShear_length (mu : ℂ) : (UniformLocalShear.word mu).length=28 := by
  simp [UniformLocalShear.word,TypedKernelWords.shearWord,hadamardWord]

/-- Every coefficient reference survives; in particular zero coefficients retain six calls. -/
/- Paper: Equations (3.12)–(3.14), pp. 17–18: parallel ordered pairs use the same 28 instruction phases and exactly six C calls per shear, including coefficient zero. -/
def matchingLayers {v r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    List (Layer v) :=
  batchWords 28 (pairPosition W hW)
    (fun i => UniformLocalShear.word ((W.get i).coefficient.eval bank)) (fun _ => localShear_length _)

@[simp] theorem matchingLayers_length {v r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    (matchingLayers bank W hW).length=28 := batchWords_length ..

theorem matchingLayers_matrix {v r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    matrix (matchingLayers bank W hW)=wordMatrix (listWord bank W) := by
  rw [matchingLayers,batchWords_matrix,matchingWord_matrix bank W hW]
  simp only [UniformLocalShear.word_matrix]

theorem matchingLayers_calls {v r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    calls (matchingLayers bank W hW)=wordCalls (listWord bank W) := by
  rw [matchingLayers,batchWords_calls,listWord_calls]
  simp [UniformLocalShear.word_calls,Nat.mul_comm]

/-- Concrete colored replay layers, expanding each matching into its 28 literal phases. -/
def shearLayers {v r : ℕ} (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hL : ∀ W∈L,Matching W) : List (Layer v) :=
  (L.attach.map (fun W => matchingLayers bank W.val (hL W.val W.property))).flatten

theorem shearLayers_matrix {v r : ℕ} (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hL : ∀ W∈L,Matching W) : matrix (shearLayers bank L hL)=wordMatrix (layersWord bank L) := by
  induction L with
  | nil => simp [shearLayers,layersWord,matrix,wordMatrix]
  | cons W L ih =>
    have he : shearLayers bank (W::L) hL = matchingLayers bank W (hL W (by simp)) ++
        shearLayers bank L (fun V hV => hL V (by simp [hV])) := by
      simp only [shearLayers,List.attach_cons,List.map_cons,List.map_map,List.flatten_cons,Function.comp_def]
    rw [he,matrix_append,matchingLayers_matrix,ih]
    change _=wordMatrix (listWord bank W++layersWord bank L)
    rw [wordMatrix_append]

theorem shearLayers_calls {v r : ℕ} (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hL : ∀ W∈L,Matching W) : calls (shearLayers bank L hL)=wordCalls (layersWord bank L) := by
  induction L with
  | nil => simp [shearLayers,layersWord,calls,wordCalls]
  | cons W L ih =>
    have he : shearLayers bank (W::L) hL = matchingLayers bank W (hL W (by simp)) ++
        shearLayers bank L (fun V hV => hL V (by simp [hV])) := by
      simp only [shearLayers,List.attach_cons,List.map_cons,List.map_map,List.flatten_cons,Function.comp_def]
    rw [he,calls_append,matchingLayers_calls,ih]
    change _=wordCalls (listWord bank W++layersWord bank L)
    rw [wordCalls_append]

theorem shearLayers_length {v r : ℕ} (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hL : ∀ W∈L,Matching W) : (shearLayers bank L hL).length=28*L.length := by
  simp [shearLayers,List.length_flatten,Function.comp_def,Nat.mul_comm]


open UniformWorkspacePlanner UniformDAGLayers
variable {v r e a : ℕ}

/- Paper: Lemma 3.3, pp. 14–15 and (3.11), p. 16: colored dirty replay fits its source, gate and target placements inside the parent coordinates. -/
def chunkSchedule {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀ p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) : List (Layer v) :=
  shearLayers bank (chunkLayers D he P hD hd huse) (chunkLayers_matching D he P hD hd huse)

theorem chunkSchedule_matrix {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀ p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    matrix (chunkSchedule D bank he P hD hd huse)=wordMatrix (chunkWord D bank he P hD hd huse) :=
  shearLayers_matrix ..

theorem chunkSchedule_calls {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀ p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    calls (chunkSchedule D bank he P hD hd huse)=wordCalls (chunkWord D bank he P hD hd huse) :=
  shearLayers_calls ..

theorem chunkSchedule_length {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀ p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    (chunkSchedule D bank he P hD hd huse).length=28*(4*(H+1)+2)*(2*delta-1) := by
  rw [chunkSchedule,shearLayers_length,chunkLayers_length,UniformDAGLayers.replayLayers_length]
  ring

def selectedSchedule (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) : List (Layer v) :=
  chunkSchedule (printedCross a e) bank (chunk_pos hv he) (selectedPlacement hv ha he source target hst)
    (printedCross_depth a e) (by decide) (printedCross_fanout a e)

theorem selectedSchedule_matrix (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    matrix (selectedSchedule hv ha he source target hst bank)=wordMatrix (selectedWord hv ha he source target hst bank) :=
  chunkSchedule_matrix ..

theorem selectedSchedule_calls (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    calls (selectedSchedule hv ha he source target hst bank)=wordCalls (selectedWord hv ha he source target hst bank) :=
  chunkSchedule_calls ..

theorem selectedSchedule_length (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    (selectedSchedule hv ha he source target hst bank).length≤1848*(8*Nat.clog 2 v+23) := by
  rw [selectedSchedule,chunkSchedule_length]
  have hk := exponent_bound ((chunk_le ha).trans (selected_le v)) ((chunk_le he).trans (selected_le v))
  omega

open UniformBalancedToeplitz

/-- Same ragged blocks, coefficient references, and borrowed placement as pairWord. -/
def pairSchedule (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) : List (Layer n) :=
  let a := size (n-n/2) (selected n) q.1
  let e := size (n/2) (selected n) q.2
  let i₀ := n/2+q.1.val*selected n
  let j₀ := q.2.val*selected n
  let M := fun i j => ToeplitzLayers.cross (n/2) (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (i₀+i) (j₀+j)
  let v₀ := fun i => -PowerSeries.coeff (i₀+i-n/2) f
  let w₀ := fun j => PowerSeries.coeff (n/2-(j₀+j)) f⁻¹
  selectedSchedule hv (size_mem _ _ q.1) (size_mem _ _ q.2) (pairSource n hv q.2) (pairTarget n hv q.1)
    (fun _ _=>left_right n _ _) (UniformToeplitzCrossDAG.sharedBank (exponent a e)
      (UniformToeplitzCrossDAG.rankKernels (exponent a e) a e M v₀ w₀))

theorem pairSchedule_matrix (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    matrix (pairSchedule n hv f q)=wordMatrix (pairWord n hv f q) := selectedSchedule_matrix ..

theorem pairSchedule_calls (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    calls (pairSchedule n hv f q)=wordCalls (pairWord n hv f q) := selectedSchedule_calls ..

theorem pairSchedule_length (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    (pairSchedule n hv f q).length≤1848*(8*Nat.clog 2 n+23) := selectedSchedule_length ..

/- Paper: Lemma 3.4, p. 17: chunk pairs are processed serially, with restored borrowed coordinates reused between pairs. -/
def correctionSchedule (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) : List (Layer n) :=
  ((pairs n).map (pairSchedule n hv f)).flatten

theorem matrix_flatten {n : ℕ} (L : List (List (Layer n))) :
    matrix L.flatten=(L.map matrix).reverse.prod := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

theorem calls_flatten {n : ℕ} (L : List (List (Layer n))) : calls L.flatten=(L.map calls).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

theorem correctionSchedule_matrix (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    matrix (correctionSchedule n hv f)=wordMatrix (correctionWord n hv f) := by
  simp only [correctionSchedule,correctionWord,matrix_flatten,TensorWords.wordMatrix_flatten,
    List.map_map,Function.comp_def,pairSchedule_matrix]

theorem correctionSchedule_calls (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    calls (correctionSchedule n hv f)=wordCalls (correctionWord n hv f) := by
  simp only [correctionSchedule,correctionWord,calls_flatten,TensorWords.wordCalls_flatten,
    List.map_map,Function.comp_def,pairSchedule_calls]

theorem list_length_bound {ι α : Type} (f : ι → List α) (L : List ι) (d : ℕ) (hf : ∀ i,(f i).length≤d) :
    ((L.map f).flatten).length≤L.length*d := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons];
                   have hi:=hf i; nlinarith

theorem correctionSchedule_length (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ) :
    (correctionSchedule n hv f).length≤crossUnit*(Nat.clog 2 n+1)^3 := by
  have hb := list_length_bound (pairSchedule n hv f) (pairs n) _ (pairSchedule_length n hv f)
  rw [pairs_length] at hb
  have ha := chunkCount_log_bound n (n-n/2) hv (Nat.sub_le _ _)
  have hs := chunkCount_log_bound n (n/2) hv (Nat.div_le_self _ _)
  have hlocal : 1848*(8*Nat.clog 2 n+23)≤42504*(Nat.clog 2 n+1) := by omega
  calc
    _ ≤ _ := hb
    _ ≤ (131072*(Nat.clog 2 n+1))*(131072*(Nat.clog 2 n+1))*(42504*(Nat.clog 2 n+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hs) hlocal
    _ = _ := by unfold crossUnit;ring

/-- Concrete Plan interpreter: children zip in parallel, ragged cross pairs run serially. -/
def render {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (Layer n) :=
  match P with
  | .direct n cap => serial (UniformBalancedToeplitz.render (.direct n cap) f hf)
  | .split n _ hv L R => parallel (coordinates n) (render L f hf) (render R f hf) ++ correctionSchedule n hv f

theorem diagonal_matrix (n : ℕ) (L : List (WordStep C (n/2))) (R : List (WordStep C (n-n/2))) :
    Matrix.reindex (coordinates n) (coordinates n) (Matrix.fromBlocks (wordMatrix L) 0 0 (wordMatrix R))=
      wordMatrix (TensorWords.embeddedWord (left n) L++TensorWords.embeddedWord (right n) R) := by
  rw [←diagonalWord_blocks]
  ext i j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem render_matrix {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    matrix (render P f hf)=wordMatrix (UniformBalancedToeplitz.render P f hf) := by
  induction P with
  | direct n cap => exact serial_matrix _
  | split n hn hv L R ihL ihR =>
    change matrix (parallel (coordinates n) (render L f hf) (render R f hf)++correctionSchedule n hv f)=_
    rw [matrix_append,parallel_matrix,ihL,ihR,correctionSchedule_matrix,diagonal_matrix,←wordMatrix_append]
    rfl

theorem render_calls {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    calls (render P f hf)=wordCalls (UniformBalancedToeplitz.render P f hf) := by
  induction P with
  | direct n cap => exact serial_calls _
  | split n hn hv L R ihL ihR =>
    simp only [render,calls_append,parallel_calls,ihL,ihR,correctionSchedule_calls,
      UniformBalancedToeplitz.render,wordCalls_append,TensorWords.embeddedWord_calls]

theorem render_length {n : ℕ} (P : Plan n) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (render P f hf).length≤UniformBalancedToeplitz.depthUnit*(Nat.clog 2 n+1)^4 := by
  induction P with
  | direct n cap =>
    change (serial (UniformBalancedToeplitz.render (.direct n cap) f hf)).length≤_
    rw [serial_length]
    dsimp only [UniformBalancedToeplitz.render]
    split_ifs with hn
    · rw [UniformDirectToeplitz.word_length]
      have hcap : n+14*n*(n-1)≤532545 := by have hs:=Nat.sub_le n 1;nlinarith
      have hp : 1≤(Nat.clog 2 n+1)^4 := by
        have hh:0<(Nat.clog 2 n+1)^4:=by positivity
        omega
      have hb : 532545≤UniformBalancedToeplitz.depthUnit := by unfold UniformBalancedToeplitz.depthUnit;omega
      exact hcap.trans (hb.trans (by simpa using Nat.mul_le_mul_left UniformBalancedToeplitz.depthUnit hp))
    · simp
  | split n hn hv L R ihL ihR =>
    change (parallel (coordinates n) (render L f hf) (render R f hf)++correctionSchedule n hv f).length≤_
    rw [List.length_append,parallel_length]
    have hh := half_clog n hn
    have hl := ihL.trans (Nat.mul_le_mul_left UniformBalancedToeplitz.depthUnit (Nat.pow_le_pow_left hh.1 4))
    have hr := ihR.trans (Nat.mul_le_mul_left UniformBalancedToeplitz.depthUnit (Nat.pow_le_pow_left hh.2 4))
    have hm := max_le hl hr
    have hc := correctionSchedule_length n hv f
    have hunit : crossUnit≤UniformBalancedToeplitz.depthUnit := by unfold UniformBalancedToeplitz.depthUnit;omega
    have hstep := Nat.mul_le_mul_left UniformBalancedToeplitz.depthUnit (fourth_increment (Nat.clog 2 n))
    have hcoef := Nat.mul_le_mul_right ((Nat.clog 2 n+1)^3) hunit
    rw [Nat.mul_add] at hstep
    omega

def toeplitz (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (Layer n) := render (plan n) f hf

theorem toeplitz_matrix (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    matrix (toeplitz n f hf)=CoefficientTime.truncMatrix n f := by rw [toeplitz,render_matrix,UniformBalancedToeplitz.render_matrix]

theorem toeplitz_calls (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    calls (toeplitz n f hf)=wordCalls (UniformBalancedToeplitz.word n f hf) := render_calls ..

theorem toeplitz_length (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (toeplitz n f hf).length≤UniformBalancedToeplitz.depthUnit*(Nat.clog 2 n+1)^4 := render_length ..


/-- Transposition retains all forward C calls and their ordered placements. -/
def Layer.transpose {n : ℕ} : Layer n → Layer n
  | .step s => .step (UniformLocalFourierWord.transposeStep s)
  | .parallel e L R => .parallel e L.transpose R.transpose
  | .embed e L => .embed e L.transpose
  | .batch position steps => .batch position (fun i => UniformLocalFourierWord.transposeStep (steps i))

theorem embedded_transpose {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Matrix α α ℂ) : Embedded.matrix e M.transpose=(Embedded.matrix e M).transpose := by
  simp [Embedded.matrix,Matrix.reindex_apply,Matrix.transpose_submatrix,Matrix.fromBlocks_transpose]

theorem Layer.transpose_matrix {n : ℕ} (L : Layer n) : L.transpose.matrix=L.matrix.transpose := by
  induction L with
  | step s => simp [transpose,UniformLocalFourierWord.transposeStep_matrix]
  | parallel e L R ihL ihR =>
    simp [transpose,ihL,ihR,Matrix.reindex_apply,Matrix.transpose_submatrix,Matrix.fromBlocks_transpose]
  | embed e L ih => simp [transpose,ih,embedded_transpose]
  | batch position steps =>
    simp only [transpose,Layer.batch_matrix,UniformLocalFourierWord.transposeStep_matrix,
      ←Matrix.blockDiagonal'_transpose,embedded_transpose]

theorem Layer.transpose_calls {n : ℕ} (L : Layer n) : L.transpose.calls=L.calls := by
  induction L with
  | step s => simp [transpose,UniformLocalFourierWord.transposeStep_calls]
  | parallel e L R ihL ihR => simp [transpose,ihL,ihR]
  | embed e L ih => simp [transpose,ih]
  | batch position steps => simp [transpose,UniformLocalFourierWord.transposeStep_calls]

def transpose {n : ℕ} (L : List (Layer n)) : List (Layer n) := (L.map Layer.transpose).reverse

theorem transpose_matrix {n : ℕ} (L : List (Layer n)) : matrix (transpose L)=(matrix L).transpose := by
  induction L with
  | nil => simp [transpose]
  | cons l L ih =>
    simp only [transpose,List.map_cons,List.reverse_cons]
    change matrix (transpose L++[l.transpose])=_
    rw [matrix_append]
    simp only [matrix,Layer.transpose_matrix,List.map_singleton,List.reverse_singleton,
      List.prod_singleton] at *
    rw [ih]
    simp [Matrix.transpose_mul]

theorem transpose_calls {n : ℕ} (L : List (Layer n)) : calls (transpose L)=calls L := by
  simp [transpose,calls,List.map_map,Function.comp_def,Layer.transpose_calls]
@[simp] theorem transpose_length {n : ℕ} (L : List (Layer n)) : (transpose L).length=L.length := by simp [transpose]

open NewtonFourier CoefficientTime

def sandwich {n : ℕ} (left right : Fin n → ℂ) (hl : ∀ j,left j≠0) (hr : ∀ j,right j≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (Layer n) :=
  [Layer.step (UniformLocalFourierWord.diagonalStep right hr)] ++ toeplitz n f hf ++
  [Layer.step (UniformLocalFourierWord.diagonalStep left hl)]

theorem sandwich_matrix {n : ℕ} (left right : Fin n → ℂ) (hl : ∀ j,left j≠0) (hr : ∀ j,right j≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    matrix (sandwich left right hl hr f hf)=wordMatrix (UniformLocalFourierWord.sandwich left right hl hr f hf) := by
  rw [UniformLocalFourierWord.sandwich_matrix]
  simp only [sandwich,matrix_append,matrix_singleton,Layer.step_matrix,
    UniformLocalFourierWord.diagonalStep_matrix,toeplitz_matrix,Matrix.mul_assoc]

theorem sandwich_calls {n : ℕ} (left right : Fin n → ℂ) (hl : ∀ j,left j≠0) (hr : ∀ j,right j≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    calls (sandwich left right hl hr f hf)=wordCalls (UniformLocalFourierWord.sandwich left right hl hr f hf) := by
  rw [UniformLocalFourierWord.sandwich_calls]
  simp only [sandwich,calls_append,calls_singleton,Layer.step_calls,
    UniformLocalFourierWord.diagonalStep_calls,toeplitz_calls,zero_add,add_zero]

theorem sandwich_length {n : ℕ} (left right : Fin n → ℂ) (hl : ∀ j,left j≠0) (hr : ∀ j,right j≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (sandwich left right hl hr f hf).length≤UniformBalancedToeplitz.depthUnit*(Nat.clog 2 n+1)^4+2 := by
  have ht := toeplitz_length n f hf
  simpa only [sandwich,List.length_append,List.length_singleton] using (by omega : 1+(toeplitz n f hf).length+1≤_)

def symmetric {n : ℕ} (L : List (Layer n)) (d : Fin n → ℂ) (hd : ∀ j,d j≠0) : List (Layer n) :=
  transpose L ++ [Layer.step (UniformLocalFourierWord.diagonalStep d hd)] ++ L

theorem symmetric_matrix {n : ℕ} (L : List (Layer n)) (d : Fin n → ℂ) (hd : ∀ j,d j≠0) :
    matrix (symmetric L d hd)=matrix L*Matrix.diagonal d*(matrix L).transpose := by
  simp only [symmetric,matrix_append,matrix_singleton,Layer.step_matrix,
    UniformLocalFourierWord.diagonalStep_matrix,transpose_matrix,Matrix.mul_assoc]

theorem symmetric_calls {n : ℕ} (L : List (Layer n)) (d : Fin n → ℂ) (hd : ∀ j,d j≠0) :
    calls (symmetric L d hd)=2*calls L := by
  simp only [symmetric,calls_append,calls_singleton,Layer.step_calls,
    UniformLocalFourierWord.diagonalStep_calls,transpose_calls]
  omega

theorem symmetric_length {n : ℕ} (L : List (Layer n)) (d : Fin n → ℂ) (hd : ∀ j,d j≠0) :
    (symmetric L d hd).length=2*L.length+1 := by simp [symmetric];omega

/- Paper: Lemma 3.5, p. 17 and (3.1)–(3.2), p. 13: compile the two Newton diagonals and exact-width Toeplitz factor, then compose N^T, D_N^(-1), N. -/
def Nschedule {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) : List (Layer n) :=
  sandwich (fun j=>NewtonFourier.H omega j.val) (fun j=>scale omega j.val)
    (UniformNewton.Hvalue_ne_zero hroot) (UniformNewton.scaleValue_ne_zero hn hroot) (invH omega) (by simp)

theorem Nschedule_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    matrix (Nschedule hn hroot)=wordMatrix (UniformLocalFourierWord.NWord hn hroot) := sandwich_matrix ..

theorem Nschedule_calls {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    calls (Nschedule hn hroot)=wordCalls (UniformLocalFourierWord.NWord hn hroot) := sandwich_calls ..

def schedule {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) : List (Layer n) :=
  symmetric (Nschedule hn hroot) (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j))

theorem schedule_matrix_word {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    matrix (schedule hn hroot)=wordMatrix (UniformLocalFourierWord.word hn hroot) := by
  rw [schedule,symmetric_matrix,Nschedule_matrix,UniformLocalFourierWord.word,
    UniformLocalFourierWord.symmetricWord_matrix]

theorem schedule_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    matrix (schedule hn hroot)=RadixTwo.dft n omega := by rw [schedule_matrix_word,UniformLocalFourierWord.word_matrix]

theorem schedule_calls {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    calls (schedule hn hroot)=wordCalls (UniformLocalFourierWord.word hn hroot) := by
  rw [schedule,symmetric_calls,Nschedule_calls,UniformLocalFourierWord.word,UniformLocalFourierWord.symmetricWord_calls]

theorem schedule_length {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    (schedule hn hroot).length≤UniformLocalFourierWord.sufficientSlots n := by
  have hnlen := sandwich_length (fun j : Fin n=>NewtonFourier.H omega j.val) (fun j=>scale omega j.val)
    (UniformNewton.Hvalue_ne_zero hroot) (UniformNewton.scaleValue_ne_zero hn hroot) (invH omega) (by simp)
  rw [schedule,symmetric_length]
  unfold Nschedule UniformLocalFourierWord.sufficientSlots
  omega


/-- A literal step contributes either no pair or its one stored ordered tuple. -/
def stepIndex {n : ℕ} : WordStep C n → Type
  | .monomial _ _ => Fin 0
  | .call _ => Fin 1

@[instance_reducible] def stepFinite {n : ℕ} (s : WordStep C n) : Fintype (stepIndex s) := by
  cases s with
  | monomial M hM => change Fintype (Fin 0);infer_instance
  | call e => change Fintype (Fin 1);infer_instance
instance {n : ℕ} (s : WordStep C n) : Fintype (stepIndex s) := stepFinite s

def stepPosition {n : ℕ} : (s : WordStep C n) → (Σ _ : stepIndex s, Fin 2) ↪ Fin n
  | .monomial _ _ => ⟨fun p => Fin.elim0 p.1,by intro p;exact Fin.elim0 p.1⟩
  | .call e =>
      ⟨fun p => e p.2,by
        rintro ⟨i,x⟩ ⟨j,y⟩ h
        have hxy : x=y := e.injective h
        subst y
        have hij : i=j := by
          change @Eq (Fin 1) i j
          exact Subsingleton.elim _ _
        subst j
        rfl⟩

theorem step_card {n : ℕ} (s : WordStep C n) : Fintype.card (stepIndex s)=s.calls := by
  cases s with
  | monomial M hM => exact (Fintype.card_congr (Equiv.refl (Fin 0))).trans (by simp [WordStep.calls])
  | call e => exact (Fintype.card_congr (Equiv.refl (Fin 1))).trans (by simp [WordStep.calls])

/-- Actual finite call labels, including all branches of a parallel layer. -/
/- Paper: No separate paper lemma: finite call labels and injective pair positions make the “disjoint ordered pairs” requirement of Proposition 3.1, p. 12 explicit. -/
def Layer.Index {n : ℕ} : Layer n → Type
  | .step s => stepIndex s
  | .parallel _ L R => L.Index ⊕ R.Index
  | .embed _ L => L.Index
  | .batch _ steps => Σ i : Fin _, stepIndex (steps i)

@[instance_reducible] def Layer.finite {n : ℕ} : (L : Layer n) → Fintype L.Index
  | .step s => stepFinite s
  | .parallel _ L R => by
      change Fintype (L.Index ⊕ R.Index)
      letI := L.finite
      letI := R.finite
      infer_instance
  | .embed _ L => L.finite
  | @Layer.batch s _ _ steps => by
      change Fintype (Σ i : Fin s,stepIndex (steps i))
      infer_instance
instance {n : ℕ} (L : Layer n) : Fintype L.Index := L.finite
instance {n : ℕ} (L : Layer n) : DecidableEq L.Index := Classical.decEq _

/-- The disjoint physical ordered tuples belonging to this layer's actual calls. -/
def Layer.position {n : ℕ} : (L : Layer n) → (Σ _ : L.Index, Fin 2) ↪ Fin n
  | .step s => stepPosition s
  | .parallel e L R => PairFamily.sumEquiv.toEmbedding.trans
      ((L.position.sumMap R.position).trans e.toEmbedding)
  | .embed e L => L.position.trans e
  | .batch position steps =>
      ⟨fun p => position ⟨p.1.1, stepPosition (steps p.1.1) ⟨p.1.2,p.2⟩⟩,by
        rintro ⟨⟨i,k⟩,x⟩ ⟨⟨j,l⟩,y⟩ h
        have hs := position.injective h
        have hij : i=j := congrArg Sigma.fst hs
        subst j
        have ht := congrArg Sigma.snd hs
        have hk := (stepPosition (steps i)).injective ht
        cases hk
        rfl⟩

theorem Layer.position_distinct {n : ℕ} (L : Layer n) (i j : L.Index) (hij : i≠j) (x y : Fin 2) :
    L.position ⟨i,x⟩≠L.position ⟨j,y⟩ := by
  intro h
  exact hij (congrArg Sigma.fst (L.position.injective h))

theorem Layer.position_inside {n : ℕ} (L : Layer n) (i : L.Index) :
    L.position ⟨i,0⟩≠L.position ⟨i,1⟩ := by
  intro h
  have hh := congrArg Sigma.snd (L.position.injective h)
  exact (by decide : (0 : Fin 2)≠1) hh

theorem Layer.card_calls {n : ℕ} (L : Layer n) : Fintype.card L.Index=L.calls := by
  induction L with
  | step s =>
    calc
      _ = Fintype.card (stepIndex s) := Fintype.card_congr (Equiv.refl _)
      _ = _ := step_card s
  | parallel e L R ihL ihR =>
    calc
      _ = Fintype.card (L.Index ⊕ R.Index) := Fintype.card_congr (Equiv.refl _)
      _ = L.calls+R.calls := by rw [Fintype.card_sum,ihL,ihR]
      _ = _ := (Layer.parallel_calls ..).symm
  | embed e L ih =>
    calc
      _ = Fintype.card L.Index := Fintype.card_congr (Equiv.refl _)
      _ = L.calls := ih
      _ = _ := (Layer.embed_calls ..).symm
  | batch position steps =>
    calc
      _ = Fintype.card (Σ i,stepIndex (steps i)) := Fintype.card_congr (Equiv.refl _)
      _ = ∑ i,(steps i).calls := by simp only [Fintype.card_sigma,step_card]
      _ = _ := (Layer.batch_calls ..).symm

theorem Layer.call_capacity {n : ℕ} (L : Layer n) : 2*L.calls≤n := by
  have h := Fintype.card_le_of_injective L.position L.position.injective
  simpa only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,Layer.card_calls,Nat.mul_comm] using h

/-- Same 28 simultaneous phases, with every varying diagonal read from actual shared-DAG outputs. -/
def preparedBatch {b s n : ℕ} (d : UniformScalarPreparation.DAG b s) (roots : Fin b → ℂ)
    (unit : ∀ j,‖roots j‖=1) (hd : d.Admissible roots)
    (position : (Σ _ : Fin s,Fin 2) ↪ Fin n) : List (Layer n) :=
  batchWords 28 position (UniformShearPreparation.preparedWord d roots unit hd)
    (fun i => by rw [UniformShearPreparation.preparedWord_eq];exact localShear_length _)

theorem preparedBatch_matrix {b s n : ℕ} (d : UniformScalarPreparation.DAG b s) (roots : Fin b → ℂ)
    (unit : ∀ j,‖roots j‖=1) (hd : d.Admissible roots)
    (position : (Σ _ : Fin s,Fin 2) ↪ Fin n) :
    matrix (preparedBatch d roots unit hd position)=
      Embedded.matrix position (Matrix.blockDiagonal' (fun j => upperShear (d.run roots hd j))) := by
  rw [preparedBatch,batchWords_matrix]
  simp only [UniformShearPreparation.preparedWord_matrix]

theorem preparedBatch_calls {b s n : ℕ} (d : UniformScalarPreparation.DAG b s) (roots : Fin b → ℂ)
    (unit : ∀ j,‖roots j‖=1) (hd : d.Admissible roots)
    (position : (Σ _ : Fin s,Fin 2) ↪ Fin n) : calls (preparedBatch d roots unit hd position)=6*s := by
  rw [preparedBatch,batchWords_calls]
  simp [UniformShearPreparation.preparedWord_calls,Nat.mul_comm]

theorem preparedBatch_length {b s n : ℕ} (d : UniformScalarPreparation.DAG b s) (roots : Fin b → ℂ)
    (unit : ∀ j,‖roots j‖=1) (hd : d.Admissible roots)
    (position : (Σ _ : Fin s,Fin 2) ↪ Fin n) : (preparedBatch d roots unit hd position).length=28 := batchWords_length ..

/-- Concrete Newton bank adapter; recursive cross-bank production is a separate phase. -/
/- Paper: Lemma 3.2, p. 13 and Lemma 3.5, p. 17: substitute actual Newton-table outputs into the same factorization. PreparedOutputs is an intermediate source contract, not a hidden complex literal. -/
def preparedNschedule {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) : List (Layer n) :=
  sandwich (fun j=>UniformLocalFourierWord.preparedValue a s j 0)
    (fun j=>UniformLocalFourierWord.preparedValue a s j 1)
    (UniformLocalFourierWord.preparedH_nonzero hroot hp)
    (UniformLocalFourierWord.preparedScale_nonzero hn hroot hp)
    (UniformLocalFourierWord.preparedSeries n a s)
    (by rw [UniformLocalFourierWord.preparedSeries_constant hn hp];exact one_ne_zero)

def preparedSchedule {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) : List (Layer n) :=
  symmetric (preparedNschedule hn hroot s hp) (fun j=>UniformLocalFourierWord.preparedValue a s j 4)
    (UniformLocalFourierWord.preparedInvD_nonzero hn hroot hp)

theorem preparedNschedule_matrix {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    matrix (preparedNschedule hn hroot s hp)=wordMatrix (UniformLocalFourierWord.preparedNWord hn hroot s hp) := sandwich_matrix ..

theorem preparedNschedule_calls {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    calls (preparedNschedule hn hroot s hp)=wordCalls (UniformLocalFourierWord.preparedNWord hn hroot s hp) := sandwich_calls ..

theorem preparedSchedule_matrix {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    matrix (preparedSchedule hn hroot s hp)=RadixTwo.dft n omega := by
  rw [preparedSchedule,symmetric_matrix,preparedNschedule_matrix,UniformLocalFourierWord.preparedNWord_matrix]
  have hd : (fun j : Fin n=>UniformLocalFourierWord.preparedValue a s j 4)=
      (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹):=funext (UniformLocalFourierWord.preparedInvD_value hp)
  rw [hd,←UniformNewton.Preparation.diagonal_inverse hn hroot]
  exact (UniformNewton.fourier_factorization hn hroot).symm

theorem preparedSchedule_calls {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    calls (preparedSchedule hn hroot s hp)=wordCalls (UniformLocalFourierWord.preparedWord hn hroot s hp) := by
  rw [preparedSchedule,symmetric_calls,preparedNschedule_calls,
    UniformLocalFourierWord.preparedWord,UniformLocalFourierWord.symmetricWord_calls]

theorem preparedSchedule_length {n a : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n)
    (s : UniformMachine.State) (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    (preparedSchedule hn hroot s hp).length≤UniformLocalFourierWord.sufficientSlots n := by
  have h := sandwich_length (fun j : Fin n=>UniformLocalFourierWord.preparedValue a s j 0)
    (fun j=>UniformLocalFourierWord.preparedValue a s j 1)
    (UniformLocalFourierWord.preparedH_nonzero hroot hp)
    (UniformLocalFourierWord.preparedScale_nonzero hn hroot hp)
    (UniformLocalFourierWord.preparedSeries n a s)
    (by rw [UniformLocalFourierWord.preparedSeries_constant hn hp];exact one_ne_zero)
  rw [preparedSchedule,symmetric_length]
  unfold preparedNschedule UniformLocalFourierWord.sufficientSlots
  omega


/-- Actual shared-table output references for the six varying shear scales. -/
def scaleReference {b s : ℕ} (d : UniformScalarPreparation.DAG b s) (j : Fin s) (q : Fin 6) :
    Fin (UniformShearPreparation.table d).length :=
  (UniformShearPreparation.table d).output (finProdFinEquiv (j,⟨q.val+2,by omega⟩))

theorem scaleReference_value {b s : ℕ} (d : UniformScalarPreparation.DAG b s) (roots : Fin b → ℂ)
    (unit : ∀ j,‖roots j‖=1) (hd : d.Admissible roots) (j : Fin s) (q : Fin 6) :
    (UniformShearPreparation.table d).program.run roots
      (UniformShearPreparation.table_admissible d roots unit hd) (scaleReference d j q)=
        UniformShearPreparation.scaleValues d roots unit hd j q := by
  change (UniformShearPreparation.table d).run roots
    (UniformShearPreparation.table_admissible d roots unit hd) (finProdFinEquiv (j,⟨q.val+2,by omega⟩))=_
  rw [UniformShearPreparation.table_run d roots unit hd j ⟨q.val+2,by omega⟩,
    UniformShearPreparation.scaleValues_eq d roots unit hd j q]
  fin_cases q <;> rfl

theorem scaleReference_bound {b s : ℕ} (d : UniformScalarPreparation.DAG b s) (j : Fin s) (q : Fin 6) :
    (scaleReference d j q).val<7*(d.length+b+s+1) := UniformShearPreparation.table_output_bound d _

/-- Canonical positive Fourier schedule, including the empty axis. -/
/- Paper: Proposition 3.1, p. 12: the canonical positive root fixes the Fourier convention. The empty axis is a formal bookkeeping extension; the paper’s compiler assumes r >= 1. -/
def specifiedSchedule (n : ℕ) : List (Layer n) :=
  if hn:0<n then schedule hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) else []

theorem specifiedSchedule_matrix (n : ℕ) : matrix (specifiedSchedule n)=fourierMatrix n := by
  by_cases hn:0<n
  · simp only [specifiedSchedule,dite_eq_left hn,schedule_matrix]
    rfl
  · have hz:n=0:=by omega
    subst n
    ext i j
    exact Fin.elim0 i

theorem specifiedSchedule_action (n : ℕ) (x : Fin n → ℂ) :
    (matrix (specifiedSchedule n)).mulVec x=(fourierMatrix n).mulVec x := by rw [specifiedSchedule_matrix]

theorem specifiedSchedule_calls (n : ℕ) : calls (specifiedSchedule n)=wordCalls (UniformLocalFourierWord.specifiedWord n) := by
  by_cases hn:0<n
  · simpa only [specifiedSchedule,UniformLocalFourierWord.specifiedWord,dite_eq_left hn] using
      schedule_calls hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))
  · simp [specifiedSchedule,UniformLocalFourierWord.specifiedWord,hn,wordCalls]

theorem specifiedSchedule_call_bound (n : ℕ) : calls (specifiedSchedule n)≤32*n^3 := by
  rw [specifiedSchedule_calls]
  exact UniformLocalFourierWord.specifiedWord_calls n

theorem specifiedSchedule_length (n : ℕ) : (specifiedSchedule n).length≤UniformLocalFourierWord.sufficientSlots n := by
  by_cases hn:0<n
  · simpa only [specifiedSchedule,dite_eq_left hn] using
      schedule_length hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn))
  · simp [specifiedSchedule,hn]

theorem specifiedSchedule_length_bound (n : ℕ) :
    (specifiedSchedule n).length≤UniformLocalFourierWord.depthUnit*(Nat.clog 2 n+1)^4 :=
  (specifiedSchedule_length n).trans (UniformLocalFourierWord.sufficientSlots_bound n)


/-- Verify legality from the explicit data, without extracting a circuit witness. -/
theorem round_embed {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) {M : Matrix α α ℂ} (h : Round M) : Round (Embedded.matrix e M) :=
  (h.sum Round.one).reindex (Embedded.coordinates e)

theorem round_step {n : ℕ} (s : WordStep C n) : Round s.matrix := by
  cases s with
  | monomial M hM => exact Round.mono M hM
  | call e =>
    change Round (embeddedCall C e)
    rw [Packing.embeddedCall_eq]
    exact round_embed e (Round.pair C UniformDirectToeplitz.C_unit)

theorem round_blocks (s : ℕ) (M : Fin s → Matrix (Fin 2) (Fin 2) ℂ) (hM : ∀ i,Round (M i)) :
    Round (Matrix.blockDiagonal' M) := by
  induction s with
  | zero =>
    have he : Matrix.blockDiagonal' M=(1 : Matrix (Σ _ : Fin 0,Fin 2) (Σ _ : Fin 0,Fin 2) ℂ) := by
      ext ⟨i,x⟩ j
      exact Fin.elim0 i
    rw [he]
    exact Round.one
  | succ s ih =>
    have h := (hM 0).sum (ih (fun i=>M i.succ) (fun i=>hM i.succ))
    let e := sigmaFinSucc (fun _ : Fin (s+1)=>Fin 2)
    have he : Matrix.reindex e.symm e.symm
        (Matrix.fromBlocks (M 0) 0 0 (Matrix.blockDiagonal' (fun i : Fin s=>M i.succ)))=
          Matrix.blockDiagonal' M := by
      ext ⟨i,x⟩ ⟨j,y⟩
      refine Fin.cases ?_ (fun i=>?_) i x <;> intro x <;>
        refine Fin.cases ?_ (fun j=>?_) j y <;> intro y <;>
        simp [e,Matrix.reindex_apply,sigmaFinSucc,Matrix.blockDiagonal'_apply,Fin.succ_ne_zero,eq_comm]
    rw [←he]
    exact h.reindex e.symm

theorem Layer.round {n : ℕ} (L : Layer n) : Round L.matrix := by
  induction L with
  | step s => rw [Layer.step_matrix];exact round_step s
  | parallel e L R ihL ihR => rw [Layer.parallel_matrix];exact (ihL.sum ihR).reindex e
  | embed e L ih => rw [Layer.embed_matrix];exact round_embed e ih
  | batch position steps =>
    rw [Layer.batch_matrix]
    exact round_embed position (round_blocks _ _ (fun i=>round_step (steps i)))

end
end ExactFourierCircuits.UniformLocalFourierLayers
