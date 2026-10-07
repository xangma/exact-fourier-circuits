import UniformDirectToeplitz
import UniformLayeredReplay
import UniformDAGLayers
import UniformWorkspacePlanner
import UniformRankKernelPreparation
import OAI.Computability.FourierCircuit.CircuitCost

set_option autoImplicit false

/-! Exact-width literal six-C compilation. Topology contains only integer ports
and prepared references. Complex semantics and table/RAM production are separate. -/
namespace ExactFourierCircuits.UniformToeplitzChunkWord
open OAI.ExactFourier TypedKernelWords UniformReplayPrint
open scoped BigOperators

variable {r v e g a : ℕ}

/-- Explicit disjoint source, dirty gate, and target assignments. -/
structure Placement (e g a v : ℕ) where
  source : Fin e ↪ Fin v
  gates : Fin g ↪ Fin v
  target : Fin a ↪ Fin v
  source_gates : ∀ i j, source i ≠ gates j
  source_target : ∀ i j, source i ≠ target j
  gates_target : ∀ i j, gates i ≠ target j

def Placement.coordinates (P : Placement e g a v) : ((Fin e ⊕ Fin g) ⊕ Fin a) ↪ Fin v where
  toFun := Sum.elim (Sum.elim P.source P.gates) P.target
  inj' := by
    intro i j h
    rcases i with (i|i)|i <;> rcases j with (j|j)|j
    · exact congrArg Sum.inl (congrArg Sum.inl (P.source.injective h))
    · exact False.elim (P.source_gates i j h)
    · exact False.elim (P.source_target i j h)
    · exact False.elim (P.source_gates j i h.symm)
    · exact congrArg Sum.inl (congrArg Sum.inr (P.gates.injective h))
    · exact False.elim (P.gates_target i j h)
    · exact False.elim (P.source_target j i h.symm)
    · exact False.elim (P.gates_target j i h.symm)
    · exact congrArg Sum.inr (P.target.injective h)

def flatten (e g a : ℕ) : ((Fin e ⊕ Fin g) ⊕ Fin a) ≃ Fin (e+g+a) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def Placement.embedding (P : Placement e g a v) : Fin (e+g+a) ↪ Fin v :=
  (flatten e g a).symm.toEmbedding.trans P.coordinates

/-- Every retained occurrence has its own six-call word, even when it evaluates to zero. -/
noncomputable def shearWord (bank : Fin r → ℂ) (s : ShearCode (Fin v) r) :
    List (WordStep C v) :=
  UniformDirectToeplitz.shear s.dst ⟨s.src,s.different.symm⟩ (s.coefficient.eval bank)

noncomputable def listWord (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) :
    List (WordStep C v) := (W.map (shearWord bank)).flatten

theorem shearWord_matrix (bank : Fin r → ℂ) (s : ShearCode (Fin v) r) :
    wordMatrix (shearWord bank s) =
      Embedded.matrix (Embedded.pair s.dst s.src s.different) (upperShear (s.coefficient.eval bank)) := by
  rw [shearWord, UniformDirectToeplitz.shear, TensorWords.embeddedWord_matrix,
    UniformLocalShear.word_matrix]

@[simp] theorem shearWord_calls (bank : Fin r → ℂ) (s : ShearCode (Fin v) r) :
    wordCalls (shearWord bank s) = 6 := UniformDirectToeplitz.shear_calls _ _ _

@[simp] theorem shearWord_length (bank : Fin r → ℂ) (s : ShearCode (Fin v) r) :
    (shearWord bank s).length = 28 := UniformDirectToeplitz.shear_length _ _ _

theorem shearWord_action (bank : Fin r → ℂ) (s : ShearCode (Fin v) r) (X : Fin v → ℂ) :
    (wordMatrix (shearWord bank s)).mulVec X = (s.eval bank).act X := by
  classical
  rw [shearWord, UniformDirectToeplitz.shear_matrix]
  funext i
  simp only [ShearCode.eval]
  unfold OAI.ExactFourier.Shear.act
  by_cases hi : i = s.dst <;> simp [Matrix.add_mulVec, Matrix.single_mulVec, hi]


theorem listWord_action (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (X : Fin v → ℂ) :
    (wordMatrix (listWord bank W)).mulVec X = runShears (W.map (ShearCode.eval bank)) X := by
  induction W generalizing X with
  | nil => simp [listWord, wordMatrix]
  | cons s W ih =>
    change (wordMatrix (shearWord bank s ++ listWord bank W)).mulVec X = _
    rw [wordMatrix_append, ← Matrix.mulVec_mulVec, ih, shearWord_action]
    rfl

@[simp] theorem listWord_calls (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) :
    wordCalls (listWord bank W) = 6 * W.length := by
  induction W with
  | nil => simp [listWord, wordCalls]
  | cons s W ih =>
    change wordCalls (shearWord bank s ++ listWord bank W) = _
    rw [wordCalls_append, shearWord_calls, ih, List.length_cons]
    omega

@[simp] theorem listWord_length (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) :
    (listWord bank W).length = 28 * W.length := by
  induction W with
  | nil => simp [listWord]
  | cons s W ih =>
    change (shearWord bank s ++ listWord bank W).length = _
    rw [List.length_append, shearWord_length, ih, List.length_cons]
    omega

/-- Indexed occurrences in a color layer occupy disjoint coordinate pairs. -/
def Matching (W : List (ShearCode (Fin v) r)) : Prop :=
  W.Pairwise (fun s t => s.dst≠t.dst ∧ s.dst≠t.src ∧ s.src≠t.dst ∧ s.src≠t.src)

theorem matching_get {W : List (ShearCode (Fin v) r)} (hW : Matching W)
    (i j : Fin W.length) (hne : i ≠ j) :
    (W.get i).dst≠(W.get j).dst ∧ (W.get i).dst≠(W.get j).src ∧
      (W.get i).src≠(W.get j).dst ∧ (W.get i).src≠(W.get j).src := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hW.rel_get_of_lt hij
  · have h := hW.rel_get_of_lt hji
    exact ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩

def pairPosition (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    (Σ _ : Fin W.length, Fin 2) ↪ Fin v where
  toFun x := Embedded.pair (W.get x.1).dst (W.get x.1).src (W.get x.1).different x.2
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    by_cases hij : i = j
    · subst j
      have hbc := (Embedded.pair (W.get i).dst (W.get i).src (W.get i).different).injective h
      cases hbc
      rfl
    · have hp := matching_get hW i j hij
      fin_cases b <;> fin_cases c
      · exact False.elim (hp.1 h)
      · exact False.elim (hp.2.1 h)
      · exact False.elim (hp.2.2.1 h)
      · exact False.elim (hp.2.2.2 h)

theorem pairPosition_at (W : List (ShearCode (Fin v) r)) (hW : Matching W) (i : Fin W.length) :
    Embedded.pair (W.get i).dst (W.get i).src (W.get i).different =
      (Embedded.sigmaIn i).trans (pairPosition W hW) := by
  ext b
  rfl

noncomputable section

theorem embedded_prod {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (L : List (Matrix α α ℂ)) :
    Embedded.matrix f L.prod = (L.map (Embedded.matrix f)).prod := by
  induction L with
  | nil => simp
  | cons A L ih => simp only [List.prod_cons, List.map_cons, Embedded.matrix_mul, ih]

theorem block_product {m : ℕ} (A : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (L : List (Fin m)) (hn : L.Nodup) (hall : ∀ i, i∈L) :
    (L.map (fun i => Embedded.matrix (Embedded.sigmaIn i) (A i))).prod = Matrix.blockDiagonal' A := by
  classical
  let φ := Matrix.blockDiagonal'RingHom (m' := fun _ : Fin m => Fin 2) (α := ℂ)
  simp_rw [Embedded.matrix_sigmaIn A]
  rw [show L.map (fun i => Matrix.blockDiagonal' (Function.update
      (1 : Fin m → Matrix (Fin 2) (Fin 2) ℂ) i (A i))) =
      (L.map (fun i => Function.update (1 : Fin m → Matrix (Fin 2) (Fin 2) ℂ) i (A i))).map φ by
    rw [List.map_map]; rfl]
  rw [← map_list_prod]
  change φ ((L.map (fun i => Function.update (1 : Fin m → Matrix (Fin 2) (Fin 2) ℂ) i (A i))).prod) = φ A
  congr 1
  funext i
  rw [Embedded.list_update_prod A L hn i, ite_eq_left (hall i)]

/-- The literal serial tape equals the parallel family of its disjoint ordered pairs. -/
theorem matchingWord_matrix (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    wordMatrix (listWord bank W) = Embedded.matrix (pairPosition W hW)
      (Matrix.blockDiagonal' (fun i : Fin W.length => upperShear ((W.get i).coefficient.eval bank))) := by
  rw [listWord, TensorWords.wordMatrix_flatten]
  simp only [List.map_map, Function.comp_def, shearWord_matrix]
  have hm : (List.finRange W.length).map W.get = W := by rw [← List.ofFn_eq_map, List.ofFn_get]
  have hs : W.map (fun s => Embedded.matrix (Embedded.pair s.dst s.src s.different)
      (upperShear (s.coefficient.eval bank))) =
      (List.finRange W.length).map (fun i => Embedded.matrix
        (Embedded.pair (W.get i).dst (W.get i).src (W.get i).different)
        (upperShear ((W.get i).coefficient.eval bank))) := by
    conv_lhs => rw [← hm, List.map_map]
    rfl
  rw [hs, ← List.map_reverse]
  simp_rw [pairPosition_at W hW, ← Embedded.matrix_comp]
  rw [show (List.map (fun i => Embedded.matrix (pairPosition W hW)
      (Embedded.matrix (Embedded.sigmaIn i) (upperShear ((W.get i).coefficient.eval bank))))
      (List.finRange W.length).reverse) =
      ((List.finRange W.length).reverse.map (fun i =>
        Embedded.matrix (Embedded.sigmaIn i) (upperShear ((W.get i).coefficient.eval bank)))).map
          (Embedded.matrix (pairPosition W hW)) from by rw [List.map_map]; rfl]
  rw [← embedded_prod]
  congr 1
  exact block_product _ (List.finRange W.length).reverse
    (by simpa using List.nodup_finRange W.length) (fun i => by simp)

theorem matchingWord_depth (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hW : Matching W) :
    Layered (wordMatrix (listWord bank W)) 28 := by
  rw [matchingWord_matrix bank W hW]
  apply Layered.embed
  apply Layered.blocks_fin W.length (fun _ => Fin 2) _ 28
  intro i
  have h := UniformDirectToeplitz.word_layered (UniformLocalShear.word ((W.get i).coefficient.eval bank))
  rw [UniformLocalShear.word_matrix] at h
  simpa [UniformLocalShear.word, TypedKernelWords.shearWord, hadamardWord] using h

end

open UniformDAGLayers

/-- Dense logical ports omit the unused zero-reference hole. -/
def natPorts (e g a : ℕ) : Fin (e+g+a) ↪ ℕ :=
  (flatten e g a).symm.toEmbedding.trans (replayEmbedding e g a)

/-- Integer-only decoder; the fallback branch is never used for actual ports. -/
def port (he : 0<e) (p : ℕ) : Fin (e+g+a) :=
  if hp : p<e then ⟨p,by omega⟩
  else if hp : p<e+1+g+a then ⟨p-1,by omega⟩
  else ⟨0,by omega⟩

theorem port_natPorts (he : 0<e) (i : Fin (e+g+a)) : port (g := g) (a := a) he (natPorts e g a i) = i := by
  obtain ⟨q,rfl⟩ := (flatten e g a).surjective i
  simp only [natPorts, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.symm_apply_apply]
  rcases q with (q|q)|q
  · apply Fin.ext
    change (port (g := g) (a := a) he q.val).val = q.val
    rw [port, dite_eq_left q.isLt]
  · apply Fin.ext
    change (port (g := g) (a := a) he (e+1+q.val)).val = e+q.val
    have hq := q.isLt
    rw [port, dite_eq_right (by omega : ¬e+1+q.val<e),
      dite_eq_left (by omega : e+1+q.val<e+1+g+a)]
    dsimp
    omega
  · apply Fin.ext
    change (port (g := g) (a := a) he (e+1+g+q.val)).val = e+g+q.val
    have hq := q.isLt
    rw [port, dite_eq_right (by omega : ¬e+1+g+q.val<e),
      dite_eq_left (by omega : e+1+g+q.val<e+1+g+a)]
    dsimp
    omega

def Stored (e g a : ℕ) (s : ShearCode ℕ r) : Prop :=
  s.dst∈Set.range (natPorts e g a) ∧ s.src∈Set.range (natPorts e g a)

theorem natPorts_port (he : 0<e) (p : ℕ) (hp : p∈Set.range (natPorts e g a)) :
    natPorts e g a (port (g := g) (a := a) he p) = p := by
  obtain ⟨i,rfl⟩ := hp
  rw [port_natPorts]

theorem port_ne (he : 0<e) (p q : ℕ) (hp : p∈Set.range (natPorts e g a))
    (hq : q∈Set.range (natPorts e g a)) (hne : p≠q) : port (g := g) (a := a) he p ≠ port (g := g) (a := a) he q := by
  intro h
  have hn := congrArg (natPorts e g a) h
  rw [natPorts_port (g := g) (a := a) he p hp, natPorts_port (g := g) (a := a) he q hq] at hn
  exact hne hn

def packCode (he : 0<e) (s : ShearCode ℕ r) (hs : Stored e g a s) :
    ShearCode (Fin (e+g+a)) r :=
  ⟨port (g := g) (a := a) he s.dst,port (g := g) (a := a) he s.src,port_ne he s.dst s.src hs.1 hs.2 s.different,s.coefficient⟩

def packList (he : 0<e) : (W : List (ShearCode ℕ r)) →
    (∀ s∈W, Stored e g a s) → List (ShearCode (Fin (e+g+a)) r)
  | [], _ => []
  | s::W, hs => packCode he s (hs s (by simp)) ::
      packList he W (fun t ht => hs t (by simp [ht]))

@[simp] theorem packList_length (he : 0<e) (W : List (ShearCode ℕ r))
    (hs : ∀ s∈W, Stored e g a s) : (packList he W hs).length = W.length := by
  induction W with
  | nil => rfl
  | cons s W ih => simp only [packList,List.length_cons,ih]

theorem mem_packList (he : 0<e) (W : List (ShearCode ℕ r)) (hs : ∀ s∈W, Stored e g a s)
    (t : ShearCode (Fin (e+g+a)) r) (ht : t∈packList he W hs) :
    ∃ s, ∃ h : s∈W, t=packCode he s (hs s h) := by
  induction W with
  | nil => simp [packList] at ht
  | cons s W ih =>
    simp only [packList,List.mem_cons] at ht
    rcases ht with rfl|ht
    · exact ⟨s,by simp,rfl⟩
    · obtain ⟨u,hu,heq⟩ := ih _ ht
      subst t
      exact ⟨u,List.mem_cons_of_mem s hu,rfl⟩

theorem packList_append (he : 0<e) (W V : List (ShearCode ℕ r))
    (hs : ∀ s∈W++V, Stored e g a s) :
    packList he (W++V) hs = packList he W (fun s h => hs s (List.mem_append_left V h)) ++
      packList he V (fun s h => hs s (List.mem_append_right W h)) := by
  induction W with
  | nil => rfl
  | cons s W ih => simp only [List.cons_append,packList,ih]

theorem packList_matching (he : 0<e) (W : List (ShearCode ℕ r))
    (hs : ∀ s∈W, Stored e g a s) (hm : UniformDAGLayers.Matching W) : Matching (packList he W hs) := by
  induction W with
  | nil => simp [packList,Matching]
  | cons s W ih =>
    have hp := List.pairwise_cons.mp hm
    apply List.pairwise_cons.mpr
    constructor
    · intro t ht
      obtain ⟨u,hu,rfl⟩ := mem_packList he W _ t ht
      have hr := hp.1 u hu
      exact ⟨port_ne he _ _ (hs s (by simp)).1 (hs u (by simp [hu])).1 hr.1,
        port_ne he _ _ (hs s (by simp)).1 (hs u (by simp [hu])).2 hr.2.1,
        port_ne he _ _ (hs s (by simp)).2 (hs u (by simp [hu])).1 hr.2.2.1,
        port_ne he _ _ (hs s (by simp)).2 (hs u (by simp [hu])).2 hr.2.2.2⟩
    · exact ih _ hp.2

noncomputable section

theorem packCode_act (he : 0<e) (bank : Fin r → ℂ) (s : ShearCode ℕ r)
    (hs : Stored e g a s) (X : ℕ → ℂ) :
    ((packCode he s hs).eval bank).act (X ∘ natPorts e g a) =
      (s.eval bank).act X ∘ natPorts e g a := by
  classical
  dsimp only [ShearCode.eval,packCode]
  unfold OAI.ExactFourier.Shear.act
  dsimp only [Function.comp_def]
  funext i
  have hiff : i = port (g := g) (a := a) he s.dst ↔ natPorts e g a i = s.dst := by
    constructor
    · intro hi; rw [hi]; exact natPorts_port (g := g) (a := a) he _ hs.1
    · intro hi
      have hp := congrArg (port (g := g) (a := a) he) hi
      rwa [port_natPorts] at hp
  rw [hiff, natPorts_port (g := g) (a := a) he _ hs.2]

theorem packList_action (he : 0<e) (bank : Fin r → ℂ) (W : List (ShearCode ℕ r))
    (hs : ∀ s∈W, Stored e g a s) (X : ℕ → ℂ) :
    runShears ((packList he W hs).map (ShearCode.eval bank)) (X ∘ natPorts e g a) =
      runShears (W.map (ShearCode.eval bank)) X ∘ natPorts e g a := by
  induction W generalizing X with
  | nil => rfl
  | cons s W ih =>
    simp only [packList,List.map_cons,runShears_cons]
    rw [packCode_act,ih]

end

/-- Every actual layered endpoint comes from the zero-hole-free replay embedding. -/
theorem replayLayers_stored {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    ∀ s∈(replayLayers D H delta).flatten, Stored e D.size a s := by
  intro s hs
  have hn := (replayLayers_perm D hD hd huse).mem_iff.mp hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hn
  constructor
  · exact ⟨flatten e D.size a t.dst,by simp [natPorts,relabelCode]⟩
  · exact ⟨flatten e D.size a t.src,by simp [natPorts,relabelCode]⟩


def packLayers (he : 0<e) : (L : List (List (ShearCode ℕ r))) →
    (∀ s∈L.flatten, Stored e g a s) → List (List (ShearCode (Fin (e+g+a)) r))
  | [], _ => []
  | W::L, hs => packList he W (fun s h => hs s (List.mem_flatten.mpr ⟨W,by simp,h⟩)) ::
      packLayers he L (fun s h => hs s (by simp only [List.flatten_cons,List.mem_append];exact Or.inr h))

@[simp] theorem packLayers_length (he : 0<e) (L : List (List (ShearCode ℕ r)))
    (hs : ∀ s∈L.flatten, Stored e g a s) : (packLayers he L hs).length = L.length := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [packLayers,List.length_cons,ih]

theorem packLayers_flatten (he : 0<e) (L : List (List (ShearCode ℕ r)))
    (hs : ∀ s∈L.flatten, Stored e g a s) :
    (packLayers he L hs).flatten = packList he L.flatten hs := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [packLayers,List.flatten_cons,ih,packList_append]

theorem packLayers_matching (he : 0<e) (L : List (List (ShearCode ℕ r)))
    (hs : ∀ s∈L.flatten, Stored e g a s) (hm : ∀ W∈L, UniformDAGLayers.Matching W) :
    ∀ W∈packLayers he L hs, Matching W := by
  induction L with
  | nil => simp [packLayers]
  | cons W L ih =>
    intro V hV
    simp only [packLayers,List.mem_cons] at hV
    rcases hV with rfl|hV
    · exact packList_matching he W _ (hm W (by simp))
    · exact ih _ (fun U hU => hm U (by simp [hU])) V hV

def relabelLayers {w : ℕ} (f : Fin w ↪ Fin v) (L : List (List (ShearCode (Fin w) r))) :
    List (List (ShearCode (Fin v) r)) := L.map (fun W => W.map (relabelCode f))

theorem relabelLayers_flatten {w : ℕ} (f : Fin w ↪ Fin v) (L : List (List (ShearCode (Fin w) r))) :
    (relabelLayers f L).flatten = L.flatten.map (relabelCode f) := by
  simp [relabelLayers,List.map_flatten]

@[simp] theorem relabelLayers_length {w : ℕ} (f : Fin w ↪ Fin v) (L : List (List (ShearCode (Fin w) r))) :
    (relabelLayers f L).length = L.length := by simp [relabelLayers]

theorem matching_relabel {w : ℕ} (f : Fin w ↪ Fin v) (W : List (ShearCode (Fin w) r))
    (hm : Matching W) : Matching (W.map (relabelCode f)) := by
  apply hm.map
  intro s t h
  exact ⟨fun e => h.1 (f.injective e),fun e => h.2.1 (f.injective e),
    fun e => h.2.2.1 (f.injective e),fun e => h.2.2.2 (f.injective e)⟩

theorem relabelLayers_matching {w : ℕ} (f : Fin w ↪ Fin v) (L : List (List (ShearCode (Fin w) r)))
    (hm : ∀ W∈L, Matching W) : ∀ W∈relabelLayers f L, Matching W := by
  intro V hV
  obtain ⟨W,hW,rfl⟩ := List.mem_map.mp hV
  exact matching_relabel f W (hm W hW)

noncomputable section

def layersWord (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r))) : List (WordStep C v) :=
  (L.map (listWord bank)).flatten

theorem listWord_append (bank : Fin r → ℂ) (W V : List (ShearCode (Fin v) r)) :
    listWord bank (W++V) = listWord bank W ++ listWord bank V := by simp [listWord]

theorem layersWord_eq (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r))) :
    layersWord bank L = listWord bank L.flatten := by
  induction L with
  | nil => rfl
  | cons W L ih => simp only [layersWord,List.map_cons,List.flatten_cons,listWord_append,← ih]

@[simp] theorem layersWord_calls (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r))) :
    wordCalls (layersWord bank L) = 6 * L.flatten.length := by rw [layersWord_eq,listWord_calls]

theorem layersWord_action (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r))) (X : Fin v → ℂ) :
    (wordMatrix (layersWord bank L)).mulVec X = runShears (L.flatten.map (ShearCode.eval bank)) X := by
  rw [layersWord_eq,listWord_action]

/-- Each actual matching is compiled in 28 parallel primitive/monomial rounds. -/
theorem layersWord_depth (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hm : ∀ W∈L, Matching W) : Layered (wordMatrix (layersWord bank L)) (28*L.length) := by
  induction L with
  | nil => simpa [layersWord,wordMatrix] using
      (Layered.identity : Layered (1 : Matrix (Fin v) (Fin v) ℂ) 0)
  | cons W L ih =>
    change Layered (wordMatrix (listWord bank W ++ layersWord bank L)) _
    rw [wordMatrix_append]
    have h := (ih (fun U hU => hm U (by simp [hU]))).mul (matchingWord_depth bank W (hm W (by simp)))
    simpa [List.length_cons,Nat.mul_add] using h

end

/-- Physical colored topology is a computable relabeling of the actual replay. -/
def chunkLayers {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) : List (List (ShearCode (Fin v) r)) :=
  relabelLayers P.embedding (packLayers he (replayLayers D H delta) (replayLayers_stored D hD hd huse))

@[simp] theorem chunkLayers_length {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    (chunkLayers D he P hD hd huse).length = (replayLayers D H delta).length := by simp [chunkLayers]

theorem chunkLayers_matching {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    ∀ W∈chunkLayers D he P hD hd huse, Matching W := by
  apply relabelLayers_matching
  apply packLayers_matching
  exact replayLayers_matching D hd huse

noncomputable section

def chunkWord {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) : List (WordStep C v) :=
  layersWord bank (chunkLayers D he P hD hd huse)

theorem chunkWord_calls {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    wordCalls (chunkWord D bank he P hD hd huse) = 6 * (replayCode D.program D.outputs).length := by
  rw [chunkWord,layersWord_calls,chunkLayers,relabelLayers_flatten,List.length_map,
    packLayers_flatten,packList_length,replayLayers_instruction_count D hD hd huse]

theorem chunkWord_call_bound {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    wordCalls (chunkWord D bank he P hD hd huse) ≤ 48*D.size+12*a := by
  rw [chunkWord_calls]
  have h := replayCode_length D.program D.outputs
  omega

theorem chunkWord_depth {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ) (he : 0<e)
    (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    Layered (wordMatrix (chunkWord D bank he P hD hd huse)) (28*(4*(H+1)+2)*(2*delta-1)) := by
  have h := layersWord_depth bank _ (chunkLayers_matching D he P hD hd huse)
  rw [chunkLayers_length,replayLayers_length] at h
  simpa [chunkWord,Nat.mul_assoc] using h


theorem placedList_action (he : 0<e) (P : Placement e g a v) (bank : Fin r → ℂ)
    (W : List (ShearCode ℕ r)) (hs : ∀ s∈W, Stored e g a s) (X : Fin v → ℂ) :
    runShears (((packList he W hs).map (relabelCode P.embedding)).map (ShearCode.eval bank)) X ∘
        P.coordinates =
      runShears (W.map (ShearCode.eval bank))
        (fun p => X (P.embedding (port (g:=g) (a:=a) he p))) ∘ replayEmbedding e g a := by
  let Y : ℕ → ℂ := fun p => X (P.embedding (port (g:=g) (a:=a) he p))
  have hin : Y ∘ natPorts e g a = X ∘ P.embedding := by
    funext i
    simp [Y,port_natPorts]
  have hp := packList_action he bank W hs Y
  rw [hin] at hp
  have hr := relabel_run P.embedding bank (packList he W hs) X
  have hc := congrArg (fun f : Fin (e+g+a) → ℂ => f ∘ flatten e g a) (hr.trans hp)
  simpa only [Y,Function.comp_def,Placement.embedding,Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply,Equiv.symm_apply_apply,natPorts] using hc

theorem relabelList_outside {w : ℕ} (f : Fin w ↪ Fin v) (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin w) r)) (X : Fin v → ℂ) (q : Fin v) (hq : ∀ i, q≠f i) :
    runShears ((W.map (relabelCode f)).map (ShearCode.eval bank)) X q = X q := by
  induction W generalizing X with
  | nil => rfl
  | cons s W ih =>
    simp only [List.map_cons,runShears_cons]
    rw [ih]
    exact Shear.act_other _ _ (hq s.dst)

/-- Actual dirty borrowed storage is restored; targets receive the clean DAG output. -/
theorem chunkWord_spec {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
        (fun j => X (P.target j) + (D.program.eval bank).eval (X ∘ P.source) (D.outputs j)) := by
  rw [chunkWord,layersWord_action,chunkLayers,relabelLayers_flatten,packLayers_flatten]
  rw [placedList_action,replayLayers_action D bank hD hd huse,natReplayCode_spec]
  have hn (q : (Fin e ⊕ Fin D.size) ⊕ Fin a) :
      X (P.embedding (port (g:=D.size) (a:=a) he (replayEmbedding e D.size a q))) = X (P.coordinates q) := by
    have hr : replayEmbedding e D.size a q = natPorts e D.size a (flatten e D.size a q) := by
      simp [natPorts]
    rw [hr,port_natPorts]
    simp [Placement.embedding]
  have hi : (fun p => X (P.embedding (port (g:=D.size) (a:=a) he p))) ∘
      (fun i : Fin e => i.val) = X ∘ P.source := by
    funext i
    exact hn (Sum.inl (Sum.inl i))
  have hg : (fun p => X (P.embedding (port (g:=D.size) (a:=a) he p))) ∘
      (fun j : Fin D.size => e+1+j.val) = X ∘ P.gates := by
    funext j
    exact hn (Sum.inl (Sum.inr j))
  have ht : (fun p => X (P.embedding (port (g:=D.size) (a:=a) he p))) ∘
      (fun j : Fin a => e+1+D.size+j.val) = X ∘ P.target := by
    funext j
    exact hn (Sum.inr j)
  simp only [Function.comp_def] at hi hg ht
  rw [hi,hg]
  exact congrArg (fun Y : Fin a → ℂ => Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
    (fun j => Y j + (D.program.eval bank).eval (X ∘ P.source) (D.outputs j))) ht


theorem chunkWord_source {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ) (i : Fin e) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X (P.source i) = X (P.source i) :=
  congrFun (chunkWord_spec D bank he P hD hd huse X) (Sum.inl (Sum.inl i))

theorem chunkWord_gates {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ) (i : Fin D.size) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X (P.gates i) = X (P.gates i) :=
  congrFun (chunkWord_spec D bank he P hD hd huse X) (Sum.inl (Sum.inr i))

theorem chunkWord_target {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ) (j : Fin a) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X (P.target j) =
      X (P.target j) + (D.program.eval bank).eval (X ∘ P.source) (D.outputs j) :=
  congrFun (chunkWord_spec D bank he P hD hd huse X) (Sum.inr j)

theorem chunkWord_outside {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ)
    (q : Fin v) (hq : q∉Set.range P.coordinates) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X q = X q := by
  rw [chunkWord,layersWord_action,chunkLayers,relabelLayers_flatten,packLayers_flatten]
  apply relabelList_outside
  intro i hi
  exact hq ⟨(flatten e D.size a).symm i,hi.symm⟩

/-- Every coordinate outside the target bank is unchanged, including dirty borrowed storage. -/
theorem chunkWord_other {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a)
    (bank : Fin r → ℂ) (he : 0<e) (P : Placement e D.size a v)
    (hD : UniformToeplitzCrossDAG.DepthBound D H) (hd : 2≤delta)
    (huse : ∀ p, UniformToeplitzCrossDAG.physicalUseCount D p≤delta) (X : Fin v → ℂ)
    (q : Fin v) (hq : q∉Set.range P.target) :
    (wordMatrix (chunkWord D bank he P hD hd huse)).mulVec X q = X q := by
  by_cases hc : q∈Set.range P.coordinates
  · obtain ⟨i,rfl⟩ := hc
    rcases i with (i|i)|i
    · exact chunkWord_source D bank he P hD hd huse X i
    · exact chunkWord_gates D bank he P hD hd huse X i
    · exact False.elim (hq ⟨i,rfl⟩)
  · exact chunkWord_outside D bank he P hD hd huse X q hc

end

open UniformWorkspacePlanner

def positions {w : ℕ} (f : Fin w ↪ Fin v) : Finset (Fin v) := Finset.univ.map f

@[simp] theorem positions_card {w : ℕ} (f : Fin w ↪ Fin v) : (positions f).card = w := by
  simp [positions]

theorem positions_disjoint (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (hst : ∀ i j, source i ≠ target j) : Disjoint (positions source) (positions target) := by
  apply Finset.disjoint_left.mpr
  intro q hs ht
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hs
  obtain ⟨j,_,hj⟩ := Finset.mem_map.mp ht
  exact hst i j (hi.trans hj.symm)

/-- Measured fit allocates every dirty gate by the actual complement scan. -/
def placementOfFit (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v)
    (hst : ∀ i j, source i ≠ target j) (hfit : g+a+e≤v) : Placement e g a v :=
  let hg : g≤(available (positions source) (positions target)).card := by
    rw [available_card _ _ (positions_disjoint source target hst) (positions_card source) (positions_card target)]
    omega
  let gates := borrowedEmbedding (positions source) (positions target) g hg
  { source := source
    gates := gates
    target := target
    source_gates := by
      intro i j h
      exact (borrowedEmbedding_avoids _ _ g hg j).1 (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,h⟩)
    source_target := hst
    gates_target := by
      intro i j h
      exact (borrowedEmbedding_avoids _ _ g hg i).2 (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,h.symm⟩) }

/-- Selection is a pure integer certificate for the physical embedding. -/
def selectedPlacement (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i ≠ target j) :
    Placement e (printedCross a e).size a v :=
  placementOfFit source target hst (by rw [printedCross_size];exact selected_fit hv ha he)

noncomputable section
open UniformToeplitzCrossDAG

def crossWord (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (bank : Fin (bankSize k) → ℂ) (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    List (WordStep C v) :=
  chunkWord (crossDAG k a e (by omega) (by omega)) bank he P (crossDAG_depth _ _ _ _ _)
    (by omega) (crossDAG_physicalFanout _ _ _ _ _)

theorem crossWord_calls (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (bank : Fin (bankSize k) → ℂ) (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    wordCalls (crossWord k a e ha he hsize bank P) = 6*(crossReplay k a e (by omega) (by omega)).length := by
  rw [crossWord,chunkWord_calls]
  rfl

theorem crossWord_call_bound (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (bank : Fin (bankSize k) → ℂ) (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    wordCalls (crossWord k a e ha he hsize bank P) ≤ 288*(3*k*2^k+2*2^k)+108*a := by
  rw [crossWord_calls]
  have h := crossReplay_length k a e (by omega) (by omega)
  omega

theorem crossWord_depth (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (bank : Fin (bankSize k) → ℂ) (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    Layered (wordMatrix (crossWord k a e ha he hsize bank P)) (1848*(8*k+7)) := by
  apply (chunkWord_depth _ bank he P (crossDAG_depth _ _ _ _ _)
    (by omega) (crossDAG_physicalFanout _ _ _ _ _)).weaken
  omega

theorem crossWord_spec (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k) (M : ℕ → ℕ → ℂ) (v₀ w₀ : ℕ → ℂ)
    (hrec : ∀ i j, i+1<a → j+1<e → M (i+1) (j+1)=M i j+v₀ (i+1)*w₀ (j+1))
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) (X : Fin v → ℂ) :
    (wordMatrix (crossWord k a e ha he hsize (sharedBank k (rankKernels k a e M v₀ w₀)) P)).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
        (fun j => X (P.target j) + Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (X ∘ P.source) j) := by
  rw [crossWord,chunkWord_spec]
  have h := crossDAG_eval k a e ha he hsize M v₀ w₀ hrec (X ∘ P.source)
  exact congrArg (fun o : Fin a → ℂ => Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
    (fun j => X (P.target j)+o j)) h

theorem crossWord_other (k a e : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (bank : Fin (bankSize k) → ℂ) (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v)
    (X : Fin v → ℂ) (q : Fin v) (hq : q∉Set.range P.target) :
    (wordMatrix (crossWord k a e ha he hsize bank P)).mulVec X q=X q :=
  chunkWord_other _ bank he P (crossDAG_depth _ _ _ _ _)
    (by omega) (crossDAG_physicalFanout _ _ _ _ _) X q hq

/-- Closed Toeplitz cross specialization, using the paper's actual displacement identity. -/
theorem toeplitzChunk_spec (k s a e i₀ j₀ : ℕ) (ha : 0<a) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k) (h f : ℕ → ℂ) (hi : s ≤ i₀) (hj : j₀ + e ≤ s)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) (X : Fin v → ℂ) :
    let M := fun i j => OAI.ExactFourier.ToeplitzLayers.cross s h f (i₀+i) (j₀+j)
    let v₀ := fun i => -h (i₀+i-s)
    let w₀ := fun j => f (s-(j₀+j))
    (wordMatrix (crossWord k a e ha he hsize (sharedBank k (rankKernels k a e M v₀ w₀)) P)).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
        (fun j => X (P.target j) + Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (X ∘ P.source) j) := by
  dsimp only
  exact crossWord_spec k a e ha he hsize _ _ _
    (OAI.ExactFourier.ToeplitzLayers.cross_interior s a e i₀ j₀ h f hi hj) P X

/-- The selected integer chunk sizes and complement scan instantiate the literal word. -/
def selectedWord (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (bank : Fin (bankSize (exponent a e)) → ℂ) : List (WordStep C v) :=
  chunkWord (printedCross a e) bank (chunk_pos hv he) (selectedPlacement hv ha he source target hst)
    (printedCross_depth a e) (by decide) (printedCross_fanout a e)

theorem selectedWord_call_bound (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (bank : Fin (bankSize (exponent a e)) → ℂ) :
    wordCalls (selectedWord hv ha he source target hst bank)≤48*v := by
  have h := chunkWord_call_bound (printedCross a e) bank (chunk_pos hv he)
    (selectedPlacement hv ha he source target hst) (printedCross_depth a e)
    (by decide) (printedCross_fanout a e)
  rw [printedCross_size] at h
  have hf := selected_fit hv ha he
  dsimp only [selectedWord]
  omega

theorem selectedWord_depth (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (bank : Fin (bankSize (exponent a e)) → ℂ) :
    Layered (wordMatrix (selectedWord hv ha he source target hst bank))
      (1848*(8*Nat.clog 2 v+23)) := by
  have h := chunkWord_depth (printedCross a e) bank (chunk_pos hv he)
    (selectedPlacement hv ha he source target hst) (printedCross_depth a e)
    (by decide) (printedCross_fanout a e)
  apply h.weaken
  have hk := exponent_bound ((chunk_le ha).trans (selected_le v)) ((chunk_le he).trans (selected_le v))
  omega

theorem selectedWord_spec (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (M : ℕ → ℕ → ℂ) (v₀ w₀ : ℕ → ℂ)
    (hrec : ∀ i j, i+1<a → j+1<e → M (i+1) (j+1)=M i j+v₀ (i+1)*w₀ (j+1)) (X : Fin v → ℂ) :
    let P := selectedPlacement hv ha he source target hst
    (wordMatrix (selectedWord hv ha he source target hst
      (sharedBank (exponent a e) (rankKernels (exponent a e) a e M v₀ w₀)))).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ source) (X ∘ P.gates))
        (fun j => X (target j)+Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (X ∘ source) j) := by
  exact crossWord_spec (exponent a e) a e (chunk_pos hv ha) (chunk_pos hv he)
    (by rw [UniformRadixTwoDAG.width_eq];exact no_alias a e) M v₀ w₀ hrec
    (selectedPlacement hv ha he source target hst) X

theorem selectedWord_other (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (bank : Fin (bankSize (exponent a e)) → ℂ) (X : Fin v → ℂ)
    (q : Fin v) (hq : q∉Set.range target) :
    (wordMatrix (selectedWord hv ha he source target hst bank)).mulVec X q = X q :=
  chunkWord_other (printedCross a e) bank (chunk_pos hv he)
    (selectedPlacement hv ha he source target hst) (printedCross_depth a e)
    (by decide) (printedCross_fanout a e) X q hq

/-- Actual Toeplitz displacement supplies the recurrence; no action hypothesis is used. -/
theorem selectedToeplitzWord_spec (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j)
    (s i₀ j₀ : ℕ) (h f : ℕ → ℂ) (hi : s ≤ i₀) (hj : j₀+e ≤ s) (X : Fin v → ℂ) :
    let M := fun i j => OAI.ExactFourier.ToeplitzLayers.cross s h f (i₀+i) (j₀+j)
    let v₀ := fun i => -h (i₀+i-s)
    let w₀ := fun j => f (s-(j₀+j))
    let P := selectedPlacement hv ha he source target hst
    (wordMatrix (selectedWord hv ha he source target hst
      (sharedBank (exponent a e) (rankKernels (exponent a e) a e M v₀ w₀)))).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ source) (X ∘ P.gates))
        (fun j => X (target j)+Matrix.mulVec (fun i : Fin a => fun j : Fin e => M i.val j.val) (X ∘ source) j) := by
  exact selectedWord_spec hv ha he source target hst _ _ _
    (OAI.ExactFourier.ToeplitzLayers.cross_interior s a e i₀ j₀ h f hi hj) X

/-- This word consumes the actual shared coefficient preparation, retaining its roots. -/
def preparedCrossWord {o : ℕ} (k : ℕ) (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) : List (WordStep C v) :=
  crossWord k a e c.positive he hsize
    ((UniformRankKernelPreparation.spectrumBank k d c omega).run roots
      (UniformRankKernelPreparation.spectrumBank_admissible k d c omega roots hd)) P

theorem preparedCrossWord_spec {o : ℕ} (k : ℕ) (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (h f : ℕ → ℂ)
    (hh : ∀ i, d.program.eval roots (c.h i)=h i.val)
    (hf : ∀ i, d.program.eval roots (c.g i)=f i.val)
    (homega : d.program.eval roots omega=zeta (UniformRadixTwoDAG.width k))
    (he : 0<e) (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (hi : c.s ≤ c.i₀) (hj : c.j₀+e ≤ c.s)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) (X : Fin v → ℂ) :
    (wordMatrix (preparedCrossWord k d c omega roots hd he hsize P)).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
        (fun j => X (P.target j)+Matrix.mulVec
          (fun i : Fin a => fun j : Fin e => c.matrix h f i.val j.val) (X ∘ P.source) j) := by
  rw [preparedCrossWord,crossWord,chunkWord_spec]
  have h := UniformRankKernelPreparation.spectrumBank_cross_action
    k d c omega roots hd h f hh hf homega he hsize hi hj (X ∘ P.source)
  exact congrArg (fun o : Fin a → ℂ => Sum.elim (Sum.elim (X ∘ P.source) (X ∘ P.gates))
    (fun j => X (P.target j)+o j)) h

theorem preparedCrossWord_call_bound {o : ℕ} (k : ℕ) (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    wordCalls (preparedCrossWord k d c omega roots hd he hsize P)≤288*(3*k*2^k+2*2^k)+108*a :=
  crossWord_call_bound k a e c.positive he hsize _ P

theorem preparedCrossWord_depth {o : ℕ} (k : ℕ) (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v) :
    Layered (wordMatrix (preparedCrossWord k d c omega roots hd he hsize P)) (1848*(8*k+7)) :=
  crossWord_depth k a e c.positive he hsize _ P

theorem preparedCrossWord_other {o : ℕ} (k : ℕ) (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (he : 0<e)
    (hsize : 2*(a+e)≤UniformRadixTwoDAG.width k)
    (P : Placement e (crossDAG k a e (by omega) (by omega)).size a v)
    (X : Fin v → ℂ) (q : Fin v) (hq : q∉Set.range P.target) :
    (wordMatrix (preparedCrossWord k d c omega roots hd he hsize P)).mulVec X q=X q :=
  crossWord_other k a e c.positive he hsize _ P X q hq

/-- The planner-selected physical chunk consumes the literal shared scalar DAG output. -/
theorem preparedSelectedWord_spec {o : ℕ} (d : UniformScalarPreparation.DAG r o)
    (c : UniformRankKernelPreparation.Sources d.length a e) (omega : Fin d.length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots) (h f : ℕ → ℂ)
    (hh : ∀ i, d.program.eval roots (c.h i)=h i.val)
    (hf : ∀ i, d.program.eval roots (c.g i)=f i.val)
    (homega : d.program.eval roots omega=zeta (UniformRadixTwoDAG.width (exponent a e)))
    (hi : c.s ≤ c.i₀) (hj : c.j₀+e ≤ c.s) (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j, source i≠target j) (X : Fin v → ℂ) :
    let P := selectedPlacement hv ha he source target hst
    (wordMatrix (selectedWord hv ha he source target hst
      ((UniformRankKernelPreparation.spectrumBank (exponent a e) d c omega).run roots
        (UniformRankKernelPreparation.spectrumBank_admissible (exponent a e) d c omega roots hd)))).mulVec X ∘ P.coordinates =
      Sum.elim (Sum.elim (X ∘ source) (X ∘ P.gates))
        (fun j => X (target j)+Matrix.mulVec
          (fun i : Fin a => fun j : Fin e => c.matrix h f i.val j.val) (X ∘ source) j) :=
  preparedCrossWord_spec (exponent a e) d c omega roots hd h f hh hf homega (chunk_pos hv he)
    (by rw [UniformRadixTwoDAG.width_eq];exact no_alias a e) hi hj
    (selectedPlacement hv ha he source target hst) X

end
end ExactFourierCircuits.UniformToeplitzChunkWord
