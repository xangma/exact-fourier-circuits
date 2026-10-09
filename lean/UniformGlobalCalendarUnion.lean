import UniformGlobalCalendarGeometry

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarUnion
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformGlobalCalendarGeometry UniformLocalCacheTiming

namespace Calls
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {β : σ → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

def family (P : ∀ i, UniformLayerSnapshot.Calls (β i)) : UniformLayerSnapshot.Calls (Σ i, β i) where
  index := Σ i, (P i).index
  finite := inferInstance
  dec := inferInstance
  position := (flattenEquiv (fun i => (P i).index)).toEmbedding.trans
    (Embedded.sigmaEmbed (fun i => (P i).position))

@[simp] theorem family_matrix (P : ∀ i, UniformLayerSnapshot.Calls (β i)) :
    (family P).matrix = Matrix.blockDiagonal' (fun i => (P i).matrix) := by
  change Embedded.matrix
    ((flattenEquiv (fun i => (P i).index)).toEmbedding.trans
      (Embedded.sigmaEmbed (fun i => (P i).position)))
    (Matrix.blockDiagonal' (fun _ : (Σ i, (P i).index) => C)) = _
  rw [← Embedded.matrix_comp,Embedded.matrix_equiv,flatten_constant_blocks,
    Embedded.matrix_sigmaEmbed]
  rfl
end Calls

namespace Snapshot
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {β : σ → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

def family (S : ∀ i, UniformLayerSnapshot.Snapshot (β i)) : UniformLayerSnapshot.Snapshot (Σ i, β i) where
  calls := Calls.family (fun i => (S i).calls)
  diagonal x := (S x.1).diagonal x.2
  nonzero x := (S x.1).nonzero x.2
  active_one := by
    change ∀ x : (Σ _ : (Σ i, (S i).calls.index), Fin 2),
      (S x.1.1).diagonal ((S x.1.1).calls.position ⟨x.1.2,x.2⟩) = 1
    intro x
    exact (S x.1.1).active_one _

@[simp] theorem family_matrix (S : ∀ i, UniformLayerSnapshot.Snapshot (β i)) :
    (family S).matrix = Matrix.blockDiagonal' (fun i => (S i).matrix) := by
  have hd : Matrix.diagonal (fun x : (Σ i, β i) => (S x.1).diagonal x.2) =
      Matrix.blockDiagonal' (fun i => Matrix.diagonal (S i).diagonal) := by
    ext ⟨i,x⟩ ⟨j,y⟩
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply,Matrix.blockDiagonal'_apply]
    · simp [Matrix.blockDiagonal'_apply,hij]
  change Matrix.diagonal (fun x : (Σ i, β i) => (S x.1).diagonal x.2) *
    (Calls.family (fun i => (S i).calls)).matrix = _
  rw [hd,Calls.family_matrix,← Matrix.blockDiagonal'_mul]
  rfl
end Snapshot

/-- Disjoint genuine event bands give one injection for all roles and ordered calls. -/
def intervalEmbedding {σ : Type} (r : ℕ) (low width : σ → ℕ)
    (bounds : ∀ i, low i + width i ≤ r)
    (separated : ∀ i j, i ≠ j → low i + width i ≤ low j ∨ low j + width j ≤ low i) :
    (Σ i, Fin (width i)) ↪ Fin r where
  toFun x := ⟨low x.1 + x.2.val,by have := bounds x.1; have := x.2.isLt; omega⟩
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have eq : low i + x.val = low j + y.val := congrArg Fin.val h
    by_cases same : i = j
    · subst j
      have eqxy : x = y := Fin.ext (by omega)
      subst y
      rfl
    · obtain before | after := separated i j same
      · have := x.isLt; have := y.isLt; omega
      · have := x.isLt; have := y.isLt; omega

def Event.width : UniformLocalCacheTiming.Event → ℕ
  | .direct v _ => v
  | .rectangle q => q.width

lemma event_high (e : UniformLocalCacheTiming.Event) :
    UniformGlobalCalendarGeometry.Event.high e =
      UniformGlobalCalendarGeometry.Event.low e + Event.width e := by cases e <;> rfl

abbrev ActiveIndex (L : List TimedEvent) (t : ℕ) := {i : Fin L.length // Active (L.get i) t}

instance (L : List TimedEvent) (t : ℕ) : Fintype (ActiveIndex L t) := by
  classical
  infer_instance

instance (L : List TimedEvent) (t : ℕ) : DecidableEq (ActiveIndex L t) := Classical.decEq _

lemma active_separated (L : List TimedEvent) (t : ℕ)
    (pairwise : L.Pairwise (SeparatedAt t)) (i j : ActiveIndex L t) (ne : i ≠ j) :
    DisjointBands (L.get i.val) (L.get j.val) := by
  have ij : i.val ≠ j.val := by intro eq; exact ne (Subtype.ext eq)
  rcases lt_or_gt_of_ne ij with before | after
  · exact pairwise.rel_get_of_lt before i.property j.property
  · rcases pairwise.rel_get_of_lt after j.property i.property with before | after
    · exact Or.inr before
    · exact Or.inl after

/-- Actual timed-tree geometry establishes the union injection; disjointness is
proved from the recursive schedule rather than assumed for the call endpoints. -/
def treeEmbedding {v : ℕ} (P : UniformBalancedToeplitz.Plan v) (o start t r : ℕ)
    (extent : o + v ≤ r) :
    (Σ i : ActiveIndex (treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)) t,
      Fin (Event.width ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event)) ↪ Fin r :=
  intervalEmbedding (σ := ActiveIndex (treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)) t) r
    (fun i => UniformGlobalCalendarGeometry.Event.low
      ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event)
    (fun i => Event.width ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event)
    (by
      intro i
      rw [← event_high]
      have b := tree_band P o start _ (List.get_mem _ i.val)
      omega)
    (by
      intro i j ne
      have sep := active_separated _ t (tree_separated P o start t) i j ne
      simpa only [DisjointBands,event_high] using sep)

/-- Every simultaneously active local snapshot contributes its diagonal and all
ordered calls, including mixed phases from distinct parallel subtrees. -/
def treeSnapshot {v : ℕ} (P : UniformBalancedToeplitz.Plan v) (o start t r : ℕ)
    (extent : o + v ≤ r)
    (S : ∀ i : ActiveIndex (treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)) t,
      UniformLayerSnapshot.Snapshot
        (Fin (Event.width ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event))) :
    UniformLayerSnapshot.Snapshot (Fin r) :=
  (Snapshot.family S).embed (treeEmbedding P o start t r extent)

@[simp] theorem treeSnapshot_matrix {v : ℕ} (P : UniformBalancedToeplitz.Plan v)
    (o start t r : ℕ) (extent : o + v ≤ r)
    (S : ∀ i : ActiveIndex (treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)) t,
      UniformLayerSnapshot.Snapshot
        (Fin (Event.width ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event))) :
    (treeSnapshot P o start t r extent S).matrix =
      Embedded.matrix (treeEmbedding P o start t r extent) (Matrix.blockDiagonal' (fun i => (S i).matrix)) := by
  rw [treeSnapshot,UniformLayerSnapshot.Snapshot.embed_matrix,Snapshot.family_matrix]

end
end ExactFourierCircuits.UniformGlobalCalendarUnion
