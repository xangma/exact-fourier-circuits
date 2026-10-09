import UniformCalendarOrderedCalls

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPreparationOrder
noncomputable section
open OAI.ExactFourier TypedKernelWords UniformLayerSnapshot
open UniformGlobalCalendarDispatch UniformCalendarEventProducts UniformCalendarCallReindex

variable {σ : Type} [Fintype σ] [DecidableEq σ] {β : σ → Type}
variable [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- Elementary correspondence of cached source lanes and endpoint cells to the
local active phases. Both event order and each local call order may vary. -/
structure LocalSources (r : ℕ) (es : List Event) (S : ∀ i, Snapshot (β i))
    (band : (Σ i, β i) ↪ Fin r) (events : Fin es.length ≃ σ) where
  calls : ∀ i, Fin (callCount r (es.get i)) ≃ (S (events i)).calls.index
  records : ∀ i j, (es.get i).records j.val =
    ((band ⟨events i,(S (events i)).calls.position ⟨calls i j,0⟩⟩).val,
     (band ⟨events i,(S (events i)).calls.position ⟨calls i j,1⟩⟩).val)
  factor : ∀ i (x : Fin r), phaseFactor (es.get i).phase (es.get i).factor x.val =
    ((S (events i)).embed ((Embedded.sigmaIn (events i)).trans band)).diagonal x

abbrev union {r : ℕ} (S : ∀ i, Snapshot (β i)) (band : (Σ i, β i) ↪ Fin r) : Snapshot (Fin r) :=
  (UniformGlobalCalendarUnion.Snapshot.family S).embed band

variable {r : ℕ} {es : List Event} {S : ∀ i, Snapshot (β i)}
variable {band : (Σ i, β i) ↪ Fin r} {events : Fin es.length ≃ σ}

/-- The finite index follows the dispatcher's actual flatMap preparation order. -/
def callOrder (h : LocalSources r es S band events) :
    Fin (callTotal r es) ≃ (union S band).calls.index :=
  (UniformCalendarOrderedCalls.order r es).symm.trans (familyOrder (J := fun i => (S i).calls.index) events h.calls)

lemma callOrder_event (h : LocalSources r es S band events)
    (i : Fin es.length) (j : Fin (callCount r (es.get i))) :
    callOrder h (UniformCalendarOrderedCalls.order r es ⟨i,j⟩) = ⟨events i,h.calls i j⟩ := by
  change familyOrder (J := fun i => (S i).calls.index) events h.calls
    ((UniformCalendarOrderedCalls.order r es).symm (UniformCalendarOrderedCalls.order r es ⟨i,j⟩)) = _
  rw [Equiv.symm_apply_apply, familyOrder_apply]

def position (h : LocalSources r es S band events) :
    (Σ _ : Fin (callTotal r es), Fin 2) ↪ Fin r :=
  (Equiv.sigmaCongrLeft (β := fun _ : (union S band).calls.index => Fin 2)
    (callOrder h)).toEmbedding.trans (union S band).calls.position

lemma position_event (h : LocalSources r es S band events)
    (i : Fin es.length) (j : Fin (callCount r (es.get i))) (side : Fin 2) :
    position h ⟨UniformCalendarOrderedCalls.order r es ⟨i,j⟩,side⟩ =
      band ⟨events i,(S (events i)).calls.position ⟨h.calls i j,side⟩⟩ := by
  change band ⟨(callOrder h (UniformCalendarOrderedCalls.order r es ⟨i,j⟩)).1,
    (S (callOrder h (UniformCalendarOrderedCalls.order r es ⟨i,j⟩)).1).calls.position
      ⟨(callOrder h (UniformCalendarOrderedCalls.order r es ⟨i,j⟩)).2,side⟩⟩ = _
  rw [callOrder_event]


lemma allRows_position (h : LocalSources r es S band events) :
    allRows r es = List.ofFn (fun i : Fin (callTotal r es) =>
      ((position h ⟨i,0⟩).val,(position h ⟨i,1⟩).val)) := by
  apply List.ext_getElem
  · simp [allRows_length]
  · intro k hk₁ hk₂
    have hk : k < callTotal r es := by simpa using hk₂
    let a := (UniformCalendarOrderedCalls.order r es).symm ⟨k,hk⟩
    have ord : UniformCalendarOrderedCalls.order r es a = ⟨k,hk⟩ :=
      Equiv.apply_symm_apply _ _
    have ord' : UniformCalendarOrderedCalls.order r es ⟨a.1,a.2⟩ = ⟨k,hk⟩ := ord
    have values := UniformCalendarOrderedCalls.allRows_get_records r es a.1 a.2
    rw [h.records a.1 a.2] at values
    have p₀ := position_event h a.1 a.2 0
    have p₁ := position_event h a.1 a.2 1
    rw [ord] at p₀ p₁
    simpa only [List.get_eq_getElem, ord', List.getElem_ofFn, ← p₀, ← p₁] using values

lemma foldValues_diagonal (h : LocalSources r es S band events) (x : Fin r) :
    foldValues es (fun _ => 1) x.val = (union S band).diagonal x := by
  rw [foldValues_product, mul_one, product_get]
  simp_rw [h.factor]
  exact (Equiv.prod_comp events (fun i =>
    ((S i).embed ((Embedded.sigmaIn i).trans band)).diagonal x)).trans
    (family_diagonal_product S band x).symm

lemma position_kernel (h : LocalSources r es S band events) :
    Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (union S band).calls.matrix := by
  apply calls_matrix (union S band).calls (callOrder h)
  intro i side
  simp [position, Equiv.sigmaCongrLeft]

/-- The literal dispatcher factor and its literal ordered rows represent the
union of all active local phases. -/
theorem matrix (h : LocalSources r es S band events) :
    Matrix.diagonal (fun x : Fin r => foldValues es (fun _ => 1) x.val) *
      Embedded.matrix (position h) (Matrix.blockDiagonal' (fun _ : Fin (callTotal r es) => C)) =
      (union S band).matrix := by
  simp only [foldValues_diagonal h, position_kernel h, Snapshot.matrix]

end
end ExactFourierCircuits.UniformCalendarPreparationOrder
