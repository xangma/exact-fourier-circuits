import UniformGlobalCalendarDispatchCycle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine
open UniformGlobalMatchingScaleMachine (Phase)
noncomputable section

structure Event where
 descriptor : Descriptor
 phase : Phase
 factor : ℕ→ℂ
 records : ℕ→ℕ×ℕ

def callCount (r : ℕ) (e : Event) : ℕ:=phaseCalls e.phase (r-e.descriptor.widthCount)
def callTotal (r : ℕ) (es : List Event) : ℕ:=(es.map (callCount r)).sum

def foldValues : List Event→(ℕ→ℂ)→ℕ→ℂ
 | [],g=>g
 | e::es,g=>foldValues es (fun i=>phaseFactor e.phase e.factor i*g i)

def foldRows (r T : ℕ) : ℕ→List Event→(ℕ→Option ℕ)→ℕ→Option ℕ
 | _,[],heap=>heap
 | used,e::es,heap=>foldRows r T (used+callCount r e) es
  (rowAction T used (r-e.descriptor.widthCount) e.phase e.records heap)

/-- Factual stored cache cells and separation. The only semantic data are the
source lane values or actual ordered endpoint cells; produced output is not
an input. The kind law is the real phase decoder policy. -/
structure CachedEvent (r O T B : ℕ) (e : Event) (s : State) : Prop where
 decoded : Decoded e.descriptor e.phase
 stored : Stored e.descriptor s
 source : Source r e.descriptor e.phase e.factor e.records s
 entryFit : e.descriptor.address+7 ≤ T
 sourcePool : e.descriptor.pool+9*r ≤ O
 sourceRows : e.descriptor.permutation+2*(r-e.descriptor.widthCount) ≤ T
 matching : 2*(r-e.descriptor.widthCount) ≤ r
 values : ∀i,i<r-e.descriptor.widthCount→(e.records i).1 ≤ B∧(e.records i).2 ≤ B

lemma CachedEvent.transfer {r O T B : ℕ} {e : Event} {s u : State}
 (h : CachedEvent r O T B e s) (natKeep : ∀z,z<T→u.natHeap z=s.natHeap z)
 (scalarKeep : ∀z,z<O→u.scalarHeap z=s.scalarHeap z) : CachedEvent r O T B e u := by
 refine ⟨h.decoded,?_,?_,h.entryFit,h.sourcePool,h.sourceRows,h.matching,h.values⟩
 · rcases h.stored with ⟨pool,width,permutation,kind⟩
   exact ⟨(natKeep _ (by have:=h.entryFit;omega)).trans pool,
    (natKeep _ (by have:=h.entryFit;omega)).trans width,
    (natKeep _ (by have:=h.entryFit;omega)).trans permutation,
    (natKeep _ (by have:=h.entryFit;omega)).trans kind⟩
 · have source:=h.source
   cases phase : e.phase with
   | diagonal lane=>
    simp only [phase,Source] at source ⊢
    intro i hi
    have mul : lane.val*r ≤ 8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
    rw [scalarKeep _ (by have:=h.sourcePool;omega)]
    exact source i hi
   | kernel=>
    simp only [phase,Source] at source ⊢
    intro i hi
    exact ⟨(natKeep _ (by have:=h.sourceRows;omega)).trans (source i hi).1,
     (natKeep _ (by have:=h.sourceRows;omega)).trans (source i hi).2⟩

def Selections (A : ℕ) : ℕ→List Event→State→Prop
 | _,[],_=>True
 | j,e::es,s=>Selected A j e.descriptor s∧Selections A (j+1) es s

lemma Selections.transfer {A N T : ℕ} {es : List Event} {s u : State} (j : ℕ)
 (h : Selections A j es s) (indices : j+es.length ≤ N) (fit : A+2*N ≤ T)
 (keep : ∀z,z<T→u.natHeap z=s.natHeap z) : Selections A j es u := by
 induction es generalizing j with
 | nil=>trivial
 | cons e es ih=>
   rcases h with ⟨head,tail⟩
   refine ⟨?_,ih (j+1) tail (by simp only [List.length_cons] at indices;omega)⟩
   exact ⟨(keep _ (by simp only [List.length_cons] at indices;omega)).trans head.1,
    (keep _ (by simp only [List.length_cons] at indices;omega)).trans head.2⟩

lemma printed_transfer {T H : ℕ} {s u : State}
 (printed : UniformFixedNetworkScheduleMachine.Printed T UniformGlobalCalendarPhaseDirectory.words s)
 (fit : T+56 ≤ H) (keep : ∀z,z<H→u.natHeap z=s.natHeap z) :
 UniformFixedNetworkScheduleMachine.Printed T UniformGlobalCalendarPhaseDirectory.words u := by
 intro i hi
 have bound : i<56:=by rwa [UniformGlobalCalendarPhaseDirectory.words_length] at hi
 exact (keep _ (by omega)).trans (printed i hi)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
