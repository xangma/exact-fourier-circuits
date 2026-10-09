import UniformActualCalendarSelectionBank
import UniformCacheRangeSelectorOutput

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
namespace S
export UniformGlobalCalendarSelector (active duration selected)
end S
noncomputable section

/-- An actual cache entry supplies events at its own physical address/time;
only elapsed values within its literal duration are dispatched. -/
structure Produced (r O T B address time kind : ℕ) (s : State) where
 event : ℕ→Event
 address_eq : ∀elapsed,(event elapsed).descriptor.address=address
 elapsed_eq : ∀elapsed,(event elapsed).descriptor.elapsed=elapsed
 cached : ∀elapsed,elapsed<S.duration kind→CachedEvent r O T B (event elapsed) s

def events (D stride tick : ℕ) (records : ℕ→ℕ×ℕ)
 (make : ℕ→ℕ→Event) : ℕ→ℕ→List Event
 | _,0=>[]
 | j,fuel+1=>if S.active tick (records j).1 (records j).2 then
  make j (tick-(records j).1)::events D stride tick records make (j+1) fuel
  else events D stride tick records make (j+1) fuel

theorem event_pairs (D stride tick N : ℕ) (records : ℕ→ℕ×ℕ) (make : ℕ→ℕ→Event)
 (address : ∀j,j<N→∀elapsed,(make j elapsed).descriptor.address=D+stride*j)
 (elapsed : ∀j,j<N→∀phase,(make j phase).descriptor.elapsed=phase)
 (j fuel : ℕ) (endBound : j+fuel≤N) :
 UniformActualCalendarSelectionBank.pairs (events D stride tick records make j fuel)=
 S.selected D stride tick records j fuel:=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  have bound:j<N:=by omega
  simp only[events,S.selected,UniformGlobalCalendarSelector.selected]
  split_ifs
  · simp only[UniformActualCalendarSelectionBank.pairs,List.map_cons,address j bound,elapsed j bound]
    exact congrArg (List.cons _) (ih (j+1) (by omega))
  · exact ih (j+1) (by omega)

theorem events_cached {r O T B D stride tick N : ℕ} {s : State}
 (records : ℕ→ℕ×ℕ) (make : ℕ→ℕ→Event)
 (produced : ∀j,j<N→∀elapsed,elapsed<S.duration (records j).2→CachedEvent r O T B (make j elapsed) s)
 (j fuel : ℕ) (endBound : j+fuel≤N) :
 ∀e∈events D stride tick records make j fuel,CachedEvent r O T B e s:=by
 induction fuel generalizing j with
 | zero=>simp[events]
 | succ fuel ih=>
  by_cases active:S.active tick (records j).1 (records j).2
  · simp only[events,ite_eq_left active,List.mem_cons]
    intro e he
    rcases he with rfl|he
    · apply produced j (by omega)
      obtain ⟨lo,hi⟩:=active
      omega
    · exact ih (j+1) (by omega) e he
  · simp only[events,ite_eq_right active]
    exact ih (j+1) (by omega)

end
end ExactFourierCircuits.UniformActualCalendarRegistry
