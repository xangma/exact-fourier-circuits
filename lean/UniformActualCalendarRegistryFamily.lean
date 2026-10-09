import UniformActualCalendarRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

def Produced.cast {r r' O T B address address' time time' kind kind' : ℕ} {s : State}
 (p : Produced r O T B address time kind s) (radix : r=r') (whereAt : address=address')
 (_whenAt : time=time') (which : kind=kind') : Produced r' O T B address' time' kind' s where
 event:=p.event
 address_eq:=fun elapsed=>(p.address_eq elapsed).trans whereAt
 elapsed_eq:=p.elapsed_eq
 cached:=by
  subst r';subst time';subst kind'
  exact p.cached

theorem Produced.cast_event {r r' O T B address address' time time' kind kind' : ℕ} {s : State}
 (p : Produced r O T B address time kind s) (radix : r=r') (whereAt : address=address')
 (whenAt : time=time') (which : kind=kind') :
 (p.cast radix whereAt whenAt which).event=p.event:=rfl

/-- A registry consists only of genuine produced cache-entry factories,
indexed by the actual contiguous physical bank. -/
structure Family (r O T B D stride : ℕ) (L : List (ℕ×ℕ)) (s : State) where
 entry : ∀j:Fin L.length,Produced r O T B (D+stride*j.val) (L.get j).1 (L.get j).2 s

def defaultEvent : Event where
 descriptor:=⟨0,0,0,0,0,0⟩
 phase:=.diagonal 0
 factor:=fun _=>1
 records:=fun _=>(0,0)

def Family.make {r O T B D stride L s} (f : Family r O T B D stride L s)
 (j elapsed : ℕ) : Event:=
 if bound:j<L.length then (f.entry ⟨j,bound⟩).event elapsed else defaultEvent

def Family.selected {r O T B D stride L s} (f : Family r O T B D stride L s) (tick : ℕ) : List Event:=
 events D stride tick (fun i=>L[i]?.getD (0,0)) f.make 0 L.length

theorem Family.pairs {r O T B D stride L s} (f : Family r O T B D stride L s) (tick : ℕ) :
 UniformActualCalendarSelectionBank.pairs (f.selected tick)=
 S.selected D stride tick (fun i=>L[i]?.getD (0,0)) 0 L.length:=by
 apply event_pairs (N:=L.length)
 · intro j bound elapsed
   simp only[Family.make,dite_eq_left bound]
   exact (f.entry ⟨j,bound⟩).address_eq elapsed
 · intro j bound elapsed
   simp only[Family.make,dite_eq_left bound]
   exact (f.entry ⟨j,bound⟩).elapsed_eq elapsed
 · omega

theorem Family.cached {r O T B D stride L s} (f : Family r O T B D stride L s) (tick : ℕ) :
 ∀e∈f.selected tick,CachedEvent r O T B e s:=by
 apply events_cached (N:=L.length)
 · intro j bound elapsed phaseBound
   simp only[Family.make,dite_eq_left bound]
   apply (f.entry ⟨j,bound⟩).cached
   simpa only[List.getElem?_eq_getElem bound,Option.getD_some,List.get_eq_getElem] using phaseBound
 · omega

end
end ExactFourierCircuits.UniformActualCalendarRegistry
