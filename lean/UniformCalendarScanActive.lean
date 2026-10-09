import UniformCalendarRefinementActive
import UniformActualCalendarMacroOrder

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarScanActive
noncomputable section
open UniformLocalCacheTiming UniformGlobalCalendarUnion UniformGlobalCalendarDispatch
open UniformCalendarActualAtoms UniformCalendarRefinementActive
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder

abbrev fineRecords (n:ℕ)(E:List TimedEvent):List (ℕ×ℕ):=E.flatMap (records n)
def recordAt (L:List (ℕ×ℕ))(i:ℕ):ℕ×ℕ:=L[i]?.getD (0,0)

def naturalEquiv (n:ℕ)(E:List TimedEvent)(t:ℕ):
 {i //0 ≤ i ∧ i < 0+(fineRecords n E).length ∧
  S.active t (recordAt (fineRecords n E) i).1 (recordAt (fineRecords n E) i).2}≃FineIndex n E t where
 toFun i:=by
  have bound:i.val<(fineRecords n E).length:=by have:=i.property.2.1;omega
  refine ⟨⟨i.val,bound⟩,?_⟩
  have cell:recordAt (fineRecords n E) i.val=(fineRecords n E).get ⟨i.val,bound⟩:=by
   unfold recordAt
   rw[List.getElem?_eq_getElem bound,Option.getD_some]
   rfl
  have active:=i.property.2.2
  rw[cell] at active
  exact active
 invFun i:=by
  refine ⟨i.val.val,Nat.zero_le _,?_,?_⟩
  · change i.val.val<0+(E.flatMap (records n)).length
    simpa only[Nat.zero_add] using i.val.isLt
  · have cell:recordAt (fineRecords n E) i.val.val=(fineRecords n E).get i.val:=by
     unfold recordAt
     rw[List.getElem?_eq_getElem i.val.isLt,Option.getD_some]
     rfl
    rw[cell]
    exact i.property

 left_inv _:=rfl
 right_inv _:=rfl

/-- Exact active macro indexing, derived from the literal finite scan. -/
def enumeration (n:ℕ)(E:List TimedEvent)(t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event):
 Fin (events 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).length≃ActiveIndex E t:=
 (UniformRegistryActiveEnumeration.enumeration 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).trans
  ((naturalEquiv n E t).trans (UniformCalendarRefinementActive.collapse n E t))

/-- The concrete original DFS preparation and its genuine fine cache clocks
select exactly the original parallel tree's active macro occurrences. -/
def rootEnumeration (n v o R t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event):
 Fin (events 0 0 t
  (recordAt (fineRecords n (preparationEvents (UniformLocalCacheTreeMachine.walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1)))
  make 0 (fineRecords n (preparationEvents (UniformLocalCacheTreeMachine.walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1)).length).length≃
 ActiveIndex (treeTimed 0 (UniformLocalCacheTreeMachine.ofPlan (UniformBalancedToeplitz.plan v) o)) t:=
 (enumeration n _ t make).trans
  (UniformCalendarPermutationActive.activeEquiv (root_preparation_perm v o R) t)

end
end ExactFourierCircuits.UniformCalendarScanActive
