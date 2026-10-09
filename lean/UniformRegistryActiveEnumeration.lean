import UniformActualCalendarRegistry
import UniformCanonicalRectangleSnapshot
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRegistryActiveEnumeration
noncomputable section
open UniformActualCalendarRegistry UniformGlobalCalendarDispatch

/-- Literal selected input indices in exactly the charged scan's order. -/
def indices (tick : ℕ) (records : ℕ→ℕ×ℕ) (j fuel : ℕ) : List ℕ:=
 (List.range' j fuel).filter (fun i=>decide (S.active tick (records i).1 (records i).2))

lemma events_map (D stride tick : ℕ) (records : ℕ→ℕ×ℕ) (make : ℕ→ℕ→Event) (j fuel : ℕ) :
 events D stride tick records make j fuel=
 (indices tick records j fuel).map (fun i=>make i (tick-(records i).1)):=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  simp only[events,indices,List.range'_succ,List.filter_cons]
  by_cases active:S.active tick (records j).1 (records j).2
  · simp only[active,decide_true,ite_true,List.map_cons]
    exact congrArg (List.cons _) (ih (j+1))
  · simp only[active,decide_false,ite_false]
    exact ih (j+1)

lemma indices_mem (tick : ℕ) (records : ℕ→ℕ×ℕ) (j fuel i : ℕ) :
 i∈indices tick records j fuel↔j ≤ i ∧ i < j + fuel ∧ S.active tick (records i).1 (records i).2:=by
 simp only[indices,List.mem_filter,List.mem_range',decide_eq_true_eq,Nat.one_mul]
 constructor
 · rintro ⟨⟨a,ha,eq⟩,active⟩
   exact ⟨by omega,by omega,active⟩
 · rintro ⟨lo,hi,active⟩
   exact ⟨⟨i-j,by omega,by omega⟩,active⟩

lemma indices_nodup (tick : ℕ) (records : ℕ→ℕ×ℕ) (j fuel : ℕ) :
 (indices tick records j fuel).Nodup:=(List.nodup_range' (s := j) (n := fuel) 1).filter _

def membershipEquiv (tick : ℕ) (records : ℕ→ℕ×ℕ) (j fuel : ℕ) :
 {i //i∈indices tick records j fuel}≃
 {i //j ≤ i ∧ i < j + fuel ∧ S.active tick (records i).1 (records i).2} where
 toFun i:=⟨i.val,(indices_mem tick records j fuel i).mp i.property⟩
 invFun i:=⟨i.val,(indices_mem tick records j fuel i).mpr i.property⟩
 left_inv _:=rfl
 right_inv _:=rfl

/-- Exact selected-event indexing is derived from the actual scan, even when
numerical events happen to coincide; no supplied event bijection is needed. -/
def enumeration (D stride tick : ℕ) (records : ℕ→ℕ×ℕ) (make : ℕ→ℕ→Event) (j fuel : ℕ) :
 Fin (events D stride tick records make j fuel).length≃
 {i //j ≤ i ∧ i < j + fuel ∧ S.active tick (records i).1 (records i).2}:=
 (finCongr (by rw[events_map,List.length_map])).trans
  ((List.Nodup.getEquiv (indices tick records j fuel) (indices_nodup tick records j fuel)).trans
   (membershipEquiv tick records j fuel))

lemma enumeration_event (D stride tick : ℕ) (records : ℕ→ℕ×ℕ) (make : ℕ→ℕ→Event) (j fuel : ℕ)
 (i : Fin (events D stride tick records make j fuel).length) :
 (events D stride tick records make j fuel).get i=
 make (enumeration D stride tick records make j fuel i).val
  (tick-(records (enumeration D stride tick records make j fuel i).val).1):=by
 have eq:=events_map D stride tick records make j fuel
 have hi:i.val<(indices tick records j fuel).length:=by
  simpa only[eq,List.length_map] using i.isLt
 have get:=congrArg (fun L : List Event=>L[i.val]?) eq
 have result:(events D stride tick records make j fuel)[i.val]'i.isLt=
  make ((indices tick records j fuel)[i.val]'hi)
   (tick-(records ((indices tick records j fuel)[i.val]'hi)).1):=by
  simpa only[List.getElem?_map,List.getElem?_eq_getElem i.isLt,
   List.getElem?_eq_getElem hi,Option.map_some,Option.some.injEq] using get
 exact result

end
end ExactFourierCircuits.UniformRegistryActiveEnumeration
