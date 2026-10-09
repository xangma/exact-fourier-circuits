import UniformCalendarScanActive

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarScanAtoms
noncomputable section
open UniformActualCalendarRegistry UniformGlobalCalendarDispatch UniformLocalCacheTiming
open UniformCalendarScanActive UniformCalendarRefinementActive UniformCalendarActualAtoms
open UniformCalendarAtomCollapse UniformCalendarIntervalPartition

def atomEnumeration (n:ℕ)(E:List TimedEvent)(t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event):
 Fin (events 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).length≃
 ActiveAtom E (pieces n E) t:=
 (UniformRegistryActiveEnumeration.enumeration 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).trans
  ((naturalEquiv n E t).trans (fineEquiv n E t).symm)

lemma atom_index (n:ℕ)(E:List TimedEvent)(t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event)
 (i:Fin (events 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).length):
 (order n E (atomEnumeration n E t make i).val).val=
 (UniformRegistryActiveEnumeration.enumeration 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length i).val:=by
 let a:=atomEnumeration n E t make i
 let e:=UniformRegistryActiveEnumeration.enumeration 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length i
 have eq: fineEquiv n E t a=naturalEquiv n E t e:=
  (fineEquiv n E t).apply_symm_apply _
 exact congrArg (fun q:FineIndex n E t=>q.val.val) eq

/-- The selected event's elapsed value is measured from the exact active
native atom's stored prefix clock. This follows from the charged scan. -/
theorem atom_event (n:ℕ)(E:List TimedEvent)(t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event)
 (i:Fin (events 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).length):
 (events 0 0 t (recordAt (fineRecords n E)) make 0 (fineRecords n E).length).get i=
 make (order n E (atomEnumeration n E t make i).val).val
  (t-((E.get (atomEnumeration n E t make i).val.1).start+
   prefixDuration (pieces n E (atomEnumeration n E t make i).val.1)
    (atomEnumeration n E t make i).val.2.val)):=by
 rw[UniformRegistryActiveEnumeration.enumeration_event,←atom_index]
 let a:=atomEnumeration n E t make i
 have cell:recordAt (fineRecords n E) (order n E a.val).val=
  (fineRecords n E).get (order n E a.val):=by
  unfold recordAt
  rw[List.getElem?_eq_getElem (order n E a.val).isLt,Option.getD_some]
  rfl
 rw[cell,order_get]

end
end ExactFourierCircuits.UniformCalendarScanAtoms
