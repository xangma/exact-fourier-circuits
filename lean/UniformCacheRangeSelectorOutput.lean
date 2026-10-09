import UniformCacheRangeSelectorPreservation
import UniformGlobalCalendarSelected
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
lemma writeSelections_high(O used:ℕ)(qs:List (ℕ × ℕ))(heap:ℕ → Option ℕ)(a:ℕ)
 (ha:O+2*(used+qs.length) ≤ a):S.writeSelections O used qs heap a=heap a:=by
 simp only[S.writeSelections]
 induction qs generalizing used heap with
 | nil=>rfl
 | cons q qs ih=>
  simp only[List.length_cons] at ha
  rw[UniformGlobalCalendarSelector.writeSelections,ih _ _ (by omega)]
  simp (disch:=omega) [UniformGlobalCalendarSelector.storeSelection]
structure Result(r control rectangleCount tick O:ℕ)(rectangle:ℕ → ℕ × ℕ)(nodes:List Range)(s u:State):Prop where
 count:u.natReg 6705=(selections r control rectangleCount tick rectangle nodes).length
 clock:u.natReg 6703=tick
 bank:∀i:Fin (selections r control rectangleCount tick rectangle nodes).length,
  u.natHeap (O+2*i.val)=some ((selections r control rectangleCount tick rectangle nodes).get i).1 ∧
  u.natHeap (O+2*i.val+1)=some ((selections r control rectangleCount tick rectangle nodes).get i).2
 outside:∀a,(a<O ∨ O+2*(selections r control rectangleCount tick rectangle nodes).length ≤ a) → u.natHeap a=s.natHeap a
 frame:Frame s u
 registers:∀q,(q<6700 ∨ 6723<q) → (q<7100 ∨ 7129<q) → u.natReg q=s.natReg q

theorem complete_execution {n r tasks control tick O rectangleCount B}(x:Fin n → ℂ)
 (rectangle:ℕ → ℕ × ℕ)(nodes:List Range)(s:State)
 (args:Args r tasks control tick O s)(source:RangeSource r tasks control rectangleCount rectangle nodes s.natHeap)
 (layout:Layout r tasks control rectangleCount O B nodes)
 (rectangleValues:∀j,j<rectangleCount → (rectangle j).1+28 ≤ B ∧ (rectangle j).2 ≤ B)
 (nodeValues:∀q∈nodes,∀j,j<q.count → (q.records j).1+28 ≤ B ∧ (q.records j).2 ≤ B)
 (code:90 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ 21*(rectangleCount+total nodes)+16*nodes.length+31 ∧u.pc=89 ∧
 Result r control rectangleCount tick O rectangle nodes s u:=by
 obtain ⟨u,t,run,cost,up,count,clock,heap⟩:=execution x rectangle nodes s args source layout rectangleValues nodeValues code pc wb
 refine ⟨u,t,run,cost,up,⟨count,clock,?_,?_,execution_frame run,execution_register run⟩⟩
 · intro i
   rw[heap]
   simpa only[Nat.zero_add] using UniformGlobalCalendarSelector.writeSelections_get O 0
    (selections r control rectangleCount tick rectangle nodes) s.natHeap i
 · intro a outside
   rw[heap]
   rcases outside with low|high
   · exact writeSelections_low _ _ _ _ _ low
   · exact writeSelections_high _ _ _ _ _ (by simpa only[Nat.zero_add] using high)
end ExactFourierCircuits.UniformCacheRangeSelector
