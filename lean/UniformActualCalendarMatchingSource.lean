import UniformGlobalCalendarDispatchEvents
import UniformProducedMatchingSlotDirectory
import UniformMatchingKernelAmbient

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarMatchingSource
open UniformMachine UniformMatchingAxisTableMachine
open UniformGlobalCalendarDispatch
open UniformGlobalMatchingScaleMachine (Phase)
open UniformMatchingPackingPreparation
noncomputable section

def endpoints {M : ℕ} (E : Fin M→UniformColoring.Edge) (i : ℕ) : ℕ×ℕ :=
 if h:i<M then ((E ⟨i,h⟩).left,(E ⟨i,h⟩).right) else (0,0)

lemma endpoints_at {M : ℕ} (E : Fin M→UniformColoring.Edge) (i : ℕ) (hi:i<M) :
 endpoints E i=((E ⟨i,hi⟩).left,(E ⟨i,hi⟩).right):=by simp only[endpoints,dite_eq_left hi]

/-- The two entries read by the literal row copier are the actual ordered
left/right endpoints printed by Matching55, including its singleton suffix. -/
theorem ordered_rows {r M W P : ℕ} (E : Fin M→UniformColoring.Edge)
 (hm : Matching E) (hr : InRange r E) (hp : 2≤r) (s : State)
 (stored : UniformSectorPackingMachine.Permutations [physicalAxis r W P E hm hr hp] s) :
 UniformGlobalCalendarUnionRows.Rows P M (endpoints E) s.natHeap:=by
 intro i hi
 let a:=physicalAxis r W P E hm hr hp
 let l:=UniformSectorPacking.blockEncode _ (matchingPosition r E hm hr hp ⟨i,hi⟩ 0)
 let u:=UniformSectorPacking.blockEncode _ (matchingPosition r E hm hr hp ⟨i,hi⟩ 1)
 have left:=stored a (by exact List.mem_singleton.mpr rfl) l
 have right:=stored a (by exact List.mem_singleton.mpr rfl) u
 have lv:l.val=2*i:=by simpa only[l,Fin.val_zero,Nat.add_zero] using
  matching_position_encode r E hm hr hp ⟨i,hi⟩ 0
 have uv:u.val=2*i+1:=matching_position_encode r E hm hr hp ⟨i,hi⟩ 1
 have lp:(a.geometry.originalPermutation l).val=(E ⟨i,hi⟩).left:=by
  exact matching_position_original r E hm hr hp ⟨i,hi⟩ 0
 have up:(a.geometry.originalPermutation u).val=(E ⟨i,hi⟩).right:=by
  exact matching_position_original r E hm hr hp ⟨i,hi⟩ 1
 change s.natHeap (P+l.val)=_ at left
 change s.natHeap (P+u.val)=_ at right
 rw[lv,lp] at left
 rw[uv,up] at right
 rw[endpoints_at E i hi]
 exact ⟨left,by simpa only[Nat.add_assoc] using right⟩

def factor {r : ℕ} (values : Fin 9→Fin r→ℂ) (p : Phase) (i : ℕ) : ℂ:=
 match p with
 | .diagonal lane=>if h:i<r then values lane ⟨i,h⟩ else 1
 | .kernel=>1

def event {r M : ℕ} (D elapsed pool P kind : ℕ) (p : Phase)
 (values : Fin 9→Fin r→ℂ) (E : Fin M→UniformColoring.Edge) : Event where
 descriptor:=⟨D,elapsed,pool,r-M,P,kind⟩
 phase:=p
 factor:=factor values p
 records:=endpoints E

/-- This adapter consumes genuine cache source cells, not a prepared action
or an asserted dispatcher output. Geometry supplies its capacity and bounds. -/
theorem cached_event {r M D time elapsed pool W P kind O T B : ℕ}
 (E : Fin M→UniformColoring.Edge) (hm : Matching E) (hr : InRange r E) (hp : 2≤r)
 (p : Phase) (values : Fin 9→Fin r→ℂ) (s : State)
 (decoded : Decoded ⟨D,elapsed,pool,r-M,P,kind⟩ p)
 (abi : UniformLocalMatchingSlotDirectory.Entry D time r pool (r-M) W P kind s)
 (pools : ∀lane (i:Fin r),s.scalarHeap (pool+lane.val*r+i.val)=some (UniformPairMachine.prepared (values lane i)))
 (permutation : UniformSectorPackingMachine.Permutations [physicalAxis r W P E hm hr hp] s)
 (entryFit : D+7≤T) (sourcePool : pool+9*r≤O) (sourceRows : P+r≤T) (radixBound : r≤B) :
 CachedEvent r O T B (event D elapsed pool P kind p values E) s:=by
 have capacity:=matching_capacity r E hm hr
 have count:r-(r-M)=M:=by omega
 refine ⟨decoded,?_,?_,entryFit,sourcePool,?_,?_,?_⟩
 · exact ⟨abi.2.2.1,abi.2.2.2.1,abi.2.2.2.2.2.1,abi.2.2.2.2.2.2⟩
 · cases p with
   | diagonal lane=>
    intro i hi
    change s.scalarHeap ((pool+lane.val*r)+i)=some (UniformPairMachine.prepared (factor values (.diagonal lane) i))
    simpa only[factor,dite_eq_left hi] using pools lane ⟨i,hi⟩
   | kernel=>
    change UniformGlobalCalendarUnionRows.Rows P (r-(r-M)) (endpoints E) s.natHeap
    rw[count]
    exact ordered_rows E hm hr hp s permutation
 · change P+2*(r-(r-M))≤T
   rw[count];omega
 · change 2*(r-(r-M))≤r
   rw[count];exact capacity
 · intro i hi
   change i<r-(r-M) at hi
   rw[count] at hi
   change (endpoints E i).1≤B∧(endpoints E i).2≤B
   rw[endpoints_at E i hi]
   exact ⟨(hr ⟨i,hi⟩).1.le.trans radixBound,(hr ⟨i,hi⟩).2.le.trans radixBound⟩

/-- Factual finite-grid transport through an entry's actual radix equality. -/
lemma pool_grid {r P : ℕ} (a : UniformGlobalDiagonalRowsMachine.Entry)
 (radix : a.radix=r) (pool : a.pool=P) (s : State)
 (cells : UniformGlobalDiagonalRowsMachine.Pools [a] s) :
 ∀lane (i:Fin r),s.scalarHeap (P+lane.val*r+i.val)=
  some (UniformPairMachine.prepared (a.value lane (Fin.cast radix.symm i))):=by
 subst r
 subst P
 intro lane i
 simpa only[Fin.cast_refl,id_eq] using cells a (by exact List.mem_singleton.mpr rfl) lane i

end
end ExactFourierCircuits.UniformActualCalendarMatchingSource
