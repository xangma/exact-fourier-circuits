import UniformActualCalendarRegistryFamily
import UniformDirectLeafForestRangeSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

lemma selected_congr (D stride tick N:ℕ)(a b:ℕ→ℕ×ℕ)
 (same:∀i,i<N→a i=b i)(j fuel:ℕ)(endBound:j+fuel≤N):
 S.selected D stride tick a j fuel=S.selected D stride tick b j fuel:=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  simp only[S.selected,UniformGlobalCalendarSelector.selected,same j (by omega)]
  split_ifs <;> first | exact congrArg (List.cons _) (ih _ (by omega)) | exact ih _ (by omega)

lemma selected_ofFn (D stride tick N:ℕ)(records:ℕ→ℕ×ℕ):
 S.selected D stride tick (fun i=>(List.ofFn (fun j:Fin N=>records j.val))[i]?.getD (0,0)) 0
   (List.ofFn (fun j:Fin N=>records j.val)).length=
 S.selected D stride tick records 0 N:=by
 rw[List.length_ofFn]
 apply selected_congr (N:=N)
 · intro i hi
   have bound:i<(List.ofFn (fun j:Fin N=>records j.val)).length:=by rw[List.length_ofFn];exact hi
   rw[List.getElem?_eq_getElem bound,Option.getD_some]
   exact List.getElem_ofFn bound
 · omega

lemma selectedRanges_eq_map (r tick:ℕ)(L:List UniformCacheRangeSelector.Range):
 UniformCacheRangeSelector.selectedRanges r tick L=
 (L.map (fun q=>S.selected q.base (3*r+11) tick q.records 0 q.count)).flatten:=by
 induction L with
 | nil=>rfl
 | cons q qs ih=>simp only[UniformCacheRangeSelector.selectedRanges,List.map_cons,List.flatten_cons,ih,
   UniformCacheRangeSelector.S.selected,UniformCacheRangeSelector.stride]

end
end ExactFourierCircuits.UniformActualCalendarRegistry
