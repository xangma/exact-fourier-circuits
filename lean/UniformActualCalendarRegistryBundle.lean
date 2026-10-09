import UniformActualCalendarRegistrySelections

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

structure Bundle (r O T B D:ℕ)(L:List (ℕ×ℕ))(nodes:List UniformCacheRangeSelector.Range)(s:State) where
 rectangle:Family r O T B D (3*r+11) L s
 node:∀i:Fin nodes.length,Family r O T B (nodes.get i).base (3*r+11)
  (List.ofFn (fun j:Fin (nodes.get i).count=>(nodes.get i).records j.val)) s

def Bundle.events {r O T B D L nodes s}(b:Bundle r O T B D L nodes s)(tick:ℕ):List Event:=
 b.rectangle.selected tick++(List.ofFn (fun i:Fin nodes.length=>(b.node i).selected tick)).flatten

lemma Bundle.pairs {r O T B D L nodes s}(b:Bundle r O T B D L nodes s)(tick:ℕ):
 UniformActualCalendarSelectionBank.pairs (b.events tick)=
 S.selected D (3*r+11) tick (fun i=>L[i]?.getD (0,0)) 0 L.length++
 UniformCacheRangeSelector.selectedRanges r tick nodes:=by
 rw[Bundle.events,UniformActualCalendarSelectionBank.pairs,List.map_append]
 rw[←UniformActualCalendarSelectionBank.pairs,b.rectangle.pairs]
 congr 1
 rw[selectedRanges_eq_map]
 simp only[List.map_flatten,List.map_ofFn,
  Function.comp_def]
 have nodeEq:∀i:Fin nodes.length,
  UniformActualCalendarSelectionBank.pairs ((b.node i).selected tick)=
  S.selected (nodes.get i).base (3*r+11) tick (nodes.get i).records 0 (nodes.get i).count:=by
  intro i
  rw[(b.node i).pairs]
  exact selected_ofFn _ _ _ _ _
 dsimp only[UniformActualCalendarSelectionBank.pairs] at nodeEq
 simp_rw[nodeEq]
 have result:=congrArg (fun L:List UniformCacheRangeSelector.Range=>
  (L.map (fun q=>S.selected q.base (3*r+11) tick q.records 0 q.count)).flatten) (List.ofFn_get nodes)
 simpa only[List.map_ofFn,Function.comp_def] using result

lemma Bundle.cached {r O T B D L nodes s}(b:Bundle r O T B D L nodes s)(tick:ℕ):
 ∀e∈b.events tick,CachedEvent r O T B e s:=by
 intro e member
 rw[Bundle.events,List.mem_append] at member
 rcases member with rectangle|node
 · exact b.rectangle.cached tick e rectangle
 · obtain ⟨part,partMember,eventMember⟩:=List.mem_flatten.mp node
   obtain ⟨i,rfl⟩:=List.mem_ofFn.mp partMember
   exact (b.node i).cached tick e eventMember

end
end ExactFourierCircuits.UniformActualCalendarRegistry
