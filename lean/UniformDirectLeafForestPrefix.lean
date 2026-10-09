import UniformDirectLeafForestModel
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestPrefix
open UniformDirectLeafForestModel UniformLocalCacheTreeMachine
lemma before_succ (visits:List Visit)(i:ℕ):before visits i≤before visits (i+1):=by
 by_cases hi:i<visits.length
 · rw[before_next visits i hi];omega
 · have a:visits.take i=visits:=List.take_of_length_le (by omega)
   have b:visits.take (i+1)=visits:=List.take_of_length_le (by omega)
   simp only[before,a,b]
   exact le_rfl
lemma before_mono (visits:List Visit){i j:ℕ}(h:i≤j):before visits i≤before visits j:=by
 induction j with
 | zero=>
  have eq:i=0:=by omega
  subst i
  exact le_rfl
 | succ j ih=>
  by_cases lower:i≤j
  · exact (ih lower).trans (before_succ visits j)
  · have eq:i=j+1:=by omega
    subst i
    exact le_rfl
end ExactFourierCircuits.UniformDirectLeafForestPrefix
