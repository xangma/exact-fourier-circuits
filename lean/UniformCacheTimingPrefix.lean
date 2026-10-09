import UniformCacheTimingRows
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingPrefix
open UniformCacheTimingRows UniformLocalRectangleDescriptors
lemma amounts_eq (L:List Row):amounts L=UniformLocalCacheTiming.rectanglesDuration L:=by
 have eq:L.map (fun q=>UniformCacheRowDurationMachine.amount q.a q.e)=
   L.map UniformLocalCacheTiming.rectangleDuration:=by
  apply List.map_congr_left
  intro q _
  exact UniformCacheRowDurationMachine.amount_rectangle q
 exact congrArg List.sum eq
lemma writePrefixes_outside (T ordinal c a:ℕ)(L:List Row)(heap:ℕ→Option ℕ)
 (outside:a<T+ordinal∨T+ordinal+L.length≤a):writePrefixes T ordinal c L heap a=heap a:=by
 induction L generalizing ordinal c heap with
 | nil=>rfl
 | cons q qs ih=>
  rw [writePrefixes,ih (ordinal+1) (c+UniformCacheRowDurationMachine.amount q.a q.e)
   (Function.update heap (T+ordinal) (some c)) (by simp only [List.length_cons] at outside;omega)]
  exact Function.update_of_ne (by simp only [List.length_cons] at outside;omega) _ _
lemma writePrefixes_inside (T ordinal c:ℕ)(L:List Row)(heap:ℕ→Option ℕ)(i:ℕ)(hi:i<L.length):
 writePrefixes T ordinal c L heap (T+ordinal+i)=some (c+amounts (L.take i)):=by
 induction L generalizing ordinal c heap i with
 | nil=>simp at hi
 | cons q qs ih=>
  cases i with
  | zero=>
   rw [writePrefixes,writePrefixes_outside]
   · simp [amounts]
   · left;omega
  | succ i=>
   have bound:i<qs.length:=by simpa using hi
   have out:=ih (ordinal+1) (c+UniformCacheRowDurationMachine.amount q.a q.e)
    (Function.update heap (T+ordinal) (some c)) i bound
   simpa [writePrefixes,amounts,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using out
end ExactFourierCircuits.UniformCacheTimingPrefix
