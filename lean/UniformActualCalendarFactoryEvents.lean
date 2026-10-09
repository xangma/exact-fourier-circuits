import UniformActualCalendarRegistryActual

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

lemma Family.cast_make {r r' O T B D D' stride stride' L L' s}
 (f:Family r O T B D stride L s)(radix:r=r')(address:D=D')(spacing:stride=stride')(rows:L=L'):
 (f.cast radix address spacing rows).make=f.make:=by
 subst r';subst D';subst stride';subst L'
 rfl

lemma Family.append_make_left {r O T B D stride xs ys s}(a:Family r O T B D stride xs s)
 (b:Family r O T B (D+stride*xs.length) stride ys s)(j elapsed:ℕ)(bound:j<xs.length):
 (a.append b).make j elapsed=a.make j elapsed:=by
 have total:j<(xs++ys).length:=by rw[List.length_append];omega
 simp only[Family.make,dite_eq_left total,dite_eq_left bound,Family.append,Produced.cast_event]

lemma Family.append_make_right {r O T B D stride xs ys s}(a:Family r O T B D stride xs s)
 (b:Family r O T B (D+stride*xs.length) stride ys s)(j elapsed:ℕ)(bound:j<ys.length):
 (a.append b).make (xs.length+j) elapsed=b.make j elapsed:=by
 have total:xs.length+j<(xs++ys).length:=by rw[List.length_append];omega
 have high:¬xs.length+j<xs.length:=by omega
 simp only[Family.make,dite_eq_left total,dite_eq_left bound,Family.append,dite_eq_right high,
  Produced.cast_event]
 exact congrArg (fun i:Fin ys.length=>(b.entry i).event elapsed) (Fin.ext (by change xs.length+j-xs.length=j;omega))

end
end ExactFourierCircuits.UniformActualCalendarRegistry
