import UniformCalendarAxisAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarActionPosition
noncomputable section
open UniformGlobalCalendarDispatch UniformCalendarAxisAction

/-- Literal preparation-order rows uniquely determine the ordered C injection. -/
lemma unique {r:ℕ}{es:List Event}{M N:Matrix (Fin r) (Fin r) ℂ}
 (a:Action r es M)(b:Action r es N):a.position=b.position:=by
 apply Function.Embedding.ext
 rintro ⟨i,j⟩
 apply Fin.ext
 have h:=congrArg (fun l:List (ℕ×ℕ)=>l[i.val]?) (a.rows.symm.trans b.rows)
 simp only[List.getElem?_ofFn,dite_eq_left i.isLt,Option.some.injEq] at h
 fin_cases j
 · exact congrArg Prod.fst h
 · exact congrArg Prod.snd h

end
end ExactFourierCircuits.UniformCalendarActionPosition
