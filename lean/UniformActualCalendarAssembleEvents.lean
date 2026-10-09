import UniformActualCalendarBlockEvents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleRegistry
open UniformMachine UniformActualCalendarRegistry UniformLocalRequestPlan
noncomputable section

lemma make_address_cast {r O T B D D' stride L s}
 (f:Family r O T B D stride L s)(e:D=D'):
 (Eq.mp (congrArg (fun x=>Family r O T B x stride L s) e) f).make=f.make:=by
 subst D';rfl

lemma make_address_mp {r O T B D D' stride L s}
 (f:Family r O T B D stride L s)(e:Family r O T B D stride L s=Family r O T B D' stride L s)
 (d:D=D'):(Eq.mp e f).make=f.make:=by
 subst D';cases e;rfl
lemma make_address_mpr {r O T B D D' stride L s}
 (f:Family r O T B D stride L s)(e:Family r O T B D' stride L s=Family r O T B D stride L s)
 (d:D=D'):(Eq.mpr e f).make=f.make:=by
 subst D';cases e;rfl

lemma make_metadata_mp {r O T B D D' stride L L' s}
 (f:Family r O T B D stride L s)(e:Family r O T B D stride L s=Family r O T B D' stride L' s)
 (d:D=D')(l:L=L'):(Eq.mp e f).make=f.make:=by
 subst D';subst L';cases e;rfl
lemma make_metadata_mpr {r O T B D D' stride L L' s}
 (f:Family r O T B D stride L s)(e:Family r O T B D' stride L' s=Family r O T B D stride L s)
 (d:D=D')(l:L=L'):(Eq.mpr e f).make=f.make:=by
 subst D';subst L';cases e;rfl

lemma entries_length (n:ℕ)(qs:List Request):
 (entries n qs).length=slotPrefix n qs qs.length:=by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simpa only[entries,List.flatMap_cons,List.length_append,block,List.length_ofFn,
   List.length_cons,slotPrefix] using congrArg (slotCount n q.row+·) ih

lemma global_bound (n:ℕ)(qs:List Request)(i:ℕ)(hi:i<qs.length)(t:ℕ)(ht:t<slotCount n qs[i].row):
 slotPrefix n qs i+t<(entries n qs).length:=by
 rw[entries_length]
 have next:=prefix_step n qs i hi
 have last:=prefix_mono n qs (i:=i+1) (j:=qs.length) (by omega) le_rfl
 omega

attribute [local irreducible] Family.append Family.make

lemma assemble_make (n r O T B D stride:ℕ)(qs:List Request)(s:State)
 (h:∀i (hi:i<qs.length),Family r O T B (D+stride*slotPrefix n qs i) stride (block n qs[i]) s)
 (i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)(ht:t<slotCount n qs[i].row):
 (assemble n r O T B D stride qs s h).make (slotPrefix n qs i+t) elapsed=
 (h i hi).make t elapsed:=by
 induction qs generalizing D i with
 | nil=>simp at hi
 | cons q qs ih=>
  let first:Family r O T B D stride (block n q) s:=h 0 (by simp)
  let tail:(j:ℕ)→(hj:j<qs.length)→Family r O T B
   (D+stride*slotCount n q.row+stride*slotPrefix n qs j) stride (block n qs[j]) s:=fun j hj=>by
    have current:=h (j+1) (by simp;omega)
    change Family r O T B (D+stride*(slotCount n q.row+slotPrefix n qs j)) stride (block n qs[j]) s at current
    simpa only[Nat.mul_add,Nat.add_assoc] using current
  let rest:Family r O T B (D+stride*(block n q).length) stride (entries n qs) s:=by
   simpa only[block,List.length_ofFn] using assemble n r O T B (D+stride*slotCount n q.row) stride qs s tail
  have expose:assemble n r O T B D stride (q::qs) s h=first.append rest:=rfl
  have exposed:=congrArg (fun f:Family r O T B D stride (entries n (q::qs)) s=>
   f.make (slotPrefix n (q::qs) i+t) elapsed) expose
  refine exposed.trans ?_
  cases i with
  | zero=>
   have moved:=congrArg (fun j=>(first.append rest).make j elapsed)
    (show slotPrefix n (q::qs) 0+t=t by simp only[slotPrefix,Nat.zero_add])
   exact moved.trans (Family.append_make_left first rest t elapsed (by rw[block,List.length_ofFn];exact ht))
  | succ i=>
   have bound:i<qs.length:=by have hh:=hi; simp only[List.length_cons] at hh;omega
   have ht':t<slotCount n qs[i].row:=ht
   have shift:slotPrefix n (q::qs) (i+1)+t=(block n q).length+(slotPrefix n qs i+t):=by
    simp only[slotPrefix,block,List.length_ofFn,Nat.add_assoc]
   have moved:=congrArg (fun j=>(first.append rest).make j elapsed) shift
   refine moved.trans ((Family.append_make_right first rest _ elapsed (global_bound n qs i bound t ht')).trans ?_)
   have rest_make:rest.make=(assemble n r O T B (D+stride*slotCount n q.row) stride qs s tail).make:=by
    dsimp only[rest]
    apply make_address_mpr
    simp only[block,List.length_ofFn]
   rw[rest_make,ih _ tail i bound ht']
   have tail_make:(tail i bound).make=(h (i+1) hi).make:=by
    dsimp only[tail,id]
    simp (disch := simp only[slotPrefix,List.getElem_cons_succ,Nat.mul_add,Nat.add_assoc]) only[
     make_metadata_mpr]
    apply make_metadata_mp
    · simp only[Nat.mul_add]
    · rfl
   exact congrFun (congrFun tail_make t) elapsed

end
end ExactFourierCircuits.UniformActualCalendarRectangleRegistry
