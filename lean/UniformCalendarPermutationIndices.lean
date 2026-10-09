import UniformCalendarIntervalPartition
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPermutationIndices
noncomputable section

/-- A list permutation preserves occurrences, even when values repeat. -/
theorem exists_index_equiv {α : Type} {xs ys : List α} (h : xs.Perm ys) :
 ∃e : Fin xs.length≃Fin ys.length,∀i,ys.get (e i)=xs.get i:=by
 induction h with
 | nil=>exact ⟨Equiv.refl _,fun _=>rfl⟩
 | @cons a xs ys h ih=>
  obtain ⟨e,eq⟩:=ih
  let f:Fin (a::xs).length≃Fin (a::ys).length:=
   (finSuccEquiv xs.length).trans ((Equiv.optionCongr e).trans (finSuccEquiv ys.length).symm)
  refine ⟨f,?_⟩
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [f]
  · simpa [f] using eq j
 | swap a b xs=>
  refine ⟨Equiv.swap 0 1,?_⟩
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp
    · have h0:k.succ.succ≠(0:Fin (b::a::xs).length):=by
       intro eq;have:=congrArg Fin.val eq;simp at this
      have h1:k.succ.succ≠(1:Fin (b::a::xs).length):=by
       intro eq;have:=congrArg Fin.val eq;simp at this
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
 | trans h1 h2 ih1 ih2=>
  obtain ⟨e,he⟩:=ih1
  obtain ⟨f,hf⟩:=ih2
  exact ⟨e.trans f,fun i=>(hf (e i)).trans (he i)⟩

def indexEquiv {α : Type} {xs ys : List α} (h : xs.Perm ys) : Fin xs.length≃Fin ys.length:=
 Classical.choose (exists_index_equiv h)
lemma indexEquiv_get {α : Type} {xs ys : List α} (h : xs.Perm ys) (i : Fin xs.length):
 ys.get (indexEquiv h i)=xs.get i:=Classical.choose_spec (exists_index_equiv h) i

end
end ExactFourierCircuits.UniformCalendarPermutationIndices
