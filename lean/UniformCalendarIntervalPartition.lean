import UniformRegistryActiveEnumeration

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarIntervalPartition
noncomputable section

def prefixDuration (ds : List ℕ) (j : ℕ) : ℕ:=(ds.take j).sum

/-- Prefix intervals partition the actual sequential duration, including empty
zero-duration components. The selected component is unique. -/
theorem partition (ds : List ℕ) (elapsed : ℕ) (bound : elapsed < ds.sum) :
 ∃!j:Fin ds.length,prefixDuration ds j.val ≤ elapsed ∧ elapsed < prefixDuration ds j.val+ds.get j:=by
 induction ds generalizing elapsed with
 | nil=>simp at bound
 | cons d ds ih=>
  by_cases first : elapsed < d
  · refine ⟨0,?_,?_⟩
    · simpa only[prefixDuration,Fin.val_zero,List.take_zero,List.sum_nil,List.get_cons_zero,Nat.zero_add]
       using And.intro (Nat.zero_le elapsed) first
    · intro i hi
      by_cases zero:i.val = 0
      · exact Fin.ext zero
      · let j:Fin ds.length:=⟨i.val-1,by have:=i.isLt;simp only[List.length_cons] at this;omega⟩
        have eq:i=j.succ:=Fin.ext (by simp only[j,Fin.val_succ];omega)
        rw[eq] at hi
        simp only[prefixDuration,Fin.val_succ,List.take_succ_cons,List.sum_cons] at hi
        omega
  · have rest:elapsed-d<ds.sum:=by simp only[List.sum_cons] at bound;omega
    obtain ⟨j,hj,unique⟩:=ih (elapsed-d) rest
    refine ⟨j.succ,?_,?_⟩
    · simp only[prefixDuration,Fin.val_succ,List.take_succ_cons,List.sum_cons,
       List.get_eq_getElem,List.getElem_cons_succ] at hj ⊢
      omega
    · intro i hi
      by_cases zero:i.val = 0
      · have eq:i=0:=Fin.ext zero
        rw[eq] at hi
        simp only[prefixDuration,Fin.val_zero,List.take_zero,List.sum_nil,List.get_cons_zero,Nat.zero_add] at hi
        omega
      · let k:Fin ds.length:=⟨i.val-1,by have:=i.isLt;simp only[List.length_cons] at this;omega⟩
        have eq:i=k.succ:=Fin.ext (by simp only[k,Fin.val_succ];omega)
        rw[eq] at hi ⊢
        apply congrArg Fin.succ
        apply unique k
        simp only[prefixDuration,Fin.val_succ,List.take_succ_cons,List.sum_cons,
         List.get_eq_getElem,List.getElem_cons_succ] at hi ⊢
        omega

lemma before_sum (ds : List ℕ) (i : Fin ds.length) :
 prefixDuration ds i.val+ds.get i≤ds.sum:=by
 have eq:prefixDuration ds i.val+ds.get i=prefixDuration ds (i.val+1):=by
  unfold prefixDuration
  rw[List.take_succ_eq_append_getElem i.isLt,List.sum_append]
  rfl
 rw[eq]
 exact (List.take_sublist _ _).sum_le_sum (fun a _=>Nat.zero_le a)

end
end ExactFourierCircuits.UniformCalendarIntervalPartition
