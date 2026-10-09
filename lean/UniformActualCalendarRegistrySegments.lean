import UniformActualCalendarRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformGlobalCalendarDispatch
noncomputable section

lemma events_split (D stride tick:ℕ)(records:ℕ→ℕ×ℕ)(make:ℕ→ℕ→Event)(j a b:ℕ):
 events D stride tick records make j (a+b)=
 events D stride tick records make j a++events D stride tick records make (j+a) b:=by
 induction a generalizing j with
 | zero=>simp only[Nat.zero_add,events,List.nil_append,Nat.add_zero]
 | succ a ih=>
  rw[Nat.succ_add]
  simp only[events]
  split_ifs <;>rw[ih]
  · simp only[List.cons_append,Nat.add_assoc,Nat.add_comm 1]
  · simp only[Nat.add_assoc,Nat.add_comm 1]

lemma events_congr (D stride tick:ℕ)(a b:ℕ→ℕ×ℕ)(f g:ℕ→ℕ→Event)(j fuel:ℕ)
 (records : ∀ i, j ≤ i → i < j+fuel → a i=b i)
 (make : ∀ i, j ≤ i → i < j+fuel → ∀ elapsed, f i elapsed=g i elapsed):
 events D stride tick a f j fuel=events D stride tick b g j fuel:=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  have tail:=ih (j+1) (fun i lo hi=>records i (by omega) (by omega))
   (fun i lo hi=>make i (by omega) (by omega))
  simp only[events,records j le_rfl (by omega),make j le_rfl (by omega)]
  split_ifs
  · exact congrArg (List.cons _) tail
  · exact tail

lemma events_shift (D stride tick:ℕ)(records:ℕ→ℕ×ℕ)(make:ℕ→ℕ→Event)(offset j fuel:ℕ):
 events D stride tick records make (offset+j) fuel=
 events D stride tick (fun i=>records (offset+i)) (fun i=>make (offset+i)) j fuel:=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  simp only[events]
  split_ifs <;>rw[show offset+j+1=offset+(j+1) by omega,ih]

end
end ExactFourierCircuits.UniformActualCalendarRegistry
