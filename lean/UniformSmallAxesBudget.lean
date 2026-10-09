import UniformSmallAxisFourierMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSmallAxesBudget
open UniformInitialPreparation (ell len)
open UniformSelectedAxisFiberPreparation (radices)
noncomputable section
open scoped BigOperators

def small (n T:ℕ) : Finset (Fin (ell n+1)) := Finset.univ.filter (fun i=>radices n i<T)

theorem odd_axis_index {n T:ℕ} (i:Fin (ell n+1)) (h:radices n i<T) (last:i.val≠ell n) : i.val<T := by
 let j:Fin (ell n):=⟨i.val,by have:=i.isLt;omega⟩
 have eq:i=j.castSucc:=Fin.ext rfl
 have low:=UniformWorkingLength.oddPrime_lower i.val
 rw [eq] at h
 simp only [radices,UniformCRTTraversalCycle.radices,UniformSelectedCRT.radices,Fin.snoc_castSucc] at h
 change UniformWorkingLength.oddPrime i.val<T at h
 omega

theorem small_card (n T:ℕ) : (small n T).card≤T+1 := by
 let f:{i // i∈small n T}→Fin (T+1):=fun i=>
  ⟨if i.val.val=ell n then T else i.val.val,by
   have hs:radices n i.val<T:=(Finset.mem_filter.mp i.property).2
   split_ifs with h
   · omega
   · have:=odd_axis_index i.val hs h;omega⟩
 have inj:Function.Injective f:=by
  intro i j eq
  have iv:radices n i.val<T:=(Finset.mem_filter.mp i.property).2
  have jv:radices n j.val<T:=(Finset.mem_filter.mp j.property).2
  have values:=congrArg Fin.val eq
  change (if i.val.val=ell n then T else i.val.val)=(if j.val.val=ell n then T else j.val.val) at values
  apply Subtype.ext
  apply Fin.ext
  by_cases hi:i.val.val=ell n <;> by_cases hj:j.val.val=ell n
  · omega
  · have:=odd_axis_index j.val jv hj;simp only [hi,hj,ite_true,ite_false] at values;omega
  · have:=odd_axis_index i.val iv hi;simp only [hi,hj,ite_true,ite_false] at values;omega
  · simpa only [hi,hj,ite_false] using values
 simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f inj

/-- Sum of the actual161 caller costs for every selected small axis. -/
theorem actual_small_axes_cost (n T:ℕ) :
 (∑i∈small n T,UniformSmallAxisFourierMachine.runtime n i)≤
  (T+1)*((8*T+96)*len n+14*ell n+50) := by
 calc
  _≤∑i∈small n T,((8*T+96)*len n+14*ell n+50):=by
    apply Finset.sum_le_sum
    intro i hi
    have hs:radices n i<T:=(Finset.mem_filter.mp hi).2
    have cost:=UniformSmallAxisFourierMachine.small_cost_bound i hs
    have idx:=i.isLt
    omega
  _=(small n T).card*((8*T+96)*len n+14*ell n+50):=by simp
  _≤(T+1)*((8*T+96)*len n+14*ell n+50):=Nat.mul_le_mul_right _ (small_card n T)
end
end ExactFourierCircuits.UniformSmallAxesBudget
