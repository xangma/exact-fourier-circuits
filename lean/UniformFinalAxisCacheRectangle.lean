import UniformActualCalendarGlobalEvents
import UniformAxisCacheContents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisCacheRectangle
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry UniformLocalCacheSlotConductorMachine
open UniformActualCalendarRegistry UniformActualCalendarRectangleRegistry
noncomputable section

variable {c:Constants}{n:ℕ}{j:Fin (ell n)}{qs:List Request}{R T:ℕ}
 (g:Geometry c n j qs R T){s:State}
 (all:∀i (hi:i<qs.length),Complete c n j qs R T g i hi s)

include g in
/-- Actual allocated ends, rather than the conservative three-slab bound. -/
lemma bounds (i:ℕ)(hi:i<qs.length)(t:ℕ)(ht:t<slotCount n qs[i].row):
 (Cursor.shifted (controller c n j qs i) t).pool+9*radix n j≤(axis c n j).endScalar ∧
 (Cursor.shifted (controller c n j qs i) t).cacheDirectory+7≤(axis c n j).endNat ∧
 (Cursor.shifted (controller c n j qs i) t).cachePermutation+radix n j≤(axis c n j).endNat:=by
 have next:=past_prefix n qs hi (Nat.le_refl qs.length) hi
 have cap:slotPrefix n qs i+t<UniformJointCacheExtent.capacity (radix n j):=by
  have:=g.capacity
  omega
 have fit:(slot (axis c n j) (slotPrefix n qs i+t)).abi+7≤(axis c n j).leafForward ∧
  (slot (axis c n j) (slotPrefix n qs i+t)).factor+9*radix n j≤(axis c n j).endScalar:=by
  unfold axis
  exact slot_fit _ _ _ _ cap
 have leaf:(axis c n j).leafForward≤(axis c n j).endNat:=by dsimp only[axis,axisBank];omega
 have top:=fit.1.trans leaf
 rw[controller,requestAt_eq qs i hi]
 change
  (axis c n j).pool+9*radix n j*slotPrefix n qs i+9*radix n j*t+9*radix n j≤(axis c n j).endScalar ∧
  (axis c n j).control+(3*radix n j+11)*slotPrefix n qs i+3*radix n j+4+(3*radix n j+11)*t+7≤(axis c n j).endNat ∧
  (axis c n j).control+(3*radix n j+11)*slotPrefix n qs i+(3*radix n j+11)*t+radix n j≤(axis c n j).endNat
 dsimp only[slot,axis_radix] at fit top
 simp only[Nat.mul_add] at fit top
 exact ⟨by omega,by omega,by omega⟩

def family (radixRoom:radix n j≤envelope c n)(i:ℕ)(hi:i<qs.length):
 Family (radix n j) (axis c n j).endScalar (axis c n j).endNat (envelope c n)
  (base c n j+(3*radix n j+11)*slotPrefix n qs i) (3*radix n j+11) (block n qs[i]) s where
 entry:=fun t=>by
  have ht:t.val<slotCount n qs[i].row:=by simpa only[block,List.length_ofFn] using t.isLt
  let d:=data g all i hi t.val ht
  have b:=bounds g i hi t.val ht
  have produced:=d.produced _ _ _ _ _ _ _ _ (show (controller c n j qs i).kind=0 from rfl)
   b.2.1 b.1 b.2.2 radixRoom
  apply Produced.cast produced rfl
  · change (axis c n j).control+(3*radix n j+11)*slotPrefix n qs i+3*radix n j+4+
     (3*radix n j+11)*t.val=base c n j+(3*radix n j+11)*slotPrefix n qs i+(3*radix n j+11)*t.val
    unfold base;omega
  · rw[block_get,controller,requestAt_eq qs i hi];rfl
  · rw[block_get]

def whole (radixRoom:radix n j≤envelope c n):
 Family (radix n j) (axis c n j).endScalar (axis c n j).endNat (envelope c n)
  (base c n j) (3*radix n j+11) (entries n qs) s:=
 assemble n _ _ _ _ _ _ qs s (fun i hi=>family g all radixRoom i hi)

lemma family_make (radixRoom:radix n j≤envelope c n)(i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)
 (ht:t<slotCount n qs[i].row):
 (family g all radixRoom i hi).make t elapsed=(data g all i hi t ht).event _ _ _ _ _ _ _ _ elapsed:=by
 simp only[Family.make,show t<(block n qs[i]).length by simpa only[block,List.length_ofFn] using ht,
  dite_true,family,Produced.cast,UniformActualCalendarRectangleProduced.Data.produced]

lemma whole_make (radixRoom:radix n j≤envelope c n)(i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)
 (ht:t<slotCount n qs[i].row):
 (whole g all radixRoom).make (slotPrefix n qs i+t) elapsed=(data g all i hi t ht).event _ _ _ _ _ _ _ _ elapsed:=by
 exact (assemble_make n _ _ _ _ _ _ qs s (fun i hi=>family g all radixRoom i hi) i hi t elapsed ht).trans
  (family_make g all radixRoom i hi t elapsed ht)

lemma entries_index (n:ℕ)(qs:List Request)(k:ℕ)(hk:k<(entries n qs).length):
 ∃i, ∃hi:i<qs.length, ∃t, ∃_ht:t<slotCount n qs[i].row,k=slotPrefix n qs i+t:=by
 induction qs generalizing k with
 | nil=>simp[entries] at hk
 | cons q qs ih=>
  by_cases low:k<slotCount n q.row
  · exact ⟨0,by simp,k,low,by simp only[slotPrefix,Nat.zero_add]⟩
  · have rest:k-slotCount n q.row<(entries n qs).length:=by
     have len:k<slotCount n q.row+(entries n qs).length:=by
      simpa only[entries,List.flatMap_cons,List.length_append,block,List.length_ofFn] using hk
     omega
    obtain ⟨i,hi,t,ht,eq⟩:=ih _ rest
    refine ⟨i+1,by simpa using Nat.succ_lt_succ hi,t,ht,?_⟩
    change k=slotCount n q.row+slotPrefix n qs i+t
    omega

lemma whole_make_eq (hn:0<n)(radixRoom:radix n j≤envelope c n):
 (whole g all radixRoom).make=(wholeFamily g all hn (Nat.le_refl (3*slab c n))
  (Nat.le_refl (3*slab c n)) radixRoom).make:=by
 funext k elapsed
 by_cases hk:k<(entries n qs).length
 · obtain ⟨i,hi,t,ht,rfl⟩:=entries_index n qs k hk
   rw[whole_make g all radixRoom i hi t elapsed ht,
    wholeFamily_make g all hn (Nat.le_refl _) (Nat.le_refl _) radixRoom i hi t elapsed ht]
 · simp only[Family.make,dite_eq_right hk]

end
end ExactFourierCircuits.UniformFinalAxisCacheRectangle
