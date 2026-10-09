import UniformDirectLeafForestExecution
import UniformLocalStoredRequestEndpoints
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCacheRectangleRetention
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformLocalCacheSlotConductorMachine UniformDirectLeafForestData

/-- The measured rectangle cache precedes the leaf cache. Only ordinary
interval separation is needed to preserve every actual rectangle Contents. -/
structure Before (c:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))(qs:List Request)
 (p:Parameters)(visits:List UniformLocalCacheTreeMachine.Visit):Prop where
 radix_eq:p.radix=radix n axisIndex
 permutation:p.start.permutation=(axis c n axisIndex).control+
  (3*radix n axisIndex+11)*slotPrefix n qs qs.length
 pool:p.start.pool=(axis c n axisIndex).pool+9*radix n axisIndex*slotPrefix n qs qs.length
 rows:p.start.rows+3 ≤ (axis c n axisIndex).control
 ranges:p.ranges+2*visits.length ≤ (axis c n axisIndex).control
 counts:UniformDirectLeafForestBoot.countHeader p+2 ≤ (axis c n axisIndex).control

lemma complete {c n axisIndex qs R T}(g:UniformLocalRequestGeometry.Geometry c n axisIndex qs R T)
 {p visits s u}(before:Before c n axisIndex qs p visits)
 (frame:UniformDirectLeafForestExecution.Frame p visits s u)
 (i:ℕ)(hi:i < qs.length)(old:Complete c n axisIndex qs R T g i hi s):
 Complete c n axisIndex qs R T g i hi u:=by
 intro t ht
 have order:slotPrefix n qs i+(t+1) ≤ slotPrefix n qs qs.length:=by
  have h:=prefix_mono n qs (show i+1 ≤ qs.length by omega) le_rfl
  rw[prefix_step n qs i hi] at h
  omega
 have natFit:=Nat.mul_le_mul_left (3*radix n axisIndex+11) order
 have scalarFit:=Nat.mul_le_mul_left (9*radix n axisIndex) order
 rw[Nat.mul_add,Nat.mul_add,Nat.mul_one] at natFit scalarFit
 obtain ⟨slot,hs,l,bl,contents⟩:=old t ht
 refine ⟨slot,hs,l,bl,contents.transport (cache_shift (g.slots i hi).cache t) ?_ ?_⟩
 · intro a lo high
   change (axis c n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
    (3*radix n axisIndex+11)*t ≤ a at lo
   change a < (axis c n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
    (3*radix n axisIndex+11)*t+(3*radix n axisIndex+11) at high
   apply frame.natBefore a
   · rw[before.permutation];omega
   · exact Or.inr (by have:=before.rows;omega)
   · exact Or.inr (by have:=before.ranges;omega)
   · exact Or.inr (by have:=before.counts;omega)
 · intro a lo high
   change (axis c n axisIndex).pool+9*radix n axisIndex*slotPrefix n qs i+
    9*radix n axisIndex*t ≤ a at lo
   change a < (axis c n axisIndex).pool+9*radix n axisIndex*slotPrefix n qs i+
    9*radix n axisIndex*t+9*radix n axisIndex at high
   exact frame.scalarOutside a (Or.inl (by rw[before.pool];omega))

lemma all_completed {c n axisIndex qs R T}(g:UniformLocalRequestGeometry.Geometry c n axisIndex qs R T)
 {p visits s u}(before:Before c n axisIndex qs p visits)
 (frame:UniformDirectLeafForestExecution.Frame p visits s u)
 (old:∀i (hi:i < qs.length),Complete c n axisIndex qs R T g i hi s):
 ∀i (hi:i < qs.length),Complete c n axisIndex qs R T g i hi u:=by
 intro i hi
 exact complete g before frame i hi (old i hi)
end ExactFourierCircuits.UniformActualCacheRectangleRetention
