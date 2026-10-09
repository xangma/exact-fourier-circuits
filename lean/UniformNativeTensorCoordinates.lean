import UniformSmallAxesMachine
import OAI.Computability.FourierCircuit.PiTensor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeTensorCoordinates
open UniformCRTTraversalCycle (place decoded ordinalEquiv)
open UniformSelectedAxisFiberPreparation (radices lower upper)
open UniformAllTensorFibersCopyMachine (fibers native nativeEquiv)
open UniformTensorAddressMachine (address)
noncomputable section
open scoped BigOperators

theorem address_mod_dvd (P r j t R:ℕ) (hd:R∣P) : address P r j t%R=j%R := by
 simp only [address,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd,
  Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]
 exact Nat.mod_mod_of_dvd j hd

theorem address_div_supra (P r j t c:ℕ) (hp:0<P) (hr:0<r) (ht:t<r) :
 address P r j t/(P*r*c)=(j/P)/c := by
 rw [←Nat.div_div_eq_div_mul,←Nat.div_div_eq_div_mul,
  UniformTensorAddressMachine.address_quotient P r j t hp,
  Nat.add_mul_div_left _ _ hr,Nat.div_eq_of_lt ht,Nat.zero_add]

theorem decoded_address_other {a:ℕ} (r:Fin a→ℕ) (hr:∀i,0<r i)
 (i j:Fin a) (hne:j≠i) (fiber t:ℕ) (ht:t<r i) :
 decoded r (address (place r i.val) (r i) fiber t) j=
 decoded r (address (place r i.val) (r i) fiber 0) j := by
 have ne:j.val≠i.val:=by intro h;exact hne (Fin.ext h)
 rcases lt_or_gt_of_ne ne with low|high
 · have hd:place r j.val*r j∣place r i.val:=by
    rw [←UniformCRTTraversalCycle.place_succ r j]
    exact UniformCRTTraversalCycle.place_dvd r (by omega)
   unfold decoded
   rw [←Nat.mod_mul_right_div_self,←Nat.mod_mul_right_div_self,
    address_mod_dvd _ _ _ _ _ hd,address_mod_dvd _ _ _ _ _ hd]
 · have hd:place r i.val*r i∣place r j.val:=by
    rw [←UniformCRTTraversalCycle.place_succ r i]
    exact UniformCRTTraversalCycle.place_dvd r (by omega)
   obtain ⟨c,hc⟩:=hd
   unfold decoded
   rw [hc,address_div_supra _ _ _ _ c (UniformCRTTraversalCycle.place_pos r hr _) (hr i) ht,
    address_div_supra _ _ _ _ c (UniformCRTTraversalCycle.place_pos r hr _) (hr i) (hr i)]

/-- The physical strided address changes precisely one mixed-radix digit. -/
theorem ordinal_native_update (n:ℕ) (i:Fin (UniformInitialPreparation.ell n+1))
 (j:Fin (fibers n i)) (t:Fin (radices n i)) :
 ordinalEquiv n (nativeEquiv n i (j,t))=
 Function.update (ordinalEquiv n (nativeEquiv n i (j,⟨0,UniformSelectedCRT.radix_pos n i⟩))) i t := by
 funext k
 apply Fin.ext
 by_cases h:k=i
 · subst k
   simp only [Function.update_self]
   change decoded (radices n) (native n i j.val t.val) i=t.val
   exact UniformTensorAddressMachine.selected_digit n i j.val t.val t.isLt
 · rw [Function.update_of_ne h]
   change decoded (radices n) (native n i j.val t.val) k=
    decoded (radices n) (native n i j.val 0) k
   exact decoded_address_other (radices n) (UniformSelectedCRT.radix_pos n) i k h j.val t.val t.isLt

/-- Changing the local digit retains all spectators of an arbitrary native cell. -/
theorem ordinal_native_replace (n:ℕ) (i:Fin (UniformInitialPreparation.ell n+1))
 (z:Fin (UniformInitialPreparation.len n)) (t:Fin (radices n i)) :
 let p:Fin (fibers n i)×Fin (radices n i):=(nativeEquiv n i).symm z
 nativeEquiv n i (p.1,t)=(ordinalEquiv n).symm (Function.update (ordinalEquiv n z) i t) := by
 dsimp only
 let p:Fin (fibers n i)×Fin (radices n i):=(nativeEquiv n i).symm z
 have pe:nativeEquiv n i p=z:=(nativeEquiv n i).apply_symm_apply z
 apply (ordinalEquiv n).injective
 rw [Equiv.apply_symm_apply]
 change ordinalEquiv n (nativeEquiv n i (p.1,t))=Function.update (ordinalEquiv n z) i t
 have target:ordinalEquiv n z=Function.update
  (ordinalEquiv n (nativeEquiv n i (p.1,⟨0,UniformSelectedCRT.radix_pos n i⟩))) i p.2:=by
  calc
   _=ordinalEquiv n (nativeEquiv n i p):=congrArg (ordinalEquiv n) pe.symm
   _=_:=ordinal_native_update n i p.1 p.2
 calc
  _=Function.update (ordinalEquiv n (nativeEquiv n i (p.1,⟨0,UniformSelectedCRT.radix_pos n i⟩))) i t:=
   ordinal_native_update n i p.1 t
  _=_:=by rw [target,Function.update_idem]

theorem ordinal_native_digit (n:ℕ) (i:Fin (UniformInitialPreparation.ell n+1))
 (z:Fin (UniformInitialPreparation.len n)) :
 ((nativeEquiv n i).symm z).2=ordinalEquiv n z i := by
 let p:Fin (fibers n i)×Fin (radices n i):=(nativeEquiv n i).symm z
 have pe:nativeEquiv n i p=z:=(nativeEquiv n i).apply_symm_apply z
 have digit:ordinalEquiv n z i=p.2:=by
  calc
   _=ordinalEquiv n (nativeEquiv n i p) i:=by rw [pe]
   _=p.2:=by rw [ordinal_native_update,Function.update_self]
 exact digit.symm

/-- One physical fiber pass is exactly the corresponding mixed-radix digit DFT. -/
theorem axisTransform_digits (n:ℕ) (i:Fin (UniformInitialPreparation.ell n+1))
 (X:Fin (UniformInitialPreparation.len n)→ℂ) (z:Fin (UniformInitialPreparation.len n)) :
 UniformSmallAxesMachine.axisTransform i X z=
 ∑t:Fin (radices n i),OAI.ExactFourier.zeta (radices n i)^((ordinalEquiv n z i).val*t.val)*
  X ((ordinalEquiv n).symm (Function.update (ordinalEquiv n z) i t)) := by
 unfold UniformSmallAxesMachine.axisTransform
 apply Finset.sum_congr rfl
 intro t _
 rw [ordinal_native_digit,ordinal_native_replace]

end
end ExactFourierCircuits.UniformNativeTensorCoordinates
