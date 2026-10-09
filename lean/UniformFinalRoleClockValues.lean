import UniformFinalRoleAlpha
import UniformActualClockEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleClockValues
open UniformMachine UniformFinalRoleModel UniformFinalNumericJoin
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
lemma source {n:ℕ} (v:ℕ→Fin (V n)→Scalar) (s:State)
 (cells:∀i:Fin W,∀j:Fin (V n),s.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (v i.val j)):
 UniformActualClockEntry.Source n v s:=fun i hi j=>cells ⟨i,hi⟩ j
lemma prepared {n:ℕ} (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)):
 UniformActualClockEntry.Prepared (values x true AP):=fun i _ j=>UniformFinalRoleModel.prepared x AP i j
lemma generic_one {roles volume S:ℕ} (v:ℕ→Fin volume→Scalar) (f:Fin volume→ℂ) (s:State)
 (cells:∀r,r<roles→∀j:Fin volume,s.scalarHeap (S+r*volume+j.val)=some (v r j))
 (hr:1<roles) (value:∀j,(v 1 j).value=f j):NumericValues (S+volume) f s:=by
 intro j
 have h:=cells 1 hr j
 rw[Nat.one_mul] at h
 rw[h,Option.map_some,value j]
lemma generic_zero {roles volume S:ℕ} (v:ℕ→Fin volume→Scalar) (f:Fin volume→ℂ) (s:State)
 (cells:∀r,r<roles→∀j:Fin volume,s.scalarHeap (S+r*volume+j.val)=some (v r j))
 (hr:0<roles) (value:∀j,(v 0 j).value=f j):NumericValues S f s:=by
 intro j
 have h:=cells 0 hr j
 rw[Nat.zero_mul,Nat.add_zero] at h
 rw[h,Option.map_some,value j]
lemma kernel_numeric {n:ℕ} [NeZero (V n)] (x:Fin n→ℂ) (mode:Bool)
 (AP:Fin (V n)≃Fin (V n)) (s:State)
 (cells:UniformActualClockEntry.Source n (values x mode AP) s):
 NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP j)) s:=
 generic_one (roles:=W) (volume:=V n) (S:=2*UniformJointAllocation.slab c n) (values x mode AP) _ s cells UniformFinalRoleGeometry.roles_two
  (UniformFinalRoleModel.kernel_one AP mode x)
lemma data_numeric {n:ℕ} [NeZero (V n)] (x:Fin n→ℂ)
 (AP:Fin (V n)≃Fin (V n)) (s:State)
 (cells:UniformActualClockEntry.Source n (UniformFinalRoleAlpha.physical x AP) s):
 NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (AP j)) s:=
 generic_zero (roles:=W) (volume:=V n) (S:=2*UniformJointAllocation.slab c n) (UniformFinalRoleAlpha.physical x AP) _ s cells
  (by have:=UniformFinalRoleGeometry.roles_two;omega)
  (UniformFinalRoleAlpha.numeric_zero x AP)
end
end ExactFourierCircuits.UniformFinalRoleClockValues
