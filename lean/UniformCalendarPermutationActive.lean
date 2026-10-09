import UniformCalendarPermutationIndices

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPermutationActive
noncomputable section
open UniformLocalCacheTiming UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarPermutationIndices

/-- Occurrence-preserving transport of active indices through a genuine list permutation. -/
def activeEquiv {E F : List TimedEvent} (h:E.Perm F) (t:ℕ):ActiveIndex E t≃ActiveIndex F t where
 toFun i:=⟨indexEquiv h i.val,by rw[indexEquiv_get];exact i.property⟩
 invFun i:=⟨(indexEquiv h).symm i.val,by
  have eq:=indexEquiv_get h ((indexEquiv h).symm i.val)
  rw[Equiv.apply_symm_apply] at eq
  rw[←eq];exact i.property⟩
 left_inv i:=Subtype.ext ((indexEquiv h).symm_apply_apply i.val)
 right_inv i:=Subtype.ext ((indexEquiv h).apply_symm_apply i.val)
lemma activeEquiv_get {E F : List TimedEvent} (h:E.Perm F) (t:ℕ)(i:ActiveIndex E t):
 F.get (activeEquiv h t i).val=E.get i.val:=indexEquiv_get h i.val

end
end ExactFourierCircuits.UniformCalendarPermutationActive
