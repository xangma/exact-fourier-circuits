import UniformNativeScheduleSemantics
import UniformPhysicalTensorSplit
import UniformNativeResidualSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeSchedulePrefix
open OAI.ExactFourier UniformFixedNetwork UniformNativeScheduleSemantics
open UniformBinaryTensorCoordinates UniformNativeCopiedInverse
noncomputable section

/-- The exact typed record interpreter gives the same physical scalar values
as the real low-axis prefix, independently for every arbitrary W role. -/
theorem interpret_prefix_values (q r : ℕ)
 (X : Fin W→Fin (2^(q*m+r))→UniformMachine.Scalar) (i : Fin W) :
 (fun z => interpret q r instructions
  (RoleWords.arrayValues (q*m+r) (fun j a => (X j a).value))
  (RoleWords.roleAddresses W (q*m+r) (i,z)))=
 (fun z => (applyAxes (q*m+r) ((List.finRange (q*m+r)).take (q*m)) (X i) z).value) := by
 funext z
 obtain ⟨⟨s,z⟩,rfl⟩ := (spectatorSplit (q*m) r).symm.surjective z
 rw [interpret_array]
 have prefixValues := congrFun (UniformPhysicalTensorSplit.low_prefix_values (q*m) r (X i))
  ((spectatorSplit (q*m) r).symm (s,z))
 rw [UniformNativeResidualSemantics.spectator_array] at prefixValues
 exact prefixValues.symm

end
end ExactFourierCircuits.UniformNativeSchedulePrefix
