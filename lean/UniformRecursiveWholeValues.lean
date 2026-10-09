import UniformNativeSchedulePrefix
import UniformNativeHandlerSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveWholeValues
open UniformMachine UniformFixedNetwork UniformBinaryTensorCoordinates UniformNativeScheduleSemantics
open UniformNativeHandlerSemantics (arrayValues)
noncomputable section

lemma suffix_congr (k b:ℕ)(X Y:Fin (2^k)→Scalar)
 (h:(fun z=>(X z).value)=(fun z=>(Y z).value)):
 (fun z=>(UniformBinarySpectatorCMachine.transformed k b X z).value)=
 (fun z=>(UniformBinarySpectatorCMachine.transformed k b Y z).value):=by
 unfold UniformBinarySpectatorCMachine.transformed
 rw [applyAxes_values,applyAxes_values,h]

/-- Numeric prefix equality suffices even when real arithmetic has different
Scalar dependency flags from the explanatory prefix array. -/
theorem suffix_values (q rest:ℕ)(X Y:Fin W→Fin (2^(q*m+rest))→Scalar)
 (h:arrayValues q rest Y=interpret q rest instructions (arrayValues q rest X))(i:Fin W):
 (fun z=>(UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (Y i) z).value)=
 (physicalMatrix (q*m+rest)).mulVec (fun z=>(X i z).value):=by
 have lowValues:(fun z=>(Y i z).value)=
  (fun z=>(applyAxes (q*m+rest) ((List.finRange (q*m+rest)).take (q*m)) (X i) z).value):=by
  funext z
  have eq:=congrFun h (RoleWords.roleAddresses W (q*m+rest) (i,z))
  simp only [arrayValues,RoleWords.arrayValues_at] at eq
  exact eq.trans (congrFun (UniformNativeSchedulePrefix.interpret_prefix_values q rest X i) z)
 exact (suffix_congr _ _ _ _ lowValues).trans (UniformBinarySpectatorCMachine.prefix_suffix_values _ _ _)
end
end ExactFourierCircuits.UniformRecursiveWholeValues
