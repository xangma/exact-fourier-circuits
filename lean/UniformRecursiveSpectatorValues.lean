import UniformRecursiveSpectatorFinish
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSpectatorValues
open UniformMachine UniformBinaryTensorCoordinates
noncomputable section

/-- Binary field operations depend on input values, while their conservative
dependency flags may differ. This transports numeric prefix semantics. -/
lemma applyAxes_values_congr (k:ℕ)(axes:List (Fin k))(v w:Fin (2^k)→Scalar)
 (eq:(fun z=>(v z).value)=(fun z=>(w z).value)):
 (fun z=>(applyAxes k axes v z).value)=(fun z=>(applyAxes k axes w z).value):=by
 rw [applyAxes_values,applyAxes_values,eq]

/-- A proved low-prefix value equality closes the numeric full tensor after
the executed spectator suffix; no equality of dependency flags is required. -/
theorem prefix_values_suffix (k b:ℕ)(input lowStage:Fin (2^k)→Scalar)
 (eq:(fun z=>(lowStage z).value)=
  (fun z=>(applyAxes k ((List.finRange k).take b) input z).value)):
 (fun z=>(UniformBinarySpectatorCMachine.transformed k b lowStage z).value)=
 (physicalMatrix k).mulVec (fun z=>(input z).value):=by
 have bridge:=applyAxes_values_congr k ((List.finRange k).drop b) lowStage
  (applyAxes k ((List.finRange k).take b) input) eq
 exact bridge.trans (UniformBinarySpectatorCMachine.prefix_suffix_values k b input)

end
end ExactFourierCircuits.UniformRecursiveSpectatorValues
