import UniformForwardMatchingFactorExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine
noncomputable section
variable {B:ℕ} {c:Config} {l:Layout c B} {ha he}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
/-- The coefficient is the actual selected typed forward leaf, not an arbitrary
rational leaf routed to a normalization slot. -/
def selectedValue (c:Config) (l:Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ)
 (i:Fin (rows c l ha he).length):ℂ:=
 (UniformMatchingCoefficientValueBridge.selectedReference c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he) (selectedIndex c l ha he i)).eval bank
lemma Result.factor_values (h:Result c l ha he bank s u) (i:Fin (rows c l ha he).length):
 UniformGlobalMatchingScaleMachine.FullFactorTable c.pool c.ambient
  ((rows c l ha he)[i.val]'i.isLt).dst ((rows c l ha he)[i.val]'i.isLt).src
  (selectedValue c l ha he bank i) u:=by
 have table:=h.factors.done i i.isLt
 rw[coefficient_value c l ha he bank i] at table
 exact table
/-- All nine native diagonal banks, including every singleton identity, are
read from the physically generated pool. -/
lemma Result.pool_coefficients (h:Result c l ha he bank s u) (lane:Fin 9):
 UniformTensorDiagonalBankMachine.Coefficients c.ambient (c.pool+lane.val*c.ambient)
 (fun d=>UniformGlobalMatchingScaleBankBridge.nativeFactor
  (UniformGlobalMatchingScaleBankBridge.rowEdges (rows c l ha he) (rows_geometry c l ha he).2.1)
  (selectedValue c l ha he bank) lane d.val) u:=by
 have ready:=UniformGlobalMatchingScaleBankBridge.pool_coefficients
  (rows_geometry c l ha he).2.1 (rows_geometry c l ha he).2.2 h.factors lane
 have eq:(fun i=>UniformMatchingConjugateLoadMachine.value c.chunk.height.K bank (coefficient c l ha he i))=
  selectedValue c l ha he bank:=by
  funext i;exact coefficient_value c l ha he bank i
 rw[eq] at ready
 exact ready
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
