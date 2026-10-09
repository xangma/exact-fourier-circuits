import UniformForwardMatchingFactorValues
import UniformGlobalDiagonalRowsMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine
noncomputable section
variable {B:ℕ}
lemma Layout.ambientPositive {c:Config} (l:Layout c B):0<c.ambient:=by
 have:=l.extent;have:=l.chunk.radixPositive;omega
/-- A retained directory entry contains the actual selected forward coefficients
at translated endpoints. It is suitable for the real49→81 tensor consumer. -/
def poolEntry (c:Config) (l:Layout c B)
 (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ)
:UniformGlobalDiagonalRowsMachine.Entry where
 radix:=c.ambient
 positive:=l.ambientPositive
 pool:=c.pool
 value:=fun lane d=>UniformGlobalMatchingScaleBankBridge.nativeFactor
  (UniformGlobalMatchingScaleBankBridge.rowEdges (rows c l ha he) (rows_geometry c l ha he).2.1)
  (selectedValue c l ha he bank) lane d.val
lemma Result.tensor_pool {c:Config} {l:Layout c B} {ha he}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he bank s u):
 UniformGlobalDiagonalRowsMachine.Pools [poolEntry c l ha he bank] u:=by
 intro a member lane j
 have eq:a=poolEntry c l ha he bank:=by simpa only[List.mem_singleton] using member
 subst a
 exact h.pool_coefficients lane j
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
