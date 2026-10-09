import UniformInverseMatchingFactorPool
import UniformGlobalDiagonalRowsMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly
noncomputable section
variable {B:ℕ}
/-- The physical translated forward table is an output of the genuine chunk
producer. This continuation prints its reversed, correctly negated coefficient
pointers and then prepares all nine factor lanes, charging every setup. -/
theorem execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (I:ℕ)
 (il:InverseLayout c l I) (x:Fin n → ℂ)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ) (orig s:State)
 (args:UniformForwardMatchingFactorPreparation.Header c orig)
 (generated:UniformForwardMatchingFactorPreparation.AfterTranslation c l ha he orig s)
 (sources:UniformMatchingConjugateLoadMachine.Sources c.chunk.height.K c.chunk.height.C
  c.negative c.chunk.height.P c.conjugates bank orig)
 (constants:UniformHadamardPairMachine.Constants orig)
 (ip:s.natReg 4460=I) (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedExecution program n x B s t u ∧t≤45*c.ambient+142*(rows c l ha he).length+37 ∧
 u.pc=192 ∧Result c l ha he I bank orig u ∧u.natReg 894=(rows c l ha he).length:=by
 obtain ⟨a,t,first,cost,ap,ready⟩:=inverse_execution c l ha he I il x orig s args generated ip pc wb
 obtain ⟨u,t',last,cost',up,result,count⟩:=factors_execution c l ha he I il x bank orig a args ready
  sources constants ap first.final_bound
 exact ⟨u,t+t',first.executes last,by omega,up,result,count⟩
def selectedValue (c:F.Config) (l:F.Layout c B) (ha he)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ)
 (i:Fin (rows c l ha he).length):ℂ:=
 -(reference c l ha he (reverseIndex c l ha he i)).eval bank
lemma Result.factor_values {c:F.Config} {l:F.Layout c B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he I bank s u) (i:Fin (rows c l ha he).length):
 UniformGlobalMatchingScaleMachine.FullFactorTable c.pool c.ambient
  ((rows c l ha he)[i.val]'i.isLt).dst ((rows c l ha he)[i.val]'i.isLt).src
  (selectedValue c l ha he bank i) u:=by
 have table:=h.factors.done i i.isLt
 rw[coefficient_value c l ha he bank i] at table
 exact table
lemma Result.pool_coefficients {c:F.Config} {l:F.Layout c B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he I bank s u) (lane:Fin 9):
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
def poolEntry (c:F.Config) (l:F.Layout c B)
 (ha:c.chunk.height.a≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (he:c.chunk.height.e≤UniformCrossHeightPreparationMachine.widthOf c.chunk.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ)
:UniformGlobalDiagonalRowsMachine.Entry where
 radix:=c.ambient
 positive:=by have:=l.extent;have:=l.chunk.radixPositive;omega
 pool:=c.pool
 value:=fun lane d=>UniformGlobalMatchingScaleBankBridge.nativeFactor
  (UniformGlobalMatchingScaleBankBridge.rowEdges (rows c l ha he) (rows_geometry c l ha he).2.1)
  (selectedValue c l ha he bank) lane d.val
lemma Result.tensor_pool {c:F.Config} {l:F.Layout c B} {ha he I}
 {bank:Fin (UniformToeplitzCrossDAG.bankSize c.chunk.height.K) → ℂ} {s u:State}
 (h:Result c l ha he I bank s u):
 UniformGlobalDiagonalRowsMachine.Pools [poolEntry c l ha he bank] u:=by
 intro a member lane j
 have eq:a=poolEntry c l ha he bank:=by simpa only[List.mem_singleton] using member
 subst a
 exact h.pool_coefficients lane j
end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
