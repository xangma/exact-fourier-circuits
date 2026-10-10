import DFTModelSavingNativeRootSmall
import DFTModelSavingNativeRootLarge

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, pp.11–12. The root of the same fixed saving program
allocates its stack, executes the chronological recursive network, and halts.
The one compiled paired computation is billed against those actual ticks.
Outer DFT stages, cache provenance and the global clock are separate. -/
namespace ExactFourierCircuits.DFTModelSavingNativeRoot
open UniformMachine DFTModelAdmissibilityControl
open UniformFixedNetworkShearChildMachine (Present)
noncomputable section
attribute [local irreducible] P.program P.threshold R.reserve

/-- All exponents, including the finite base and zero, with no smaller-body
or billing callback. The word/space and initialized-entry conditions are
ordinary source caller obligations. -/
theorem execution (n B k A F K : ℕ) (x : Fin n→ℂ) (s s0 : State)
    (input input0 : Fin W→Fin (2^k)→Scalar)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 4120=k)
    (base : s.natReg 4121=A) (size : s.natReg 4122=2^k) (frontier : s.natReg 4123=F)
    (dp : s.natReg 4151=0) (data : Present A W (2^k) input s) (data0 : Present A W (2^k) input0 s0)
    (heapBase : 3≤A) (extent : A+W*2^k≤F) (code : P.program.length≤B)
    (room : F+34*(k+1)+R.reserve*(k+1)*2^k≤B) (square : (2^k)^2≤B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 ticks output output0,Result n B k A F K x s s0 u u0 ticks input input0 output output0 := by
  by_cases small:k<P.threshold
  · exact small_execution n B k A F K x s s0 input input0 cap same pc bits base size frontier dp small
      data data0 heapBase extent code room constants bound
  · have large:P.threshold≤k:=by omega
    obtain ⟨qp,qlt,rp,form⟩:=UniformRecursiveSavingExecution.recursive_geometry k large
    generalize hq:k/ExplicitSeedBudget.m=q at qp qlt form
    generalize hr:k%ExplicitSeedBudget.m=rest at rp form
    have decomposition:k=q*UniformFixedNetwork.m+rest:=form
    clear form
    cases decomposition
    exact large_execution n B A F q rest K x s s0 input input0 cap same large qp rp qlt pc bits base size
      frontier dp data data0 heapBase extent code room square constants bound

end
end ExactFourierCircuits.DFTModelSavingNativeRoot
