import DFTModelSavingNativeSmallBilling
import DFTModelSavingNativeBilledPrintedBody
import UniformRecursiveReserve

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, pp.11–12. This is the source-facing contract for the
root call of the fixed saving network, including its charged final halt.
It is a component contract, not the outer DFT compiler. -/
namespace ExactFourierCircuits.DFTModelSavingNativeRoot
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine DFTModelAdmissibilityControl DFTModelAffine
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address threshold seedLength unitLength
  seedPrinterLength unitPrinterLength size)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
abbrev W := UniformRecursiveSelfCallMachine.W
noncomputable abbrev cost := UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
noncomputable section
attribute [local irreducible] P.program P.address P.size DFTModelSavingProgram.program

structure Result (n B k A F K : ℕ) (x : Fin n→ℂ) (s s0 u u0 : State) (ticks : ℕ)
    (input input0 output output0 : Fin W→Fin (2^k)→Scalar) : Prop where
  actual : BoundedExecution P.program n x B s ticks u
  baseline : BoundedExecution P.program n (fun _=>0) B s0 ticks u0
  matched : StateMatch u u0
  pc : u.pc=P.address .halt
  pc0 : u0.pc=P.address .halt
  data : Present A W (2^k) output u
  data0 : Present A W (2^k) output0 u0
  values : ∀i,(fun z=>(output i z).value)=
    (UniformBinaryTensorCoordinates.physicalMatrix k).mulVec (fun z=>(input i z).value)
  values0 : ∀i,(fun z=>(output0 i z).value)=
    (UniformBinaryTensorCoordinates.physicalMatrix k).mulVec (fun z=>(input0 i z).value)
  natHeap : ∀z,z<F→u.natHeap z=s.natHeap z
  natHeap0 : ∀z,z<F→u0.natHeap z=s0.natHeap z
  scalarHeap : ∀z,z<F→(z<A∨A+W*2^k≤z)→u.scalarHeap z=s.scalarHeap z
  scalarHeap0 : ∀z,z<F→(z<A∨A+W*2^k≤z)→u0.scalarHeap z=s0.scalarHeap z
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  roots : u.rootOrders=s.rootOrders
  roots0 : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  outputs0 : u0.outputs=s0.outputs
  compiled : (run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).val=
    paired output output0
  work : (run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).work≤K*ticks

/-- The source halt is an instruction and contributes one actual tick. -/
lemma halt (n B : ℕ) (x : Fin n→ℂ) (u : State) (pc : u.pc=P.address .halt)
    (bound : WordBound B u) : BoundedExecution P.program n x B u 1 u := by
  exact UniformRecursiveSpectatorFinish.halt_generic P.program (P.address .halt) n B x u
    UniformRecursiveSpectatorFinish.halt_code pc bound

end
end ExactFourierCircuits.DFTModelSavingNativeRoot
