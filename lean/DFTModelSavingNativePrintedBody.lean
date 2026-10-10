import DFTModelSavingNativeWholeSchedule
import DFTModelSavingNativeTerminal
import UniformRecursivePrintedBody

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.4, Proposition 2.4, p.10; §2.6, Theorem 2.6, pp.11–12.
The actual printed fixed network, padding and spectator suffix form one
continuous source execution and one typed paired computation. -/
namespace ExactFourierCircuits.DFTModelSavingNativePrintedBody
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingBinarySuffix.program

structure Result (n B T U A F H q rest stack depth stackTop : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (h : Handler ChildPort)
    (s s0 u u0 : State) (time : ℕ)
    (f f0 g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop where
  actual : BoundedRuns P.program n x B s time u
  baseline : BoundedRuns P.program n (fun _=>0) B s0 time u0
  matched : StateMatch u u0
  pc : u.pc=(if depth=0 then P.address .halt else P.address .returnSite)
  pc0 : u0.pc=(if depth=0 then P.address .halt else P.address .returnSite)
  data : Present A W (2^(q*m+rest)) g u
  data0 : Present A W (2^(q*m+rest)) g0 u0
  values : ∀i,(fun z=>(g i z).value)=
    (UniformBinaryTensorCoordinates.physicalMatrix (q*m+rest)).mulVec (fun z=>(f i z).value)
  values0 : ∀i,(fun z=>(g0 i z).value)=
    (UniformBinaryTensorCoordinates.physicalMatrix (q*m+rest)).mulVec (fun z=>(f0 i z).value)
  stackValue : u.natReg 4150=stack
  zeroStack : u0.natReg 4150=stack
  depthValue : u.natReg 4151=depth
  zeroDepth : u0.natReg 4151=depth
  natHeap : ∀z,z<H→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z
  natHeap0 : ∀z,z<H→(z<stack+34*depth∨stackTop≤z)→u0.natHeap z=s0.natHeap z
  scalarHeap : ∀z,z<F→(z<A∨A+W*2^(q*m+rest)≤z)→u.scalarHeap z=s.scalarHeap z
  scalarHeap0 : ∀z,z<F→(z<A∨A+W*2^(q*m+rest)≤z)→u0.scalarHeap z=s0.scalarHeap z
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  roots : u.rootOrders=s.rootOrders
  roots0 : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  outputs0 : u0.outputs=s0.outputs
  prefixEvidence : ∃t t0 prefixTicks middle middle0,
    DFTModelSavingNativeWholeSchedule.Result n B T U A F H q rest stack depth stackTop
      cost x Complex.I h s s0 t t0 prefixTicks f f0 middle middle0 ∧
    time=prefixTicks+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) ∧
    BoundedRuns P.program n x B t
      (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) u ∧
    BoundedRuns P.program n (fun _=>0) B t0
      (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) u0
  time_bound : time≤UniformRecursivePrintedBody.bodyTicks q rest cost
  code : (run DFTModelSavingBinarySuffix.program
    (q*m,DFTModelSavingNativeSequence.typedFold q rest Complex.I h instructions f f0)).val=
      ((q*m+rest,Complex.I),paired g g0)

/-- Finish a specific already-constructed source prefix. The cost proof can
reuse that same witness and its measured duration, rather than choose another
execution of the complete network. -/
theorem finish (n B T U A F H q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (t t0 : State) (first : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (body : DFTModelSavingNativeWholeSchedule.Result n B T U A F H q rest stack depth stackTop
      cost x Complex.I h s s0 t t0 first f f0 g g0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (metadata : s.natHeap (F-1)=some (T+P.seedLength)) :
    ∃u u0 final final0,Result n B T U A F H q rest stack depth stackTop cost x h
      s s0 u u0
        (first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20))
        f f0 final final0 := by
  have stored:t.natHeap (F-1)=some (T+P.seedLength):=body.metadata.trans metadata
  have extent:A+W*2^(q*m+rest)≤B:=geometry.arrayEnd.trans (by have z:=geometry.poolEnd;omega)
  obtain ⟨u,u0,last,last0,matched,up,up0,out,out0,frame,frame0,cu,cu0,code⟩:=
    DFTModelSavingNativeTerminal.execution n B q rest A F (T+P.seedLength) (T+P.seedLength)
      stack depth x t t0 g g0 body.matched body.pc body.parent stored (by omega)
      body.data body.data0 geometry.positive geometry.base extent body.constants
      body.actual.final_bound geometry.code
  let final:Fin W→Fin (2^(q*m+rest))→Scalar:=
    fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (g i)
  let final0:Fin W→Fin (2^(q*m+rest))→Scalar:=
    fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (g0 i)
  refine ⟨u,u0,final,final0,?_⟩
  refine {
    actual:=body.actual.trans last,baseline:=body.baseline.trans last0,matched:=matched,
    pc:=up,pc0:=up0,data:=out,data0:=out0,
    values:=UniformRecursiveWholeValues.suffix_values q rest f g body.values,
    values0:=UniformRecursiveWholeValues.suffix_values q rest f0 g0 body.values0,
    stackValue:=frame.stack.trans body.parent.stack,zeroStack:=frame0.stack.trans body.parent0.stack,
    depthValue:=frame.depth.trans body.parent.depth,zeroDepth:=frame0.depth.trans body.parent0.depth,
    natHeap:=?_,natHeap0:=?_,scalarHeap:=?_,scalarHeap0:=?_,constants:=cu,constants0:=cu0,
    roots:=frame.roots.trans body.roots,roots0:=frame0.roots.trans body.roots0,
    outputs:=frame.outputs.trans body.outputs,outputs0:=frame0.outputs.trans body.outputs0,
    prefixEvidence:=⟨t,t0,first,g,g0,body,rfl,last,last0⟩,
    time_bound:=Nat.add_le_add_right body.time_bound _,code:=?_}
  · intro z hz away;exact (congrFun frame.natHeap z).trans (body.natHeap z hz away)
  · intro z hz away;exact (congrFun frame0.natHeap z).trans (body.natHeap0 z hz away)
  · intro z hz away;exact (frame.scalarHeap z away).trans (body.scalarHeap z hz away)
  · intro z hz away;exact (frame0.scalarHeap z away).trans (body.scalarHeap0 z hz away)
  · rw [body.code]
    exact code

/-- The concrete entry discharges the whole-prefix obligation through the
actual printed schedule and its smaller-child induction hypothesis. -/
theorem execution (n B T U A F H q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies
      (q*m+rest) n B reserve stack stackTop cost x Complex.I h)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some (T+P.seedLength))
    (printed : PrintedRecords T (scheduleRecords q) s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (unitPointer : s.natHeap (F-2)=some U)
    (unitPrinted : Printed U (P.unitRecord.withColumns q).data s)
    (mainEnd : T+P.seedLength≤F-6) (unitEnd : U+P.unitLength≤F-6)
    (stackEnd : stackTop≤T) (unitAbove : stackTop≤U)
    (floorUnit : H≤U) (floorWork : H≤F-6)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 time g g0,Result n B T U A F H q rest stack depth stackTop cost x h
      s s0 u u0 time f f0 g g0 := by
  obtain ⟨t,t0,first,g,g0,body⟩:=DFTModelSavingNativeWholeSchedule.execution
    n B T U A F H q rest stack depth stackTop reserve cost x Complex.I h s s0 f f0 childIH
      geometry same pc parent metadata printed data data0 unitPointer unitPrinted mainEnd unitEnd
      stackEnd unitAbove floorUnit floorWork constants bound
  obtain ⟨u,u0,final,final0,result⟩:=finish n B T U A F H q rest stack depth stackTop reserve
    cost x h s s0 f f0 t t0 first g g0 body geometry metadata
  exact ⟨u,u0,first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20),
    final,final0,result⟩

end
end ExactFourierCircuits.DFTModelSavingNativePrintedBody
