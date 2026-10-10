import DFTModelSavingNativeLargeChild
import DFTModelSavingNativeBilledPrintedBody
import DFTModelSavingNativeLargePrefix
import DFTModelSavingClosedLarge
import DFTModelSavingNativeSmallBilledChild
import UniformRecursiveTypedLargeCost

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeLargeBilledChild
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformRecursiveNodePreparation
open UniformRecursiveTypedBody DFTModelAdmissibilityControl DFTModelAffine
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelRecursiveScalarSource (paired)
open DFTModelSavingResidualNativeGroup (ChildResult)
namespace P
export UniformRecursiveSavingProgram (program address threshold seedLength unitLength
  seedPrinterLength unitPrinterLength size)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable abbrev cost := UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
noncomputable section
attribute [local irreducible] P.program P.threshold P.seedLength P.unitLength
  P.seedPrinterLength P.unitPrinterLength P.size R.reserve DFTModelSavingProgram.program
  DFTModelSavingNativeSequence.typedFold

/-- The full positive-depth large source execution, with the actual fixed
printers and all chronological records. Only genuine strictly smaller paired
runs of the same program enter as the internal induction hypothesis. -/
theorem execution (n B A F q rest stack stackTop depth K : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (input input0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies (q*m+rest) n B R.reserve stack stackTop K K cost x Complex.I
      (DFTModelSavingSelfCall.evaluate (q*m+rest-1)))
    (cap : DFTModelSavingCost.nativeWorkFactor ≤ K) (same : StateMatch s s0) (large : P.threshold ≤ q*m+rest)
    (qp : 1 ≤ q) (rp : rest < m) (smaller : q < q*m+rest)
    (pc : s.pc=0) (bits : s.natReg 4120=q*m+rest) (base : s.natReg 4121=A)
    (size : s.natReg 4122=2^(q*m+rest)) (frontier : s.natReg 4123=F)
    (sp : s.natReg 4150=stack) (dp : s.natReg 4151=depth)
    (data : Present A W (2^(q*m+rest)) input s) (data0 : Present A W (2^(q*m+rest)) input0 s0)
    (positive : 1 ≤ depth) (heapBase : 3 ≤ A) (extent : A+W*2^(q*m+rest) ≤ F)
    (stackRoom : stack+34*(depth+(q*m+rest)+1) ≤ stackTop) (stackEnd : stackTop ≤ F)
    (code : P.program.length ≤ B) (room : F+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
    (square : (2^(q*m+rest))^2 ≤ B) (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 ticks,
      ChildResult n B (q*m+rest) A F stack stackTop depth cost x input s u ticks ∧
      ChildResult n B (q*m+rest) A F stack stackTop depth cost (fun _=>0) input0 s0 u0 ticks ∧
      StateMatch u u0 ∧
      (∀(i : Fin W)(j : Fin (2^(q*m+rest))),
        (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).val.look
          (i.val*2^(q*m+rest)+j.val) Tagged.blank=
          encodePaired ((u.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero)
            ((u0.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero)) ∧
      (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).work ≤ K*ticks := by
  obtain ⟨t,t0,a,a0,sourceRun,sourceRun0,matched,ap,ap0,parent,parent0,ptr,storedMeta,ptr0,storedMeta0,printed,printed0,
    unit,unit0,present,present0,ct,ct0,ef,ef0,nf,nf0,geometry⟩:=DFTModelSavingNativeLargePrefix.execution
      n B A F P.seedLength P.unitLength q rest stack stackTop depth x s s0 input input0 rfl rfl same large qp rp smaller
      pc bits base size frontier sp dp data data0 positive heapBase extent stackRoom stackEnd code room square constants bound
  have metadata:a.natHeap (workBase F P.seedLength P.unitLength-1)=some (F+P.seedLength):=storedMeta
  have mainEnd:F+P.seedLength ≤ workBase F P.seedLength P.unitLength-6:=by unfold workBase unitBase;omega
  have unitEnd:unitBase F P.seedLength+P.unitLength ≤ workBase F P.seedLength P.unitLength-6:=by unfold workBase;omega
  obtain ⟨u,u0,time,g,g0,body,billing⟩:=DFTModelSavingNativeBilledPrintedBody.execution
    n B F (unitBase F P.seedLength) A (workBase F P.seedLength P.unitLength) F q rest stack depth stackTop R.reserve K
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) cost x (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) a a0 input input0 childIH cap (by omega) geometry matched ap parent metadata
      printed present present0 ptr unit mainEnd unitEnd stackEnd (by unfold unitBase;omega)
      (by unfold unitBase;omega) (by unfold workBase unitBase;omega) ct sourceRun.final_bound
  obtain ⟨actual,zero,matched,pairedCode⟩:=DFTModelSavingNativeLargeChild.finish
    n B A F q rest stack stackTop depth x s s0 t t0 a a0 u u0 input input0 g g0 time
      large qp rp positive sourceRun sourceRun0 ef ef0 nf nf0 body
  refine ⟨u,u0,_,actual,zero,matched,pairedCode,?_⟩
  have closed:=(DFTModelSavingClosedLarge.program_run (q*m+rest) large Complex.I (paired input input0)).2
  change (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).work=
    (Code.run DFTModelSavingProgram.large (DFTModelSavingSelfCall.evaluate (q*m+rest-1))
      ((q*m+rest,Complex.I),paired input input0)).work+17 at closed
  rw [closed]
  omega

end
end ExactFourierCircuits.DFTModelSavingNativeLargeBilledChild
