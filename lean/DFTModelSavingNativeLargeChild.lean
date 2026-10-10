import DFTModelSavingNativePrintedBody
import DFTModelSavingNativeLargePrefix
import DFTModelSavingClosedLarge
import DFTModelSavingNativeSmallBilledChild
import UniformRecursiveTypedLargeCost

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeLargeChild
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

lemma cost_fit (q rest : ℕ) (large : P.threshold ≤ q*m+rest) (qp : 1 ≤ q) (rp : rest < m) :
    4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+
      UniformRecursivePrintedBody.bodyTicks q rest cost ≤ cost (q*m+rest) := by
  have actualLarge:UniformRecursiveRuntimeBridge.actualThreshold ≤ q*m+rest:=by
    unfold UniformRecursiveRuntimeBridge.actualThreshold
    unfold UniformRecursiveSavingProgram.threshold at large
    exact large
  have h:=UniformRecursiveTypedLargeCost.large_node_bound q rest qp rp actualLarge
  change 20+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)+
    UniformRecursivePrintedBody.bodyTicks q rest cost ≤ cost (q*m+rest) at h
  omega

/-- Package an actual large runPrefix and the actual paired printed-body witness.
This helper retains the source witnesses so measured billing can use the same
runs rather than choosing a second execution. -/
theorem finish (n B A F q rest stack stackTop depth : ℕ) (x : Fin n→ℂ)
    (s s0 t t0 a a0 u u0 : State) (input input0 output output0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (time : ℕ) (large : P.threshold ≤ q*m+rest) (qp : 1 ≤ q) (rp : rest < m) (positive : 1 ≤ depth)
    (runPrefix : BoundedRuns P.program n x B s
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) a)
    (runPrefix0 : BoundedRuns P.program n (fun _=>0) B s0
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) a0)
    (entryFrame : UniformRecursiveSavingExecution.EntryFrame s t)
    (entryFrame0 : UniformRecursiveSavingExecution.EntryFrame s0 t0)
    (nodeFrame : DFTModelSavingNativeNode.Frame F (workBase F P.seedLength P.unitLength) t a)
    (nodeFrame0 : DFTModelSavingNativeNode.Frame F (workBase F P.seedLength P.unitLength) t0 a0)
    (body : DFTModelSavingNativePrintedBody.Result n B F (unitBase F P.seedLength) A
      (workBase F P.seedLength P.unitLength) F q rest stack depth stackTop cost x
      (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) a a0 u u0 time input input0 output output0) :
    ChildResult n B (q*m+rest) A F stack stackTop depth cost x input s u
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+time) ∧
    ChildResult n B (q*m+rest) A F stack stackTop depth cost (fun _=>0) input0 s0 u0
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+time) ∧
    StateMatch u u0 ∧
    ∀(i : Fin W)(j : Fin (2^(q*m+rest))),
      (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).val.look
        (i.val*2^(q*m+rest)+j.val) Tagged.blank=
        encodePaired ((u.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero)
          ((u0.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero) := by
  have nonzero:depth≠0:=by omega
  have up:u.pc=P.address .returnSite:=by simpa only [ite_eq_right nonzero] using body.pc
  have up0:u0.pc=P.address .returnSite:=by simpa only [ite_eq_right nonzero] using body.pc0
  have workFloor:F ≤ workBase F P.seedLength P.unitLength:=by unfold workBase unitBase;omega
  have timeBound:4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+time ≤ cost (q*m+rest):=
    (Nat.add_le_add_left body.time_bound _).trans (cost_fit q rest large qp rp)
  have left:ChildResult n B (q*m+rest) A F stack stackTop depth cost x input s u
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+time) := by
    refine ⟨runPrefix.trans body.actual,up,body.stackValue,body.depthValue,?_,?_,?_,?_,body.constants,
      body.outputs.trans (nodeFrame.outputs.trans entryFrame.outputs),
      body.roots.trans (nodeFrame.roots.trans entryFrame.roots),timeBound⟩
    · intro i j;rw [body.data i j];rfl
    · intro i j;rw [body.data i j]
      exact congrArg some (congrFun (body.values i) j)
    · intro z hz away
      exact (body.natHeap z hz away).trans
        ((nodeFrame.natHeap z (Or.inl hz)).trans (congrFun entryFrame.natHeap z))
    · intro z hz away
      exact (body.scalarHeap z (lt_of_lt_of_le hz workFloor) away).trans
        ((congrFun nodeFrame.scalarHeap z).trans (congrFun entryFrame.scalarHeap z))
  have right:ChildResult n B (q*m+rest) A F stack stackTop depth cost (fun _=>0) input0 s0 u0
      (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))+time) := by
    refine ⟨runPrefix0.trans body.baseline,up0,body.zeroStack,body.zeroDepth,?_,?_,?_,?_,body.constants0,
      body.outputs0.trans (nodeFrame0.outputs.trans entryFrame0.outputs),
      body.roots0.trans (nodeFrame0.roots.trans entryFrame0.roots),timeBound⟩
    · intro i j;rw [body.data0 i j];rfl
    · intro i j;rw [body.data0 i j]
      exact congrArg some (congrFun (body.values0 i) j)
    · intro z hz away
      exact (body.natHeap0 z hz away).trans
        ((nodeFrame0.natHeap z (Or.inl hz)).trans (congrFun entryFrame0.natHeap z))
    · intro z hz away
      exact (body.scalarHeap0 z (lt_of_lt_of_le hz workFloor) away).trans
        ((congrFun nodeFrame0.scalarHeap z).trans (congrFun entryFrame0.scalarHeap z))
  refine ⟨left,right,body.matched,?_⟩
  have compiled:(run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).val=
      paired output output0 := by
    exact (DFTModelSavingClosedLarge.program_value q rest large rp Complex.I input input0).trans
      (congrArg Prod.snd body.code)
  intro i j
  rw [compiled,DFTModelRecursiveScalarSource.paired_lookup,body.data i j,body.data0 i j]
  rfl

/-- The full positive-depth large source execution, with the actual fixed
printers and all chronological records. Only genuine strictly smaller paired
runs of the same program enter as the internal induction hypothesis. -/
theorem execution (n B A F q rest stack stackTop depth : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (input input0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies (q*m+rest) n B R.reserve stack stackTop cost x Complex.I
      (DFTModelSavingSelfCall.evaluate (q*m+rest-1)))
    (same : StateMatch s s0) (large : P.threshold ≤ q*m+rest)
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
      ∀(i : Fin W)(j : Fin (2^(q*m+rest))),
        (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).val.look
          (i.val*2^(q*m+rest)+j.val) Tagged.blank=
          encodePaired ((u.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero)
            ((u0.scalarHeap (A+i.val*2^(q*m+rest)+j.val)).getD Scalar.zero) := by
  obtain ⟨t,t0,a,a0,run,run0,matched,ap,ap0,parent,parent0,ptr,storedMeta,ptr0,storedMeta0,printed,printed0,
    unit,unit0,present,present0,ct,ct0,ef,ef0,nf,nf0,geometry⟩:=DFTModelSavingNativeLargePrefix.execution
      n B A F P.seedLength P.unitLength q rest stack stackTop depth x s s0 input input0 rfl rfl same large qp rp smaller
      pc bits base size frontier sp dp data data0 positive heapBase extent stackRoom stackEnd code room square constants bound
  have metadata:a.natHeap (workBase F P.seedLength P.unitLength-1)=some (F+P.seedLength):=storedMeta
  have mainEnd:F+P.seedLength ≤ workBase F P.seedLength P.unitLength-6:=by unfold workBase unitBase;omega
  have unitEnd:unitBase F P.seedLength+P.unitLength ≤ workBase F P.seedLength P.unitLength-6:=by unfold workBase;omega
  obtain ⟨u,u0,time,g,g0,body⟩:=DFTModelSavingNativePrintedBody.execution
    n B F (unitBase F P.seedLength) A (workBase F P.seedLength P.unitLength) F q rest stack depth stackTop R.reserve
      cost x (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) a a0 input input0 childIH geometry matched ap parent metadata
      printed present present0 ptr unit mainEnd unitEnd stackEnd (by unfold unitBase;omega)
      (by unfold unitBase;omega) (by unfold workBase unitBase;omega) ct run.final_bound
  exact ⟨u,u0,_,finish n B A F q rest stack stackTop depth x s s0 t t0 a a0 u u0 input input0 g g0 time
    large qp rp positive run run0 ef ef0 nf nf0 body⟩

end
end ExactFourierCircuits.DFTModelSavingNativeLargeChild
