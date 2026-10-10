import DFTModelSavingNativeRootData
import DFTModelSavingNativeLargeRootPrefix
import DFTModelSavingNativeBilledChildInduction

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeRoot
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformRecursiveNodePreparation
open UniformRecursiveTypedBody DFTModelAdmissibilityControl DFTModelAffine
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] P.program P.threshold P.seedLength P.unitLength
  P.seedPrinterLength P.unitPrinterLength P.size R.reserve DFTModelSavingProgram.program
  DFTModelSavingNativeSequence.typedFold

/-- Real root allocation and printing feed the closed billed child induction.
The printed body, terminal suffix and halt use the very same source witnesses
whose actual duration pays the single paired typed computation. -/
theorem large_execution (n B A F q rest K : ℕ) (x : Fin n→ℂ) (s s0 : State)
    (input input0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K) (same : StateMatch s s0)
    (large : P.threshold≤q*m+rest) (qp : 1≤q) (rp : rest < m) (smaller : q<q*m+rest)
    (pc : s.pc=0) (bits : s.natReg 4120=q*m+rest) (base : s.natReg 4121=A)
    (size : s.natReg 4122=2^(q*m+rest)) (frontier : s.natReg 4123=F) (dp : s.natReg 4151=0)
    (data : Present A W (2^(q*m+rest)) input s) (data0 : Present A W (2^(q*m+rest)) input0 s0)
    (heapBase : 3≤A) (extent : A+W*2^(q*m+rest)≤F) (code : P.program.length≤B)
    (room : F+34*(q*m+rest+1)+R.reserve*(q*m+rest+1)*2^(q*m+rest)≤B)
    (square : (2^(q*m+rest))^2≤B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 ticks output output0,
      Result n B (q*m+rest) A F K x s s0 u u0 ticks input input0 output output0 := by
  let G:=F+34*(q*m+rest+1)
  obtain ⟨t,t0,a,a0,sourceRun,sourceRun0,matched,ap,_ap0,parent,_parent0,ptr,storedMeta,_ptr0,_storedMeta0,
    printed,_printed0,unit,_unit0,present,present0,ct,_ct0,ef,ef0,nf,nf0,geometry⟩:=
    DFTModelSavingNativeLargeRootPrefix.execution n B A F G P.seedLength P.unitLength q rest x s s0
      input input0 rfl rfl rfl same large qp rp smaller pc bits base size frontier dp data data0 heapBase
      extent code room square constants bound
  have before:=DFTModelSavingNativeBilledChildInduction.smaller (q*m+rest) n B F G K x cap
  have childIH:=DFTModelSavingNativeRecursiveIH.billed (q*m+rest) (q*m+rest-1) n B R.reserve F G K cost x Complex.I
    (by omega) (by have h:=DFTModelSavingCost.factor_marker;omega) before
  have metadata:a.natHeap (workBase G P.seedLength P.unitLength-1)=some (G+P.seedLength):=storedMeta
  have mainEnd:G+P.seedLength≤workBase G P.seedLength P.unitLength-6:=by unfold workBase unitBase;omega
  have unitEnd:unitBase G P.seedLength+P.unitLength≤workBase G P.seedLength P.unitLength-6:=by unfold workBase;omega
  have fg:F≤G:=by dsimp [G];omega
  have workFloor:F≤workBase G P.seedLength P.unitLength:=by unfold workBase unitBase;omega
  obtain ⟨u,u0,time,g,g0,body,billing⟩:=DFTModelSavingNativeBilledPrintedBody.execution
    n B G (unitBase G P.seedLength) A (workBase G P.seedLength P.unitLength) F q rest F 0 G R.reserve K
      (10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) cost x
      (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) a a0 input input0 childIH cap (by omega)
      geometry matched ap parent metadata printed present present0 ptr unit mainEnd unitEnd (le_refl G)
      (by unfold unitBase;omega) (by unfold unitBase;omega) (by unfold workBase unitBase;omega)
      ct sourceRun.final_bound
  have actual:=sourceRun.trans body.actual
  have zero:=sourceRun0.trans body.baseline
  have up:u.pc=P.address .halt:=by simpa only [ite_true] using body.pc
  have up0:u0.pc=P.address .halt:=by simpa only [ite_true] using body.pc0
  refine ⟨u,u0,(10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)))+time+1,g,g0,?_⟩
  refine {
    actual:=actual.executes (halt n B x u up actual.final_bound),
    baseline:=zero.executes (halt n B (fun _=>0) u0 up0 zero.final_bound),matched:=body.matched,
    pc:=up,pc0:=up0,data:=body.data,data0:=body.data0,values:=body.values,values0:=body.values0,
    natHeap:=?_,natHeap0:=?_,scalarHeap:=?_,scalarHeap0:=?_,constants:=body.constants,constants0:=body.constants0,
    roots:=body.roots.trans (nf.roots.trans ef.roots),roots0:=body.roots0.trans (nf0.roots.trans ef0.roots),
    outputs:=body.outputs.trans (nf.outputs.trans ef.outputs),outputs0:=body.outputs0.trans (nf0.outputs.trans ef0.outputs),
    compiled:=?_,work:=?_}
  · intro z hz
    exact (body.natHeap z hz (Or.inl (by simpa only [Nat.mul_zero,Nat.add_zero] using hz))).trans
      ((nf.natHeap z (Or.inl (lt_of_lt_of_le hz fg))).trans (congrFun ef.natHeap z))
  · intro z hz
    exact (body.natHeap0 z hz (Or.inl (by simpa only [Nat.mul_zero,Nat.add_zero] using hz))).trans
      ((nf0.natHeap z (Or.inl (lt_of_lt_of_le hz fg))).trans (congrFun ef0.natHeap z))
  · intro z hz away
    exact (body.scalarHeap z (lt_of_lt_of_le hz workFloor) away).trans
      ((congrFun nf.scalarHeap z).trans (congrFun ef.scalarHeap z))
  · intro z hz away
    exact (body.scalarHeap0 z (lt_of_lt_of_le hz workFloor) away).trans
      ((congrFun nf0.scalarHeap z).trans (congrFun ef0.scalarHeap z))
  · exact (DFTModelSavingClosedLarge.program_value q rest large rp Complex.I input input0).trans
      (congrArg Prod.snd body.code)
  · have closed:=(DFTModelSavingClosedLarge.program_run (q*m+rest) large Complex.I (paired input input0)).2
    change (run DFTModelSavingProgram.program ((q*m+rest,Complex.I),paired input input0)).work=
      (Code.run DFTModelSavingProgram.large (DFTModelSavingSelfCall.evaluate (q*m+rest-1))
        ((q*m+rest,Complex.I),paired input input0)).work+17 at closed
    have measured:(Code.run DFTModelSavingProgram.large (DFTModelSavingSelfCall.evaluate (q*m+rest-1))
        ((q*m+rest,Complex.I),paired input input0)).work+27≤
      K*((10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)))+time):=billing
    rw [closed]
    exact (by omega : _≤K*((10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)))+time)).trans
      (Nat.mul_le_mul_left K (by omega))

end
end ExactFourierCircuits.DFTModelSavingNativeRoot
