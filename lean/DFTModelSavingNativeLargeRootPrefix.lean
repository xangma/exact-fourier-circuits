import DFTModelSavingNativeLargePrefix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeLargeRootPrefix
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformRecursiveTypedBody UniformRecursiveNodePreparation
open UniformRecursiveResidualEdge (Parent)
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelAdmissibilityControl
namespace P
export UniformRecursiveSavingProgram (program address threshold seedLength unitLength
  seedPrinterLength unitPrinterLength size unitRecord)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable section
attribute [local irreducible] P.program P.threshold P.seedLength P.unitLength
  P.seedPrinterLength P.unitPrinterLength P.size P.unitRecord R.reserve

/-- The root's stack is allocated by the real ten-instruction entry. The
following geometry and literal printers consume that produced frontier. -/
theorem execution (n B A F G M l q rest : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (fresh : G=F+34*(q*m+rest+1)) (eqM : M=P.seedLength) (eql : l=P.unitLength)
    (same : StateMatch s s0) (large : P.threshold ≤ q*m+rest)
    (qp : 1 ≤ q) (rp : rest < m) (smaller : q < q*m+rest)
    (pc : s.pc=0) (bits : s.natReg 4120=q*m+rest) (base : s.natReg 4121=A)
    (size : s.natReg 4122=2^(q*m+rest)) (frontier : s.natReg 4123=F)
    (dp : s.natReg 4151=0)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (heapBase : 3 ≤ A) (extent : A+W*2^(q*m+rest) ≤ F)
    (code : P.program.length ≤ B)
    (room : F+34*(q*m+rest+1)+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
    (square : (2^(q*m+rest))^2 ≤ B) (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) :
    ∃t t0 u u0,
      BoundedRuns P.program n x B s
        (10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) u ∧
      BoundedRuns P.program n (fun _=>0) B s0
        (10+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) u0 ∧
      StateMatch u u0 ∧u.pc=P.address .loop ∧u0.pc=P.address .loop ∧
      Parent (q*m+rest) q A (workBase G M l) G rest F 0 u ∧
      Parent (q*m+rest) q A (workBase G M l) G rest F 0 u0 ∧
      u.natHeap (workBase G M l-2)=some (unitBase G M) ∧
      u.natHeap (workBase G M l-1)=some (unitBase G M) ∧
      u0.natHeap (workBase G M l-2)=some (unitBase G M) ∧
      u0.natHeap (workBase G M l-1)=some (unitBase G M) ∧
      PrintedRecords G (scheduleRecords q) u ∧PrintedRecords G (scheduleRecords q) u0 ∧
      Printed (unitBase G M) (P.unitRecord.withColumns q).data u ∧
      Printed (unitBase G M) (P.unitRecord.withColumns q).data u0 ∧
      Present A W (2^(q*m+rest)) f u ∧Present A W (2^(q*m+rest)) f0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧UniformBinaryCStageMachine.Constants u0 ∧
      UniformRecursiveSavingExecution.EntryFrame s t ∧UniformRecursiveSavingExecution.EntryFrame s0 t0 ∧
      DFTModelSavingNativeNode.Frame G (workBase G M l) t u ∧
      DFTModelSavingNativeNode.Frame G (workBase G M l) t0 u0 ∧
      Geometry B A (workBase G M l) q rest F 0 G R.reserve := by
  have stackExtent:F+34*(q*m+rest+1) ≤ B:=by omega
  obtain ⟨t,t0,entry,entry0,matched,ready,ready0⟩:=DFTModelSavingNativeEntry.paired
    n B (q*m+rest) A (2^(q*m+rest)) F 0 x s s0 same pc bits base size frontier dp bound code stackExtent
  have run:BoundedRuns P.program n x B s 10 t:=entry
  have run0:BoundedRuns P.program n (fun _=>0) B s0 10 t0:=entry0
  have current:t.natReg 4123=G:=by
    rw [ready.frontier]
    exact fresh.symm
  have stackHeader:t.natReg 4150=F:=ready.root_stack rfl
  have incoming:Present A W (2^(q*m+rest)) f t:=by
    intro i j;rw [ready.frame.scalarHeap];exact data i j
  have incoming0:Present A W (2^(q*m+rest)) f0 t0:=by
    intro i j;rw [ready0.frame.scalarHeap];exact data0 i j
  have con:UniformBinaryCStageMachine.Constants t:=by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [ready.frame.scalarHeap];exact constants
  have newRoom:G+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B:=by rw [fresh];exact room
  have rb:R.reserve ≤ B:=UniformRecursiveBodyGeometry.reserve_le newRoom
  have fit:M+l+11 ≤ R.reserve:=by rw [eqM,eql];exact UniformRecursiveReserve.payload_fit
  have geometry:=UniformRecursiveBodyGeometry.geometry B A G M l q rest F 0 G R.reserve
    qp rp smaller fit UniformRecursiveReserve.width_fit newRoom (by omega) heapBase
    (by omega) square code
  obtain ⟨u,u0,node,node0,matchedOut,up,up0,parent,parent0,p2,p1,p20,p10,printed,printed0,
    unit,unit0,out,out0,conOut,conOut0,fr,fr0⟩:=DFTModelSavingNativeNode.paired
      n B G M l A q rest F 0 G R.reserve x t t0 matched f f0 eqM eql geometry large
      (UniformRecursiveReserve.threshold_fit.trans rb) ready.pc ready.bits ready.base ready.volume current
      ready.nativeBase ready.nativeBits stackHeader ready.depthReg ready.one incoming incoming0 con
      (UniformRecursiveReserve.literals_fit.trans rb) run.final_bound
  exact ⟨t,t0,u,u0,run.trans node,run0.trans node0,matchedOut,up,up0,parent,parent0,
    p2,p1,p20,p10,printed,printed0,unit,unit0,out,out0,conOut,conOut0,ready.frame,ready0.frame,fr,fr0,geometry⟩

end
end ExactFourierCircuits.DFTModelSavingNativeLargeRootPrefix
