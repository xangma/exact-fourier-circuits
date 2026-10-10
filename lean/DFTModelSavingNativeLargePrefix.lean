import DFTModelSavingNativeNodePair
import UniformRecursiveBodyGeometry
import UniformRecursiveReserve

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeLargePrefix
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

/-- The positive-depth large branch starts at the actual common entry. Its
allocation geometry and both printed tapes are derived from raw headers and
the ordinary word reserve, then physically produced by charged bytecode. -/
theorem execution (n B A F M l q rest stack stackTop depth : ℕ) (x : Fin n → ℂ)
    (s s0 : State) (f f0 : Fin W → Fin (2^(q*m+rest)) → Scalar)
    (eqM : M=P.seedLength) (eql : l=P.unitLength)
    (same : StateMatch s s0) (large : P.threshold ≤ q*m+rest)
    (qp : 1 ≤ q) (rp : rest < m) (smaller : q < q*m+rest)
    (pc : s.pc=0) (bits : s.natReg 4120=q*m+rest) (base : s.natReg 4121=A)
    (size : s.natReg 4122=2^(q*m+rest)) (frontier : s.natReg 4123=F)
    (sp : s.natReg 4150=stack) (dp : s.natReg 4151=depth)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (positive : 1 ≤ depth) (heapBase : 3 ≤ A) (extent : A+W*2^(q*m+rest) ≤ F)
    (stackRoom : stack+34*(depth+(q*m+rest)+1) ≤ stackTop) (_stackEnd : stackTop ≤ F)
    (code : P.program.length ≤ B) (room : F+R.reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
    (square : (2^(q*m+rest))^2 ≤ B) (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) :
    ∃t t0 u u0,
      BoundedRuns P.program n x B s
        (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) u ∧
      BoundedRuns P.program n (fun _=>0) B s0
        (4+(9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady))) u0 ∧
      StateMatch u u0 ∧u.pc=P.address .loop ∧u0.pc=P.address .loop ∧
      Parent (q*m+rest) q A (workBase F M l) F rest stack depth u ∧
      Parent (q*m+rest) q A (workBase F M l) F rest stack depth u0 ∧
      u.natHeap (workBase F M l-2)=some (unitBase F M) ∧
      u.natHeap (workBase F M l-1)=some (unitBase F M) ∧
      u0.natHeap (workBase F M l-2)=some (unitBase F M) ∧
      u0.natHeap (workBase F M l-1)=some (unitBase F M) ∧
      PrintedRecords F (scheduleRecords q) u ∧PrintedRecords F (scheduleRecords q) u0 ∧
      Printed (unitBase F M) (P.unitRecord.withColumns q).data u ∧
      Printed (unitBase F M) (P.unitRecord.withColumns q).data u0 ∧
      Present A W (2^(q*m+rest)) f u ∧Present A W (2^(q*m+rest)) f0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧UniformBinaryCStageMachine.Constants u0 ∧
      UniformRecursiveSavingExecution.EntryFrame s t ∧UniformRecursiveSavingExecution.EntryFrame s0 t0 ∧
      DFTModelSavingNativeNode.Frame F (workBase F M l) t u ∧
      DFTModelSavingNativeNode.Frame F (workBase F M l) t0 u0 ∧
      Geometry B A (workBase F M l) q rest stack depth stackTop R.reserve := by
  have stackExtent:=UniformRecursiveReserve.stack_room room
  obtain ⟨t,t0,entry,entry0,matched,ready,ready0⟩:=DFTModelSavingNativeEntry.paired
    n B (q*m+rest) A (2^(q*m+rest)) F depth x s s0 same pc bits base size frontier dp bound code stackExtent
  have nonzero:depth≠0:=by omega
  rw [ite_eq_right nonzero] at entry entry0
  have current:t.natReg 4123=F:=by simpa only [ite_eq_right nonzero] using ready.frontier
  have stackHeader:t.natReg 4150=stack:=(ready.child_stack nonzero).trans sp
  have incoming:Present A W (2^(q*m+rest)) f t:=by
    intro i j;rw [ready.frame.scalarHeap];exact data i j
  have incoming0:Present A W (2^(q*m+rest)) f0 t0:=by
    intro i j;rw [ready0.frame.scalarHeap];exact data0 i j
  have con:UniformBinaryCStageMachine.Constants t:=by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [ready.frame.scalarHeap];exact constants
  have rb:R.reserve ≤ B:=UniformRecursiveBodyGeometry.reserve_le room
  have fit:M+l+11 ≤ R.reserve:=by rw [eqM,eql];exact UniformRecursiveReserve.payload_fit
  have geometry:=UniformRecursiveBodyGeometry.geometry B A F M l q rest stack depth stackTop R.reserve
    qp rp smaller fit UniformRecursiveReserve.width_fit room extent heapBase stackRoom square code
  obtain ⟨u,u0,node,node0,matchedOut,up,up0,parent,parent0,p2,p1,p20,p10,printed,printed0,
    unit,unit0,out,out0,conOut,conOut0,fr,fr0⟩:=DFTModelSavingNativeNode.paired
      n B F M l A q rest stack depth stackTop R.reserve x t t0 matched f f0 eqM eql geometry large
      (UniformRecursiveReserve.threshold_fit.trans rb) ready.pc ready.bits ready.base ready.volume current
      ready.nativeBase ready.nativeBits stackHeader ready.depthReg ready.one incoming incoming0 con
      (UniformRecursiveReserve.literals_fit.trans rb) entry.final_bound
  exact ⟨t,t0,u,u0,entry.trans node,entry0.trans node0,matchedOut,up,up0,parent,parent0,
    p2,p1,p20,p10,printed,printed0,unit,unit0,out,out0,conOut,conOut0,ready.frame,ready0.frame,fr,fr0,geometry⟩

end
end ExactFourierCircuits.DFTModelSavingNativeLargePrefix
