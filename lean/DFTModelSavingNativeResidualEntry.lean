import DFTModelSavingNativeDirectionLoop
import UniformRecursiveResidualEdge

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeResidual
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open FramedScheduleWords (Label NestedEdge)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
open UniformRecursiveResidualEdge (Parent parent_raw parent_frame parent_direction)
noncomputable section
attribute [local irreducible] P.program

lemma parent_match {k q A F T r stack depth:ℕ}{s s0:State}
 (same:StateMatch s s0)(h:Parent k q A F T r stack depth s):Parent k q A F T r stack depth s0:=
 ⟨(congrFun same.natReg _).trans h.cursor,(congrFun same.natReg _).trans h.nativeBase,
 (congrFun same.natReg _).trans h.original,(congrFun same.natReg _).trans h.bits,
 (congrFun same.natReg _).trans h.volume,(congrFun same.natReg _).trans h.frontier,
 (congrFun same.natReg _).trans h.rest,(congrFun same.natReg _).trans h.stack,
 (congrFun same.natReg _).trans h.depth,(congrFun same.natReg _).trans h.one,
 (congrFun same.natReg _).trans h.nativeBits,(congrFun same.natReg _).trans h.nativeRest,
 (congrFun same.natReg _).trans h.table,(congrFun same.natReg _).trans h.columns,
 (congrFun same.natReg _).trans h.width⟩

structure EntryResult (n B T nRoles R A F q w r stack depth:ℕ)
 (x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(s a:State):Prop where
 run:BoundedRuns P.program n x B s 46 a
 pc:a.pc=P.address .directionTest
 control:UniformRecursiveResidualDirection.Control (q*(w+1)+r) q A F T r stack depth 0 edge.dimension
  (T+(macroRecord q emb (.edge old new role edge)).data.length) (macroRecord q emb (.edge old new role edge)).inverse a
 printed:Printed T (macroRecord q emb (.edge old new role edge)).data a
 nat:∀z,z≠F-6→a.natHeap z=s.natHeap z
 scalar:a.scalarHeap=s.scalarHeap
 constants:UniformBinaryCStageMachine.Constants a
 roots:a.rootOrders=s.rootOrders
 outputs:a.outputs=s.outputs
 mode:a.natHeap (F-6)=some 0

theorem entry (n B T tapeEnd nRoles R A F q w r stack depth:ℕ)
 (x:Fin n→ℂ)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}
 (role:Fin nRoles)(edge:NestedEdge old new)(s:State)
 (pc:s.pc=P.address .loop)(h:Parent (q*(w+1)+r) q A F T r stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T<tapeEnd)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length≤F-6)
 (widthBound:(w+1)+1≤B)(low:6≤F)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:P.program.length≤B)(fb:F≤B):
 ∃a,EntryResult n B T nRoles R A F q w r stack depth x emb role edge s a:=by
 let record:=macroRecord q emb (.edge old new role edge)
 have recordLimit:T+record.data.length≤F-6:=recordEnd
 obtain ⟨a,t,run,ap,cursor,idx,dim,finish,flag,mode,main,unit,cf,rf⟩:=UniformRecursiveResidualControlJoin.raw_entry_cursor
  F T tapeEnd n B record x s pc h.frontier h.cursor h.one metadata live printed
  (UniformFixedNetworkOpcodeMachine.macro_wellFormed q emb (.edge old new role edge)) rfl bound code
  (by omega) widthBound low
 have ah:=parent_raw h cf rf cursor
 have pr:Printed T record.data a:=by
  intro z hz;rw [rf.natHeap _ (by omega),cf.natHeap];exact printed z hz
 have ca:UniformBinaryCStageMachine.Constants a:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  exact ⟨(congrFun rf.scalarHeap 1).trans ((congrFun cf.scalarHeap 1).trans constants.1),
   (congrFun rf.scalarHeap 2).trans ((congrFun cf.scalarHeap 2).trans constants.2)⟩
 refine ⟨a,run,ap,⟨ah.cursor,ah.nativeBase,ah.original,ah.bits,ah.volume,ah.frontier,ah.rest,
  ah.stack,ah.depth,ah.one,idx,dim,finish,flag,ah.nativeBits,ah.nativeRest,ah.table,ah.columns,ah.width⟩,
  pr,?_,rf.scalarHeap.trans cf.scalarHeap,ca,rf.roots.trans cf.roots,rf.outputs.trans cf.outputs,mode⟩
 intro z ne;exact (rf.natHeap z ne).trans (congrFun cf.natHeap z)

end
end ExactFourierCircuits.DFTModelSavingNativeResidual
