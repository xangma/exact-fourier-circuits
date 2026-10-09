import UniformRecursiveResidualEdge
import UniformRecursiveNativeRecords
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNativeParent
open UniformMachine UniformRecursiveResidualEdge
noncomputable section

def parentRegisters:List ℕ:=[3300,4120,4121,4122,4123,4127,4150,4151,4153,5300,5301,3389,4060,4061]
lemma parent_congr {k q A F T Tnext r stack depth:ℕ}{s u:State}
 (h:Parent k q A F T r stack depth s)(ptr:u.natReg 2850=Tnext)
 (kept:∀j,j∈parentRegisters→u.natReg j=s.natReg j):Parent k q A F Tnext r stack depth u:=
 ⟨ptr,(kept _ (by decide)).trans h.nativeBase,(kept _ (by decide)).trans h.original,
  (kept _ (by decide)).trans h.bits,(kept _ (by decide)).trans h.volume,
  (kept _ (by decide)).trans h.frontier,(kept _ (by decide)).trans h.rest,
  (kept _ (by decide)).trans h.stack,(kept _ (by decide)).trans h.depth,
  (kept _ (by decide)).trans h.one,(kept _ (by decide)).trans h.nativeBits,
  (kept _ (by decide)).trans h.nativeRest,(kept _ (by decide)).trans h.table,
  (kept _ (by decide)).trans h.columns,(kept _ (by decide)).trans h.width⟩

lemma scalar_parent {k q A F T Tnext r stack depth D V:ℕ}{s t u:State}
 (h:Parent k q A F T r stack depth s)(ptr:u.natReg 2850=Tnext)
 (control:UniformRecursiveRecordControl.ControlFrame s t)
 (frame:UniformNativeScalarRecordMachine.ScalarFrame D V t u):Parent k q A F Tnext r stack depth u:=by
 apply parent_congr h ptr
 intro j hj
 simp only [parentRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
 exact (frame.natReg j (by unfold UniformNativeScalarRecordMachine.ScalarChanged;omega)).trans
  (control.natReg j (by unfold UniformRecursiveRecordControl.ControlChanged;omega))

lemma exchange_parent {k q A F T Tnext r stack depth V:ℕ}{s t u:State}
 (h:Parent k q A F T r stack depth s)(ptr:u.natReg 2850=Tnext)
 (control:UniformRecursiveRecordControl.ControlFrame s t)
 (frame:UniformNativeExchangeRecordMachine.FullFrame A V t u):Parent k q A F Tnext r stack depth u:=by
 apply parent_congr h ptr
 intro j hj
 simp only [parentRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
 exact (frame.natReg j (by unfold UniformNativeExchangeRecordMachine.FullChanged UniformNativeExchangeRecordMachine.Changed;omega)).trans
  (control.natReg j (by unfold UniformRecursiveRecordControl.ControlChanged;omega))

lemma translation_parent {k q w A E F X T Tnext r stack depth V:ℕ}{s t a u:State}
 (h:Parent k q A F T r stack depth s)(ptr:u.natReg 2850=Tnext)
 (control:UniformRecursiveRecordControl.ControlFrame s t)(restore:UniformRecursiveYRestore.Frame t a)
 (frame:UniformNativeYRecordMachine.FullFrame q A V E X w k a u):Parent k q A F Tnext r stack depth u:=by
 apply parent_congr h ptr
 intro j hj
 simp only [parentRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
 exact (frame.natReg j (by unfold UniformNativeYRecordMachine.FullChanged UniformNativeYRecordMachine.Changed UniformNativePreparedYTranslationMachine.Changed UniformXorTranslationMachine.Changed;omega)).trans
  ((restore.natReg j (by unfold UniformRecursiveYRestore.Changed;omega)).trans
   (control.natReg j (by unfold UniformRecursiveRecordControl.ControlChanged;omega)))

lemma marker_parent {k q A F T Tnext r stack depth:ℕ}{s t u:State}
 (h:Parent k q A F T r stack depth s)(ptr:u.natReg 2850=Tnext)
 (control:UniformRecursiveRecordControl.ControlFrame s t)
 (frame:UniformFixedNetworkOpcodeMachine.Frame t u):Parent k q A F Tnext r stack depth u:=by
 apply parent_congr h ptr
 intro j hj
 simp only [parentRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
 exact (frame.natReg j (by omega)).trans
  (control.natReg j (by unfold UniformRecursiveRecordControl.ControlChanged;omega))
end
end ExactFourierCircuits.UniformRecursiveNativeParent
