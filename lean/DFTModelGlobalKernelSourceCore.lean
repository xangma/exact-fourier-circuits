import DFTModelGlobalSectorLoopCallerFrame
import UniformConditionalKernelLayout
set_option autoImplicit false

/-! Exact paired handoff from the unchanged packing/all-gather prefix to the
unchanged closed child loop. No source operation or child handler is added. -/
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open DFTModelAdmissibilityControl
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section
abbrev W := DFTModelGlobalSectorLoop.W
abbrev reserve := DFTModelGlobalSectorLoop.reserve
abbrev child := DFTModelGlobalSectorLoop.child
abbrev Context (F : ℕ) := UniformConditionalKernelLayout.Context W F reserve
abbrev states {F : ℕ} (c : Context F) := UniformProducedSectorChildABI.states c.physical

lemma ready_match {F i : ℕ} {c : Context F} {s s0 : State}
 (v v0 : ℕ→Fin c.packing.volume→Scalar) (same : StateMatch s s0)
 (h : UniformConditionalKernelLayout.Ready c i v s)
 (source0 : UniformGlobalRolePackingMachine.Source c.packing v0 s0) :
 UniformConditionalKernelLayout.Ready c i v0 s0 := by
 have ph : UniformGlobalRolePackingMachine.Header c.packing s0 := by
  constructor <;>rw[same.natReg]
  all_goals first|exact h.packing.volume|exact h.packing.source|exact h.packing.destination|
   exact h.packing.axes|exact h.packing.rows|exact h.packing.suffix|exact h.packing.stack|exact h.packing.inverse
 have banks : UniformGlobalRolePackingMachine.Banks c.packing c.physical s0 := by
  refine ⟨UniformGlobalInverseReturn.rows_same_heap _ _ _ _ _ h.banks.1 same.natHeap,?_,?_⟩
  · intro a ha j;exact (congrFun same.natHeap _).trans (h.banks.2.1 a ha j)
  · intro a ha j;exact (congrFun same.natHeap _).trans (h.banks.2.2 a ha j)
 have inv : UniformGlobalInverseReturn.Args c.inverse c.scatter.directory s0 := by
  constructor <;>rw[same.natReg]
  all_goals first|exact h.inverse.volume|exact h.inverse.source|exact h.inverse.directory|
   exact h.inverse.axes|exact h.inverse.rows|exact h.inverse.suffix|exact h.inverse.stack|
   exact h.inverse.inverse|exact h.inverse.temporary|exact h.inverse.destination
 refine ⟨ph,banks,source0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,inv,
  DFTModelSavingNativeEntry.constants_match same h.constants⟩
 all_goals rw[same.natReg]
 all_goals first|exact h.count|exact h.axes|exact h.metadataRows|exact h.suffix|exact h.stack|
  exact h.directory|exact h.batchDirectory|exact h.childBank|exact h.native|exact h.volume|
  exact h.ordinal|exact h.frontier

lemma filled_pending {F : ℕ} (c : Context F) (v : ℕ→ℕ→Scalar) (s : State)
 (filled : UniformAllSectorTransposeMachine.Filled c.gather v (states c).length s) :
 DFTModelGlobalSectorLoop.Pending c.gather.buffer (states c) v 0 s := by
 intro i hi _ r j
 have pow := c.loop.pow i hi
 have hj : j.val < ((states c)[i]'hi).width := by rw[pow];exact j.isLt
 have val := filled i hi hi r.val r.isLt j.val hj
 simpa only[UniformSectorTransposeMachine.targetAddress,
  UniformAllSectorTransposeMachine.Geometry.local,Bool.false_eq_true,ite_false,
  UniformAllSectorTransposeMachine.slice,DFTModelGlobalSectorLoop.input,pow] using val

def loop_geometry {F : ℕ} (c : Context F) :
 DFTModelGlobalSectorLoop.Geometry W c.inverse.layout.B F reserve c.gather.buffer c.gather.directory (states c) :=
 ⟨c.loop.volume,c.loop.fits,c.loop.ordered,c.loop.pow,c.loop.low,c.loop.bank,c.loop.directory,
  c.loop.frontier,c.loop.room,c.loop.square,c.loop.qBound,c.loop.widthBound⟩

end
end ExactFourierCircuits.DFTModelGlobalKernelSource
