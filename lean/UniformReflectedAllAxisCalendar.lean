import UniformReflectedFourierCalendar
import UniformMasterSynchronizedLayers
import UniformCalendarPhysicalAxis

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReflectedAllAxisCalendar
noncomputable section
open OAI.ExactFourier UniformSynchronizedLayers UniformLayerSnapshot

def axis (n t : ℕ) (i : axes n) : Snapshot (Fin (radix n i)) :=
  UniformReflectedFourierCalendar.specified (radix n i) t

theorem axis_matrix (n t : ℕ) (i : axes n) :
    (axis n t i).matrix=UniformCalendarRenderTick.tick (localSchedules n i) t :=
  UniformReflectedFourierCalendar.specified_matrix _ _

/-- Every axis uses its own local reflected/forward epoch at the same clock. -/
theorem tensor_tick (n : ℕ) (hn : 0<n) (t : Fin (UniformCommonSlots.slotCount n)) :
    PiTensor.matrix (fun i=>(axis n t.val i).matrix)=
      tensorSlot (localSchedules n) (localSchedules_length hn) t := by
  apply congrArg PiTensor.matrix
  funext i
  rw [axis_matrix,UniformAllAxisCalendarTensor.slot_tick]

theorem tensor_factors (n : ℕ) (hn : 0<n) (t : Fin (UniformCommonSlots.slotCount n)) :
    tensorSlot (localSchedules n) (localSchedules_length hn) t=
      PiTensor.matrix (fun i=>Matrix.diagonal (axis n t.val i).diagonal*(axis n t.val i).calls.matrix) :=
  (tensor_tick n hn t).symm

theorem tensor_product (n : ℕ) (hn : 0<n) :
    (List.ofFn (fun t : Fin (UniformCommonSlots.slotCount n)=>
      PiTensor.matrix (fun i=>(axis n t.val i).matrix))).reverse.prod=
      PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i)) := by
  simp_rw [tensor_tick n hn]
  exact selectedSchedule_product n hn

/-- The actual normal selected schedule, including its literal transpose epoch. -/
theorem selected_calendar (n : ℕ) (hn : 0<n) :
    List.ofFn (fun t : Fin (UniformCommonSlots.slotCount n)=>
      PiTensor.matrix (fun i=>(axis n t.val i).matrix))=selectedSchedule n hn := by
  simp_rw [tensor_tick n hn]
  rfl

theorem calendar_ordinal (n : ℕ) (hn : 0<n) :
    Matrix.reindex (UniformCRTTraversalCycle.ordinalEquiv n).symm
      (UniformCRTTraversalCycle.ordinalEquiv n).symm
      (List.ofFn (fun t : Fin (UniformCommonSlots.slotCount n)=>
        PiTensor.matrix (fun i=>(axis n t.val i).matrix))).reverse.prod=
      UniformMasterSynchronizedLayers.ordinalMatrix n hn := by
  rw [tensor_product n hn,UniformMasterSynchronizedLayers.ordinalMatrix,
    UniformMasterSynchronizedLayers.schedule_radices n hn]

theorem inverse_beta_restores (n : ℕ) (hn : 0<n)
    (x : Fin (UniformWorkingLength.workingLength n)→ℂ)
    (j : Fin (UniformWorkingLength.workingLength n)) :
    (Matrix.reindex (UniformCRTTraversalCycle.ordinalEquiv n).symm
      (UniformCRTTraversalCycle.ordinalEquiv n).symm
      (List.ofFn (fun t : Fin (UniformCommonSlots.slotCount n)=>
        PiTensor.matrix (fun i=>(axis n t.val i).matrix))).reverse.prod).mulVec
      (x ∘ UniformCRTTraversalCycle.alphaPermutation n)
      ((UniformCRTTraversalCycle.betaPermutation n).symm j)=
        (fourierMatrix (UniformWorkingLength.workingLength n)).mulVec x j := by
  rw [calendar_ordinal]
  exact UniformMasterSynchronizedLayers.inverse_beta_restores n hn x j

end
end ExactFourierCircuits.UniformReflectedAllAxisCalendar
