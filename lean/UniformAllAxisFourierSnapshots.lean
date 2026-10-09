import UniformFourierCalendarSnapshot
import UniformAlternateSynchronizedSchedule

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisFourierSnapshots
noncomputable section
open OAI.ExactFourier UniformSynchronizedLayers UniformLayerSnapshot

def axis (n : ℕ) (t : ℕ) (i : axes n) : Snapshot (Fin (radix n i)) :=
  UniformFourierCalendarSnapshot.specified (radix n i) t

def diagonal (n t : ℕ) (i : axes n) : Fin (radix n i)→ℂ := (axis n t i).diagonal

def calls (n t : ℕ) (i : axes n) : Calls (Fin (radix n i)) := (axis n t i).calls

theorem axis_matrix (n t : ℕ) (i : axes n) :
    (axis n t i).matrix=UniformCalendarRenderTick.tick
      (UniformAlternateSynchronizedSchedule.axisLayers n i) t :=
  UniformFourierCalendarSnapshot.specified_matrix _ _

/-- This is one simultaneous tensor tick of every genuine axis calendar. -/
theorem tensor_tick (n : ℕ) (hn : 0<n) (t : Fin (UniformCommonSlots.slotCount n)) :
    PiTensor.matrix (fun i => (axis n t.val i).matrix) =
      tensorSlot (UniformAlternateSynchronizedSchedule.axisLayers n)
        (UniformAlternateSynchronizedSchedule.local_length hn) t := by
  apply congrArg PiTensor.matrix
  funext i
  rw [axis_matrix,UniformAllAxisCalendarTensor.slot_tick]

/-- The physical contract contains all ordered calls and the actual diagonal
from all active events, even when their local compiler phases differ. -/
theorem tensor_factors (n : ℕ) (hn : 0<n) (t : Fin (UniformCommonSlots.slotCount n)) :
    tensorSlot (UniformAlternateSynchronizedSchedule.axisLayers n)
      (UniformAlternateSynchronizedSchedule.local_length hn) t =
    PiTensor.matrix (fun i => Matrix.diagonal (diagonal n t.val i) * (calls n t.val i).matrix) :=
  (tensor_tick n hn t).symm

theorem tensor_product (n : ℕ) (hn : 0<n) :
    (List.ofFn (fun t : Fin (UniformCommonSlots.slotCount n) =>
      PiTensor.matrix (fun i => (axis n t.val i).matrix))).reverse.prod =
      PiTensor.matrix (fun i : axes n => fourierMatrix (radix n i)) := by
  simp_rw [tensor_tick n hn]
  exact UniformAlternateSynchronizedSchedule.schedule_product n hn

end
end ExactFourierCircuits.UniformAllAxisFourierSnapshots
