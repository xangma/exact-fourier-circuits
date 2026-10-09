import UniformReflectedAllAxisCalendar
import UniformMultiAxisSectorMetadataPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReflectedPhysicalCalendar
noncomputable section
open OAI.ExactFourier UniformSynchronizedLayers UniformSectorPacking
open UniformCalendarPhysicalAxis

def family (n : ℕ) (hn : 0<n) (t : ℕ) (i : axes n) : Axis :=
  geometry (UniformReflectedAllAxisCalendar.axis n t i)
    (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i)

def coordinates (n : ℕ) (hn : 0<n) (t : ℕ) :
    (∀i : axes n,Fin (family n hn t i).widths.sum) ≃ (∀i : axes n,Fin (radix n i)) :=
  Equiv.piCongrRight (fun i => coordinate (UniformReflectedAllAxisCalendar.axis n t i)
    (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i))

def diagonal (n : ℕ) (hn : 0<n) (t : ℕ) (i : axes n) : Fin (family n hn t i).widths.sum→ℂ :=
  UniformCalendarPhysicalAxis.diagonal (UniformReflectedAllAxisCalendar.axis n t i)
    (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i)

/-- Real55 local axes simultaneously realize all active local calendar factors. -/
theorem tensor_tick (n : ℕ) (hn : 0<n) (t : Fin (UniformCommonSlots.slotCount n)) :
    Matrix.reindex (coordinates n hn t.val) (coordinates n hn t.val)
      (PiTensor.matrix (fun i : axes n => Matrix.diagonal (diagonal n hn t.val i) *
        UniformMatchingKernelGeometry.localKernel (family n hn t.val i))) =
      tensorSlot (localSchedules n) (localSchedules_length hn) t := by
  rw [←UniformReflectedAllAxisCalendar.tensor_tick n hn t]
  ext x y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,PiTensor.matrix]
  apply Finset.prod_congr rfl
  intro i hi
  have h:=factor (UniformReflectedAllAxisCalendar.axis n t.val i)
    (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn i)
  exact congrArg (fun M => M (x i) (y i)) h

def physicalAxes (n : ℕ) (hn : 0<n) (t : ℕ) : List Axis := List.ofFn (family n hn t)

@[simp] theorem physicalAxes_length (n : ℕ) (hn : 0<n) (t : ℕ) :
    (physicalAxes n hn t).length=UniformWorkingLength.axisCount n+1 := by
  simp [physicalAxes]

theorem physicalAxes_get (n : ℕ) (hn : 0<n) (t : ℕ)
    (i : Fin (physicalAxes n hn t).length) :
    (physicalAxes n hn t).get i = family n hn t (Fin.cast (physicalAxes_length n hn t) i) := by
  unfold physicalAxes at i ⊢
  rw [List.get_eq_getElem,List.getElem_ofFn]
  congr 1

end
end ExactFourierCircuits.UniformReflectedPhysicalCalendar
