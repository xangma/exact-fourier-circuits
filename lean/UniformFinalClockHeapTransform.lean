import UniformFinalCRTMovement
import UniformActualClockEntry
import UniformSelectedPhysicalCRT
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockHeapTransform
open UniformMachine UniformFinalNumericJoin
noncomputable section

/-- The actual synchronized MSB tensor matrix has precisely the physical
AP-input/BP-output Fourier coordinates printed by the CRT producer. -/
lemma matrix_eq (n:ℕ):UniformPhysicalSynchronizedSchedule.fourier n=
 physicalFourier (UniformSelectedPhysicalCRT.physicalAlpha n)
  (UniformSelectedPhysicalCRT.physicalBeta n):=by
 rw[UniformSelectedPhysicalCRT.physical_fourier]
 rfl

def actualValues (n:ℕ)(s:State)(r:ℕ)(j:Fin (UniformActualClockEntry.volume n)):Scalar:=
 scalars (UniformActualClockEntry.volume n)
  (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n) s j

lemma numeric_source {n:ℕ}(v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(s:State)
 (output:UniformActualClockEntry.Numeric n v s):
 UniformActualClockEntry.Source n (actualValues n s) s:=by
 intro r hr j
 exact numeric_present (output r hr) j

/-- Convert an actual all-role clock endpoint to the heap-transform contract,
using the supplied cells of that same clock run. -/
theorem heap_transform {n:ℕ}(v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)
 (s u:State)(input:UniformActualClockEntry.Source n v s)
 (output:UniformActualClockEntry.Numeric n v u)(r:ℕ)(hr:r<UniformActualClockEntry.roles):
 HeapTransform (UniformSelectedPhysicalCRT.physicalAlpha n)
  (UniformSelectedPhysicalCRT.physicalBeta n)
  (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n)
  (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n) s u:=by
 have values:∀j:Fin (UniformActualClockEntry.volume n),
  scalars (UniformActualClockEntry.volume n)
   (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n) s j=v r j:=by
  intro j
  unfold scalars
  rw[input r hr j]
  rfl
 intro j
 simp_rw[values]
 rw[←matrix_eq]
 exact output r hr j

theorem prepared_tags {n:ℕ}(u:State)(output:UniformActualClockEntry.PreparedOutput n u)
 (r:ℕ)(hr:r<UniformActualClockEntry.roles):
 ∀j:Fin (UniformActualClockEntry.volume n),
  (scalars (UniformActualClockEntry.volume n)
   (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n) u j).dependent=false:=by
 intro j
 have tag:=output r hr j
 cases cell:u.scalarHeap
  (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n+j.val) with
 | none=>simp only[cell,Option.map_none] at tag;cases tag
 | some a=>
   simpa only[scalars,cell,Option.getD_some] using (Option.some.inj (by simpa only[cell,Option.map_some] using tag))

/-- A shallow numeric join; the transform argument is the actual clock heap
postcondition obtained above, not a new algorithm/action certificate. -/
theorem kernel_spectrum {n L A D:ℕ}[NeZero L](AP BP:Fin L≃Fin L)(s u:State)
 (input:NumericValues A (fun j=>kernel (n:=n) (AP j)) s)
 (run:HeapTransform AP BP A D s u):
 NumericValues D (fun j=>kernelSpectrum (n:=n) (BP j)) u:=by
 have values:(fun j=>(scalars L A s j).value)=(fun j=>kernel (n:=n) (AP j)):=
  funext (numeric_value input)
 intro j
 have action:=kernel_transform (n:=n) AP BP j
 rw[←values] at action
 exact (run j).trans (congrArg some action)

theorem data_spectrum {n L A D:ℕ}[NeZero L](AP BP:Fin L≃Fin L)(x:Fin n→ℂ)(s u:State)
 (input:NumericValues A (fun j=>data x (AP j)) s)
 (run:HeapTransform AP BP A D s u):
 NumericValues D (fun j=>dataSpectrum x (BP j)) u:=by
 have values:(fun j=>(scalars L A s j).value)=(fun j=>data x (AP j)):=
  funext (numeric_value input)
 intro j
 have action:=data_transform AP BP x j
 rw[←values] at action
 exact (run j).trans (congrArg some action)

end
end ExactFourierCircuits.UniformFinalClockHeapTransform
