import UniformFinalRoleCaller
import UniformActualClockReady

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockLength
open UniformMachine UniformLocalFourierLayers UniformLocalCacheTiming
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
lemma specified_length (r:ℕ) (positive:0<r):
 (specifiedSchedule r).length=2*planDuration (UniformBalancedToeplitz.plan r)+5:=by
 rw[specifiedSchedule,dite_eq_left positive,schedule,symmetric_length]
 unfold Nschedule sandwich toeplitz
 simp only[List.length_append,List.length_singleton,render_duration]
 omega
lemma local_length {n:ℕ} (hn:0<n) (j:UniformSynchronizedLayers.axes n):
 (UniformSynchronizedLayers.localSchedules n j).length≤UniformFourierClockBounds.horizon n:=by
 have two:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 rw[UniformSynchronizedLayers.localSchedules,specified_length (UniformSelectedCRT.radices n j) (by omega)]
 exact UniformFourierClockBounds.selected_le n j
lemma code (n:ℕ):UniformActualGlobalClockProgram.program.length≤UniformJointAllocation.envelope c n:=
 UniformActualGlobalClockProgram.code_bound n
end
end ExactFourierCircuits.UniformFinalClockLength
