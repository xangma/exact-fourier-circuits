import UniformFinalRoleCaller
import UniformActualClockReady
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
