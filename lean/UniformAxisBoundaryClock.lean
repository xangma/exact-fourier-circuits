import UniformAxisBoundaryEvents
import UniformLocalCacheTiming

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundaryClock
noncomputable section
open UniformLocalFourierLayers UniformCalendarRenderTick UniformLayerSnapshot
open UniformFourierCalendarSnapshot (join single idle)
open UniformReflectedFourierCalendar OAI.ExactFourier

variable {r:ℕ}(left right delta:Fin r→ℂ)
 (hl:∀i,left i≠0)(hr:∀i,right i≠0)(hd:∀i,delta i≠0)
 (f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)

lemma full_start:
 (full left right delta hl hr hd f hf 0).matrix=Matrix.diagonal left:=by
 simp (disch:=omega) [full,join,single]
lemma full_right_one:
 (full left right delta hl hr hd f hf ((toeplitz r f hf).length+1)).matrix=Matrix.diagonal right:=by
 simp (disch:=omega) [full,join,single,transpose_length]
lemma full_delta:
 (full left right delta hl hr hd f hf ((toeplitz r f hf).length+2)).matrix=Matrix.diagonal delta:=by
 simp (disch:=omega) [full,join,single,transpose_length]
lemma full_right_two:
 (full left right delta hl hr hd f hf ((toeplitz r f hf).length+3)).matrix=Matrix.diagonal right:=by
 simp (disch:=omega) [full,join,single,transpose_length]
lemma full_finish:
 (full left right delta hl hr hd f hf (2*(toeplitz r f hf).length+4)).matrix=Matrix.diagonal left:=by
 simp only[full,join,single,transpose_length]
 split_ifs <;> first|omega|simp only[Snapshot.ofDiagonal_matrix]
lemma full_inactive (g:ℕ)(inactive:2*(toeplitz r f hf).length+5≤g):
 (full left right delta hl hr hd f hf g).matrix=1:=by
 simp only[full,join,single,transpose_length]
 split_ifs <;> first|omega|simp only[UniformFourierCalendarSnapshot.idle_matrix]

end
end ExactFourierCircuits.UniformAxisBoundaryClock
