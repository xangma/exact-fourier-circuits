import UniformCalendarNativePieces
import UniformActualCalendarDirectSeedValue

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNativeDirect
noncomputable section
open OAI.ExactFourier UniformDirectToeplitz UniformCanonicalDirectPhase
open UniformLocalFourierLayers UniformLocalCacheTiming UniformCalendarNativePieces
open UniformCalendarRenderTick UniformDirectLeafCacheChronology UniformTransposeDescriptorMachine
open UniformActualCalendarDirectSource

lemma topology_positive {v:ℕ}(j:Fin (topology v).length):0<v:=by
 by_contra zero
 have eq:v=0:=by omega
 subst v
 exact Fin.elim0 j

def snapshot (r v:ℕ)(j:Fin (topology v).length)(elapsed:ℕ):UniformLayerSnapshot.Snapshot (Fin v):=
 operationPhase (fun i:Fin v=>PowerSeries.coeff i.val (NewtonFourier.invH (zeta r)))
  (topology_positive j) (invH_zero r v (topology_positive j)) ((topology v).get j) elapsed

theorem snapshot_tick (r v o K:ℕ)(j:Fin (topology v).length)(elapsed:ℕ)
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta r))≠0}{L:List (Layer v)}
 (actual:Core (NewtonFourier.invH (zeta r)) hf (.direct v o) L)
 (phase:elapsed<duration (ofOperation o K ((topology v).get j))):
 (snapshot r v j elapsed).matrix=
 tick L (UniformDirectLeafCacheChronology.elapsed ((leafRecords v o K).take j.val)+elapsed):=by
 cases actual with
 | direct v o cap=>
  exact direct_piece_phase_tick v cap (topology_positive j) (NewtonFourier.invH (zeta r)) hf o K j elapsed phase

open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheSemanticExecution
def source {r v:ℕ}{c:Config}{positive:2≤r}{s:State}(o K elapsed:ℕ)
 (j:Fin (topology v).length)
 (res:SemanticResult c r (ofOperation o K ((topology v).get j))
  (UniformDirectLeafCacheSource.mu r K (ofOperation o K ((topology v).get j))) positive s)
 (band:Fin v↪Fin r)(coordinates:∀i,(band i).val=o+i.val):
 UniformActualCalendarLocalSources.Source (UniformActualCalendarDirectProduced.event res elapsed)
  (snapshot r v j elapsed) band:=
 seed_operation_source o K elapsed (topology_positive j) ((topology v).get j) res band coordinates

end
end ExactFourierCircuits.UniformActualCalendarNativeDirect
