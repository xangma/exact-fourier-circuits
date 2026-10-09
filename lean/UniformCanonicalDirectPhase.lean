import UniformCalendarRenderDirect
import UniformCalendarExplicitLocalFamily

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalDirectPhase
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformDirectToeplitz
open UniformGlobalCalendarPhases UniformGlobalCalendarMatchingPhase UniformGlobalMatchingScaleMachine
open UniformCalendarRenderDirect UniformCalendarRenderTick
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology

/-- The literal two-port cached phase, with its ordered destination/source call. -/
def pairPhase (mu : ℂ) : Phase → Snapshot (Fin 2)
 | .diagonal lane => Snapshot.ofDiagonal (factor mu lane) (factor_nonzero mu lane)
 | .kernel => Snapshot.ofCall (Function.Embedding.refl _)

@[simp] theorem pairPhase_matrix (mu : ℂ) (p : Phase) :
 (pairPhase mu p).matrix=phaseMatrix mu p:=by
 cases p with
 | diagonal lane => exact Snapshot.ofDiagonal_matrix _ _
 | kernel => simp [pairPhase,phaseMatrix]

/-- A genuine direct scale has no calls and retains the other coordinates. -/
def scalePhase {v : ℕ} (h : Fin v→ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
 (i : Fin v) : Snapshot (Fin v):=
 Snapshot.ofDiagonal (fun j=>if j=i then h ⟨0,hv⟩ else 1)
  (fun j=>by split_ifs;exact h0;exact one_ne_zero)

def shearPhase {v : ℕ} (h : Fin v→ℂ) (i : Fin v) (j : Fin i.val)
 (p : Phase) : Snapshot (Fin v):=
 (pairPhase (coefficient h i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩) p).embed
  (Embedded.pair i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩
   (by intro eq;have val : i.val=j.val:=congrArg Fin.val eq;exact (ne_of_lt j.isLt) val.symm))

def operationPhase {v : ℕ} (h : Fin v→ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
 (op : Operation v) (p : ℕ) : Snapshot (Fin v):=
 match op with
 | .scale i => scalePhase h hv h0 i
 | .shear i j => shearPhase h i j
   (phases.get ⟨p%28,by rw [phases_length];exact Nat.mod_lt _ (by decide)⟩)

/-- This snapshot is explicit; its matrix is the actual direct operation tick. -/
theorem operationPhase_tick {v : ℕ} (h : Fin v→ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
 (o K : ℕ) (op : Operation v) (p : ℕ) (hp : p<duration (ofOperation o K op)) :
 (operationPhase h hv h0 op p).matrix=tick (operationLayers h hv h0 op) p:=by
 cases op with
 | scale i =>
  exact (Snapshot.ofDiagonal_matrix _ _).trans (scale_tick h hv h0 i p hp).symm
 | shear i j =>
  have bound : p<28:=hp
  simp only [operationPhase,shearPhase,Snapshot.embed_matrix,pairPhase_matrix,Nat.mod_eq_of_lt bound]
  exact (shear_tick h hv h0 i j ⟨p,bound⟩).symm

/-- Physical direct descriptor prefix durations select the same explicit phase. -/
theorem leaf_phase_tick {v : ℕ} (h : Fin v→ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
 (o K : ℕ) (j : Fin (topology v).length) (p : ℕ)
 (hp : p<duration (ofOperation o K ((topology v).get j))) :
 (operationPhase h hv h0 ((topology v).get j) p).matrix=
 tick (UniformLocalFourierLayers.serial (UniformDirectToeplitz.word h hv h0))
  (elapsed ((leafRecords v o K).take j.val)+p):=by
 rw [leaf_tick h hv h0 o K j p hp]
 exact operationPhase_tick h hv h0 o K _ p hp

/-- Specialization to the actual native direct piece, with its real coefficient bank. -/
theorem direct_piece_phase_tick (v : ℕ) (cap : v<196) (hv : 0<v)
 (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
 (o K : ℕ) (j : Fin (topology v).length) (p : ℕ)
 (hp : p<duration (ofOperation o K ((topology v).get j))) :
 (operationPhase (fun i : Fin v=>PowerSeries.coeff i.val f) hv
  (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf)
  ((topology v).get j) p).matrix=
 tick (UniformLocalFourierLayers.render (.direct v cap) f hf)
  (elapsed ((leafRecords v o K).take j.val)+p):=by
 rw [direct_leaf_tick v cap hv f hf o K j p hp]
 exact operationPhase_tick _ hv _ o K _ p hp

end
end ExactFourierCircuits.UniformCanonicalDirectPhase
