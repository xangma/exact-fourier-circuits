import UniformCalendarRenderTick
import UniformDirectLeafCacheChronology

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderDirect
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformDirectToeplitz
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology UniformCalendarRenderTick
open UniformGlobalCalendarPhases UniformGlobalMatchingScaleMachine

theorem flatten_tick {n : ℕ} {α : Type} (L : List α) (f : α → List (Layer n))
    (j : Fin L.length) (p : ℕ) (hp : p < (f (L.get j)).length) :
    tick ((L.map f).flatten) (((L.take j.val).map (fun a => (f a).length)).sum+p) =
      tick (f (L.get j)) p := by
  induction L with
  | nil => exact Fin.elim0 j
  | cons a L ih =>
    by_cases zero : j.val=0
    · have eq : j=0 := Fin.ext zero
      subst j
      simp only [List.get_cons_zero] at hp
      simp only [Fin.val_zero,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,
        List.map_cons,List.flatten_cons,tick_append,List.get_cons_zero,hp,↓reduceIte]
    · let k : Fin L.length := ⟨j.val-1,by have:=j.isLt;simp only [List.length_cons] at this;omega⟩
      have eq : j=k.succ := Fin.ext (by simp only [k,Fin.val_succ];omega)
      rw [eq] at hp ⊢
      simp only [Fin.val_succ,List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons,
        List.get_eq_getElem,List.getElem_cons_succ,tick_append]
      have after : ¬(f a).length+((L.take k.val).map (fun a => (f a).length)).sum+p < (f a).length := by omega
      rw [ite_eq_right after]
      rw [show (f a).length+((L.take k.val).map (fun a => (f a).length)).sum+p-(f a).length=
        ((L.take k.val).map (fun a => (f a).length)).sum+p by omega]
      exact ih k hp

def operationLayers {v : ℕ} (h : Fin v → ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
    (op : Operation v) : List (Layer v) := serial (UniformDirectToeplitz.render h hv h0 op)

theorem operation_length {v : ℕ} (h : Fin v → ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
    (o K : ℕ) (op : Operation v) :
    (operationLayers h hv h0 op).length = duration (ofOperation o K op) := by
  rw [operationLayers,serial_length]
  cases op with
  | scale i => rfl
  | shear i j => exact shear_length ..

/-- The actual leaf's rendered tick uses the physical descriptor list's exact
prefix duration: a scale contributes one tick and a shear all28 literal phases. -/
theorem leaf_tick {v : ℕ} (h : Fin v → ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
    (o K : ℕ) (j : Fin (topology v).length) (p : ℕ)
    (hp : p < duration (ofOperation o K ((topology v).get j))) :
    tick (serial (UniformDirectToeplitz.word h hv h0))
      (elapsed ((leafRecords v o K).take j.val)+p) =
      tick (operationLayers h hv h0 ((topology v).get j)) p := by
  have flat : (((topology v).map (operationLayers h hv h0)).flatten) =
      serial (UniformDirectToeplitz.word h hv h0) := by
    rw [←UniformDirectToeplitz.render_topology h hv h0]
    change ((topology v).map (fun op => serial (UniformDirectToeplitz.render h hv h0 op))).flatten=_
    simp only [serial,List.map_flatten,List.map_map,Function.comp_def]
  have durationEq : elapsed ((leafRecords v o K).take j.val) =
      (((topology v).take j.val).map (fun op => (operationLayers h hv h0 op).length)).sum := by
    simp only [leafRecords,←List.map_take,elapsed,List.map_map,Function.comp_def,
      operation_length h hv h0 o K]
  rw [durationEq,←flat]
  exact flatten_tick (topology v) (operationLayers h hv h0) j p
    (by rw [operation_length h hv h0 o K];exact hp)

theorem scale_tick {v : ℕ} (h : Fin v → ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
    (i : Fin v) (p : ℕ) (hp : p<1) :
    tick (operationLayers h hv h0 (.scale i)) p =
      Matrix.diagonal (fun j => if j=i then h ⟨0,hv⟩ else 1) := by
  have eq : p=0 := by omega
  subst p
  simp [operationLayers,UniformDirectToeplitz.render,serial,tick,scaleStep,
    WordStep.matrix,scaleMatrix]

theorem shear_tick {v : ℕ} (h : Fin v → ℂ) (hv : 0<v) (h0 : h ⟨0,hv⟩≠0)
    (i : Fin v) (j : Fin i.val) (p : Fin 28) :
    tick (operationLayers h hv h0 (.shear i j)) p.val =
      Embedded.matrix
        (Embedded.pair i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩
          (by intro eq;have val : i.val=j.val := congrArg Fin.val eq;exact (ne_of_lt j.isLt) val.symm))
        (phaseMatrix (coefficient h i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩)
          (phases.get ⟨p.val,by rw [phases_length];exact p.isLt⟩)) := by
  have bound : p.val < (operationLayers h hv h0 (.shear i j)).length := by
    simp only [operationLayers,serial_length,UniformDirectToeplitz.render,shear_length]
    exact p.isLt
  rw [tick_of_lt _ p.val bound]
  simp only [operationLayers,serial,UniformDirectToeplitz.render,shear,
    TensorWords.embeddedWord,List.get_eq_getElem,List.getElem_map,Layer.step_matrix,
    TensorWords.embedStep_matrix]
  congr 1
  simpa only [List.get_eq_getElem] using word_phase_matrix
    (coefficient h i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩) p

theorem direct_leaf_tick (v : ℕ) (cap : v<196) (hv : 0<v)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (o K : ℕ) (j : Fin (topology v).length) (p : ℕ)
    (hp : p<duration (ofOperation o K ((topology v).get j))) :
    tick (UniformLocalFourierLayers.render (.direct v cap) f hf)
      (elapsed ((leafRecords v o K).take j.val)+p) =
      tick (operationLayers (fun i : Fin v => PowerSeries.coeff i.val f) hv
        (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf)
        ((topology v).get j)) p := by
  unfold UniformLocalFourierLayers.render UniformBalancedToeplitz.render
  simp only [hv,↓reduceDIte]
  exact leaf_tick _ hv _ o K j p hp

end
end ExactFourierCircuits.UniformCalendarRenderDirect
