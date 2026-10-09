import UniformCalendarRenderTick

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderMatching
noncomputable section
open OAI.ExactFourier UniformReplayPrint UniformToeplitzChunkWord UniformLocalFourierLayers
open UniformGlobalCalendarMatchingPhase UniformGlobalCalendarPhases UniformCalendarRenderTick
open UniformGlobalMatchingScaleMachine

theorem shearLayers_cons {v R : ℕ} (bank : Fin R → ℂ)
    (W : List (ShearCode (Fin v) R)) (L : List (List (ShearCode (Fin v) R)))
    (h : ∀ V∈W::L,Matching V) :
    shearLayers bank (W::L) h = matchingLayers bank W (h W (by simp)) ++
      shearLayers bank L (fun V hV => h V (by simp [hV])) := by
  simp only [shearLayers,List.attach_cons,List.map_cons,List.map_map,List.flatten_cons,Function.comp_def]

/-- Literal matching number and phase, retaining even empty matching slots. -/
theorem matching_tick {v R : ℕ} (bank : Fin R → ℂ)
    (L : List (List (ShearCode (Fin v) R))) (h : ∀ W∈L,Matching W)
    (j : Fin L.length) (p : Fin 28) :
    tick (shearLayers bank L h) (28*j.val+p.val) =
      (phaseSnapshot bank (L.get j) (h _ (List.get_mem _ _))
        (phases.get ⟨p.val,by rw [phases_length];exact p.isLt⟩)).matrix := by
  induction L with
  | nil => exact Fin.elim0 j
  | cons W L ih =>
    rw [shearLayers_cons,tick_append,matchingLayers_length]
    by_cases zero : j.val=0
    · have eq : j=0 := Fin.ext zero
      subst j
      simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_add,ite_eq_left p.isLt,List.get_cons_zero]
      rw [tick_of_lt _ p.val (by rw [matchingLayers_length];exact p.isLt)]
      exact matching_phase_snapshot bank W _ p
    · let k : Fin L.length := ⟨j.val-1,by have:=j.isLt;simp only [List.length_cons] at this;omega⟩
      have eq : j=k.succ := Fin.ext (by simp only [k,Fin.val_succ];omega)
      have after : ¬28*j.val+p.val<28 := by omega
      rw [ite_eq_right after,eq]
      simp only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ]
      have offset : 28*(k.val+1)+p.val-28=28*k.val+p.val := by omega
      rw [offset]
      exact ih (fun V hV => h V (by simp [hV])) k

/-- The physically selected ABI elapsed time gives exactly the actual typed
render's floor-divided slot and modulo-28 phase. -/
theorem ordinary_tick {v R : ℕ} (bank : Fin R → ℂ)
    (L : List (List (ShearCode (Fin v) R))) (h : ∀ W∈L,Matching W)
    (elapsed : ℕ) (bound : elapsed < 28*L.length) :
    let j : Fin L.length := ⟨elapsed/28,by omega⟩
    let p : Fin 28 := ⟨elapsed%28,Nat.mod_lt _ (by decide)⟩
    tick (shearLayers bank L h) elapsed =
      (phaseSnapshot bank (L.get j) (h _ (List.get_mem _ _))
        (phases.get ⟨p.val,by rw [phases_length];exact p.isLt⟩)).matrix := by
  dsimp only
  have eq : 28*(elapsed/28)+elapsed%28=elapsed := by omega
  simpa only [eq] using matching_tick bank L h
    ⟨elapsed/28,by omega⟩ ⟨elapsed%28,Nat.mod_lt _ (by decide)⟩

end
end ExactFourierCircuits.UniformCalendarRenderMatching
