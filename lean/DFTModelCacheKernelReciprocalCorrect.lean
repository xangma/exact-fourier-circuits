import DFTModelCacheKernelReciprocal

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheKernelReciprocal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

theorem nextValue_coefficient (n k : ℕ) (h g : Tape ℂ) (f : PowerSeries ℂ)
    (hn:0<n) (hk:k<n)
    (hh:∀i,i<n → h.look i 0=PowerSeries.coeff i f)
    (hg:∀i,i<k → g.look i 0=PowerSeries.coeff i f⁻¹) :
    nextValue h g (h.look 0 0)⁻¹ k=PowerSeries.coeff k f⁻¹ := by
  have h0:=hh 0 hn
  cases k with
  | zero => simp [nextValue,h0,PowerSeries.coeff_inv,
      PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k =>
    rw [nextValue,ite_eq_right (by omega),h0,PowerSeries.coeff_zero_eq_constantCoeff,
      UniformReciprocalPreparation.inverse_coeff_succ]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i=>PowerSeries.coeff (i+1) f *
      PowerSeries.coeff (k-i) f⁻¹) (k+1)]
    unfold partialSum
    apply Finset.sum_congr rfl
    intro i hi
    have hib:=Finset.mem_range.mp hi
    rw [hh (i+1) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [hg (k-i) (by omega)]

attribute [local irreducible] step

theorem look_set (v : Tape ℂ) (i j : ℕ) (x : ℂ) (hj:j<v.len) :
    (v.set i x).look j 0=if j=i then x else v.look j 0 := by
  simp only [Tape.look,Tape.set,hj,↓reduceDIte]

theorem steps_coefficients (n j : ℕ) (h : Tape ℂ) (f : PowerSeries ℂ)
    (hn:0<n) (hj:j≤n)
    (hh:∀i,i<n → h.look i 0=PowerSeries.coeff i f) :
    ∀i,i<j → (steps n h (h.look 0 0)⁻¹ j).val.look i 0=
      PowerSeries.coeff i f⁻¹ := by
  induction j with
  | zero => intro i hi;omega
  | succ j ih =>
    have hjn:j<n:=by omega
    have old:=ih (by omega)
    have len:=(steps_bounds n j h (h.look 0 0)⁻¹ (by omega)).1
    intro i hi
    change (run step (((n,h),(h.look 0 0)⁻¹),
      (j,(steps n h (h.look 0 0)⁻¹ j).val))).val.look i 0=_
    rw [step_value]
    have hin:i<n:=by omega
    rw [look_set _ _ _ _ (by omega)]
    by_cases he:i=j
    · subst i
      have next:=nextValue_coefficient n j h
        (steps n h (h.look 0 0)⁻¹ j).val f hn hjn hh old
      rw [ite_eq_left (rfl:j=j)]
      exact next
    · have hij:i<j:=by omega
      rw [ite_eq_right he]
      exact old i hij

theorem tape_eq_tab {α : Type} (v : Tape α) (n : ℕ) (z : α) (f : ℕ→α)
    (len:v.len=n) (values:∀i,i<n → v.look i z=f i) : v=Tape.tab n f := by
  cases v with
  | mk l p =>
    dsimp only [Tape.len] at len
    subst l
    congr 1
    funext i
    simpa [Tape.look,Tape.tab,i.isLt] using values i.val i.isLt

/-- Exact source reciprocal-series coefficients, with the original coefficient
table produced by the caller's Newton producer rather than supplied G values. -/
theorem program_value (n : ℕ) (h : Tape ℂ) (f : PowerSeries ℂ)
    (hn:0<n) (hh:∀i,i<n → h.look i 0=PowerSeries.coeff i f) :
    (run program (n,h)).val=Tape.tab n (fun i=>PowerSeries.coeff i f⁻¹) := by
  rw [program_run]
  apply tape_eq_tab _ n 0 _
  · exact (steps_bounds n n h (h.look 0 0)⁻¹ le_rfl).1
  · exact steps_coefficients n n h f hn le_rfl hh

theorem program_specification (n : ℕ) (h : Tape ℂ) (f : PowerSeries ℂ)
    (hn:0<n) (hf:PowerSeries.constantCoeff f≠0)
    (hh:∀i,i<n → h.look i 0=PowerSeries.coeff i f) :
    (run program (n,h)).val=Tape.tab n (fun i=>PowerSeries.coeff i f⁻¹) ∧
    (run program (n,h)).valid ∧ (run program (n,h)).work≤110*(n+1)^2 ∧
    (run program (n,h)).peak≤n := by
  refine ⟨program_value n h f hn hh,program_valid n h ?_,
    program_work n h,program_peak n h⟩
  simpa only [hh 0 hn,PowerSeries.coeff_zero_eq_constantCoeff] using hf

end
end ExactFourierCircuits.DFTModelCacheKernelReciprocal
