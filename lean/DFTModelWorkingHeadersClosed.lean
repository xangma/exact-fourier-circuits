import DFTModelWorkingHeadersCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] program DFTModelCRTClosed.program

/-- Closed n-only producer: selected primes, CRT metadata, and both physical tables. -/
def tables : Prog false w (p (Ty.a w) (Ty.a w)) :=
  .comp program DFTModelCRTClosed.program

theorem tables_value (n : ℕ) (hn : 0<n) :
    (run tables n).val=(run DFTModelCRT.program (DFTModelCRT.selectedInput n)).val := by
  change (run DFTModelCRTClosed.program (run program n).val).val=_
  rw [(actual_headers n hn).1]
  exact DFTModelCRTClosed.selected_value hn

theorem tables_values (n : ℕ) (hn : 0<n) (j : Fin (UniformCRTTraversalCycle.len n)) :
    (run tables n).val.1.look j.val 0=(UniformSelectedPhysicalCRT.physicalAlpha n j).val ∧
    (run tables n).val.2.look j.val 0=((UniformSelectedPhysicalCRT.physicalBeta n).symm j).val := by
  rw [tables_value n hn]
  exact DFTModelCRT.selected_values n j

theorem tables_lengths (n : ℕ) (hn : 0<n) :
    (run tables n).val.1.len=UniformCRTTraversalCycle.len n ∧
    (run tables n).val.2.len=UniformCRTTraversalCycle.len n := by
  rw [tables_value n hn]
  exact DFTModelCRT.selected_output_lengths n

theorem tables_work (n : ℕ) (hn : 0<n) :
    (run tables n).work≤16*UniformWorkingCompletion.preparationBudget n+
      520*(UniformCRTTraversalCycle.len n+1)+1 := by
  have hw := (actual_headers n hn).2.2.1
  have hc := DFTModelCRTClosed.selected_work hn
  change (run program n).work+(run DFTModelCRTClosed.program (run program n).val).work+1≤_
  rw [(actual_headers n hn).1]
  omega

theorem tables_valid (n : ℕ) (hn : 0<n) : (run tables n).valid := by
  change (run program n).valid ∧ (run DFTModelCRTClosed.program (run program n).val).valid
  rw [(actual_headers n hn).1]
  exact ⟨(actual_headers n hn).2.1,DFTModelCRTClosed.selected_valid hn⟩

theorem tables_peak (n : ℕ) (hn : 0<n) : (run tables n).peak≤(n+2)^12 := by
  have hp := peak_bound n hn
  have hc := DFTModelCRTClosed.selected_peak hn
  have hv := (UniformWorkingLength.workingLength_upper hn).le
  change UniformCRTTraversalCycle.len n≤4*n at hv
  have hsmall : (UniformCRTTraversalCycle.len n+1)^2≤16*(n+2)^2 := by nlinarith
  have hpow : 16≤(n+2)^10 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 10
    norm_num at h
    omega
  have hbig : (UniformCRTTraversalCycle.len n+1)^2≤(n+2)^12 := by
    calc
      _≤16*(n+2)^2 := hsmall
      _≤(n+2)^10*(n+2)^2 := Nat.mul_le_mul_right _ hpow
      _=(n+2)^12 := by rw [←pow_add]
  change max (max (run program n).peak
    (run DFTModelCRTClosed.program (run program n).val).peak) 0≤_
  rw [(actual_headers n hn).1]
  exact max_le (max_le hp (hc.trans hbig)) (by omega)

end
end ExactFourierCircuits.DFTModelWorkingHeaders
