import DFTModelGlobalSectorPreparationSpecification
import UniformProducedPhysicalCoordinate

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorBilling
open scoped BigOperators
open UniformWorkingLength
open DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelCacheTraversal
noncomputable section

/-- An explicit finite-base estimate, independent of the selected length. -/
theorem polynomial_exponential (ell : ℕ) : (ell+2)^5 ≤ 128*3^ell := by
 induction ell using Nat.strong_induction_on with
 | h ell ih =>
  by_cases small : ell < 4
  · interval_cases ell <;> norm_num
  · obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le (show 3≤ell-1 by omega)
    have step : (ell+2)^5≤3*((ell-1)+2)^5 := by
      have he : ell=t+4 := by omega
      rw [he]
      rw [show t+4-1=t+3 by omega]
      ring_nf
      omega
    calc
     (ell+2)^5≤3*((ell-1)+2)^5 := step
     _≤3*(128*3^(ell-1)) := Nat.mul_le_mul_left _ (ih (ell-1) (by omega))
     _=128*3^ell := by
       have he : ell=(ell-1)+1 := by omega
       conv_rhs => rw [he,pow_succ]
       ring

theorem selected_volume_lower (n : ℕ) : 3^(axisCount n)≤workingLength n := by
 have h:=primeProduct_lower (axisCount n)
 have hp : 1≤binaryFactor n := by
   unfold binaryFactor
   exact Nat.succ_le_of_lt (Nat.pow_pos (by decide))
 exact h.trans (Nat.le_mul_of_pos_right _ hp)

theorem selected_local_sum {n : ℕ} (hn : 0<n) :
 (∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^2)≤
 2130048*workingLength n := by
 have cell (i:Fin (axisCount n+1)) :
   (UniformSelectedCRT.radices n i+1)^2≤129^2*(axisCount n+2)^4 := by
  have hr:=UniformSelectedCRT.radix_quadratic hn i
  have hp:1≤(axisCount n+2)^2 :=
    Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  have h:UniformSelectedCRT.radices n i+1≤129*(axisCount n+2)^2 := by omega
  calc
   (UniformSelectedCRT.radices n i+1)^2≤(129*(axisCount n+2)^2)^2 :=
     Nat.pow_le_pow_left h 2
   _=129^2*(axisCount n+2)^4 := by ring
 calc
  (∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^2)≤
   ∑_i:Fin (axisCount n+1),129^2*(axisCount n+2)^4 := Finset.sum_le_sum (fun i _=>cell i)
  _=(axisCount n+1)*(129^2*(axisCount n+2)^4) := by simp
  _≤129^2*(axisCount n+2)^5 := by
   have h:=Nat.mul_le_mul_right (129^2*(axisCount n+2)^4)
     (show axisCount n+1≤axisCount n+2 by omega)
   convert h using 1; ring
  _≤129^2*(128*3^(axisCount n)) :=
    Nat.mul_le_mul_left _ (polynomial_exponential _)
  _≤2130048*workingLength n := by
    have h:=Nat.mul_le_mul_left 2130048 (selected_volume_lower n)
    convert h using 1; ring

/-- The selected-radix relation is ordinary geometry, not a supplied budget. -/
theorem selected_localBudget {n : ℕ} (hn : 0<n)
 (as : List UniformSectorPacking.Axis)
 (shape : UniformSectorPacking.radices as=List.ofFn (UniformSelectedCRT.radices n)) :
 localBudget as≤2130048*(UniformSectorPacking.radices as).prod := by
 have h:=selected_local_sum hn
 have he : localBudget as=
   ∑i:Fin (axisCount n+1),(UniformSelectedCRT.radices n i+1)^2 := by
  unfold localBudget
  rw [show (as.map (fun a=>(a.widths.sum+1)^2)).sum=
    ((UniformSectorPacking.radices as).map (fun r=>(r+1)^2)).sum by
      simp only [UniformSectorPacking.radices,List.map_map,Function.comp_def]]
  rw [shape,List.map_ofFn,List.sum_ofFn]
  rfl
 rw [he,shape,List.prod_ofFn,UniformSelectedCRT.radices_product]
 exact h

def preparationFactor : ℕ := 12780306000

theorem selected_work {n : ℕ} (hn : 0<n)
 (as : List UniformSectorPacking.Axis)
 (shape : UniformSectorPacking.radices as=List.ofFn (UniformSelectedCRT.radices n)) :
 (run withDirectory (ofList (as.map encodeAxis))).work≤
 preparationFactor*(UniformSectorPacking.radices as).prod := by
 have hw:=withDirectory_work as
 have hl:=selected_localBudget hn as shape
 have ha:=native_axes_le_volume as
 have hp:=native_volume_pos as
 unfold preparationFactor
 omega

/-- Instantiation with the physical family printed in increasing selected-axis order. -/
theorem family_work {n : ℕ} (hn : 0<n) (f:UniformProducedAllAxisGeometry.Family n) :
 (run withDirectory (ofList ((UniformSectorPackingMachine.physicalAxes
   (UniformProducedAllAxisGeometry.geometry f).physical).map encodeAxis))).work≤
 preparationFactor*workingLength n := by
 have h:=selected_work hn _ (UniformProducedPhysicalCoordinate.radices f)
 simpa only [UniformProducedPhysicalCoordinate.radices f,List.prod_ofFn,
   UniformSelectedCRT.radices_product] using h

end
end ExactFourierCircuits.DFTModelGlobalSectorBilling
