import DFTModelCacheDescriptorRowsBounds
import DFTModelCacheDescriptorFitsPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targets sources)
noncomputable section
attribute [local irreducible] pairSizes sourceCount targetCount rowCoordinates rowA rowE rowI0 rowJ0 rowCell

theorem row_indices (v b h : ℕ) (hb : 0<b) (hh : h<targets v b*sources v b) :
    h/sources v b≤v ∧ h%sources v b≤v := by
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  have ht:=UniformWorkspaceSearchMachine.targets_bound (v:=v) hb
  have hp : 0<sources v b := by nlinarith
  have hd : h/sources v b<targets v b := (Nat.div_lt_iff_lt_mul hp).mpr hh
  exact ⟨(Nat.le_of_lt hd).trans ht,(Nat.le_of_lt (Nat.mod_lt h hp)).trans hs⟩

theorem rowCoordinates_peak (v o b h : ℕ) (hb : 0<b) (hbv : b≤v)
    (hh : h<targets v b*sources v b) :
    (run rowCoordinates (((v,o),b),h)).peak≤4*(v+1) := by
  have hs:=(counts_peak v b hbv).2
  have hv:=sourceCount_value v b
  have hd:=row_indices v b h hb hh
  dsimp only [run] at hs hv
  rw [rowCoordinates]
  dsimp only [rowV,rowB,rowI,rowJ,rowsPair,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  rw [hv]
  simp only [max_le_iff]
  omega

theorem rowAE_peak (v o b h : ℕ) (hb : 0<b) (hbv : b≤v)
    (hh : h<targets v b*sources v b) :
    (run rowA (((v,o),b),h)).peak≤10*(v+1)^2 ∧
      (run rowE (((v,o),b),h)).peak≤10*(v+1)^2 := by
  have hc:=rowCoordinates_peak v o b h hb hbv hh
  have hd:=row_indices v b h hb hh
  have hp' : (run pairSizes (run rowCoordinates (((v,o),b),h)).val).peak≤10*(v+1)^2 := by
    rw [rowCoordinates_value]
    exact pairSizes_peak v b _ _ hbv hd.1 hd.2
  dsimp only [run] at hc hp'
  rw [rowA,rowE]
  dsimp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [max_le_iff]
  have hc' : 4*(v+1)≤10*(v+1)^2 := by nlinarith
  omega

theorem rowSmall_peak (v o b h : ℕ) (hb : 0<b) (hbv : b≤v)
    (hh : h<targets v b*sources v b) :
    (run rowSplit (((v,o),b),h)).peak≤10*(v+1)^2 ∧
      (run rowI0 (((v,o),b),h)).peak≤10*(v+1)^2 ∧
      (run rowJ0 (((v,o),b),h)).peak≤10*(v+1)^2 := by
  have hs:=(counts_peak v b hbv).2
  have hv:=sourceCount_value v b
  have hd:=row_indices v b h hb hh
  have hi:=Nat.mul_le_mul hd.1 hbv
  have hj:=Nat.mul_le_mul hd.2 hbv
  have hvv : v*v+v≤10*(v+1)^2 := by nlinarith
  have hbase : 4*(v+1)≤10*(v+1)^2 := by nlinarith
  dsimp only [run] at hs hv
  rw [rowI0,rowJ0]
  dsimp only [rowSplit,rowV,rowI,rowJ,rowB,rowsPair,split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  rw [hv]
  simp only [max_le_iff]
  have hvd:=Nat.div_le_self v 2
  omega

theorem rowCell_peak (v o b h : ℕ) (hb : 0<b) (hbv : b≤v)
    (hh : h<targets v b*sources v b) :
    (run rowCell (((v,o),b),h)).peak≤10*(v+1)^2 := by
  have hae:=rowAE_peak v o b h hb hbv hh
  have hs:=rowSmall_peak v o b h hb hbv hh
  dsimp only [run] at hae hs
  rw [rowCell]
  dsimp only [rowV,rowO,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [max_le_iff]
  omega

theorem rectangleRows_peak (v o b : ℕ) (hb : 0<b) (hbv : b≤v) :
    (run rectangleRows ((v,o),b)).peak≤10*(v+1)^2 := by
  have hc:=(counts_peak v b hbv)
  have ht:=UniformWorkspaceSearchMachine.targets_bound (v:=v) hb
  have hs:=UniformWorkspaceSearchMachine.sources_bound (v:=v) hb
  have hm:=Nat.mul_le_mul ht hs
  have cp : (run rowCount ((v,o),b)).peak≤10*(v+1)^2 := by
    dsimp only [run] at hc
    rw [rowCount]
    dsimp only [rowsPair,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
    rw [show (Code.run targetCount () (v,b)).val=targets v b from targetCount_value v b,
      show (Code.run sourceCount () (v,b)).val=sources v b from sourceCount_value v b]
    simp only [max_le_iff]
    have hbnd : 4*(v+1)≤10*(v+1)^2 := by nlinarith
    have hmul : v*v≤10*(v+1)^2 := by nlinarith
    omega
  change max (max (run rowCount ((v,o),b)).peak
    (Bill.tab (run rowCount ((v,o),b)).val Row7.blank (fun h=>run rowCell (((v,o),b),h))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak,rowCount_value]
  simp only [max_zero,max_le_iff]
  refine ⟨cp,by nlinarith,?_⟩
  apply Finset.sup_le
  intro h hh
  exact rowCell_peak _ _ _ _ hb hbv (Finset.mem_range.mp hh)

end
end ExactFourierCircuits.DFTModelCacheDescriptor
