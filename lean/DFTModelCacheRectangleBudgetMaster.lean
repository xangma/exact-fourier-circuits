import DFTModelCacheRectangleBudgetActual
import UniformAsymptotics

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleBudget
open UniformWorkingLength
noncomputable section

/-- All positive input lengths, including the finite small-axis range. -/
theorem master_log_axes {n : ℕ} (hn : 0<n) :
    Nat.log2 (UniformMasterRootMachine.order n+1)+1≤41*(axisCount n+2)^2 := by
  let ell:=axisCount n
  let E:=(ell+1)*(2*ell+10)
  have small:ell+2≤2^(ell+2):=(Nat.lt_pow_self (by decide : 1<2)).le
  have base:64*(ell+2)^2≤2^(2*ell+10) := by
    calc
      _≤2^6*(2^(ell+2))^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 2)
      _=_:=by rw [←pow_mul,←pow_add]; congr 1; omega
  have prod:primeProduct (ell+1)≤2^E := by
    calc
      _≤(64*((ell+1)+1)^2)^(ell+1):=UniformAsymptotics.primeProduct_upper _
      _≤(2^(2*ell+10))^(ell+1):=Nat.pow_le_pow_left (by simpa only [Nat.add_assoc] using base) _
      _=_:=by rw [←pow_mul]; congr 1; dsimp [E]; ring
  have max:2*n<primeProduct (ell+1):=(maximal_product hn).2
  have nPower:n≤2^E:=by omega
  have cube:=Nat.pow_le_pow_left nPower 3
  have order:UniformMasterRootMachine.order n+1≤2^(3*E+10) := by
    calc
      _≤1024*n^3:=by have h:=(UniformMasterRootMachine.order_bounds hn).2; omega
      _≤2^10*(2^E)^3:=Nat.mul_le_mul_left _ cube
      _=_:=by rw [←pow_mul,←pow_add]; congr 1; omega
  have log:Nat.log2 (UniformMasterRootMachine.order n+1)≤3*E+10 := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow order)
  dsimp [E,ell] at log
  nlinarith

theorem selected_root_work {n : ℕ} (hn : 0<n) :
    rootWork (UniformMasterRootMachine.order n)≤205000*(axisCount n+2)^2 := by
  have root:=root_work_log (UniformMasterRootMachine.order n)
  have log:=master_log_axes hn
  omega

/-- The genuine local work bound, with the master extraction cost discharged
by the selected-length construction. Multiplicity/storage are separate. -/
theorem selected_actual_work {B : ℕ} (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n))
    (q : UniformLocalRectangleDescriptors.Row) (original : UniformSeedHeightPreparation.Config)
    (c : UniformLocalCacheSlotHeaderMachine.Parameters) (slot : UniformLocalCacheChronology.Slot)
    (source : DFTModelCacheRectanglePreparation.ProducedRow (UniformAllAxisSeedPreparation.radix n j) q)
    (layout : UniformChunkMatchingPreparation.Layout
      (DFTModelCacheRectangleMetadata.chunk q original c slot) B)
    (height : slot.depth≤8*DFTModelCacheRectanglePreparation.height q+6)
    (positive : original.C+UniformToeplitzCrossDAG.bankSize
      (DFTModelCacheRectanglePreparation.height q)≤original.negative)
    (negative : original.negative+UniformToeplitzCrossDAG.bankSize
      (DFTModelCacheRectanglePreparation.height q)≤original.constants) :
    let x:=DFTModelCacheRectangleCaller.genuineInput n j q original slot
    (OAI.PowerSaving.RAM.run DFTModelCacheRectangleCaller.program x).valid ∧
    (OAI.PowerSaving.RAM.run DFTModelCacheRectangleCaller.program x).work≤
      localCoefficient*(UniformAllAxisSeedPreparation.radix n j+1)^8+
        205000*(axisCount n+2)^2 := by
  have h:=actual_work n hn j q original c slot source layout height positive negative
  exact ⟨h.1,h.2.trans (Nat.add_le_add_left (selected_root_work hn) _)⟩

end
end ExactFourierCircuits.DFTModelCacheRectangleBudget
