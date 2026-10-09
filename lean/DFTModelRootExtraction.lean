import DFTModelScalarPower
import UniformMasterRootMachine

set_option autoImplicit false

/-!
Paper §5.3, root extraction after (5.9). This finite typed code takes an order
D and its one supplied canonical root, then produces the specified divisor
root by charged binary powering. It makes no root request and accepts no
precomputed complex coefficient. `halfAngle` is the actual chirp specialization.
-/
namespace ExactFourierCircuits.DFTModelRootExtraction
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w (p w sc)

def exponent {r : Port} : Code false r Input w :=
  .comp (.fork (.comp (.atom .snd) (.atom .fst)) (.atom .fst))
    (.atom (.int .div))

def rootValue {r : Port} : Code false r Input sc :=
  .comp (.atom .snd) (.atom .snd)

def program : Prog false Input sc :=
  .comp (.fork exponent rootValue) (.importClosed DFTModelScalarPower.program)

def doubleDivisor : Prog false Input Input :=
  .fork (.comp (.fork (.atom .fst) (.atom (.lit 2))) (.atom (.int .mul)))
    (.atom .snd)

def halfAngle : Prog false Input sc := .comp doubleDivisor program

theorem exponent_run {r : Port} (h : Handler r) (d D : ℕ) (z : ℂ) :
    exponent.run h (d,(D,z)) = ⟨D/d,7,D/d,True⟩ := by
  simp [exponent, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word]

theorem rootValue_run {r : Port} (h : Handler r) (d D : ℕ) (z : ℂ) :
    rootValue.run h (d,(D,z)) = ⟨z,3,0,True⟩ := by
  simp [rootValue, Code.run, Atom.run, Bill.pass, Bill.pay, Bill.one]

attribute [local irreducible] exponent rootValue program doubleDivisor

theorem program_run (d D : ℕ) (z : ℂ) :
    run program (d,(D,z)) =
      (run DFTModelScalarPower.program (D/d,z)).pay 13 (D/d) := by
  simp only [program, run, Code.run]
  rw [exponent_run, rootValue_run]
  simp only [Bill.pass, Bill.pay, Bill.one]
  simp only [max_zero, true_and, and_true]
  congr 1 <;> omega

theorem program_value (d D : ℕ) (z : ℂ) :
    (run program (d,(D,z))).val = z^(D/d) := by
  rw [program_run]
  exact DFTModelScalarPower.program_value _ _

theorem program_valid (d D : ℕ) (z : ℂ) :
    (run program (d,(D,z))).valid := by
  rw [program_run]
  exact DFTModelScalarPower.program_valid _ _

theorem program_work (d D : ℕ) (z : ℂ) :
    (run program (d,(D,z))).work ≤ 40*(Nat.log2 (D/d+1)+1)+22 := by
  rw [program_run]
  change (run DFTModelScalarPower.program (D/d,z)).work+13 ≤ _
  have h := DFTModelScalarPower.program_work (D/d) z
  omega

theorem program_peak (d D : ℕ) (z : ℂ) :
    (run program (d,(D,z))).peak ≤ D+2 := by
  rw [program_run]
  change max (run DFTModelScalarPower.program (D/d,z)).peak (D/d) ≤ _
  have h := DFTModelScalarPower.program_peak (D/d) z
  have hd := Nat.div_le_self D d
  omega

theorem divisor_root (d D : ℕ) (hd : 0<d) (hD : 0<D) (hdiv : d∣D) :
    (run program (d,(D,OAI.ExactFourier.zeta D))).val=OAI.ExactFourier.zeta d := by
  rw [program_value]
  exact UniformRoots.specifiedRoot_divisor_power D d hD hd hdiv

theorem doubleDivisor_run (n D : ℕ) (z : ℂ) :
    run doubleDivisor (n,(D,z)) = ⟨(2*n,(D,z)),7,max 2 (2*n),True⟩ := by
  simp [doubleDivisor, run, Code.run, Atom.run, NOp.run, Bill.pass, Bill.pay,
    Bill.one, Bill.word, Nat.mul_comm]

theorem halfAngle_run (n D : ℕ) (z : ℂ) :
    run halfAngle (n,(D,z)) =
      (run program (2*n,(D,z))).pay 8 (max 2 (2*n)) := by
  simp only [halfAngle, run, Code.run]
  change ((run doubleDivisor (n,(D,z))).pass (run program)).pay 1 0 = _
  rw [doubleDivisor_run]
  simp only [Bill.pass, Bill.pay, run]
  congr 1
  · omega
  · omega
  · simp

theorem halfAngle_value {n : ℕ} (hn : 0<n) :
    (run halfAngle (n,(UniformMasterRootMachine.order n,
      OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val =
        OAI.ExactFourier.zeta (2*n) := by
  rw [halfAngle_run]
  exact divisor_root (2*n) _ (by omega) (UniformMasterRootMachine.order_bounds hn).1
    (UniformBatching.chirpOrder_dvd n (UniformWorkingLength.workingLength n))

theorem halfAngle_valid (n D : ℕ) (z : ℂ) :
    (run halfAngle (n,(D,z))).valid := by
  rw [halfAngle_run]
  exact program_valid _ _ _

theorem halfAngle_work (n D : ℕ) (z : ℂ) :
    (run halfAngle (n,(D,z))).work ≤ 40*(Nat.log2 (D/(2*n)+1)+1)+30 := by
  rw [halfAngle_run]
  change (run program (2*n,(D,z))).work+8 ≤ _
  have h := program_work (2*n) D z
  omega

theorem halfAngle_peak (n D : ℕ) (z : ℂ) :
    (run halfAngle (n,(D,z))).peak ≤ max D (2*n)+2 := by
  rw [halfAngle_run]
  change max (run program (2*n,(D,z))).peak (max 2 (2*n)) ≤ _
  have h := program_peak (2*n) D z
  omega

/-- The exact source stage charges `11+loopCost(D/(2n))` instructions for
half-angle extraction. The typed implementation preserves that budget up to
this fixed factor, rather than introducing a power-table-sized cost. -/
theorem halfAngle_work_source (n D : ℕ) (z : ℂ) :
    (run halfAngle (n,(D,z))).work ≤
      40*(11+UniformPowerMachine.loopCost (D/(2*n))) := by
  rw [halfAngle_run, program_run]
  change (run DFTModelScalarPower.program (D/(2*n),z)).work+13+8 ≤ _
  have h := DFTModelScalarPower.program_work_source (D/(2*n)) z
  omega

end
end ExactFourierCircuits.DFTModelRootExtraction
