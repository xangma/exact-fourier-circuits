import DFTModelRootExtraction
import DFTModelRootProgram
import DFTModelChirpCorrect

set_option autoImplicit false

/-!
Closed composition of the actual integer master-order algorithm, charged
divisor-root extraction, and charged interleaved chirp-table publication.
The only complex input is the single supplied master root. This is preparation
for the actual source algorithm, not the recursive DFT compiler.
-/
namespace ExactFourierCircuits.DFTModelRootChirp
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def program : Prog false DFTModelRootExtraction.Input (Ty.a sc) :=
  .comp (.fork (.atom .fst) DFTModelRootExtraction.halfAngle)
    (.importClosed DFTModelChirp.program)

def header : Prog false (p w sc) DFTModelRootExtraction.Input :=
  .fork (.atom .fst)
    (.fork (.comp (.atom .fst) (.importClosed DFTModelRoot.program)) (.atom .snd))

def masterProgram : Prog false (p w sc) (Ty.a sc) := .comp header program

attribute [local irreducible] DFTModelRootExtraction.halfAngle
  DFTModelRoot.program DFTModelChirp.program header program

theorem program_run (n D : ℕ) (z : ℂ) :
    run program (n,(D,z)) =
      ((run DFTModelRootExtraction.halfAngle (n,(D,z))).pass
        (fun eta => run DFTModelChirp.program (n,eta))).pay 4 0 := by
  simp only [program, run, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay]
  simp only [zero_max, max_zero, true_and, and_true]
  congr 1
  omega

theorem program_value {n : ℕ} (hn : 0<n) :
    (run program (n,(UniformMasterRootMachine.order n,
      OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val =
        DFTModelChirp.bank n (OAI.ExactFourier.zeta (2*n)) := by
  rw [program_run]
  change (run DFTModelChirp.program (n,
    (run DFTModelRootExtraction.halfAngle (n,(UniformMasterRootMachine.order n,
      OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val)).val = _
  rw [DFTModelRootExtraction.halfAngle_value hn]
  exact DFTModelChirp.specified_value n hn

theorem program_valid (n D : ℕ) (z : ℂ) : (run program (n,(D,z))).valid := by
  rw [program_run]
  exact ⟨DFTModelRootExtraction.halfAngle_valid _ _ _,DFTModelChirp.program_valid _ _⟩

theorem program_work (n D : ℕ) (z : ℂ) :
    (run program (n,(D,z))).work ≤
      40*(11+UniformPowerMachine.loopCost (D/(2*n)))+530*n+50 := by
  rw [program_run]
  change (run DFTModelRootExtraction.halfAngle (n,(D,z))).work+
    (run DFTModelChirp.program (n,(run DFTModelRootExtraction.halfAngle (n,(D,z))).val)).work+4 ≤ _
  have hroot := DFTModelRootExtraction.halfAngle_work_source n D z
  have hchirp := DFTModelChirp.program_work n
    (run DFTModelRootExtraction.halfAngle (n,(D,z))).val
  omega

theorem program_peak (n D : ℕ) (z : ℂ) :
    (run program (n,(D,z))).peak ≤ max (max D (2*n)+2) ((n+2)^2) := by
  rw [program_run]
  change max (max (run DFTModelRootExtraction.halfAngle (n,(D,z))).peak
    (run DFTModelChirp.program (n,(run DFTModelRootExtraction.halfAngle (n,(D,z))).val)).peak) 0 ≤ _
  have hroot := DFTModelRootExtraction.halfAngle_peak n D z
  have hchirp := DFTModelChirp.program_peak n
    (run DFTModelRootExtraction.halfAngle (n,(D,z))).val
  omega

theorem header_run (n : ℕ) (z : ℂ) :
    run header (n,z) =
      ((run DFTModelRoot.program n).pass (fun D => Bill.one (n,(D,z)))).pay 6 0 := by
  simp only [header, run, Code.run, Atom.run, Bill.one, Bill.pass, Bill.pay]
  simp only [zero_max, max_zero, true_and, and_true]
  congr 1
  omega

theorem masterProgram_run (n : ℕ) (z : ℂ) :
    run masterProgram (n,z) =
      ((run DFTModelRoot.program n).pass
        (fun D => run program (n,(D,z)))).pay 8 0 := by
  change ((run header (n,z)).pass (run program)).pay 1 0 = _
  rw [header_run]
  simp only [Bill.pass, Bill.pay, Bill.one]
  simp only [max_zero, and_true]
  congr 1
  omega

/-- From n and the one prescribed root; no length, order or coefficient table
is supplied to this actual finite preparation program. -/
theorem masterProgram_value {n : ℕ} (hn : 0<n) :
    (run masterProgram (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val =
      DFTModelChirp.bank n (OAI.ExactFourier.zeta (2*n)) := by
  rw [masterProgram_run]
  change (run program (n,((run DFTModelRoot.program n).val,
    OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val = _
  rw [(DFTModelRoot.actual_master_order n hn).1]
  exact program_value hn

theorem masterProgram_valid {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run masterProgram (n,z)).valid := by
  rw [masterProgram_run]
  exact ⟨(DFTModelRoot.actual_master_order n hn).2.1,program_valid _ _ _⟩

theorem masterProgram_work {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run masterProgram (n,z)).work ≤
      6*UniformMasterRootMachine.preparationBudget n+
      40*(11+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/(2*n)))+530*n+58 := by
  rw [masterProgram_run]
  change (run DFTModelRoot.program n).work+
    (run program (n,((run DFTModelRoot.program n).val,z))).work+8 ≤ _
  rw [(DFTModelRoot.actual_master_order n hn).1]
  have horder := (DFTModelRoot.actual_master_order n hn).2.2.1
  have hchirp := program_work n (UniformMasterRootMachine.order n) z
  omega

theorem masterProgram_peak {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run masterProgram (n,z)).peak ≤ (n+2)^13 := by
  let B := (n+2)^12
  have hB : 1≤B := by
    calc
      1 = (1:ℕ)^12 := by norm_num
      _ ≤ (n+2)^12 := Nat.pow_le_pow_left (by omega) 12
  have hsquare : (n+2)^2≤B := Nat.pow_le_pow_right (by omega) (by decide)
  have hsmall : 2*n+2≤(n+2)^2 := by nlinarith
  have hD : UniformMasterRootMachine.order n≤B :=
    ((UniformMasterRootMachine.order_bounds hn).2.le).trans
      (UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have hraise : B+2≤(n+2)^13 := by
    calc
      B+2 ≤ 3*B := by omega
      _ ≤ (n+2)*B := Nat.mul_le_mul_right _ (by omega)
      _ = (n+2)^13 := by simp [B,pow_succ,Nat.mul_comm]
  rw [masterProgram_run]
  change max (max (run DFTModelRoot.program n).peak
    (run program (n,((run DFTModelRoot.program n).val,z))).peak) 0 ≤ _
  rw [(DFTModelRoot.actual_master_order n hn).1]
  have horder := (DFTModelRoot.actual_master_order n hn).2.2.2
  have hchirp := program_peak n (UniformMasterRootMachine.order n) z
  omega

end
end ExactFourierCircuits.DFTModelRootChirp
