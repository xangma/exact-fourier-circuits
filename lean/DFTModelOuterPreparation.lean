import DFTModelChirpOperands
import DFTModelRootProgram
import DFTModelRootExtraction

set_option autoImplicit false

/-! Closed outer coefficient preparation. The integer order and working length
are computed by charged syntax. The only supplied complex scalar is the one
canonical master root; neither a half-angle root nor a coefficient table is input. -/
namespace ExactFourierCircuits.DFTModelOuterPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w sc

def orderHeader : Prog false Input DFTModelRootExtraction.Input :=
  .fork (.atom .fst)
    (.fork (.comp (.atom .fst) (.importClosed DFTModelRoot.program)) (.atom .snd))

def halfRoot : Prog false Input sc :=
  .comp orderHeader DFTModelRootExtraction.halfAngle

def lengthPair : Prog false Input (p w w) :=
  .fork (.atom .fst) (.comp (.atom .fst) DFTModelRoot.workingLength)

def header : Prog false Input DFTModelChirpTables.Input := .fork lengthPair halfRoot

def program : Prog false Input DFTModelChirpTables.Output :=
  .comp header DFTModelChirpTables.program

attribute [local irreducible] DFTModelRoot.program DFTModelRoot.workingLength
  DFTModelRootExtraction.halfAngle DFTModelChirpTables.program

theorem orderHeader_run (n : ℕ) (z : ℂ) :
    run orderHeader (n,z)=
      ((run DFTModelRoot.program n).pass (fun D => Bill.one (n,(D,z)))).pay 6 0 := by
  simp only [orderHeader,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem halfRoot_run (n : ℕ) (z : ℂ) :
    run halfRoot (n,z)=((run DFTModelRoot.program n).pass
      (fun D => run DFTModelRootExtraction.halfAngle (n,(D,z)))).pay 8 0 := by
  change ((run orderHeader (n,z)).pass (run DFTModelRootExtraction.halfAngle)).pay 1 0 = _
  rw [orderHeader_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,and_true]
  congr 1
  omega

theorem lengthPair_run (n : ℕ) (z : ℂ) :
    run lengthPair (n,z)=
      ((run DFTModelRoot.workingLength n).pass (fun L => Bill.one (n,L))).pay 3 0 := by
  simp only [lengthPair,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem headerThen_run {t : Ty} (f : Prog false DFTModelChirpTables.Input t)
    (n : ℕ) (z : ℂ) :
    run (.comp header f) (n,z)=
      ((run DFTModelRoot.workingLength n).pass (fun L =>
        (run DFTModelRoot.program n).pass (fun D =>
          (run DFTModelRootExtraction.halfAngle (n,(D,z))).pass
            (fun eta => run f ((n,L),eta))))).pay 14 0 := by
  change (((run lengthPair (n,z)).pass (fun a =>
    (run halfRoot (n,z)).pass (fun b => Bill.one (a,b)))).pass (run f)).pay 1 0 = _
  rw [lengthPair_run,halfRoot_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,and_true]
  congr 1
  · omega
  · omega
  · simp only [and_assoc]

theorem header_value {n : ℕ} (hn : 0<n) :
    (run header (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=
      ((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)) := by
  change ((run lengthPair _).val,(run halfRoot _).val)=_
  rw [lengthPair_run,halfRoot_run]
  change ((n,(run DFTModelRoot.workingLength n).val),
    (run DFTModelRootExtraction.halfAngle (n,((run DFTModelRoot.program n).val,
      OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).val)=_
  rw [(DFTModelRoot.workingLength_spec n hn).1,(DFTModelRoot.actual_master_order n hn).1,
    DFTModelRootExtraction.halfAngle_value hn]

theorem program_run (n : ℕ) (z : ℂ) :
    run program (n,z)=
      ((run DFTModelRoot.workingLength n).pass (fun L =>
        (run DFTModelRoot.program n).pass (fun D =>
          (run DFTModelRootExtraction.halfAngle (n,(D,z))).pass
            (fun eta => run DFTModelChirpTables.program ((n,L),eta))))).pay 14 0 :=
  headerThen_run _ n z

theorem program_value {n : ℕ} (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=
      DFTModelChirpTables.values n (UniformWorkingLength.workingLength n)
        (DFTModelChirp.bank n (OAI.ExactFourier.zeta (2*n))) := by
  change (run DFTModelChirpTables.program (run header _).val).val=_
  rw [header_value hn]
  exact DFTModelChirpTables.program_value n _ _ hn (DFTModelChirp.specified_period n hn)

theorem program_valid {n : ℕ} (hn : 0<n) (z : ℂ) : (run program (n,z)).valid := by
  rw [program_run]
  refine ⟨(DFTModelRoot.workingLength_spec n hn).2.2.2,
    (DFTModelRoot.actual_master_order n hn).2.1,
    DFTModelRootExtraction.halfAngle_valid _ _ _,?_⟩
  rw [(DFTModelRoot.workingLength_spec n hn).1]
  exact DFTModelChirpTables.program_valid _ _ _ (UniformWorkingLength.workingLength_pos hn)

def budget (n : ℕ) : ℕ :=
  6*UniformWorkingCompletion.preparationBudget n+
  6*UniformMasterRootMachine.preparationBudget n+
  40*(11+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/(2*n)))+
  3500*(n+1)+20

theorem program_work {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run program (n,z)).work≤budget n := by
  rw [program_run]
  dsimp only [Bill.pass,Bill.pay]
  rw [(DFTModelRoot.workingLength_spec n hn).1,(DFTModelRoot.actual_master_order n hn).1]
  have hL := (DFTModelRoot.workingLength_spec n hn).2.1
  have hD := (DFTModelRoot.actual_master_order n hn).2.2.1
  have hroot := DFTModelRootExtraction.halfAngle_work_source n (UniformMasterRootMachine.order n) z
  have htables := DFTModelChirpTables.program_work n (UniformWorkingLength.workingLength n)
    (run DFTModelRootExtraction.halfAngle (n,(UniformMasterRootMachine.order n,z))).val
  have hl := UniformWorkingLength.workingLength_upper hn
  unfold budget
  omega

end
end ExactFourierCircuits.DFTModelOuterPreparation
