import DFTModelWorkingHeadersClosed
import DFTModelOuterPreparationOperands
import DFTModelCConstantsActual

set_option autoImplicit false

/-! One closed typed entry for the initial header, permutation and scalar
producers. The only inputs are n, its master root and the original data.
Paper E, §1.1 and §5 (arbitrary-length reduction): every producer's work is
charged. This packages preparation components; it does not generate the
remaining recursive cache forest or claim a whole source-state simulation. -/
namespace ExactFourierCircuits.DFTModelInitialPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := DFTModelOuterPreparation.OperandInput
abbrev Permutations := p (Ty.a w) (Ty.a w)
abbrev Output := p DFTModelCRTMetadata.Input
  (p Permutations (p (Ty.a sc) DFTModelChirpOperands.Output))

def length : Prog false Input w := .comp (.atom .fst) (.atom .fst)
def root : Prog false Input sc := .comp (.atom .fst) (.atom .snd)
def headers : Prog false Input DFTModelCRTMetadata.Input :=
  .comp length DFTModelWorkingHeaders.program
def permutations : Prog false Input Permutations :=
  .comp length DFTModelWorkingHeaders.tables
def constants : Prog false Input (Ty.a sc) :=
  .comp (.fork (.comp length DFTModelRoot.program) root) DFTModelCConstants.program
def program : Prog false Input Output :=
  .fork headers (.fork permutations (.fork constants DFTModelOuterPreparation.operands))

attribute [local irreducible] DFTModelWorkingHeaders.program
  DFTModelWorkingHeaders.tables DFTModelRoot.program DFTModelCConstants.program
  DFTModelOuterPreparation.operands

theorem program_run (n : ℕ) (z : ℂ) (x : Tape ℂ) :
    run program ((n,z),x)=
      ((run DFTModelWorkingHeaders.program n).pass (fun h =>
        (run DFTModelWorkingHeaders.tables n).pass (fun t =>
          (run DFTModelRoot.program n).pass (fun D =>
            (run DFTModelCConstants.program (D,z)).pass (fun c =>
              (run DFTModelOuterPreparation.operands ((n,z),x)).pass
                (fun y => Bill.one (h,(t,(c,y))))))))).pay 19 0 := by
  simp only [program,headers,permutations,constants,length,root,run,Code.run,
    Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  · omega
  · omega
  · simp only [and_assoc]

def budget (n : ℕ) : ℕ :=
  32*UniformWorkingCompletion.preparationBudget n+
  520*(UniformCRTTraversalCycle.len n+1)+
  6*UniformMasterRootMachine.preparationBudget n+
  400*(UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/4)+1)+
  DFTModelOuterPreparation.operandBudget n+21

/-- All four outputs are produced by actual finite code at this input boundary. -/
theorem specification {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    (run program ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).val=
      (DFTModelCRTMetadata.selectedInput n,
        ((run DFTModelCRT.program (DFTModelCRT.selectedInput n)).val,
          (DFTModelCConstants.bank,
            (DFTModelChirpTables.values n (UniformWorkingLength.workingLength n)
              (DFTModelChirp.bank n (OAI.ExactFourier.zeta (2*n))),
              Tape.tab (UniformWorkingLength.workingLength n) (fun i =>
                (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x i).value))))) ∧
    (run program ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).valid ∧
    (run program ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).work≤budget n ∧
    (run program ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).peak≤(n+2)^13 := by
  obtain ⟨hv,hd,hw,hp⟩ := DFTModelWorkingHeaders.actual_headers n hn
  obtain ⟨dv,dd,dw,dp⟩ := DFTModelRoot.actual_master_order n hn
  obtain ⟨cv,cd,cw,cp⟩ := DFTModelCConstants.selected_specification hn
  have tv := DFTModelWorkingHeaders.tables_value n hn
  have td := DFTModelWorkingHeaders.tables_valid n hn
  have tw := DFTModelWorkingHeaders.tables_work n hn
  have tp := DFTModelWorkingHeaders.tables_peak n hn
  have ov := DFTModelOuterPreparation.operands_value hn x
  have od := DFTModelOuterPreparation.operands_valid hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)) (Tape.mk n x)
  have ow := DFTModelOuterPreparation.operands_work hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)) (Tape.mk n x)
  have op := DFTModelOuterPreparation.operands_peak hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)) (Tape.mk n x)
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,and_true]
  rw [dv]
  refine ⟨?_,⟨hd,td,dd,cd,od⟩,?_,?_⟩
  · rw [hv,tv,cv,ov]
  · unfold budget
    omega
  · have hpow : (n+2)^12≤(n+2)^13 := Nat.pow_le_pow_right (by omega) (by omega)
    have hD : UniformMasterRootMachine.order n≤(n+2)^12 := by
      exact ((UniformMasterRootMachine.order_bounds hn).2.le).trans
        (UniformMasterRootMachine.wordBound_setup hn).2.2.2
    have hD2 : UniformMasterRootMachine.order n+2≤(n+2)^13 := by
      have hbase : 0<(n+2)^12 := pow_pos (by omega) _
      have hs : 3*(n+2)^12≤(n+2)^13 := by
        calc
          _≤(n+2)*(n+2)^12 := Nat.mul_le_mul_right _ (by omega)
          _=(n+2)^13 := (Nat.mul_comm _ _).trans (pow_succ (n+2) 12).symm
      omega
    omega

end
end ExactFourierCircuits.DFTModelInitialPreparation
