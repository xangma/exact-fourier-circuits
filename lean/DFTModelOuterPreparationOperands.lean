import DFTModelOuterPreparationCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev OperandInput := p Input (Ty.a (c .left))

def operandHeader : Prog false OperandInput DFTModelChirpOperands.Input :=
  .fork (.comp (.atom .fst) header) (.atom .snd)

def operands : Prog false OperandInput DFTModelChirpOperands.Output :=
  .comp operandHeader DFTModelChirpOperands.program

attribute [local irreducible] header DFTModelChirpOperands.program

theorem operands_run (n : ℕ) (z : ℂ) (v : Tape ℂ) :
    run operands ((n,z),v)=((run header (n,z)).pass
      (fun h => run DFTModelChirpOperands.program (h,v))).pay 5 0 := by
  simp only [operands,operandHeader,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem header_components (n : ℕ) (z : ℂ) :
    (run header (n,z)).val=
      ((n,(run DFTModelRoot.workingLength n).val),(run halfRoot (n,z)).val) := by
  unfold header
  change ((run lengthPair (n,z)).val,(run halfRoot (n,z)).val)=_
  rw [lengthPair_run]
  rfl

theorem operands_source_value {n : ℕ} (hn : 0<n) (v : Tape ℂ) :
    (run operands ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),v)).val=
      (run DFTModelChirpOperands.program
        (((n,UniformWorkingLength.workingLength n),OAI.ExactFourier.zeta (2*n)),v)).val := by
  rw [operands_run]
  change (run DFTModelChirpOperands.program ((run header _).val,v)).val=_
  rw [header_value hn]

theorem operands_value {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    (run operands ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).val=
      (DFTModelChirpTables.values n (UniformWorkingLength.workingLength n)
        (DFTModelChirp.bank n (OAI.ExactFourier.zeta (2*n))),
      Tape.tab (UniformWorkingLength.workingLength n)
        (fun i => (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x i).value)) := by
  rw [operands_source_value hn]
  apply Prod.ext
  · rw [DFTModelChirpOperands.program_first]
    exact DFTModelChirpTables.program_value n _ _ hn (DFTModelChirp.specified_period n hn)
  · exact DFTModelChirpOperands.padded_value hn x _ _ (DFTModelChirp.specified_period n hn)

theorem operands_valid {n : ℕ} (hn : 0<n) (z : ℂ) (v : Tape ℂ) :
    (run operands ((n,z),v)).valid := by
  rw [operands_run]
  refine ⟨header_valid hn z,?_⟩
  rw [header_components,(DFTModelRoot.workingLength_spec n hn).1]
  exact DFTModelChirpOperands.program_valid _ _ _ _ (UniformWorkingLength.workingLength_pos hn)

theorem header_work_le_program (n : ℕ) (z : ℂ) :
    (run header (n,z)).work≤(run program (n,z)).work := by
  change (run header (n,z)).work≤(run header (n,z)).work+
    (run DFTModelChirpTables.program (run header (n,z)).val).work+1
  omega

def operandBudget (n : ℕ) : ℕ := budget n+3500*(n+1)+5

theorem operands_work {n : ℕ} (hn : 0<n) (z : ℂ) (v : Tape ℂ) :
    (run operands ((n,z),v)).work≤operandBudget n := by
  rw [operands_run]
  change (run header (n,z)).work+(run DFTModelChirpOperands.program ((run header (n,z)).val,v)).work+5≤_
  rw [header_components,(DFTModelRoot.workingLength_spec n hn).1]
  have hh := (header_work_le_program n z).trans (program_work hn z)
  have hp := DFTModelChirpOperands.program_work n (UniformWorkingLength.workingLength n)
    (run halfRoot (n,z)).val v
  have hL := UniformWorkingLength.workingLength_upper hn
  unfold operandBudget
  omega

theorem operands_peak {n : ℕ} (hn : 0<n) (z : ℂ) (v : Tape ℂ) :
    (run operands ((n,z),v)).peak≤(n+2)^13 := by
  rw [operands_run]
  change max (max (run header (n,z)).peak
    (run DFTModelChirpOperands.program ((run header (n,z)).val,v)).peak) 0≤_
  rw [header_components,(DFTModelRoot.workingLength_spec n hn).1]
  have hh := header_peak hn z
  have hp := DFTModelChirpOperands.program_peak n (UniformWorkingLength.workingLength n)
    (run halfRoot (n,z)).val v
  have hL := UniformWorkingLength.workingLength_upper hn
  have hbase : n+UniformWorkingLength.workingLength n+2≤(n+2)^2 := by nlinarith
  have hs := Nat.pow_le_pow_left hbase 2
  have he : ((n+2)^2)^2=(n+2)^4 := by ring
  rw [he] at hs
  have h413 : (n+2)^4≤(n+2)^13 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Exact physical bank correspondence and actual padded data, from n, the
one master root and the original input. Neither L nor any table is input. -/
theorem operands_source_preparation {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃t u,UniformMachine.BoundedExecution UniformNormalizationPreparation.fullProgram n x
      ((n+2)^19) UniformMachine.initial t u ∧
      DFTModelChirpTables.SourceMatch x
        (run operands ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).val.1 u ∧
      (∀j,j<UniformWorkingLength.workingLength n →
        (u.scalarHeap (UniformPaddedInputPreparation.dataBase n+j)).map UniformMachine.Scalar.value=
          some ((run operands ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n x)).val.2.look j 0)) ∧
      t≤UniformNormalizationPreparation.fullPreparationBudget n := by
  rw [operands_source_value hn]
  exact DFTModelChirpOperands.source_preparation hn x

end
end ExactFourierCircuits.DFTModelOuterPreparation
