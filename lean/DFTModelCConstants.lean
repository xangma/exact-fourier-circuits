import DFTModelRootExtraction
import DFTModelBinaryCoefficients
import UniformCConstantsMachine

set_option autoImplicit false

/-!
Five prepared C constants, derived by closed upstream code from the one supplied
master root. The fourth root is computed by binary powering; the five output
cells are built with a charged fresh tabulation. There is no data input, complex
literal, extra root request, or supplied table/handler.
-/
namespace ExactFourierCircuits.DFTModelCConstants
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier
noncomputable section

attribute [local irreducible] DFTModelRootExtraction.program DFTModelScalarPower.program

abbrev Input := p w sc
abbrev Coefficients := DFTModelBinaryPair.Coefficients
abbrev Cell := p Coefficients w
abbrev Output := Ty.a sc

def fourthRoot : Prog false Input sc :=
  .comp (.fork (.atom (.lit 4)) (.atom .id)) DFTModelRootExtraction.program

def inverseA : Prog false Coefficients sc := .comp (.atom .fst) (.atom .inv)
def imaginary : Prog false Coefficients sc :=
  .comp (.fork (.atom .fst) (.atom .snd)) (.atom (.sub .scalar))
def imaginaryInverse : Prog false Coefficients sc :=
  .comp (.fork imaginary inverseA) (.atom (.scale .scalar))

def loweredIndex (k : ℕ) : Prog false Cell w :=
  .comp (.fork (.atom .snd) (.atom (.lit k))) (.atom (.int .sub))

def cell : Prog false Cell sc :=
  .ifz (.atom .snd) (.comp (.atom .fst) (.atom .fst))
    (.ifz (loweredIndex 1) (.comp (.atom .fst) (.atom .snd))
      (.ifz (loweredIndex 2) (.comp (.atom .fst) inverseA)
        (.ifz (loweredIndex 3) (.comp (.atom .fst) imaginary)
          (.comp (.atom .fst) imaginaryInverse))))

def suffix : Prog false Coefficients Output := .tab (.atom (.lit 5)) cell

def program : Prog false Input Output :=
  .comp fourthRoot (.comp DFTModelBinaryCoefficients.program suffix)

def coefficientCell (u v : ℂ) (j : ℕ) : ℂ :=
  if j=0 then u else if j=1 then v else if j=2 then u⁻¹
    else if j=3 then u-v else (u-v)*u⁻¹

def bank : Tape ℂ := Tape.tab 5 (coefficientCell a b)

theorem fourthRoot_run (D : ℕ) (z : ℂ) :
    run fourthRoot (D,z) = (run DFTModelRootExtraction.program (4,(D,z))).pay 4 4 := by
  simp [fourthRoot,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    Nat.add_comm,max_comm]
  omega

theorem fourthRoot_value (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run fourthRoot (D,zeta D)).val=Complex.I := by
  rw [fourthRoot_run]
  change (run DFTModelRootExtraction.program (4,(D,zeta D))).val=Complex.I
  exact (DFTModelRootExtraction.divisor_root 4 D (by omega) hD h4).trans
    UniformCKernelPreparation.zeta_four

theorem cell_value (u v : ℂ) (j : ℕ) (hj : j<5) :
    (run cell ((u,v),j)).val=coefficientCell u v j := by
  interval_cases j <;>
    simp [cell,loweredIndex,inverseA,imaginary,imaginaryInverse,coefficientCell,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem cell_valid (u v : ℂ) (hu : u≠0) (j : ℕ) (hj : j<5) :
    (run cell ((u,v),j)).valid := by
  interval_cases j <;>
    simp [cell,loweredIndex,inverseA,imaginary,imaginaryInverse,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hu]

theorem cell_work (u v : ℂ) (j : ℕ) (hj : j<5) :
    (run cell ((u,v),j)).work≤50 := by
  interval_cases j <;>
    norm_num [cell,loweredIndex,inverseA,imaginary,imaginaryInverse,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem cell_peak (u v : ℂ) (j : ℕ) (hj : j<5) :
    (run cell ((u,v),j)).peak≤4 := by
  interval_cases j <;>
    norm_num [cell,loweredIndex,inverseA,imaginary,imaginaryInverse,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem suffix_value (u v : ℂ) :
    (run suffix (u,v)).val=Tape.tab 5 (coefficientCell u v) := by
  change (Bill.tab 5 sc.blank (fun j => run cell ((u,v),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  change (⟨5,fun j : Fin 5 => (run cell ((u,v),j.val)).val⟩ : Tape ℂ)=
    ⟨5,fun j => coefficientCell u v j.val⟩
  congr 1
  funext j
  exact cell_value u v j.val j.isLt

theorem suffix_valid (u v : ℂ) (hu : u≠0) : (run suffix (u,v)).valid := by
  change True ∧ (Bill.tab 5 sc.blank (fun j => run cell ((u,v),j))).valid
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j hj => cell_valid u v hu j hj)⟩

theorem suffix_work (u v : ℂ) : (run suffix (u,v)).work≤274 := by
  change 1+(Bill.tab 5 sc.blank (fun j => run cell ((u,v),j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j ∈ Finset.range 5,(run cell ((u,v),j)).work)≤250 := by
    calc
      _ ≤ ∑_j ∈ Finset.range 5,50 := Finset.sum_le_sum (fun j hj =>
        cell_work u v j (Finset.mem_range.mp hj))
      _ = 250 := by norm_num
  omega

theorem suffix_peak (u v : ℂ) : (run suffix (u,v)).peak≤5 := by
  change max (max 5 (Bill.tab 5 sc.blank (fun j => run cell ((u,v),j))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs : (Finset.range 5).sup (fun j => (run cell ((u,v),j)).peak)≤4 := by
    exact Finset.sup_le (fun j hj => cell_peak u v j (Finset.mem_range.mp hj))
  omega

theorem fourthRoot_valid (D : ℕ) (z : ℂ) : (run fourthRoot (D,z)).valid := by
  rw [fourthRoot_run]
  exact DFTModelRootExtraction.program_valid 4 D z

theorem fourthRoot_work_source (D : ℕ) (z : ℂ) :
    (run fourthRoot (D,z)).work≤40*UniformPowerMachine.loopCost (D/4)+26 := by
  rw [fourthRoot_run,DFTModelRootExtraction.program_run]
  change (run DFTModelScalarPower.program (D/4,z)).work+13+4≤_
  have h := DFTModelScalarPower.program_work_source (D/4) z
  omega

theorem fourthRoot_peak (D : ℕ) (z : ℂ) (hD : 4≤D) :
    (run fourthRoot (D,z)).peak≤D+2 := by
  rw [fourthRoot_run]
  change max (run DFTModelRootExtraction.program (4,(D,z))).peak 4≤_
  have h := DFTModelRootExtraction.program_peak 4 D z
  omega

attribute [local irreducible] fourthRoot suffix DFTModelBinaryCoefficients.program

theorem program_run (D : ℕ) (z : ℂ) :
    run program (D,z) =
      ((run fourthRoot (D,z)).pass (fun i =>
        ((run DFTModelBinaryCoefficients.program i).pass
          (fun uv => run suffix uv)).pay 1 0)).pay 1 0 := rfl

theorem program_value (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run program (D,zeta D)).val=bank := by
  rw [program_run]
  change (run suffix (run DFTModelBinaryCoefficients.program
    (run fourthRoot (D,zeta D)).val).val).val=bank
  rw [fourthRoot_value D hD h4,DFTModelBinaryCoefficients.program_C]
  exact suffix_value a b

theorem program_valid (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run program (D,zeta D)).valid := by
  rw [program_run]
  change (run fourthRoot (D,zeta D)).valid ∧
    ((run DFTModelBinaryCoefficients.program (run fourthRoot (D,zeta D)).val).valid ∧
      (run suffix (run DFTModelBinaryCoefficients.program
        (run fourthRoot (D,zeta D)).val).val).valid)
  rw [fourthRoot_value D hD h4,DFTModelBinaryCoefficients.program_C]
  exact ⟨fourthRoot_valid D _,trivial,suffix_valid a b a_ne_zero⟩

theorem program_work_source (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run program (D,zeta D)).work≤400*(UniformPowerMachine.loopCost (D/4)+1) := by
  rw [program_run]
  change (run fourthRoot (D,zeta D)).work+
    ((run DFTModelBinaryCoefficients.program (run fourthRoot (D,zeta D)).val).work+
      (run suffix (run DFTModelBinaryCoefficients.program
        (run fourthRoot (D,zeta D)).val).val).work+1)+1≤_
  rw [fourthRoot_value D hD h4,DFTModelBinaryCoefficients.program_C]
  have hp := fourthRoot_work_source D (zeta D)
  have hs := suffix_work a b
  dsimp only [Bill.val,Bill.work]
  omega

theorem program_peak (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run program (D,zeta D)).peak≤D+2 := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  rw [fourthRoot_value D hD h4,DFTModelBinaryCoefficients.program_C]
  have hp := fourthRoot_peak D (zeta D) (Nat.le_of_dvd hD h4)
  have hs := suffix_peak a b
  dsimp only [Bill.val,Bill.peak]
  omega

theorem bank_length : bank.len=5 := rfl

theorem bank_cell (j : Fin 5) : bank.look j.val 0 =
    (![a,b,a⁻¹,Complex.I,Complex.I*a⁻¹] : Fin 5 → ℂ) j := by
  fin_cases j <;> simp [bank,Tape.look,Tape.tab,coefficientCell,
    UniformCConstantsMachine.a_sub_b]

/-- The supplied root's positive order divisible by four is the only scalar
preparation hypothesis; every inverse in the executed target path is valid. -/
theorem specification (D : ℕ) (hD : 0<D) (h4 : 4∣D) :
    (run program (D,zeta D)).val=bank ∧
    (run program (D,zeta D)).valid ∧
    (run program (D,zeta D)).work≤400*(UniformPowerMachine.loopCost (D/4)+1) ∧
    (run program (D,zeta D)).peak≤D+2 :=
  ⟨program_value D hD h4,program_valid D hD h4,
    program_work_source D hD h4,program_peak D hD h4⟩

end
end ExactFourierCircuits.DFTModelCConstants
