import DFTModelCacheMatchingFactorsScalar
import DFTModelScalarPower
import UniformReplayCoefficientMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open DFTModelCacheMatchingFactors (natural ratio natural_run ratio_run negative_run)
noncomputable section

abbrev PairBank := Ty.a (p sc sc)
abbrev ConstantBank := Ty.a sc

def reciprocal : Prog false w sc :=
  .comp (.comp (.fork (.atom .id) (natural 2)) DFTModelScalarPower.program) (.atom .inv)
def constantSeed : Prog false w (p w sc) := .fork (.atom .id) reciprocal
abbrev ConstantCell := p (p w sc) w

def slotAtMost (j : ℕ) : Prog false ConstantCell w :=
  .comp (.fork (.atom .snd) (.atom (.lit j))) (.atom (.int .sub))
def reciprocalAt : Prog false ConstantCell sc := .comp (.atom .fst) (.atom .snd)
def constantCell : Prog false ConstantCell sc :=
  .ifz (slotAtMost 0) (.atom .cone)
  (.ifz (slotAtMost 1) (negative (.atom .cone))
  (.ifz (slotAtMost 2) reciprocalAt
  (.ifz (slotAtMost 3) (negative reciprocalAt)
  (.ifz (slotAtMost 4) (ratio 5 4) (ratio 4 5)))))
def constantsBody : Prog false (p w sc) ConstantBank := .tab (.atom (.lit 6)) constantCell
def constants : Prog false w ConstantBank := .comp constantSeed constantsBody

attribute [local irreducible] DFTModelScalarPower.program natural ratio

theorem reciprocal_run (K : ℕ) : run reciprocal K=
    ⟨((2:ℂ)^K)⁻¹,(run DFTModelScalarPower.program (K,(2:ℂ))).work+14,
      (run DFTModelScalarPower.program (K,(2:ℂ))).peak,True⟩ := by
  have v:=DFTModelScalarPower.program_value K (2:ℂ)
  have valid:=DFTModelScalarPower.program_valid K (2:ℂ)
  simp only [reciprocal,comp_run,fork_run,atom_run,natural_run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  norm_num only [Nat.cast_ofNat]
  rw [v]
  simp only [valid,true_and,and_true,zero_max,max_zero]
  congr 1
  · omega
  · norm_num

theorem constantSeed_run (K : ℕ) : run constantSeed K=
    ⟨(K,((2:ℂ)^K)⁻¹),(run DFTModelScalarPower.program (K,(2:ℂ))).work+16,
      (run DFTModelScalarPower.program (K,(2:ℂ))).peak,True⟩ := by
  rw [constantSeed,fork_run,reciprocal_run]
  simp [run,Code.run,Atom.run,Bill.one,Bill.pass]
  omega

theorem slotAtMost_run (a K j : ℕ) (z : ℂ) :
    run (slotAtMost a) ((K,z),j)=⟨j-a,5,max a (j-a),True⟩ := by
  simp [slotAtMost,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem reciprocalAt_run (K j : ℕ) (z : ℂ) : run reciprocalAt ((K,z),j)=⟨z,3,0,True⟩ := by
  simp [reciprocalAt,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem constantCell_spec (K j : ℕ) (hj : j<6) :
    (run constantCell ((K,((2:ℂ)^K)⁻¹),j)).val=UniformReplayCoefficientMachine.constant K j ∧
    (run constantCell ((K,((2:ℂ)^K)⁻¹),j)).valid ∧
    (run constantCell ((K,((2:ℂ)^K)⁻¹),j)).work≤73 ∧
    (run constantCell ((K,((2:ℂ)^K)⁻¹),j)).peak≤5 := by
  interval_cases j <;>
    simp [constantCell,slotAtMost,reciprocalAt,negative,natural,ratio,
      run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,UniformReplayCoefficientMachine.constant]
  all_goals norm_num

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
