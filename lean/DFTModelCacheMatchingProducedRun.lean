import DFTModelCacheMatchingProducedProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelCacheSelectedCoefficients.produced
  DFTModelCacheMatchingNat.program DFTModelCConstants.program DFTModelCacheMatchingFactors.program

theorem matchingArgument_run (x : Input.T) :
    run matchingArgument x=⟨(x.1,x.2.2.2),7,0,True⟩ := by
  simp [matchingArgument,rawRows,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem masterArgument_run (x : Input.T) :
    run masterArgument x=⟨x.2.2.1.2,7,0,True⟩ := by
  simp [masterArgument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem coefficients_run (x : Input.T) :
    run coefficients x=((run DFTModelCacheSelectedCoefficients.produced x.2).pass
      (fun z=>Bill.one (x,z))).pay 3 0 := by
  simp [coefficients,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem matching_run (v : Seed.T) :
    run matching v=((run DFTModelCacheMatchingNat.program (v.1.1,v.1.2.2.2)).pass
      (fun z=>Bill.one (v,z))).pay 11 0 := by
  simp [matching,matchingArgument,rawRows,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem constants_run (v : Matched.T) :
    run constants v=((run DFTModelCConstants.program v.1.1.2.2.1.2).pass
      (fun z=>Bill.one (v,z))).pay 13 0 := by
  simp [constants,masterArgument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem factorArgument_run (v : Ready.T) :
    run factorArgument v=⟨factorArgs v,37,3,True⟩ := by
  simp [factorArgument,ambient,permutation,coefficientPairs,constantCell,factorArgs,
    DFTModelCacheMatchingFactors.args,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem finish_run (v : Ready.T) :
    run finish v=((run DFTModelCacheMatchingFactors.program (factorArgs v)).pass
      (fun z=>Bill.one (v,z))).pay 39 3 := by
  rw [finish,fork_run,comp_run,factorArgument_run]
  simp [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] Code.run

theorem program_run (x : Input.T) :
    run program x=
      ⟨(readyValue x,(run DFTModelCacheMatchingFactors.program (factorArgs (readyValue x))).val),
        (run DFTModelCacheSelectedCoefficients.produced x.2).work+
        (run DFTModelCacheMatchingNat.program (x.1,x.2.2.2)).work+
        (run DFTModelCConstants.program x.2.2.1.2).work+
        (run DFTModelCacheMatchingFactors.program (factorArgs (readyValue x))).work+73,
        max (run DFTModelCacheSelectedCoefficients.produced x.2).peak
          (max (run DFTModelCacheMatchingNat.program (x.1,x.2.2.2)).peak
            (max (run DFTModelCConstants.program x.2.2.1.2).peak
              (max (run DFTModelCacheMatchingFactors.program (factorArgs (readyValue x))).peak 3))),
        (run DFTModelCacheSelectedCoefficients.produced x.2).valid ∧
        (run DFTModelCacheMatchingNat.program (x.1,x.2.2.2)).valid ∧
        (run DFTModelCConstants.program x.2.2.1.2).valid ∧
        (run DFTModelCacheMatchingFactors.program (factorArgs (readyValue x))).valid⟩ := by
  simp only [program,comp_run,coefficients_run,matching_run,constants_run,finish_run,
    Bill.pass,Bill.pay,Bill.one,readyValue,matchedValue,seedValue,max_zero,and_true]
  congr 1; omega

theorem retained (x : Input.T) : (run program x).val.1=readyValue x := by
  rw [program_run]

end
end ExactFourierCircuits.DFTModelCacheMatchingProduced
