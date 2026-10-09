import UniformCacheLowProtected
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalCacheRegisters
open UniformMachine UniformNewtonTableMachine

def protectedInstruction:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>
   decide ((d<200∨209<d)∧(d<6020∨6037<d))
 | _=>true
lemma relocated (p:Program) (a b:ℕ):
 (p.map (UniformAssembly.relocate a b)).all protectedInstruction=p.all protectedInstruction:=by
 induction p with
 | nil=>rfl
 | cons i p ih=>
  simp only[List.map_cons,List.all_cons,ih]
  cases i <;>rfl
lemma code:UniformAxisCacheWholeProgram.program.all protectedInstruction=true:=by
 simp only [UniformAxisCacheWholeProgram.program,UniformAxisCacheWholeProgram.body,
  UniformAxisCacheWholeProgram.resetCode,UniformAxisCacheWholeProgram.startupCode,
  UniformAxisCacheWholeProgram.saveCode,UniformAxisCacheWholeProgram.prepareCode,
  UniformAxisCacheWholeProgram.horizonCode,UniformAxisCacheWholeProgram.headerCode,
  UniformAxisCacheWholeProgram.requestCode,UniformAxisCacheWholeProgram.forestCode,
  UniformAxisCacheWholeProgram.tailCode,UniformAxisCacheWholeProgram.advanceCode,
  UniformLocalStoredRequestLoop.program,UniformLocalStoredRequestLoop.beforeAdvance,
  UniformLocalStoredRequestLoop.beforeCache,UniformLocalStoredRectanglePreparation.program,
  UniformLocalRectangleCachePreparation.program,UniformLocalRectanglePhaseBanks.program,
  UniformLocalRectangleReplayPreparation.program,UniformLocalRectangleCoefficientMachine.program,
  UniformLocalRectangleBankMachine.program,UniformSeedHeightPreparation.program,
  UniformSeedHeightPreparation.beforeHeight,UniformSeedHeightPreparation.beforeSeed,
  UniformSeedRankCrossPreparation.program,UniformSeedRankCrossPreparation.head,
  UniformAssembly.embed,UniformRankCrossReplayPreparationMachine.program,
  UniformRankCrossReplayPreparationMachine.beforeCoefficient,UniformRankCrossReplayPreparationMachine.beforeBucket,
  UniformConjugateRankSpectrumPreparation.program,UniformRankCrossPreparationMachine.program,
  UniformLocalCacheContextConductor.program,UniformLocalCacheSlotConductorMachine.program,
  UniformLocalCacheSlotConductorMachine.beforeAdvance,UniformLocalCacheSlotConductorMachine.beforeDirectory,
  UniformLocalCacheSlotConductorMachine.beforeFactors,UniformLocalCacheSlotConductorMachine.beforeHeader,
  UniformLocalFactorDispatchMachine.program,UniformLocalFactorDispatchMachine.beforeInverseBody,
  UniformLocalFactorDispatchMachine.beforeInverse,UniformLocalFactorDispatchMachine.beforeBroadcast,
  UniformDirectLeafForestProgram.program,UniformDirectLeafForestProgram.frontCode,
  UniformDirectLeafForestProgram.suffix,List.all_append,relocated,Bool.and_eq_true]
 and_intros
 all_goals decide +kernel
lemma keeps(q:ℕ)(range:(200≤q∧q≤209)∨(6020≤q∧q≤6037)):
 ∀ins∈UniformAxisCacheWholeProgram.program,KeepsNat q ins:=by
 intro ins mem
 have h:=List.all_eq_true.mp code ins mem
 cases ins <;>simp only[protectedInstruction,KeepsNat] at *
 all_goals simp only[decide_eq_true_eq] at h
 all_goals omega
lemma execution {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformAxisCacheWholeProgram.program n x B s ticks u)
 (q:ℕ)(range:(200≤q∧q≤209)∨(6020≤q∧q≤6037)):
 u.natReg q=s.natReg q:=Executes.keeps_nat run.executes (keeps q range)
end ExactFourierCircuits.UniformFinalCacheRegisters
