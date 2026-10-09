import UniformFinalDataClockProductExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDataClockProduct
open UniformMachine UniformSequentialExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
attribute [local irreducible] Nat.add Nat.mul UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program

lemma Result.beforePC {n p:ℕ}{hn:0<n}{x:Fin n→ℂ}{y:Fin (volume n)→ℂ}
 {s dataOut productOut thirdIn:State}(h:Result hn x y s dataOut productOut thirdIn):
 Result hn x y {s with pc:=p} dataOut productOut thirdIn:=
 ⟨h.transform,h.clockSaved,h.numeric,h.reindex,h.standard,h.thirdNumeric,h.source,h.entry,h.table,
  h.cache,h.runtime,h.saved,h.thirdSaved,h.frame.beforePC p,h.movement,h.pc⟩

lemma Result.table_actual {n:ℕ}{hn:0<n}{x:Fin n→ℂ}{y:Fin (volume n)→ℂ}
 {s dataOut productOut thirdIn:State}(h:Result hn x y s dataOut productOut thirdIn):
 UniformFinalPhysicalTablePrefix.Result n x thirdIn:=h.table.withPC (pc:=thirdIn.pc)

/-- Entry reset is the charged relocation convention already proved by
LocalStages; it adds no host state writes between the three helpers. -/
theorem execution_local {n ticks:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (volume n)→Scalar)(y:Fin (volume n)→ℂ)(s dataOut:State)
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x (budget n) {s with pc:=0} ticks dataOut)
 (output:UniformActualCompleteClockExecution.Output hn x v {s with pc:=0} dataOut)
 (table:UniformFinalPhysicalTablePrefix.Result n x s)
 (cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
 (saved:∀j:Fin (volume n),s.scalarHeap (savedBase n+j.val)=some (UniformPairMachine.prepared (y j))):
 ∃productOut thirdIn,LocalStages n (budget n) x
  [UniformActualGlobalClockProgram.program,UniformRolePointwiseMachine.program,UniformPhysicalCRTConsumerMachine.program]
  s (ticks+27*volume n+27) thirdIn ∧ Result hn x y s dataOut productOut thirdIn:=by
 have cache0:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) {s with pc:=0}:=by
  intro j hj
  exact UniformAxisCacheContents.transport (cache j hj) ⟨by intros;rfl,by intros;rfl⟩
 obtain ⟨p,u,stages,result⟩:=execution hn x v y {s with pc:=0} dataOut rfl run output
  table.withPC cache0 source saved
 exact ⟨p,u,stages_beforePC (s:={s with pc:=0}) (p:=s.pc) stages,result.beforePC (p:=s.pc)⟩

end
end ExactFourierCircuits.UniformFinalDataClockProduct
