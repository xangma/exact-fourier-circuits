import UniformFourierAxisCommonExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonFrontiers
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformFourierAxisCommonResult UniformFourierAxisCommonInputs UniformFourierAxisOperationalCases
noncomputable section

lemma Branch.frontiers {c:Constants}{n d g rectangleCount:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List UniformCacheRangeSelector.Range}{x:Fin n→ℂ}{s u:State}
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u):
 u.natReg 6819=(axis c n j).endNat∧u.natReg 6821=(axis c n j).endScalar:=by
 cases actual with
 | tree _ a=>exact ⟨a.allocation.endNat,a.allocation.endScalar⟩
 | boundary _ _ a=>exact ⟨a.allocation.endNat,a.allocation.endScalar⟩
 | inactive _ a=>exact ⟨a.allocation.endNat,a.allocation.endScalar⟩

/-- The same real389 run leaves the producer's exact cache frontiers, even
though the subsequent footer also publishes the fresh workspace frontier. -/
theorem frontiers {c:Constants}{n g ticks:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s u:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (keep:UniformAxisCachePhysical.Heaps c n j original s)
 (clock:ClockArgs c n g j x s)
 (run:BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u):
 u.natReg 6819=(axis c n j).endNat∧u.natReg 6821=(axis c n j).endScalar:=by
 obtain ⟨v,t,real,_,branch⟩:=UniformFourierAxisOperationalCases.execution c hn j
  (rectangle c n j) (nodes c n j) x s (of_interval cache keep clock)
 have same:=(real.executes.deterministic run.executes).2
 subst u
 exact Branch.frontiers branch

end
end ExactFourierCircuits.UniformFourierAxisCommonFrontiers
