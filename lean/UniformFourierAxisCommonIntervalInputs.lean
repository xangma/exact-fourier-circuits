import UniformFourierAxisCommonInputs

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonInputs
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformFourierAxisCommonResult
noncomputable section

/-- The permanent cache starts at tasks. Earlier physical directory cells may
be rewritten by later clocks and are not retained-cache hypotheses. -/
theorem of_interval {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (keep:UniformAxisCachePhysical.Heaps c n j original s)
 (clock:ClockArgs c n g j x s):
 UniformFourierAxisOperationalCases.Inputs c n (depth n j) g (records c n j).length j
  (rectangle c n j) (nodes c n j) x s:=by
 have f:=UniformFinalAxisCacheSource.transport cache keep
 rw[records_count]
 exact ⟨clock.head,clock.later,clock.input,clock.natFrontier,clock.scalarFrontier,clock.epoch,
  f.duration,f.durationWord,clock.pc,clock.bound,f.source,f.layout,f.rectangleValues,f.nodeValues,
  clock.pool,clock.physical,clock.directory⟩
end
end ExactFourierCircuits.UniformFourierAxisCommonInputs
