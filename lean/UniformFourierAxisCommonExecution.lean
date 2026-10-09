import UniformFourierAxisCommonIntervalInputs
import UniformFinalAxisCacheIntervalRetention
import UniformFourierAxisCanonicalActionFactory

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonExecution
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformFourierAxisCommonResult UniformFourierAxisCommonInputs
open UniformFourierAxisOperationalCases
noncomputable section

/-- Assemble the factual postcondition of the same literal389 run. The ordered
Action is supplied by the pure canonical calendar proof, independently of heaps. -/
theorem postcondition {c:Constants}{n g ticks:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s u:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (keep:UniformAxisCachePhysical.Heaps c n j original s)
 (clock:ClockArgs c n g j x s)
 (run:BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u)
 (branch:Branch c n (depth n j) g (records c n j).length hn j (rectangle c n j) (nodes c n j) x s u)
 (action:Nonempty (UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events)
  (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix)):
 Result c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events x s u:=by
 have input:=of_interval cache keep clock
 have f:=UniformFinalAxisCacheSource.of_contents cache
 have capacity:(records c n j).length+UniformCacheRangeSelector.total (nodes c n j)≤
  UniformJointCacheExtent.capacity (UniformAllAxisSeedPreparation.radix n j):=by
  rw[records_count];exact f.countFit
 have outside:=branch.natOutside input capacity run
 have frame:=branch.frame
 have pc:=branch.pc
 have inputs:=branch.inputs
 cases branch with
 | tree active actual=>
  let bundle:=UniformFinalAxisCacheIntervalRetention.transferred c n hn j cache keep
  have before:=UniformFourierAxisWorkspace.caches_before c n j j
  have facts:=UniformFourierAxisTreeRegistryFacts.factual bundle actual before.1 before.2
  have cached:=UniformFourierAxisPhaseReadBounds.tree bundle actual before.1 before.2
  have eventEq:events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events=
   bundle.events (UniformFourierAxisPrepareTree.localTick (depth n j) g):=by
   rw[events,UniformFourierAxisCanonicalEvents.eventsAt_tree _ active]
   exact ((UniformFinalAxisCacheIntervalRetention.transferred_events c n hn j cache keep _).trans
    (UniformFinalAxisCacheBundle.events_eq c n hn j cache _)).symm
  have count:(bundle.events (UniformFourierAxisPrepareTree.localTick (depth n j) g)).length=
   UniformFourierAxisPrepareTree.count c n (depth n j) g (records c n j).length j
    (rectangle c n j) (nodes c n j):=facts.2.2
  refine ⟨pc,?_,?_,?_,action,inputs,outside,frame.scalarOutside,frame.outputs,frame.roots,frame.natReg⟩
  · rw[eventEq,count];exact actual.footer
  · rw[eventEq];exact facts.1
  · rw[eventEq];exact cached
 | boundary q active actual=>
  have facts:=UniformFourierAxisCanonicalEvents.boundary
   (UniformFinalAxisCacheBundle.reference c n hn j cache).events actual
  have cached:=UniformFourierAxisPhaseReadBounds.boundary
   (UniformFinalAxisCacheBundle.reference c n hn j cache).events actual
  have length:(events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events).length=1:=by
   rw[events,UniformFourierAxisCanonicalEvents.eventsAt_boundary _ active]
   rfl
  refine ⟨pc,?_,facts.1,cached,action,inputs,outside,frame.scalarOutside,frame.outputs,frame.roots,frame.natReg⟩
  rw[length,clock.physical,clock.directory]
  exact actual.footer
 | inactive inactive actual=>
  have facts:=UniformFourierAxisCanonicalEvents.inactive hn
   (UniformFinalAxisCacheBundle.reference c n hn j cache).events actual
  have eventEq:events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events=[]:=by
   exact UniformFourierAxisCanonicalEvents.eventsAt_inactive _ inactive
  refine ⟨pc,?_,facts.1,?_,action,inputs,outside,frame.scalarOutside,frame.outputs,frame.roots,frame.natReg⟩
  · rw[eventEq];exact actual.footer
  · rw[eventEq];simp

/-- Operational execution and exact fixed-factory postcondition, ready for the
closed pure Action constructor. No selected list, source or table is an input. -/
theorem execution_of_action {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (keep:UniformAxisCachePhysical.Heaps c n j original s)
 (clock:ClockArgs c n g j x s)
 (action:Nonempty (UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events)
  (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix)):
 ∃u ticks,BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u∧
 ticks≤budget (UniformAllAxisSeedPreparation.radix n j) (records c n j).length (nodes c n j)∧
 Result c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events x s u:=by
 obtain ⟨u,t,run,time,branch⟩:=UniformFourierAxisOperationalCases.execution c hn j
  (rectangle c n j) (nodes c n j) x s (of_interval cache keep clock)
 exact ⟨u,t,run,time,postcondition cache keep clock run branch action⟩


/-- Closed actual389 execution at every epoch. All source facts, event identity,
ordered action and capacity facts come from the genuine initial cache. -/
theorem execution {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (keep:UniformAxisCachePhysical.Heaps c n j original s)
 (clock:ClockArgs c n g j x s):
 ∃u ticks,BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u∧
 ticks≤budget (UniformAllAxisSeedPreparation.radix n j) (records c n j).length (nodes c n j)∧
 Result c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events x s u:=
 execution_of_action cache keep clock ⟨UniformFourierAxisCanonicalActionFactory.action c n hn j cache g⟩

end
end ExactFourierCircuits.UniformFourierAxisCommonExecution
