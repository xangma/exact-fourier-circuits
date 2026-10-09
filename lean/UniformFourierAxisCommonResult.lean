import UniformFourierAxisPhaseReadBounds

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonResult
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformGlobalCalendarDispatch
noncomputable section

abbrev depth(n:ℕ)(j:Fin (ell n)):ℕ:=UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)
def events(c:Constants)(n g:ℕ)(j:Fin (ell n))(treeEvents:ℕ→List Event):List Event:=
 UniformFourierAxisCanonicalEvents.eventsAt c n j (depth n j) g treeEvents

/-- Common factual and semantic postcondition of the same literal389, at one
fixed axis and global clock. Event identity is inherited from the retained
initial cache, so a finite clock family never re-chooses its event factories. -/
structure Result(c:Constants)(n g:ℕ)(j:Fin (ell n))(treeEvents:ℕ→List Event)
 (x:Fin n→ℂ)(s u:State):Prop where
 pc:u.pc=388
 footer:UniformFourierAxisPrepareFooter.Result (UniformAllAxisSeedPreparation.radix n j)
  (UniformFourierAxisPrepareHead.freshNat c n j) (UniformFourierAxisPrepareHead.freshScalar c n j)
  (events c n g j treeEvents).length j.val (s.natReg 6028) (s.natReg 5923)
  (UniformJointCacheAllocation.axis c n j).endNat (UniformJointCacheAllocation.axis c n j).endScalar u
 selections:Selections (UniformFourierAxisWorkspace.axis c n j).selected 0 (events c n g j treeEvents) u
 cached:∀e∈events c n g j treeEvents,CachedEvent (UniformAllAxisSeedPreparation.radix n j)
  (UniformFourierAxisWorkspace.axis c n j).pool (UniformFourierAxisWorkspace.axis c n j).phase (envelope c n) e u
 action:Nonempty (UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (events c n g j treeEvents) (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix)
 inputs:UniformAxisCacheInputs.Inputs n x u
 natOutside:∀z,(z<(UniformFourierAxisWorkspace.axis c n j).selected∨(UniformFourierAxisWorkspace.axis c n j).phase≤z)→
  u.natHeap z=s.natHeap z
 scalarOutside:∀z,(z<slab c n∨slab c n+9*UniformAllAxisSeedPreparation.radix n j≤z)→u.scalarHeap z=s.scalarHeap z
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,UniformFourierAxisPrepareHead.Protected q→u.natReg q=s.natReg q

lemma Result.dispatch{c:Constants}{n g:ℕ}{j:Fin (ell n)}{treeEvents:ℕ→List Event}
 {x:Fin n→ℂ}{s u:State}(actual:Result c n g j treeEvents x s u):
 Inputs (UniformFourierAxisWorkspace.axis c n j).selected (events c n g j treeEvents).length
  (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (UniformFourierAxisWorkspace.axis c n j).phase u:=
 ⟨actual.footer.selected,actual.footer.count,actual.footer.radix,actual.footer.pool,actual.footer.rows,actual.footer.phase⟩

end
end ExactFourierCircuits.UniformFourierAxisCommonResult
