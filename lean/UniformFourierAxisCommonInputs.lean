import UniformFourierAxisCommonResult
import UniformFinalAxisCacheSource
import UniformFinalAxisCacheRetention

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonInputs
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformFourierAxisCommonResult
noncomputable section

/-- Only the actual clock/allocator links are supplied. Cache source, shape,
count, duration and word-fit facts are derived from the genuine cache producer. -/
structure ClockArgs(c:Constants)(n g:ℕ)(j:Fin (ell n))(x:Fin n→ℂ)(s:State):Prop where
 head:UniformAxisCacheClockLookup.Header c n j.val s
 later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s
 input:UniformAxisCacheInputs.Inputs n x s
 natFrontier:s.natReg 5924=UniformFourierAxisPrepareHead.freshNat c n j
 scalarFrontier:s.natReg 5925=UniformFourierAxisPrepareHead.freshScalar c n j
 epoch:s.natReg 5920=g
 pc:s.pc=0
 bound:WordBound (envelope c n) s
 pool:s.natReg 6020=slab c n
 physical:s.natReg 6028=5*slab c n
 directory:s.natReg 5923=slab c n+2*j.val

abbrev records(c:Constants)(n:ℕ)(j:Fin (ell n)):=UniformFinalAxisCacheBundle.records c n j
abbrev nodes(c:Constants)(n:ℕ)(j:Fin (ell n)):=UniformFinalAxisCacheBundle.nodes c n j
abbrev rectangle(c:Constants)(n:ℕ)(j:Fin (ell n))(i:ℕ):ℕ×ℕ:=(records c n j)[i]?.getD (0,0)

lemma records_count(c:Constants)(n:ℕ)(j:Fin (ell n)):
 (records c n j).length=UniformAxisCacheForestEntry.rectangleCount c n j:=by
 exact UniformActualCalendarRectangleRegistry.entries_length n (UniformAxisCacheCanonicalRequests.canonical c n j)

/-- Retained cache intervals suffice after earlier axes and earlier complete
clock traversals; event factories are separately transported without re-choice. -/
theorem of_cache {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{x:Fin n→ℂ}{original s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j original)
 (natKeep:∀z,z<(axis c n j).endNat→s.natHeap z=original.natHeap z)
 (scalarKeep:∀z,(axis c n j).pool≤z→z<(axis c n j).endScalar→s.scalarHeap z=original.scalarHeap z)
 (clock:ClockArgs c n g j x s):
 UniformFourierAxisOperationalCases.Inputs c n (depth n j) g (records c n j).length j
  (rectangle c n j) (nodes c n j) x s:=by
 have physical:UniformAxisCachePhysical.Heaps c n j original s:=⟨fun z _ hz=>natKeep z hz,scalarKeep⟩
 have f:=UniformFinalAxisCacheSource.transport cache physical
 rw[records_count]
 exact ⟨clock.head,clock.later,clock.input,clock.natFrontier,clock.scalarFrontier,clock.epoch,
  f.duration,f.durationWord,clock.pc,clock.bound,f.source,f.layout,f.rectangleValues,f.nodeValues,
  clock.pool,clock.physical,clock.directory⟩

end
end ExactFourierCircuits.UniformFourierAxisCommonInputs
