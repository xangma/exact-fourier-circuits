import UniformFourierAxisTreeTail
import UniformFourierAxisGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareTree
open UniformMachine
open UniformJointAllocation (Constants envelope)
open UniformJointCacheAllocation (ell)
open UniformAxisCacheSelectedPreparation (natAt scalarAt)
namespace H
export UniformFourierAxisPrepareHead (freshNat freshScalar Protected)
end H
namespace R
export UniformCacheRangeSelector (Range RangeSource Layout selections total)
end R
noncomputable section

def localTick(d g:ℕ):ℕ:=if g≤d then d-g else g-d-4
lemma tree_values{d g:ℕ}{s:State}(selected:UniformEpochSelectorMachine.Selected d g s)
 (tree:(1≤g∧g≤d)∨(d+4≤g∧g<2*d+4)):s.natReg 7080=0∧s.natReg 6703=localTick d g:=by
 refine ⟨selected.tree_iff.mpr tree,?_⟩
 rcases tree with early|late
 · simpa only[localTick,ite_eq_left early.2] using selected.forward_stage early.1 early.2
 · simpa only[localTick,ite_eq_right (show ¬g≤d by omega)] using selected.reverse_stage late.1 late.2

lemma frontier_below_selected(c:Constants)(n:ℕ)(j:Fin (ell n)):
 natAt c n j.val≤(UniformFourierAxisWorkspace.axis c n j).selected:=by
 have bound: natAt c n j.val≤(UniformJointCacheAllocation.axis c n j).endNat:=by
  rw[UniformJointCacheAllocation.axis,(UniformJointCacheAllocation.axis_ends _ _ _).1]
  exact Nat.le_add_right _ _
 exact bound.trans (UniformFourierAxisWorkspace.caches_before c n j j).1

def count(c:Constants)(n d g rectangleCount:ℕ)(j:Fin (ell n))(rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range):ℕ:=
 (R.selections (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).control
  rectangleCount (localTick d g) rectangle nodes).length
structure Result(c:Constants)(n d g rectangleCount:ℕ)(j:Fin (ell n))(rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)
 (x:Fin n→ℂ)(s u:State):Prop where
 pc:u.pc=388
 footer:UniformFourierAxisPrepareFooter.Result (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) (count c n d g rectangleCount j rectangle nodes) j.val
  (s.natReg 6028) (s.natReg 5923) (UniformJointCacheAllocation.axis c n j).endNat
  (UniformJointCacheAllocation.axis c n j).endScalar u
 allocation:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u
 seed:u.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val
 tick:u.natReg 6703=localTick d g
 mode:u.natReg 7080=0
 bank:u.natHeap=UniformCacheRangeSelector.S.writeSelections (UniformFourierAxisWorkspace.axis c n j).selected 0
  (R.selections (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).control
   rectangleCount (localTick d g) rectangle nodes) s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 registers:∀q,H.Protected q→u.natReg q=s.natReg q
 inputs:UniformAxisCacheInputs.Inputs n x u

/-- Actual389 entry through the genuine TREE range selection and halt.
Stored physical source tables, their ordinary bounds, and the actual clock are
inputs; all selected rows, output count and matching-dispatch headers are produced. -/
theorem execution(c:Constants){n d g rectangleCount:ℕ}(hn:0<n)(j:Fin (ell n))
 (rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)(x:Fin n→ℂ)(s:State)
 (head:UniformAxisCacheClockLookup.Header c n j.val s)
 (later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s)
 (input:UniformAxisCacheInputs.Inputs n x s)
 (natFrontier:s.natReg 5924=H.freshNat c n j)(scalarFrontier:s.natReg 5925=H.freshScalar c n j)
 (epoch:s.natReg 5920=g)(duration:s.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d)
 (fit:2*d+5≤envelope c n)(pc:s.pc=0)(bound:WordBound (envelope c n) s)
 (tree:(1≤g∧g≤d)∨(d+4≤g∧g<2*d+4))
 (source:R.RangeSource (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).tasks
  (UniformJointCacheAllocation.axis c n j).control rectangleCount rectangle nodes s.natHeap)
 (layout:R.Layout (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).tasks
  (UniformJointCacheAllocation.axis c n j).control rectangleCount (UniformFourierAxisWorkspace.axis c n j).selected (envelope c n) nodes)
 (rectangleValues:∀k,k<rectangleCount→(rectangle k).1+28≤envelope c n∧(rectangle k).2≤envelope c n)
 (nodeValues:∀q∈nodes,∀k,k<q.count→(q.records k).1+28≤envelope c n∧(q.records k).2≤envelope c n)
 (physicalFit:s.natReg 6028+4*j.val≤envelope c n):
 ∃u ticks,BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u∧
 ticks≤4*Nat.clog 2 (4*UniformAllAxisSeedPreparation.radix n j)+169+
  21*(rectangleCount+R.total nodes)+16*nodes.length∧Result c n d g rectangleCount j rectangle nodes x s u:=by
 have geometry:=UniformFourierAxisGeometry.geometry c hn j
 obtain ⟨a,t,first,cheap,ap,workspace,allocation,radix,seed,selected,_input,frame⟩:=
  UniformFourierAxisPrepareHead.execution c hn j x s head later input natFrontier scalarFrontier epoch duration
   fit geometry.code pc bound
 have values:=tree_values selected tree
 have tailHeader:UniformFourierAxisTreeTail.Header (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) j.val (s.natReg 6028) (s.natReg 5923)
  (UniformJointCacheAllocation.axis c n j).endNat (UniformJointCacheAllocation.axis c n j).endScalar a:=
  ⟨workspace,radix,(frame.natReg _ (by unfold H.Protected;omega)).trans head.axis,
   frame.natReg _ (by unfold H.Protected;omega),frame.natReg _ (by unfold H.Protected;omega),
   allocation.endNat,allocation.endScalar⟩
 have args:UniformCacheRangeSelector.Args (UniformAllAxisSeedPreparation.radix n j)
  (UniformJointCacheAllocation.axis c n j).tasks (UniformJointCacheAllocation.axis c n j).control
  (localTick d g) (UniformFourierAxisWorkspace.axis c n j).selected a:=
  ⟨radix,allocation.tasks,allocation.control,values.2,workspace.selected⟩
 have sourceA:R.RangeSource (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).tasks
  (UniformJointCacheAllocation.axis c n j).control rectangleCount rectangle nodes a.natHeap:=by
  rw[frame.natHeap];exact source
 obtain ⟨u,more,tail,time,up,footer,heap,sh,sr,uo,ur,tick,regs⟩:=
  UniformFourierAxisTreeTail.execution x rectangle nodes a tailHeader args sourceA layout rectangleValues nodeValues
   values.1 ap first.final_bound geometry.code physicalFit
 have scalarHeap:u.scalarHeap=s.scalarHeap:=sh.trans frame.scalarHeap
 have scalarReg:u.scalarReg=s.scalarReg:=sr.trans frame.scalarReg
 have outputs:u.outputs=s.outputs:=uo.trans frame.outputs
 have roots:u.rootOrders=s.rootOrders:=ur.trans frame.roots
 have registers:∀q,H.Protected q→u.natReg q=s.natReg q:=
  fun q h=>(regs q (Or.inl h)).trans (frame.natReg q h)
 have bank:u.natHeap=UniformCacheRangeSelector.S.writeSelections (UniformFourierAxisWorkspace.axis c n j).selected 0
  (R.selections (UniformAllAxisSeedPreparation.radix n j) (UniformJointCacheAllocation.axis c n j).control
   rectangleCount (localTick d g) rectangle nodes) s.natHeap:=by rw[heap,frame.natHeap];rfl
 have inputU:UniformAxisCacheInputs.Inputs n x u:=UniformAxisCacheInputs.transport c n j.val hn x s u input
  ⟨scalarHeap,scalarReg,outputs,roots⟩ (by
   intro q hq
   rw[bank]
   exact UniformCacheRangeSelector.writeSelections_low _ _ _ _ _ (lt_of_lt_of_le hq (frontier_below_selected c n j)))
  (by intro q lo hi;exact registers q (by unfold H.Protected;omega))
 have allocU:=UniformFourierAxisPrepareHead.allocation_transfer allocation (u:=u) (by
  intro q lo hi;apply regs q;unfold UniformFourierAxisTreeTail.Kept;omega)
 have seedU:u.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val:=
  (regs _ (by unfold UniformFourierAxisTreeTail.Kept;omega)).trans seed
 have modeU:u.natReg 7080=0:=(regs _ (by unfold UniformFourierAxisTreeTail.Kept;omega)).trans values.1
 refine ⟨u,_,first.executes tail,by omega,⟨up,footer,allocU,seedU,tick,modeU,bank,scalarHeap,scalarReg,outputs,roots,registers,inputU⟩⟩
end
end ExactFourierCircuits.UniformFourierAxisPrepareTree
