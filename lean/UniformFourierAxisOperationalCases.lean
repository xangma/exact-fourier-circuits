import UniformFourierAxisPrepareTree
import UniformFourierAxisPrepareBoundary
import UniformFourierAxisPrepareInactive

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisOperationalCases
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
noncomputable section
namespace H
export UniformFourierAxisPrepareHead (freshNat freshScalar)
end H
namespace R
export UniformCacheRangeSelector (Range RangeSource Layout total)
end R

def TreeAt(d g:ℕ):Prop:=(1≤g∧g≤d)∨(d+4≤g∧g<2*d+4)
def budget(r rectangleCount:ℕ)(nodes:List R.Range):ℕ:=
 4*Nat.clog 2 (4*r)+70*r+233+21*(rectangleCount+R.total nodes)+16*nodes.length

/-- Factual retained inputs to the literal389. The source/layout facts describe
already printed cache cells; no selected output or matrix action is assumed. -/
structure Inputs(c:Constants)(n d g rectangleCount:ℕ)(j:Fin (ell n))
 (rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)(x:Fin n→ℂ)(s:State):Prop where
 head:UniformAxisCacheClockLookup.Header c n j.val s
 later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s
 input:UniformAxisCacheInputs.Inputs n x s
 natFrontier:s.natReg 5924=H.freshNat c n j
 scalarFrontier:s.natReg 5925=H.freshScalar c n j
 epoch:s.natReg 5920=g
 duration:s.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d
 fit:2*d+5≤envelope c n
 pc:s.pc=0
 bound:WordBound (envelope c n) s
 source:R.RangeSource (UniformAllAxisSeedPreparation.radix n j)
  (UniformJointCacheAllocation.axis c n j).tasks (UniformJointCacheAllocation.axis c n j).control
  rectangleCount rectangle nodes s.natHeap
 layout:R.Layout (UniformAllAxisSeedPreparation.radix n j)
  (UniformJointCacheAllocation.axis c n j).tasks (UniformJointCacheAllocation.axis c n j).control
  rectangleCount (UniformFourierAxisWorkspace.axis c n j).selected (envelope c n) nodes
 rectangleValues:∀k,k<rectangleCount→(rectangle k).1+28≤envelope c n∧(rectangle k).2≤envelope c n
 nodeValues:∀q∈nodes,∀k,k<q.count→(q.records k).1+28≤envelope c n∧(q.records k).2≤envelope c n
 pool:s.natReg 6020=slab c n
 physical:s.natReg 6028=5*slab c n
 directory:s.natReg 5923=slab c n+2*j.val

/-- The actual branch result, with all three constructors tied to the same
literal program, local duration and real input/output states. -/
inductive Branch(c:Constants)(n d g rectangleCount:ℕ)(hn:0<n)(j:Fin (ell n))
 (rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)(x:Fin n→ℂ)(s u:State):Prop where
 | tree (active:TreeAt d g)
   (actual:UniformFourierAxisPrepareTree.Result c n d g rectangleCount j rectangle nodes x s u):
   Branch c n d g rectangleCount hn j rectangle nodes x s u
 | boundary(q:Fin 3)(active:UniformFourierAxisPrepareBoundary.BoundaryAt d g)
   (actual:UniformFourierAxisPrepareBoundary.Result c n d g hn j q x s u):
   Branch c n d g rectangleCount hn j rectangle nodes x s u
 | inactive(inactive:2*d+5≤g)
   (actual:UniformFourierAxisPrepareInactive.Result c n d g j x s u):
   Branch c n d g rectangleCount hn j rectangle nodes x s u

/-- Every epoch executes one of the genuine three branches; each helper halt
and continuation is included in its actual charged execution. -/
theorem execution(c:Constants){n d g rectangleCount:ℕ}(hn:0<n)(j:Fin (ell n))
 (rectangle:ℕ→ℕ×ℕ)(nodes:List R.Range)(x:Fin n→ℂ)(s:State)
 (input:Inputs c n d g rectangleCount j rectangle nodes x s):∃u ticks,
 BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u∧
 ticks≤budget (UniformAllAxisSeedPreparation.radix n j) rectangleCount nodes∧
 Branch c n d g rectangleCount hn j rectangle nodes x s u:=by
 have geo:=UniformFourierAxisGeometry.geometry c hn j
 have physicalFit:s.natReg 6028+4*j.val≤envelope c n:=by
  rw[input.physical]
  have fit:=geo.axisRowFit
  omega
 by_cases tree:TreeAt d g
 · obtain ⟨u,t,run,time,result⟩:=UniformFourierAxisPrepareTree.execution c hn j rectangle nodes x s
    input.head input.later input.input input.natFrontier input.scalarFrontier input.epoch input.duration
    input.fit input.pc input.bound tree input.source input.layout input.rectangleValues input.nodeValues physicalFit
   exact ⟨u,t,run,by unfold budget;omega,.tree tree result⟩
 · by_cases boundary:UniformFourierAxisPrepareBoundary.BoundaryAt d g
   · obtain ⟨u,t,q,run,time,result⟩:=UniformFourierAxisPrepareBoundary.execution c hn j x s
      input.head input.later input.input input.natFrontier input.scalarFrontier input.epoch input.duration
      input.fit input.pc input.bound boundary input.pool input.physical input.directory
     exact ⟨u,t,run,by unfold budget;omega,.boundary q boundary result⟩
   · have inactive:2*d+5≤g:=by
      unfold TreeAt at tree
      unfold UniformFourierAxisPrepareBoundary.BoundaryAt at boundary
      omega
     obtain ⟨u,t,run,time,result⟩:=UniformFourierAxisPrepareInactive.execution c hn j x s
      input.head input.later input.input input.natFrontier input.scalarFrontier input.epoch input.duration
      input.fit geo.code input.pc input.bound inactive physicalFit
     exact ⟨u,t,run,by unfold budget;omega,.inactive inactive result⟩

end
end ExactFourierCircuits.UniformFourierAxisOperationalCases
