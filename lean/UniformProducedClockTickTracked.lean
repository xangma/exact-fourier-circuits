import UniformProducedClockTickAtEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedClockTickTracked
open UniformMachine UniformSynchronizedLayers UniformGlobalCalendarDispatch UniformAllAxisSeedPreparation
open UniformProducedClockTick (stored budget)
open UniformActualGlobalConstants (constants)
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program

/-- Optional collective tag tracking uses the same actual program and returned
heap, allowing the numerical and prepared outer transforms to share one loop. -/
theorem execution {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (x:Fin n→ℂ) (s:State)
 (printed:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
 (tagged:Prop) (prepared:tagged→UniformActualClockEntry.Prepared v)
 (volume:s.natReg 103=UniformInitialPreparation.len n)
 (count:s.natReg 102+1=axisCount n)
 (allocated:UniformJointAllocationMachine.observed s=UniformJointAllocation.allocate constants n)
 (constantsReady:UniformBinaryCStageMachine.Constants s)
 (pc:s.pc=756) (wb:WordBound (UniformJointAllocation.envelope constants n) s)
 (one:s.natReg 5939=1) (clock:s.natReg 5920=t.val) (horizon:s.natReg 5921=H):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n)
  s ticks u ∧
 ticks≤budget hn es length t actual ∧u.pc=5 ∧u.natReg 5920=t.val+1 ∧
 UniformActualClockEntry.Source n (stored n u) u ∧
 (∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
  (stored n u r j).value=(UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (fun k=>(v r k).value) j) ∧
 (tagged→UniformActualClockEntry.Prepared (stored n u)) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,5920≤j→j<5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000≤j∧j<6200∨6300≤j)→u.natReg j=s.natReg j) ∧
 (∀j,100≤j→j<107→u.natReg j=s.natReg j) :=by
 classical
 by_cases active:tagged
 · obtain ⟨u,ticks,run,cheap,pc,advanced,sourceOut,numeric,tags,_preparedOutput,rest⟩:=
    UniformProducedClockTickAtEntry.prepared hn es length t actual v x s printed source (prepared active)
     volume count allocated constantsReady pc wb one clock horizon
   exact ⟨u,ticks,run,cheap,pc,advanced,sourceOut,numeric,fun _=>tags,rest⟩
 · obtain ⟨u,ticks,run,cheap,pc,advanced,sourceOut,numeric,rest⟩:=
    UniformProducedClockTickAtEntry.numeric hn es length t actual v x s printed source
     volume count allocated constantsReady pc wb one clock horizon
   exact ⟨u,ticks,run,cheap,pc,advanced,sourceOut,numeric,fun h=>False.elim (active h),rest⟩
end
end ExactFourierCircuits.UniformProducedClockTickTracked
