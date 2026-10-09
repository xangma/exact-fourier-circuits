import UniformProducedClockTick
import UniformProducedClockTickPrepared
import UniformActualAxisPreparedCycle
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, Proposition 4.2 proof, PDF p. 20 (`prop:tensor-fourier`).

This entry-point adapter equates the placed kernel state with the caller’s current state. The paper has no register/PC counterpart; the equality ensures proof-level PC relocation does not splice unrelated heap executions.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedClockTickAtEntry
open UniformMachine UniformSynchronizedLayers UniformGlobalCalendarDispatch UniformAllAxisSeedPreparation
open UniformProducedClockTick (stored budget)
open UniformTensorMonomialMachine (setPC)
open UniformActualGlobalConstants (constants)
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program

theorem numeric {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (x:Fin n→ℂ) (s:State)
 (printed:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
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
 (∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,5920≤j→j<5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000≤j∧j<6200∨6300≤j)→u.natReg j=s.natReg j) ∧
 (∀j,100≤j→j<107→u.natReg j=s.natReg j) :=by
 have printedPC:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) (setPC s 0):=by
  intro i hi
  have old:=printed i hi
  exact ⟨old.rows,old.widths,old.permutations,old.directory,old.pool⟩
 obtain ⟨u,ticks,run,rest⟩:=UniformProducedClockTick.execution hn es length t actual v x (setPC s 0)
  printedPC source volume count allocated constantsReady rfl
  (UniformMachine.changePC_bound _ s 0 wb (Nat.zero_le _)) one clock horizon
 rw[UniformActualAxisPreparedCycle.kernel_entry s pc] at run
 exact ⟨u,ticks,run,rest⟩

theorem prepared {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (x:Fin n→ℂ) (s:State)
 (printed:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
 (prepared:UniformActualClockEntry.Prepared v)
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
 UniformActualClockEntry.Prepared (stored n u) ∧UniformActualClockEntry.PreparedOutput n u ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,5920≤j→j<5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000≤j∧j<6200∨6300≤j)→u.natReg j=s.natReg j) ∧
 (∀j,100≤j→j<107→u.natReg j=s.natReg j) :=by
 have printedPC:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) (setPC s 0):=by
  intro i hi
  have old:=printed i hi
  exact ⟨old.rows,old.widths,old.permutations,old.directory,old.pool⟩
 obtain ⟨u,ticks,run,rest⟩:=UniformProducedClockTickPrepared.execution hn es length t actual v x (setPC s 0)
  printedPC source prepared volume count allocated constantsReady rfl
  (UniformMachine.changePC_bound _ s 0 wb (Nat.zero_le _)) one clock horizon
 rw[UniformActualAxisPreparedCycle.kernel_entry s pc] at run
 exact ⟨u,ticks,run,rest⟩

end
end ExactFourierCircuits.UniformProducedClockTickAtEntry
