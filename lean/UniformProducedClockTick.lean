import UniformActualClockHeaderInputs
import UniformCalendarPrintedPrefix
import UniformProducedCalendarAction
import UniformProducedSynchronizedAction
import UniformActualTickCallerFrame
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, proof of Proposition 4.2, PDF p. 20 (`prop:tensor-fourier`), using §2.6, Theorem 2.6, pp. 11–12 (`net:tensor-bound`).

One literal kernel/diagonal tick consumes already produced axis banks and returns actual heap values with the synchronized matrix action. Its local Action/printed-bank premises are internal; `UniformActualCompleteClockTick.execution` constructs them.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedClockTick
open UniformMachine UniformSynchronizedLayers UniformGlobalCalendarDispatch UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformActualGlobalTickContext
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program

def stored (n:ℕ) (s:State) (r:ℕ) (j:Fin (UniformActualClockEntry.volume n)):Scalar:=
 UniformExecutedTaggedBank.values (UniformActualClockEntry.sourceBase n) (UniformActualClockEntry.volume n) s r j.val

def family {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix):=
 UniformProducedCalendarAction.family hn es (fun i=>(slot (localSchedules n i) (length i) t).matrix) actual

def budget {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix):ℕ:=
 let a:=UniformProducedAllAxisGeometry.geometry (family hn es length t actual)
 UniformGlobalKernelDiagonalRetention.budget (kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  UniformRecursiveChildInduction.cost+2

/-- One actual kernel/diagonal clock step consumes the produced full-axis banks.
The common389 per-axis Action supplies matrix semantics, while the closed same
recursive program discharges every real sector child. -/
theorem execution {n H:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (actual:∀i,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n i) (es i) (slot (localSchedules n i) (length i) t).matrix)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (x:Fin n→ℂ) (s:State)
 (printed:UniformCalendarPrintedPrefix.Printed hn es (fun i=>(actual i).position) (axisCount n) s)
 (source:UniformActualClockEntry.Source n v s)
 (volume:s.natReg 103=UniformInitialPreparation.len n)
 (count:s.natReg 102+1=axisCount n)
 (allocated:UniformJointAllocationMachine.observed s=UniformJointAllocation.allocate constants n)
 (constantsReady:UniformBinaryCStageMachine.Constants s)
 (pc:s.pc=0) (wb:WordBound (UniformJointAllocation.envelope constants n) s)
 (one:s.natReg 5939=1) (clock:s.natReg 5920=t.val) (horizon:s.natReg 5921=H):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n)
  (UniformAssembly.placed (UniformGlobalClockConductor.kernelBase UniformFourierAxisPrepareMachine.program) s) ticks u ∧
 ticks≤budget hn es length t actual ∧u.pc=5 ∧u.natReg 5920=t.val+1 ∧
 UniformActualClockEntry.Source n (stored n u) u ∧
 (∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
  (stored n u r j).value=(UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (fun k=>(v r k).value) j) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z) ∧
 (∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,5920≤j→j<5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000≤j∧j<6200∨6300≤j)→u.natReg j=s.natReg j) ∧
 (∀j,100≤j→j<107→u.natReg j=s.natReg j):=by
 let f:=family hn es length t actual
 let a:=UniformProducedAllAxisGeometry.geometry f
 let g:=kernel hn a
 let d:=UniformActualGlobalTickContext.diagonal hn a
 let links:=UniformActualGlobalTickContext.links hn a
 /- Proposition 4.2 proof, p. 20: consume the actual printed axis banks; the kernel’s former child obligation is closed by the fixed recursive program through `UniformActualGlobalTickContext.execution`. -/
 obtain ⟨banks,directory,pools⟩:=UniformCalendarPrintedPrefix.complete hn es (fun i=>(actual i).position) s printed
 have kernelInput:=UniformActualClockHeaderInputs.kernel_input hn a s volume count allocated
 have diagonalInput:=UniformActualClockHeaderInputs.diagonal_input hn a s volume count allocated
 have rawSource:=UniformActualClockHeaderInputs.source hn a v s source
 obtain ⟨u,ticks,run,cheap,done,advanced,values,outputs,roots,nat,scalar,clockFrame,high,startup⟩:=
  UniformActualGlobalTickContext.execution hn a UniformFourierAxisPrepareMachine.program v x s kernelInput diagonalInput
   banks rawSource directory pools constantsReady (UniformActualGlobalClockProgram.code_bound n) pc wb one
   (by rw[clock,horizon];exact t.isLt)
 /- Equation (4.5), p. 20: derive the slot matrix from the same printed pair order and lane-zero factors, then read values from the returned physical heap. -/
 have localMatrices:=UniformProducedCalendarAction.local_matrices hn es length t actual
 have numeric:∀r,r<UniformActualClockEntry.roles→∀j:Fin (UniformActualClockEntry.volume n),
  (u.scalarHeap (UniformActualClockEntry.sourceBase n+r*UniformActualClockEntry.volume n+j.val)).map Scalar.value=
  some ((UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (fun k=>(v r k).value) j):=by
  intro r hr j
  have h:=values r hr j
  rw[UniformProducedSynchronizedAction.action hn f length t localMatrices v r j] at h
  exact h
 refine ⟨u,ticks,run,cheap,done,advanced.trans (congrArg (fun q=>q+1) clock),?_,?_,?_,?_,outputs,roots,clockFrame,high,startup⟩
 · intro r hr j;exact UniformExecutedTaggedBank.present (numeric r hr j)
 · intro r hr j;exact UniformExecutedTaggedBank.value (numeric r hr j)
 · intro z hz
   apply nat z hz
   · change z<2*UniformJointAllocation.slab constants n;exact hz
   · change z<3*UniformJointAllocation.slab constants n;omega
   · change z<4*UniformJointAllocation.slab constants n;omega
 · intro z hz
   apply scalar z hz
   · change z<2*UniformJointAllocation.slab constants n+
      UniformRecursiveSelfCallMachine.W*UniformInitialPreparation.len n;omega
   · change z<3*UniformJointAllocation.slab constants n;omega
   · change z<2*UniformJointAllocation.slab constants n;exact hz
   · change z<4*UniformJointAllocation.slab constants n;omega
end
end ExactFourierCircuits.UniformProducedClockTick
