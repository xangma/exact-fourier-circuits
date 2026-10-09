import UniformActualClockReady
import UniformProducedClockTickAtEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockReadyAfterKernel
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformActualClockReady
open UniformTensorMonomialMachine (setPC)
noncomputable section

/-- The closed kernel/147 low2U and caller frames restore every persistent
clock condition. The next source is the genuine executed tagged output. -/
theorem restore {n H seedDirectory t:ℕ} (hn:0<n) (x:Fin n→ℂ)
 (v w:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s u:State)
 (ready:Ready hn H seedDirectory x t v (setPC s 5))
 (pc:u.pc=5) (wb:WordBound (UniformJointAllocation.envelope constants n) u)
 (clock:u.natReg 5920=t+1) (source:UniformActualClockEntry.Source n w u)
 (nat:∀z,z<2*UniformJointAllocation.slab constants n→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<2*UniformJointAllocation.slab constants n→u.scalarHeap z=s.scalarHeap z)
 (outputs:u.outputs=s.outputs) (roots:u.rootOrders=s.rootOrders)
 (clockFrame:∀j,5920≤j→j<5940→j≠5920→u.natReg j=s.natReg j)
 (high:∀j,(6000≤j∧j<6200∨6300≤j)→u.natReg j=s.natReg j)
 (startup:∀j,100≤j→j<107→u.natReg j=s.natReg j):
 Ready hn H seedDirectory x (t+1) w u:=by
 have input:=UniformClockCacheInputsRetention.inputs constants hn x (setPC s 5) u ready.inputs
  (fun z hz=>nat z (by omega)) (fun z hz=>scalar z (by omega))
  (fun z lo hi=>startup z lo (by omega)) outputs roots
 have cache:UniformAxisCacheLoopState.All constants n hn (axisCount n) u:=by
  intro i hi
  have beforeN:=UniformGlobalCalendarArena.prior_nat constants n i
  have beforeS:=UniformGlobalCalendarArena.prior_scalar constants n i
  have fitN:=UniformGlobalCalendarArena.nat_fits constants hn
  have fitS:=UniformGlobalCalendarArena.scalar_fits constants hn
  apply UniformAxisCacheContents.transport (ready.cache i hi)
  exact ⟨fun z _ hz=>nat z (by omega),fun z _ hz=>scalar z (by omega)⟩
 have allocated:UniformJointAllocationMachine.observed u=UniformJointAllocationMachine.observed s:=by
  unfold UniformJointAllocationMachine.observed
  congr 1 <;>apply high <;>omega
 have constantsReady:UniformBinaryCStageMachine.Constants u:=by
  have pos:=UniformJointAllocation.actual_arithmetic constants n hn
  exact ⟨(scalar 1 (by omega)).trans ready.constants.1,(scalar 2 (by omega)).trans ready.constants.2⟩
 refine ⟨pc,wb,allocated.trans ready.allocator,?_,?_,?_,clock,?_,?_,?_,?_,?_,?_,?_,source,
  constantsReady,ready.length,input,cache⟩
 · exact (startup 102 (by omega) (by omega)) ▸ ready.axisCount
 · exact (startup 103 (by omega) (by omega)).trans ready.volume
 · exact (clockFrame 5921 (by omega) (by omega) (by omega)).trans ready.horizon
 · exact (clockFrame 5936 (by omega) (by omega) (by omega)).trans ready.natArena
 · exact (clockFrame 5937 (by omega) (by omega) (by omega)).trans ready.scalarArena
 · exact (clockFrame 5938 (by omega) (by omega) (by omega)).trans ready.axes
 · exact (clockFrame 5939 (by omega) (by omega) (by omega)).trans ready.one
 · exact (high 6904 (by omega)).trans ready.seed
 · exact (high 6909 (by omega)).trans ready.initialNat
 · exact (high 6910 (by omega)).trans ready.initialScalar
end
end ExactFourierCircuits.UniformActualClockReadyAfterKernel
