import UniformFinalActualClockCost
import UniformProducedClockTickPrepared

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualProducedTickCost
noncomputable section
open UniformJointAllocation UniformJointConditionalKernelContext UniformActualGlobalTickContext
open UniformActualGlobalConstants (constants roles_positive)
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program

/-- The actual enlarged child reserve changes room proofs, while the charged
kernel count uses the same actual child-cost function and numerical geometry. -/
lemma reserve_ticks (c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles)
 (R:ℕ)(reserve:R≤fixed c)(physical:List UniformSectorPackingMachine.PhysicalAxis)
 (shape:PhysicalGeometry c n physical):
 UniformActualKernelCost.kernelTicks (context c n hn roles R reserve physical shape)=
 UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles physical shape):=rfl

lemma entries_two {n:ℕ}(hn:0<n)(a:Geometry n):∀q∈a.entries,2≤q.radix:=by
 intro q member
 have present:q.radix∈a.entries.map UniformGlobalDiagonalRowsMachine.Entry.radix:=
  List.mem_map.mpr ⟨q,member,rfl⟩
 rw[a.selected] at present
 obtain ⟨j,eq⟩:=List.mem_ofFn.mp present
 exact eq ▸ UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j

/-- Every ordinary bank link and every selected radix condition comes from
the actual produced geometry. The reserve is the proved same-program reserve. -/
lemma retention_bound {n:ℕ}(hn:0<n)(a:Geometry n):
 UniformGlobalKernelDiagonalRetention.budget (kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  UniformRecursiveChildInduction.cost≤
 UniformActualKernelCost.kernelTicks
  (actualReserveContext constants n hn roles_positive a.physical a.placement.shape)+
  (130*constants.roles+100)*UniformInitialPreparation.len n:=by
 have h:=UniformFinalActualClockCost.actual_tick_bound (kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  (links hn a) (entries_two hn a)
 have same:UniformActualKernelCost.kernelTicks (kernel hn a)=
  UniformActualKernelCost.kernelTicks
   (actualReserveContext constants n hn roles_positive a.physical a.placement.shape):=
  reserve_ticks constants hn roles_positive UniformRecursiveReserve.reserve
   UniformActualGlobalConstants.reserve_le a.physical a.placement.shape
 have volume:(kernel hn a).packing.volume=UniformInitialPreparation.len n:=rfl
 rw[same,volume] at h
 exact h

end
end ExactFourierCircuits.UniformActualProducedTickCost
