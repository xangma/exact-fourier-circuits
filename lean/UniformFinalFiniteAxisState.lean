import UniformFinalAxisReadyTransport
import UniformFinalAxisPrinted
import UniformFourierAxisCommonExecution
import UniformFourierAxisCommonFrontiers
import UniformGlobalFiniteClockInduction

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalFiniteAxisState
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformJointAllocation (slab envelope)
open UniformTensorMonomialMachine (setPC)
open UniformFinalAxisRetention UniformFinalAxisPrinted
noncomputable section

structure AxisReady {n H g:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(original:State)
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original)
 (k:ℕ)(s:State):Prop where
 pc:s.pc=10
 index:s.natReg 5922=k
 directory:s.natReg 5923=slab constants n+2*k
 natFrontier:s.natReg 5924=UniformGlobalCalendarArena.natBase constants n+UniformFourierAxisWorkspace.natPrefix n k
 scalarFrontier:s.natReg 5925=UniformGlobalCalendarArena.scalarBase constants n+9*prefixSum n k
 cacheFrontiers:0<k→UniformAxisCacheStartupMachine.Frontiers constants n k s
 ready:UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC s 5)
 retained:Frame hn original s
 printed:UniformCalendarPrintedPrefix.Printed hn (events hn cache g) (position hn cache g) k s
 seed:∀q,200≤q→q<210→s.natReg q=original.natReg q
 allocatorFrontiers:0<k→s.natReg 6819=UniformAxisCacheSelectedPreparation.natAt constants n k∧
  s.natReg 6821=UniformAxisCacheSelectedPreparation.scalarAt constants n k

lemma allocator_slab {n H g:ℕ}{hn:0<n}{x:Fin n→ℂ}
 {v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar}{s:State}
 (ready:UniformActualClockReady.Ready hn H (directoryBase n) x g v (setPC s 5)):
 s.natReg 6020=slab constants n∧s.natReg 6028=5*slab constants n:=by
 have pool:=congrArg UniformJointAllocation.Addresses.factorDirectory ready.allocator
 have physical:=congrArg UniformJointAllocation.Addresses.packed ready.allocator
 exact ⟨pool,physical⟩

lemma natAt_zero (c:UniformJointAllocation.Constants)(n:ℕ):
 UniformAxisCacheSelectedPreparation.natAt c n 0=UniformJointCacheAllocation.natStart c n:=by
 simp only[UniformAxisCacheSelectedPreparation.natAt,UniformJointCacheAllocation.offsetSum,
  Finset.range_zero,Finset.sum_empty,Nat.add_zero]
lemma scalarAt_zero (c:UniformJointAllocation.Constants)(n:ℕ):
 UniformAxisCacheSelectedPreparation.scalarAt c n 0=UniformJointCacheAllocation.scalarStart c n:=by
 simp only[UniformAxisCacheSelectedPreparation.scalarAt,UniformJointCacheAllocation.offsetSum,
  Finset.range_zero,Finset.sum_empty,Nat.add_zero]

lemma clock {n H g:ℕ}{hn:0<n}{x:Fin n→ℂ}
 {v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar}{original s:State}
 {cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i original}
 {k:ℕ}(state:AxisReady (H:=H) (g:=g) hn x v original cache k s)(hk:k<axisCount n):
 UniformFourierAxisCommonInputs.ClockArgs constants n g ⟨k,hk⟩ x (setPC s 0):=by
 have slabHeader:=allocator_slab state.ready
 refine ⟨?_,?_,state.ready.inputs.withPC,state.natFrontier,state.scalarFrontier,
  state.ready.clock,rfl,?_,slabHeader.1,slabHeader.2,state.directory⟩
 · exact ⟨state.index,state.ready.seed,state.ready.initialNat.trans (natAt_zero constants n).symm,
    state.ready.initialScalar.trans (scalarAt_zero constants n).symm⟩
 · intro positive
   have h:=state.cacheFrontiers positive
   exact ⟨h.natFrontier,h.scalarFrontier⟩
 · exact changePC_bound _ (setPC s 5) 0 state.ready.bound (Nat.zero_le _)

lemma cache_next {n:ℕ}(j:Fin (axisCount n)):
 (UniformJointCacheAllocation.axis constants n j).endNat=UniformAxisCacheSelectedPreparation.natAt constants n (j.val+1)∧
 (UniformJointCacheAllocation.axis constants n j).endScalar=UniformAxisCacheSelectedPreparation.scalarAt constants n (j.val+1):=by
 have nstep:=UniformAxisCacheAdvanceMachine.nat_succ constants n j
 have sstep:=UniformAxisCacheAdvanceMachine.scalar_succ constants n j
 unfold UniformJointCacheAllocation.axis
 rw[(UniformJointCacheAllocation.axis_ends _ _ _).1,(UniformJointCacheAllocation.axis_ends _ _ _).2]
 exact ⟨nstep,sstep⟩

lemma workspace_next {n:ℕ}(j:Fin (axisCount n)):
 (UniformFourierAxisWorkspace.axis constants n j).endNat=UniformGlobalCalendarArena.natBase constants n+
  UniformFourierAxisWorkspace.natPrefix n (j.val+1)∧
 (UniformFourierAxisWorkspace.axis constants n j).endScalar=UniformGlobalCalendarArena.scalarBase constants n+
  9*prefixSum n (j.val+1):=by
 unfold UniformFourierAxisWorkspace.axis
 rw[(UniformFourierAxisWorkspace.axis_ends _ _ _).1,(UniformFourierAxisWorkspace.axis_ends _ _ _).2]
 rw[UniformFourierAxisWorkspace.prefix_step,prefix_succ,radixAt_eq]
 constructor <;>omega

end
end ExactFourierCircuits.UniformFinalFiniteAxisState
