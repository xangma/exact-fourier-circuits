import UniformAxisCacheInputs
import UniformActualClockEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformClockCacheInputsRetention
open UniformMachine UniformJointAllocation
namespace S
export UniformAllAxisSeedPreparation (axisCount axisBase directoryBase word_setup compact_address_before)
end S
namespace C
export UniformAllAxisConjugatePreparation (axisBase directoryBase word_setup compact_address_before)
end C
noncomputable section

/-- Cache source metadata and coefficient tables lie belowU, so actual data
changes at2U and fresh calendar/boundary writes do not invalidate their input
contract. No whole scalar heap equality is required. -/
theorem inputs (c:Constants){n:ℕ}(hn:0<n)(x:Fin n→ℂ)(s u:State)
 (input:UniformAxisCacheInputs.Inputs n x s)
 (nat:∀z,z<slab c n→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<slab c n→u.scalarHeap z=s.scalarHeap z)
 (regs:∀z,100≤z→z≤106→u.natReg z=s.natReg z)
 (outputs:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders):
 UniformAxisCacheInputs.Inputs n x u:=by
 have seedBound:=S.word_setup hn
 have conjugateBound:=C.word_setup hn
 have slabBound:=UniformAxisCachePreparationRetention.slab_above_seed_word c n
 have seedPool:S.axisBase n (S.axisCount n)≤ slab c n:=seedBound.2.1.trans slabBound
 have seedDirectory:S.directoryBase n+2*S.axisCount n≤ slab c n:=seedBound.2.2.trans slabBound
 have conjugatePool:C.axisBase n (S.axisCount n)≤ slab c n:=conjugateBound.2.1.trans slabBound
 have conjugateDirectory:C.directoryBase n+2*S.axisCount n≤ slab c n:=conjugateBound.2.2.trans slabBound
 have globalBelow:UniformGlobalLocalPreparation.globalEnd n≤ slab c n:=by
  unfold S.axisBase UniformLocalSeedTableMachine.poolBase at seedPool
  omega
 have guardFrame:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=
  ⟨fun z _ hi=>nat z (by omega),fun z hi=>scalar z (hi.trans_le globalBelow),regs,outputs,roots⟩
 refine ⟨guardFrame.metadata input.metadata,guardFrame.operands input.operands,?_,?_⟩
 · constructor
   · intro j hj q l
     exact (scalar _ ((S.compact_address_before j hj q l).trans_le seedPool)).trans (input.original.coefficients j hj q l)
   · intro j hj
     exact (nat _ (by have:=j.isLt;omega)).trans (input.original.address j hj)
   · intro j hj
     exact (nat _ (by have:=j.isLt;omega)).trans (input.original.width j hj)
 · constructor
   · intro j hj q l
     exact (scalar _ ((C.compact_address_before j hj q l).trans_le conjugatePool)).trans (input.conjugate.coefficients j hj q l)
   · intro j hj
     exact (nat _ (by have:=j.isLt;omega)).trans (input.conjugate.address j hj)
   · intro j hj
     exact (nat _ (by have:=j.isLt;omega)).trans (input.conjugate.width j hj)
end
end ExactFourierCircuits.UniformClockCacheInputsRetention
