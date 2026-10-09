import UniformAxisCacheTransition
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheFinalEnds
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation

lemma nat_end (c:A.Constants)(n:ℕ)(j:Fin (C.ell n))(last:j.val+1=C.ell n):
 (UniformJointCacheAllocation.axisBank (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val)).endNat=
 UniformJointCacheAllocation.natEnd c n:=by
 rw [(UniformJointCacheAllocation.axis_ends _ _ _).1]
 have step:=UniformAxisCacheAdvanceMachine.nat_succ c n j
 simpa only [natAt,last,UniformJointCacheAllocation.natEnd,UniformJointCacheAllocation.natTotal] using step

lemma scalar_end (c:A.Constants)(n:ℕ)(j:Fin (C.ell n))(last:j.val+1=C.ell n):
 (UniformJointCacheAllocation.axisBank (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val)).endScalar=
 UniformJointCacheAllocation.scalarEnd c n:=by
 rw [(UniformJointCacheAllocation.axis_ends _ _ _).2]
 have step:=UniformAxisCacheAdvanceMachine.scalar_succ c n j
 simpa only [scalarAt,last,UniformJointCacheAllocation.scalarEnd,UniformJointCacheAllocation.scalarTotal] using step

/-- The actual retained last-axis allocator Result supplies the final global
arena addresses. No last-axis frontier reset or extra transition is required. -/
theorem registers (c:A.Constants)(n:ℕ)(j:Fin (C.ell n))(last:j.val+1=C.ell n)(s:State)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) s):
 s.natReg 6819=UniformJointCacheAllocation.natEnd c n∧
 s.natReg 6821=UniformJointCacheAllocation.scalarEnd c n:=
 ⟨result.endNat.trans (nat_end c n j last),result.endScalar.trans (scalar_end c n j last)⟩

end ExactFourierCircuits.UniformAxisCacheFinalEnds
