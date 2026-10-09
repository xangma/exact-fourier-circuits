import UniformFinalStartupFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStartupFrames
open UniformMachine UniformTensorMonomialMachine
noncomputable section
lemma scale_keeps6002 (c:UniformJointAllocation.Constants)(s:State):
 (applyBlock (UniformJointAllocationMachine.scaleOps c) s).natReg 6002=s.natReg 6002:=by
 simp [UniformJointAllocationMachine.scaleOps,applyBlock,Op.apply,writeNat,next]
lemma allocation_stride (c:UniformJointAllocation.Constants)(n:ℕ)(s:State):
 (UniformJointAllocationMachine.result c n s).natReg 6002=UniformJointCacheWorkspace.stride n:=by
 have header:=UniformJointAllocationMachine.headers_natReg 6020 UniformJointAllocationMachine.factors
  (UniformJointAllocationMachine.scaled c n s) 6002 (by decide) (Or.inl (by decide))
 have h1:(UniformJointAllocationMachine.result c n s).natReg 6002=
  (UniformJointAllocationMachine.scaled c n s).natReg 6002:=by
  unfold UniformJointAllocationMachine.result
  exact header
 have h2:(UniformJointAllocationMachine.scaled c n s).natReg 6002=
  (UniformJointAllocationMachine.powered n s).natReg 6002:=by
  unfold UniformJointAllocationMachine.scaled
  exact scale_keeps6002 c (UniformJointAllocationMachine.powered n s)
 exact h1.trans (h2.trans (UniformJointAllocationMachine.pow_values n s).2)
end
end ExactFourierCircuits.UniformFinalStartupFrames
