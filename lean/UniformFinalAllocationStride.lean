import UniformFinalStartupFrames

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 three-transform construction and §5.4 Theorem 1.1 proof,
PDF pp.22-24 (`eq:chirp`, `thm:main`), with the model in §1.1, PDF p.2 (`sec:model`).

Startup, header, continuation and output bookkeeping refines the fixed
deterministic program. There is no separate paper counterpart for these state
layouts; the surrounding paper argument requires their preparation/index cost.
-/
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
