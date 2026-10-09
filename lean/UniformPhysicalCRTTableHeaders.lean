import UniformFinalOuterHeaders
import UniformPhysicalCRTTableHeaderProgram
import UniformNatHeaderFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalCRTTableHeaders
open UniformMachine UniformNatBlockMachine UniformFinalOuterHeaders
noncomputable section
lemma raw_alpha(s:State):
 (applyBlock operations s).natReg 7310=s.natReg 6026-s.natReg 103*2:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_inverse(s:State):
 (applyBlock operations s).natReg 7311=s.natReg 6026-s.natReg 103:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_storage(s:State):
 (applyBlock operations s).natReg 7300=s.natReg 6026-s.natReg 103:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_axes(s:State):
 (applyBlock operations s).natReg 7790=s.natReg 102+1:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_volume(s:State):
 (applyBlock operations s).natReg 7791=s.natReg 103:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_seed(s:State):
 (applyBlock operations s).natReg 7792=s.natReg 6904:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_sourceAlpha(s:State):
 (applyBlock operations s).natReg 7793=s.natReg 105+(s.natReg 102*6+5):=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_sourceBeta(s:State):
 (applyBlock operations s).natReg 7794=s.natReg 105+(s.natReg 102*6+5)+s.natReg 103:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_destAlpha(s:State):
 (applyBlock operations s).natReg 7795=s.natReg 6026-s.natReg 103*2:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_destInverse(s:State):
 (applyBlock operations s).natReg 7796=s.natReg 6026-s.natReg 103:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]

lemma raw_work(s:State):(applyBlock operations s).natReg 7797=s.natReg 6026:=by
 simp[operations,applyBlock,literal_reg,binary_reg,evalNat]

structure Args(c:UniformJointAllocation.Constants)(n:ℕ)(s:State):Prop where
 alpha:s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n
 inverse:s.natReg 7311=UniformKernelSpectrumStorage.betaInverseBase c n
 storage:s.natReg 7300=UniformKernelSpectrumStorage.base c n
 axes:s.natReg 7790=UniformAllAxisSeedPreparation.axisCount n
 volume:s.natReg 7791=UniformInitialPreparation.len n
 seed:s.natReg 7792=s.natReg 6904
 sourceAlpha:s.natReg 7793=UniformInitialPreparation.copyBase n+UniformInitialPreparation.alphaBase n
 sourceBeta:s.natReg 7794=UniformInitialPreparation.copyBase n+UniformInitialPreparation.betaBase n
 destAlpha:s.natReg 7795=UniformKernelSpectrumStorage.alphaBase c n
 destInverse:s.natReg 7796=UniformKernelSpectrumStorage.betaInverseBase c n
 work:s.natReg 7797=2*UniformJointAllocation.slab c n

def Changed(q:ℕ):Prop:=(7390≤q∧q≤7395)∨q=7310∨q=7311∨q=7300∨(7790≤q∧q≤7797)
lemma frame(s:State):
 (applyBlock operations s).natHeap=s.natHeap∧
 (applyBlock operations s).scalarHeap=s.scalarHeap∧
 (applyBlock operations s).scalarReg=s.scalarReg∧
 (applyBlock operations s).outputs=s.outputs∧
 (applyBlock operations s).rootOrders=s.rootOrders∧
 (∀q,¬Changed q→(applyBlock operations s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q h;unfold Changed at h
 apply UniformNatHeaderFrame.block_natReg
 simp [operations,UniformNatHeaderFrame.keeps]
 omega

theorem values(c:UniformJointAllocation.Constants)(n:ℕ)(s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (source:s.natReg 6026=2*UniformJointAllocation.slab c n):
 Args c n (applyBlock operations s):=by
 have width:=metadata.saved.workingLength
 have count:=metadata.saved.count
 have copy:=metadata.saved.copyAddress
 have kept:(applyBlock operations s).natReg 6904=s.natReg 6904:=
  (frame s).2.2.2.2.2 6904 (by unfold Changed;omega)
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw[raw_alpha,source,width]
   simp[UniformKernelSpectrumStorage.alphaBase,Nat.mul_comm]
 · rw[raw_inverse,source,width]
   rfl
 · rw[raw_storage,source,width]
   rfl
 · rw[raw_axes,count]
 · exact (raw_volume s).trans width
 · exact (raw_seed s).trans kept.symm
 · rw[raw_sourceAlpha,copy,count]
   simp[UniformInitialPreparation.alphaBase,UniformCRTTraversalMachine.alphaBase,
    UniformCRTTraversalMachine.digitBase,Nat.mul_comm,Nat.add_assoc]
   omega
 · rw[raw_sourceBeta,copy,count,width]
   simp[UniformInitialPreparation.betaBase,UniformCRTTraversalMachine.betaBase,
    UniformCRTTraversalMachine.alphaBase,UniformCRTTraversalMachine.digitBase,Nat.mul_comm,Nat.add_assoc]
   omega
 · rw[raw_destAlpha,source,width]
   simp[UniformKernelSpectrumStorage.alphaBase,Nat.mul_comm]
 · rw[raw_destInverse,source,width]
   rfl
 · exact (raw_work s).trans source

lemma safe(s:State)(B:ℕ)(source:s.natReg 6026≤B)
 (low:s.natReg 105+12*s.natReg 102+4*s.natReg 103+s.natReg 6904+100≤B):
 readable operations s∧peak operations s≤B:=by
 simp[operations,readable,peak,Op.readable,Op.peak,literal_reg,binary_reg,evalNat]
 omega
end
end ExactFourierCircuits.UniformPhysicalCRTTableHeaders
