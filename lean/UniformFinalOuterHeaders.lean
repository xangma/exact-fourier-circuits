import UniformKernelSpectrumStorage
import UniformNatBlockMachine
import UniformNatHeaderFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterHeaders
open UniformMachine UniformNatBlockMachine
noncomputable section

lemma literal_reg(s:State)(d v q:ℕ):
 ((Op.literal d v).apply s).natReg q=if q=d then v else s.natReg q:=by
 by_cases h:q=d <;>simp [Op.apply,writeNat,next,h]
lemma binary_reg(s:State)(op:NatOp)(d a b q:ℕ):
 ((Op.binary op d a b).apply s).natReg q=
 if q=d then (evalNat op (s.natReg a) (s.natReg b)).getD 0 else s.natReg q:=by
 by_cases h:q=d <;>simp [Op.apply,writeNat,next,h]

/-- Compute loader arguments from the saved input geometry and charged slab
headers. Kernel mode supplies prepared data to every active role. -/
def common(W:ℕ):List Op:=[
 .literal 7390 0,.literal 7391 1,.literal 7392 2,.literal 7393 7,
 .literal 7394 6,.literal 7395 5,.literal 6300 W,
 .binary .add 6301 103 7390,.binary .add 6302 6026 7390,
 .binary .mul 7396 101 7392,.binary .add 6304 102 7393,
 .binary .add 6304 6304 7396,.binary .add 6304 6304 103,
 .binary .add 6305 7310 7390,.binary .sub 7312 6304 103,
 .binary .sub 7300 6026 103]
def tail(kernel:Bool):List Op:=if kernel then [.binary .add 6303 6304 7390]
 else [.binary .add 6303 6304 103,.binary .add 6303 6303 7391]
def roleArgs(W:ℕ)(kernel:Bool):List Op:=common W++tail kernel
lemma common_length(W:ℕ):(common W).length=16:=rfl
lemma roleArgs_length(W:ℕ)(kernel:Bool):(roleArgs W kernel).length=if kernel then 17 else 18:=by
 cases kernel <;>rfl

lemma append_apply(a b:List Op)(s:State):applyBlock (a++b) s=applyBlock b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>rfl
 | cons o a ih=>exact ih (o.apply s)

structure Args(c:UniformJointAllocation.Constants)(n W:ℕ)(kernel:Bool)(s:State):Prop where
 roles:s.natReg 6300=W
 volume:s.natReg 6301=UniformInitialPreparation.len n
 source:s.natReg 6302=2*UniformJointAllocation.slab c n
 input:s.natReg 6303=if kernel then UniformChirpKernelPreparation.kernelBase n
  else UniformInputPermutationPreparation.destination n
 kernel:s.natReg 6304=UniformChirpKernelPreparation.kernelBase n
 alpha:s.natReg 6305=UniformKernelSpectrumStorage.alphaBase c n
 padded:s.natReg 7312=UniformPaddedInputPreparation.dataBase n
 storage:s.natReg 7300=UniformKernelSpectrumStorage.base c n

lemma raw_roles(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6300=W:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg]
lemma raw_volume(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6301=s.natReg 103:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_source(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6302=s.natReg 6026:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_input(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6303=if kernel then s.natReg 102+7+s.natReg 101*2+s.natReg 103 else s.natReg 102+7+s.natReg 101*2+s.natReg 103+s.natReg 103+1:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_kernel(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6304=s.natReg 102+7+s.natReg 101*2+s.natReg 103:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_alpha(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 6305=s.natReg 7310:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_padded(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 7312=s.natReg 102+7+s.natReg 101*2:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]
lemma raw_storage(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natReg 7300=s.natReg 6026-s.natReg 103:=by
 cases kernel <;>simp [roleArgs,common,tail,applyBlock,literal_reg,binary_reg,evalNat]

theorem roleArgs_values(c:UniformJointAllocation.Constants)(n W:ℕ)(kernel:Bool)(s:State)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (source:s.natReg 6026=2*UniformJointAllocation.slab c n)
 (physical:s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n):
 Args c n W kernel (applyBlock (roleArgs W kernel) s):=by
 have width:=metadata.saved.workingLength
 have count:=metadata.saved.count
 have length:=metadata.saved.inputLength
 refine ⟨raw_roles W kernel s,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (raw_volume W kernel s).trans width
 · exact (raw_source W kernel s).trans source
 · rw [raw_input,width,count,length]
   cases kernel <;>simp [UniformChirpKernelPreparation.kernelBase,
    UniformInputPermutationPreparation.destination,UniformPaddedInputPreparation.dataBase,
    UniformNormalizationPreparation.normBase,Nat.add_assoc,Nat.mul_comm]
 · rw [raw_kernel,width,count,length]
   simp [UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,Nat.mul_comm]
 · exact (raw_alpha W kernel s).trans physical
 · rw [raw_padded,count,length]
   simp [UniformPaddedInputPreparation.dataBase,Nat.mul_comm]
 · rw [raw_storage,source,width]
   rfl

def Changed(q:ℕ):Prop:=(6300≤q∧q≤6305)∨q=7300∨q=7312∨(7390≤q∧q≤7396)
lemma roleArgs_frame(W:ℕ)(kernel:Bool)(s:State):
 (applyBlock (roleArgs W kernel) s).natHeap=s.natHeap∧
 (applyBlock (roleArgs W kernel) s).scalarHeap=s.scalarHeap∧
 (applyBlock (roleArgs W kernel) s).scalarReg=s.scalarReg∧
 (applyBlock (roleArgs W kernel) s).outputs=s.outputs∧
 (applyBlock (roleArgs W kernel) s).rootOrders=s.rootOrders∧
 (∀q,¬Changed q→(applyBlock (roleArgs W kernel) s).natReg q=s.natReg q):=by
 cases kernel <;>refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 all_goals
  intro q h;unfold Changed at h
  simp (disch:=omega) [roleArgs,common,tail,applyBlock,Op.apply,writeNat,next]

lemma roleArgs_safe(W:ℕ)(kernel:Bool)(s:State)(B:ℕ)
 (roles:W≤B)(source:s.natReg 6026≤B)(physical:s.natReg 7310≤B)
 (low:s.natReg 105+12*s.natReg 102+4*s.natReg 101+4*s.natReg 103+100≤B):
 readable (roleArgs W kernel) s∧peak (roleArgs W kernel) s≤B:=by
 cases kernel <;>
  simp [roleArgs,common,tail,readable,peak,Op.readable,Op.peak,literal_reg,binary_reg,evalNat]
 all_goals omega

def output:List Op:=[.literal 7390 0,.literal 7391 2,.literal 7392 7,
 .binary .add 8 101 7390,.binary .add 17 103 7390,.binary .add 25 102 7392,
 .binary .add 26 6025 7390,.binary .mul 7393 101 7391,
 .binary .add 27 25 7393,.binary .add 27 27 103,.binary .add 27 27 103]
lemma output_length:output.length=11:=rfl
lemma output_values{n:ℕ}(s:State)(metadata:UniformPermutationInversePreparation.Metadata n s):
 (applyBlock output s).natReg 8=n∧(applyBlock output s).natReg 17=UniformInitialPreparation.len n∧
 (applyBlock output s).natReg 25=UniformInitialPreparation.ell n+7∧
 (applyBlock output s).natReg 26=s.natReg 6025∧
 (applyBlock output s).natReg 27=UniformNormalizationPreparation.normBase n:=by
 simp [output,applyBlock,literal_reg,binary_reg,evalNat,metadata.saved.inputLength,
  metadata.saved.workingLength,metadata.saved.count,UniformNormalizationPreparation.normBase,
  UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,Nat.add_assoc,Nat.mul_comm]
def OutputChanged(q:ℕ):Prop:=q=8∨q=17∨q=25∨q=26∨q=27∨(7390≤q∧q≤7393)
lemma output_frame(s:State):
 (applyBlock output s).natHeap=s.natHeap∧(applyBlock output s).scalarHeap=s.scalarHeap∧
 (applyBlock output s).scalarReg=s.scalarReg∧(applyBlock output s).outputs=s.outputs∧
 (applyBlock output s).rootOrders=s.rootOrders∧
 (∀q,¬OutputChanged q→(applyBlock output s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q h;unfold OutputChanged at h
 apply UniformNatHeaderFrame.block_natReg
 simp [output,UniformNatHeaderFrame.keeps]
 omega
lemma output_safe(s:State)(B:ℕ)(source:s.natReg 6025≤B)
 (low:s.natReg 102+2*s.natReg 101+2*s.natReg 103+7≤B):
 readable output s∧peak output s≤B:=by
 simp[output,readable,peak,Op.readable,Op.peak,literal_reg,binary_reg,evalNat]
 omega

end
end ExactFourierCircuits.UniformFinalOuterHeaders
