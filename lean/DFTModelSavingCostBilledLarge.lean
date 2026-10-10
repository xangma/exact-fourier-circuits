import DFTModelSavingCostLarge
import DFTModelSavingCostBilledSuffix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.large DFTModelCacheRecords.seed
  DFTModelSavingRecords.stream DFTModelSavingBinarySuffix.program UniformBatching.width seedAllowance

lemma join_native_large (work A streamWork suffixWork K prefixTicks streamTicks suffixTicks : ℕ)
    (actual : work≤A+48+streamWork+suffixWork)
    (stream : streamWork≤K*streamTicks+12) (suffix : suffixWork≤32*suffixTicks)
    (fixed : A+87≤K) (factor : 32≤K) (positive : 1≤prefixTicks) :
    work+27≤K*(prefixTicks+streamTicks+suffixTicks) := by
  have first:=Nat.mul_le_mul_left K positive
  have last:=Nat.mul_le_mul_right suffixTicks factor
  nlinarith only [actual,stream,suffix,fixed,first,last]

/-- Compare the real large branch with its real native prefix, chronological
stream and terminal durations. The +27 also pays body and closed-entry syntax.
The stream bound is supplied by the operational billed-record induction. -/
theorem large_native_billed_work (h : Handler ChildPort) (k K prefixTicks streamTicks : ℕ)
    (I : ℂ) (v : Tape Tagged.T) (even : 2*(v.len/2)=v.len)
    (len : v.len=UniformBatching.width*2^k)
    (stream : (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
      (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val,
        ((k,I),v)))).work≤K*streamTicks+12)
    (fixed : seedAllowance+87≤K) (factor : 32≤K) (positive : 1≤prefixTicks) :
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).work+27≤
      K*(prefixTicks+streamTicks+(4*(k/UniformFixedNetwork.m*UniformFixedNetwork.m)+
        UniformBatching.width*UniformBinarySpectatorCMachine.arrayCost k
          (k/UniformFixedNetwork.m*UniformFixedNetwork.m)+20)) := by
  have cap:=large_work_bound h k I v even
  have suffix:=suffix_native_billed UniformBatching.width
    (k/UniformFixedNetwork.m*UniformFixedNetwork.m) k I v
    (by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _)
    (Nat.div_mul_le_self _ _) even len
  have actual : (Code.run DFTModelSavingProgram.large h ((k,I),v)).work≤
      seedAllowance+48+
      (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
        (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val,((k,I),v)))).work+
      (run DFTModelSavingBinarySuffix.program
        (k/UniformFixedNetwork.m*UniformFixedNetwork.m,((k,I),v))).work := by
    rw [suffix_work _ k I v even]
    nlinarith only [cap]
  exact join_native_large _ seedAllowance _ _ K prefixTicks streamTicks _ actual stream suffix fixed factor positive

end
end ExactFourierCircuits.DFTModelSavingCost
