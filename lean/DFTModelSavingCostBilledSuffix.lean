import DFTModelSavingCostSuffix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
attribute [local irreducible] DFTModelSavingBinarySuffix.program

/-- Every bank with the genuine physical length is charged identically,
including arbitrary intermediate dependency flags. Compare directly to the
actual terminal source duration, not to a recursive source budget. -/
theorem suffix_native_billed (R b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (roles : 0<R) (cap : b≤k) (even : 2*(v.len/2)=v.len) (len : v.len=R*2^k) :
    (run DFTModelSavingBinarySuffix.program (b,((k,I),v))).work≤
      32*(4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+20) := by
  let zero : Fin R→Fin (2^k)→Scalar:=fun _ _=>Scalar.zero
  have bill:=DFTModelSavingBinarySuffix.program_native_work zero zero b cap roles
  rw [DFTModelSavingBinarySuffix.program_work zero zero b cap] at bill
  rw [suffix_work b k I v even,len]
  have larger : 32*(4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+9)≤
      32*(4*b+R*UniformBinarySpectatorCMachine.arrayCost k b+20) := by omega
  exact bill.trans larger

end
end ExactFourierCircuits.DFTModelSavingCost
