import DFTModelCacheRectangleCallerCorrect
import DFTModelCacheBudgetAbsorptionHeightColor

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleBudget
noncomputable section

/-- Genuine master-root extraction is kept separate from local geometry. -/
def rootWork (D : ℕ) : ℕ :=
  160*(Nat.log2 (D+1)+1)+400*(UniformPowerMachine.loopCost (D/4)+1)

def localCoefficient : ℕ := 3000000000000000000000000

theorem log2_mono {a b : ℕ} (h : a≤b) : Nat.log2 a≤Nat.log2 b := by
  by_cases ha:a=0
  · subst a; simp
  · exact (Nat.le_log2 (by omega : b≠0)).2 ((Nat.log2_self_le ha).trans h)

theorem spectrum_budget (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (width:p.N≤8*r) (split:p.split≤r) :
    DFTModelCacheSpectrumConjugate.workBudget r D p≤
      1000000*(r+1)^2+160*(Nat.log2 (D+1)+1) := by
  have rootR:=log2_mono (show D/r+1≤D+1 by have:=Nat.div_le_self D r; omega)
  have rootN:=log2_mono (show D/p.N+1≤D+1 by have:=Nat.div_le_self D p.N; omega)
  have product:=Nat.mul_le_mul width (show 52*p.split+300≤52*r+300 by omega)
  have square:=Nat.pow_le_pow_left (show p.N+1≤8*r+1 by omega) 2
  unfold DFTModelCacheSpectrumConjugate.workBudget
  nlinarith only [rootR,rootN,product,square,Nat.zero_le r,Nat.zero_le (r^2)]

theorem local_budget (r D : ℕ) (p : UniformChunkMatchingPreparation.Parameters)
    (kernel : UniformRankKernelMachine.Parameters) (M h : ℕ)
    (radix:p.radix≤r) (count:M≤r) (height:h≤8*r)
    (K:p.height.K≤8*r) (dims:p.height.a+p.height.e≤r)
    (width:kernel.N≤8*r) (split:kernel.split≤r) :
    28*h+35+DFTModelCacheSelectedPhysicalRowsCaller.mixedWorkBudget
      p r D kernel M+291≤localCoefficient*(r+1)^8+rootWork D := by
  have spectra:=spectrum_budget r D kernel width split
  have mapper:=DFTModelCacheSelectedPhysicalRows.workBudget_polynomial p.radix M
  have mSquare:=Nat.pow_le_pow_left (show p.radix+M+1≤2*r+1 by omega) 2
  have rSquare:=Nat.pow_le_pow_left (show p.radix+1≤r+1 by omega) 2
  have hc:=DFTModelCacheBudgetAbsorption.height_color_radix p.height.a p.height.e r dims
  have logK:Nat.log2 (p.height.K+1)≤8*r+1 := (Nat.log2_le_self _).trans (by omega)
  have s2:(r+1)^2≤(r+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have s1:r+1≤(r+1)^8 := le_self_pow (by omega) (by decide)
  have one:1≤(r+1)^8 := Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  unfold DFTModelCacheSelectedPhysicalRowsCaller.mixedWorkBudget
    DFTModelCacheSelectedPhysicalRowsProduced.mixedWorkBudget
    DFTModelCacheMatchingProduced.mixedWorkBudget localCoefficient rootWork
  nlinarith only [spectra,mapper,mSquare,rSquare,hc,logK,s2,s1,one,radix,count,height]

/-- Binary powering of the master root is logarithmic, including its zero case. -/
theorem root_work_log (D : ℕ) : rootWork D≤5000*(Nat.log2 (D+1)+1) := by
  have power:=UniformPowerMachine.totalCost_log_bound (D/4)
  have log:=log2_mono (show D/4+1≤D+1 by have:=Nat.div_le_self D 4; omega)
  unfold rootWork
  omega

end
end ExactFourierCircuits.DFTModelCacheRectangleBudget
