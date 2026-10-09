import UniformAxisCacheRootDuration
import UniformAxisCacheSelectedPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheHorizonBounds
open UniformLocalCacheTiming UniformBalancedToeplitz UniformJointCacheExtent
open UniformJointCacheAllocation UniformAxisCacheAllocationMachine

/-- The ordinary allocator budget also bounds the full symmetric Fourier
horizon, including its five diagonal layers. -/
theorem horizon_fits (r N S:ℕ)(radix:2≤r):
 2*planDuration (plan r)+5≤wordBudget r N S:=by
 by_cases large:4≤r
 · have duration:=UniformAxisCacheTimingGeometry.duration_cap r
   have natEnd:=endNat_formula r N S
   have scalarEnd:=(axis_ends r N S).2
   dsimp only [scalarSize] at scalarEnd
   unfold wordBudget
   change 2*planDuration (plan r)+5≤20000*(2*r+1)+(axisBank r N S).endNat+(axisBank r N S).endScalar+100
   nlinarith only [duration,natEnd,scalarEnd,large,Nat.zero_le N,Nat.zero_le S,
    Nat.zero_le (capacity r),Nat.zero_le (r^2),Nat.zero_le (7*(2*r+2)*r^2)]
 · have upper:r≤3:=by omega
   interval_cases r
   · have selected:UniformWorkspacePlanner.selected 2=0:=by decide
     have duration:planDuration (plan 2)=30:=by
      simp [UniformBalancedToeplitz.plan,selected,planDuration,directDuration]
     rw [duration]
     unfold wordBudget
     change 65≤20000*(2*2+1)+(axisBank 2 N S).endNat+(axisBank 2 N S).endScalar+100
     omega
   · have selected:UniformWorkspacePlanner.selected 3=0:=by decide
     have duration:planDuration (plan 3)=87:=by
      simp [UniformBalancedToeplitz.plan,selected,planDuration,directDuration]
     rw [duration]
     unfold wordBudget
     change 179≤20000*(2*3+1)+(axisBank 3 N S).endNat+(axisBank 3 N S).endScalar+100
     omega

theorem selected_horizon_fits (c:UniformJointAllocation.Constants)(n:ℕ)(hn:0<n)
 (j:Fin (UniformAllAxisSeedPreparation.axisCount n)):
 2*planDuration (plan (UniformAllAxisSeedPreparation.radix n j))+5≤UniformJointAllocation.envelope c n:=
 (horizon_fits _ _ _ (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)).trans
  (selected_wordBudget c n hn j)

end ExactFourierCircuits.UniformAxisCacheHorizonBounds
