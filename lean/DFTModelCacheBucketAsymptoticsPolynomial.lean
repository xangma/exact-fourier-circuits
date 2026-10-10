import DFTModelCacheBucketRaw
import DFTModelCacheTopologyPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucketAsymptotics
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section

/-- The actual topology count, including all generated convolution gates. -/
theorem count_polynomial (a e : ℕ) :
    DFTModelCacheBucketRaw.count a e  ≤  512*(a+e+1)^2  :=  by
  let K := DFTModelCacheTopology.exponent a e
  let N := UniformRadixTwoDAG.width K
  have hn:0<N := UniformRadixTwoDAG.width_pos K
  have hk:K ≤ N := UniformRadixTwoDAG.width_ge_height K
  have ha:a ≤ N := (DFTModelCacheTopology.dimensions_fit a e).1
  have n2:N ≤ N^2 := le_self_pow (by omega) (by decide)
  have g:DFTModelCacheTopology.G K ≤ 5*N^2  :=  by
    rw [DFTModelCacheTopology.G_formula]
    change 3*K*N+2*N ≤ 5*N^2
    have product := Nat.mul_le_mul_right N hk
    nlinarith
  have c:DFTModelCacheBucketRaw.count a e ≤ 32*N^2  :=  by
    change 6*DFTModelCacheTopology.G K+2*a ≤ 32*N^2
    nlinarith
  have nw:N ≤ 4*(a+e+1) := by
    have h := DFTModelCacheTopology.localWidth_bound a e
    change N ≤ _ at h
    omega
  calc
    _ ≤ 32*N^2 := c
    _ ≤ 32*(4*(a+e+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left nw 2)
    _=512*(a+e+1)^2 := by ring

/-- The dense stable bucket printer has a quartic, not cubic, count bound. -/
theorem bucket_work_polynomial (G : ℕ) :
    DFTModelCacheBucket.workBudget G  ≤  1000*(G+1)^4  :=  by
  unfold DFTModelCacheBucket.workBudget DFTModelCacheBucket.selectBudget
  nlinarith only [Nat.zero_le (G^4),Nat.zero_le (G^3),Nat.zero_le (G^2),Nat.zero_le G]

theorem bucket_peak_polynomial (N G : ℕ) :
    DFTModelCacheBucket.selectPeak N G  ≤  N+3*(G+1)^2  :=  by
  unfold DFTModelCacheBucket.selectPeak
  nlinarith

private theorem depth_work (e G s : ℕ) (hs:1 ≤ s) (he:e ≤ s) (hg:G ≤ 512*s^2) :
    DFTModelCacheDAGDepth.workBudget e G  ≤  100000000*s^4  :=  by
  have s2:s ≤ s^2 := le_self_pow (by omega) (by decide)
  have sz:1 ≤ s^2 := by nlinarith
  have size:e+1+G ≤ 514*s^2 := by omega
  unfold DFTModelCacheDAGDepth.workBudget
  calc
    _ ≤ 5*(514*s^2)+19+(512*s^2)*(35*(514*s^2)+91) := by gcongr
    _ ≤ 100000000*s^4 := by nlinarith [sq_nonneg (s^2)]

/-- Closed topology, depth and stable bucket bills from the actual raw producer. -/
theorem polynomial_budgets (a e : ℕ) :
    DFTModelCacheBucketRaw.workBudget a e  ≤  10000000000000000000000000*(a+e+1)^8 ∧
    DFTModelCacheBucketRaw.peakBudget a e  ≤  1000000000000000*(a+e+1)^4  :=  by
  let s := a+e+1
  have hs:1 ≤ s := by dsimp only [s];omega
  have h2:1 ≤ s^2 := Nat.one_le_pow _ _ hs
  have h4:s^2 ≤ s^4 := Nat.pow_le_pow_right hs (by decide)
  have h8:s^4 ≤ s^8 := Nat.pow_le_pow_right hs (by decide)
  have top := DFTModelCacheTopology.polynomial_budgets a e
  have count := count_polynomial a e
  change DFTModelCacheBucketRaw.count a e ≤ 512*s^2 at count
  have count1:DFTModelCacheBucketRaw.count a e+1 ≤ 513*s^2 := by omega
  have dep := depth_work e (DFTModelCacheBucketRaw.count a e) s hs (by dsimp only [s];omega) count
  have buc := bucket_work_polynomial (DFTModelCacheBucketRaw.count a e)
  have bp:DFTModelCacheBucket.workBudget (DFTModelCacheBucketRaw.count a e) ≤
      1000*513^4*s^8  :=  by
    calc
      _ ≤ 1000*(DFTModelCacheBucketRaw.count a e+1)^4 := buc
      _ ≤ 1000*(513*s^2)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left count1 4)
      _=1000*513^4*s^8 := by ring
  have scalarPeak := bucket_peak_polynomial e (DFTModelCacheBucketRaw.count a e)
  have pk:DFTModelCacheBucket.selectPeak e (DFTModelCacheBucketRaw.count a e) ≤
      s+3*513^2*s^4  :=  by
    calc
      _ ≤ e+3*(DFTModelCacheBucketRaw.count a e+1)^2 := scalarPeak
      _ ≤ s+3*(513*s^2)^2 := by gcongr;dsimp only [s];omega
      _=s+3*513^2*s^4 := by ring
  have s4:s ≤ s^4 := le_self_pow (by omega) (by decide)
  have one4:1 ≤ s^4 := Nat.one_le_pow _ _ hs
  have one8:1 ≤ s^8 := (Nat.one_le_pow _ _ hs)
  constructor
  · change DFTModelCacheTopology.workBudget a e+_+_+_+29 ≤ 10000000000000000000000000*s^8
    have ht := top.1
    change DFTModelCacheTopology.workBudget a e ≤ 1000000000000000000000000*s^8 at ht
    nlinarith
  · change max (DFTModelCacheTopology.peakBudget a e)
      (max (e+5*DFTModelCacheBucketRaw.count a e+5)
        (DFTModelCacheBucket.selectPeak e (DFTModelCacheBucketRaw.count a e))) ≤ 1000000000000000*s^4
    apply max_le
    · exact top.2.trans (Nat.mul_le_mul_right _ (by decide))
    · apply max_le
      · change e+5*DFTModelCacheBucketRaw.count a e+5 ≤ _
        have he:e ≤ s := by dsimp only [s];omega
        nlinarith
      · nlinarith

/-- Actual closed Code validity, native provenance and polynomial charges. -/
theorem execution (a e : ℕ) : ∃u ticks,
    DFTModelCacheTopology.Result a e u ticks ∧
    (run DFTModelCacheBucketRaw.program (a,e)).valid ∧
    (run DFTModelCacheBucketRaw.program (a,e)).work ≤ 10000000000000000000000000*(a+e+1)^8 ∧
    (run DFTModelCacheBucketRaw.program (a,e)).peak ≤ 1000000000000000*(a+e+1)^4  :=  by
  obtain ⟨u,t,source,budget⟩ := DFTModelCacheBucketRaw.execution a e
  have bounds := polynomial_budgets a e
  exact ⟨u,t,source,budget.1,budget.2.1.trans bounds.1,budget.2.2.trans bounds.2⟩

end
end ExactFourierCircuits.DFTModelCacheBucketAsymptotics
