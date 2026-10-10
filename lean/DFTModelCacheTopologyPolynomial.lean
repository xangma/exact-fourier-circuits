import DFTModelCacheTopologyClosed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section

private theorem numeric_budget (h t c k M : ℕ) (positive:1≤M)
    (hh:h≤M) (ht:t≤M) (hc:c≤M) (hk:k≤M) :
    210000+204*h+t*(35*(600+h)+1731)+5120*c+28*k+36≤1000000*M^2 ∧
    2*h+t+20000≤20003*M := by
  have product:=Nat.mul_le_mul ht hh
  have square:M≤M*M := by nlinarith
  constructor <;> nlinarith

private theorem width_bounds (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K) :
    H K a e≤2000026*(UniformRadixTwoDAG.width K)^4 ∧
    T K a≤2000*(UniformRadixTwoDAG.width K)^3 ∧
    C K a≤32*(UniformRadixTwoDAG.width K)^2 := by
  let N:=UniformRadixTwoDAG.width K
  have hn:0<N:=UniformRadixTwoDAG.width_pos K
  have hk:K≤N:=UniformRadixTwoDAG.width_ge_height K
  have n2:N≤N^2 :=le_self_pow (by omega) (by decide)
  have n4:N^2≤N^4 :=by nlinarith [sq_nonneg N]
  have one4:1≤N^4 :=Nat.succ_le_iff.mpr (pow_pos hn 4)
  have g:G K≤5*N^2 :=by
    rw [G_formula]
    change 3*K*N+2*N≤5*N^2
    have product:=Nat.mul_le_mul_right N hk
    nlinarith
  have b:B K a e≤D K+2000000*N^4 :=by
    simpa only [B,Nat.zero_add] using
      UniformToeplitzCrossTopologyMachine.budget_width K a e 0 (D K) ha he
  refine ⟨?_,UniformToeplitzCrossTopologyMachine.runtime_width K a ha,?_⟩
  · unfold H D at *;nlinarith
  · unfold C;nlinarith

private theorem ambient_bounds (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K) :
    let M:=2000026*(UniformRadixTwoDAG.width K+1)^4
    1≤M ∧ H K a e≤M ∧ T K a≤M ∧ C K a≤M ∧ K≤M := by
  let N:=UniformRadixTwoDAG.width K
  have hn:0<N:=UniformRadixTwoDAG.width_pos K
  have hk:K≤N:=UniformRadixTwoDAG.width_ge_height K
  have n2:N≤N^2 :=le_self_pow (by omega) (by decide)
  have n4:N^2≤N^4 :=by nlinarith [sq_nonneg N]
  have n3:N^3≤N^4 :=by nlinarith [Nat.mul_le_mul_left (N^2) (show 1≤N by omega)]
  have one4:1≤N^4 :=Nat.succ_le_iff.mpr (pow_pos hn 4)
  have bounds:=width_bounds K a e ha he
  have nn:N^4≤(N+1)^4:=Nat.pow_le_pow_left (Nat.le_succ N) 4
  change 1≤2000026*(N+1)^4 ∧ _
  refine ⟨by nlinarith,bounds.1.trans (Nat.mul_le_mul_left _ nn),?_,?_,?_⟩
  · have t:=bounds.2.1;nlinarith
  · have c:=bounds.2.2;nlinarith
  · nlinarith

private theorem fourth_square_product (A B x : ℕ) :
    A*(B*x^4)^2=(A*B^2)*x^8 := by
  rw [mul_pow,←pow_mul,Nat.mul_assoc]

private theorem width_polynomial (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K) :
    bodyWork K a e+28*K+36≤5000000000000000000*(UniformRadixTwoDAG.width K+1)^8 ∧
    bodyPeak K a e≤50000000000*(UniformRadixTwoDAG.width K+1)^4 := by
  let N:=UniformRadixTwoDAG.width K
  let M:=2000026*(N+1)^4
  obtain ⟨positive,h,t,c,k⟩:=ambient_bounds K a e ha he
  have numeric:=numeric_budget (H K a e) (T K a) (C K a) K M positive h t c k
  constructor
  · change 210000+204*H K a e+T K a*(35*(600+H K a e)+1731)+5120*C K a+28*K+36≤_
    calc
      _≤1000000*M^2:=numeric.1
      _=(1000000*2000026^2)*(N+1)^8 :=fourth_square_product _ _ _
      _≤_:=Nat.mul_le_mul_right _ (by decide)
  · change 2*H K a e+T K a+20000≤_
    calc
      _≤20003*M:=numeric.2
      _=(20003*2000026)*(N+1)^4 :=by dsimp only [M];rw [Nat.mul_assoc]
      _≤_:=Nat.mul_le_mul_right _ (by decide)

/-- Local polynomial envelopes; allocation uses the actual native B+1. -/
theorem polynomial_budgets (a e : ℕ) :
    workBudget a e≤1000000000000000000000000*(a+e+1)^8 ∧
    peakBudget a e≤100000000000000*(a+e+1)^4 := by
  let N:=localWidth a e
  have bounds:=width_polynomial (exponent a e) a e (dimensions_fit a e).1 (dimensions_fit a e).2
  have width:N+1≤4*(a+e+1) :=by have h:=localWidth_bound a e;change N≤_ at h;omega
  have eighth:=Nat.pow_le_pow_left width 8
  have fourth:=Nat.pow_le_pow_left width 4
  constructor
  · calc
      _≤5000000000000000000*(N+1)^8:=bounds.1
      _≤5000000000000000000*(4*(a+e+1))^8:=Nat.mul_le_mul_left _ eighth
      _=(5000000000000000000*4^8)*(a+e+1)^8 :=by rw [mul_pow,Nat.mul_assoc]
      _≤_:=Nat.mul_le_mul_right _ (by decide)
  · calc
      _≤50000000000*(N+1)^4:=bounds.2
      _≤50000000000*(4*(a+e+1))^4:=Nat.mul_le_mul_left _ fourth
      _=(50000000000*4^4)*(a+e+1)^4 :=by rw [mul_pow,Nat.mul_assoc]
      _≤_:=Nat.mul_le_mul_right _ (by decide)

/-- Public validity, actual native provenance and local polynomial charges. -/
theorem closed (a e : ℕ) : ∃u ticks,Result a e u ticks ∧
    (RAM.run program (a,e)).valid ∧
    (RAM.run program (a,e)).work≤1000000000000000000000000*(a+e+1)^8 ∧
    (RAM.run program (a,e)).peak≤100000000000000*(a+e+1)^4 := by
  obtain ⟨u,t,result,budget⟩:=execution a e
  have poly:=polynomial_budgets a e
  exact ⟨u,t,result,budget.1,budget.2.1.trans poly.1,budget.2.2.trans poly.2⟩

end
end ExactFourierCircuits.DFTModelCacheTopology
