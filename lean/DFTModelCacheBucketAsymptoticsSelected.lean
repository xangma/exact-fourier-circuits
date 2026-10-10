import DFTModelCacheBucketAsymptoticsPolynomial
import DFTModelCacheAsymptotics

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucketAsymptotics
open OAI.PowerSaving OAI.PowerSaving.RAM
open Filter Asymptotics
open scoped BigOperators
noncomputable section

abbrev Axes (n : ℕ) := Fin (UniformAllAxisSeedPreparation.axisCount n)

/-- Actual bills of the closed raw topology/depth/bucket producer. -/
def familyWork (clients : ∀n,Axes n→ℕ)
    (a e : ∀n j,Fin (clients n j)→ℕ) (n : ℕ) : ℕ :=
  ∑j:Axes n,∑i:Fin (clients n j),(run DFTModelCacheBucketRaw.program (a n j i,e n j i)).work

theorem actual_work (a e : ℕ) :
    (run DFTModelCacheBucketRaw.program (a,e)).work ≤ 10000000000000000000000000*(a+e+1)^8 := by
  obtain ⟨_,_,_,_,work,_⟩:=execution a e
  exact work

theorem selected_extent (n : ℕ) (hn:0<n) (j:Axes n) (a e:ℕ)
    (ha:a ≤ UniformAllAxisSeedPreparation.radix n j)
    (he:e ≤ UniformAllAxisSeedPreparation.radix n j) :
    a+e+1 ≤ 257*(DFTModelCacheAsymptotics.scale n)^2 := by
  have h:=DFTModelCacheAsymptotics.selected_radix_bound hn j
  have one:1 ≤ (DFTModelCacheAsymptotics.scale n)^2 :=
    Nat.one_le_pow _ _ (DFTModelCacheAsymptotics.scale_pos n)
  omega

/-- Local peak and actual work are polynomial in the genuine selected-axis scale. -/
theorem selected_execution (n : ℕ) (hn:0<n) (j:Axes n) (a e:ℕ)
    (ha:a ≤ UniformAllAxisSeedPreparation.radix n j)
    (he:e ≤ UniformAllAxisSeedPreparation.radix n j) : ∃u ticks,
    DFTModelCacheTopology.Result a e u ticks ∧
    (run DFTModelCacheBucketRaw.program (a,e)).valid ∧
    (run DFTModelCacheBucketRaw.program (a,e)).work ≤
      (10000000000000000000000000*257^8)*(DFTModelCacheAsymptotics.scale n)^16 ∧
    (run DFTModelCacheBucketRaw.program (a,e)).peak ≤
      (1000000000000000*257^4)*(DFTModelCacheAsymptotics.scale n)^8 := by
  obtain ⟨u,t,source,valid,work,peak⟩:=execution a e
  have extent:=selected_extent n hn j a e ha he
  refine ⟨u,t,source,valid,?_,?_⟩
  · calc
      _ ≤ 10000000000000000000000000*(a+e+1)^8:=work
      _ ≤ 10000000000000000000000000*(257*(DFTModelCacheAsymptotics.scale n)^2)^8:=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left extent 8)
      _=(10000000000000000000000000*257^8)*(DFTModelCacheAsymptotics.scale n)^16:=by ring
  · calc
      _ ≤ 1000000000000000*(a+e+1)^4:=peak
      _ ≤ 1000000000000000*(257*(DFTModelCacheAsymptotics.scale n)^2)^4:=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left extent 4)
      _=(1000000000000000*257^4)*(DFTModelCacheAsymptotics.scale n)^8:=by ring

/-- The client count is explicit. This is not a bound on an unassembled cache. -/
theorem family_work_bound (c d : ℕ) (clients : ∀n,Axes n→ℕ)
    (a e : ∀n j,Fin (clients n j)→ℕ) (n : ℕ) (hn:0<n)
    (count:∀j,clients n j ≤ c*(DFTModelCacheAsymptotics.scale n)^d)
    (extents:∀j i,a n j i ≤ UniformAllAxisSeedPreparation.radix n j ∧
      e n j i ≤ UniformAllAxisSeedPreparation.radix n j) :
    familyWork clients a e n ≤
      (10000000000000000000000000*257^8*c)*(DFTModelCacheAsymptotics.scale n)^(d+17) := by
  let s:=DFTModelCacheAsymptotics.scale n
  let C:=10000000000000000000000000*257^8
  have each (j:Axes n) :
      (∑i:Fin (clients n j),(run DFTModelCacheBucketRaw.program (a n j i,e n j i)).work)
        ≤ (C*c)*s^(d+16) := by
    calc
      _ ≤ ∑_i:Fin (clients n j),C*s^16:=by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨_,_,_,_,work,_⟩:=selected_execution n hn j (a n j i) (e n j i)
          (extents j i).1 (extents j i).2
        exact work
      _=clients n j*(C*s^16):=by simp
      _ ≤ (c*s^d)*(C*s^16):=Nat.mul_le_mul_right _ (count j)
      _=(C*c)*s^(d+16):=by rw [pow_add];ring
  have axes:UniformAllAxisSeedPreparation.axisCount n ≤ s:=by
    change UniformWorkingLength.axisCount n+1 ≤ s
    dsimp only [s,DFTModelCacheAsymptotics.scale]
    omega
  calc
    _ ≤ ∑_j:Axes n,(C*c)*s^(d+16):=Finset.sum_le_sum (fun j _=>each j)
    _=UniformAllAxisSeedPreparation.axisCount n*((C*c)*s^(d+16)):=by simp
    _ ≤ s*((C*c)*s^(d+16)):=Nat.mul_le_mul_right _ axes
    _=(10000000000000000000000000*257^8*c)*s^(d+17):=by
      change s*((C*c)*s^(d+16))=(C*c)*s^((d+16)+1)
      rw [pow_succ];ring

/-- Arbitrary real clients obeying the stated polynomial count have sublinear
aggregate actual Code work, including topology generation and dense tables. -/
theorem family_work_isLittleO_input (c d : ℕ) (clients : ∀n,Axes n→ℕ)
    (a e : ∀n j,Fin (clients n j)→ℕ)
    (count:∀n,0<n→∀j,clients n j ≤ c*(DFTModelCacheAsymptotics.scale n)^d)
    (extents:∀n,0<n→∀j i,a n j i ≤ UniformAllAxisSeedPreparation.radix n j ∧
      e n j i ≤ UniformAllAxisSeedPreparation.radix n j) :
    (fun n=>(familyWork clients a e n:ℝ)) =o[atTop] fun n=>(n:ℝ) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans_isLittleO
    (DFTModelCacheAsymptotics.monomial_isLittleO_input
      (10000000000000000000000000*257^8*c) (d+17))
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast family_work_bound c d clients a e n (by omega) (count n (by omega))
    (extents n (by omega))

/-- Polynomially many clients in each actual radix are a concrete sufficient
count condition, including every selected axis. -/
theorem radix_clients_isLittleO_input (c d : ℕ) (clients : ∀n,Axes n→ℕ)
    (a e : ∀n j,Fin (clients n j)→ℕ)
    (count:∀n,0<n→∀j,clients n j ≤ c*(UniformAllAxisSeedPreparation.radix n j+1)^d)
    (extents:∀n,0<n→∀j i,a n j i ≤ UniformAllAxisSeedPreparation.radix n j ∧
      e n j i ≤ UniformAllAxisSeedPreparation.radix n j) :
    (fun n=>(familyWork clients a e n:ℝ)) =o[atTop] fun n=>(n:ℝ) := by
  apply family_work_isLittleO_input (c*129^d) (2*d) clients a e _ extents
  intro n hn j
  have r:=DFTModelCacheAsymptotics.selected_radix_bound hn j
  have one:1 ≤ (DFTModelCacheAsymptotics.scale n)^2:=
    Nat.one_le_pow _ _ (DFTModelCacheAsymptotics.scale_pos n)
  calc
    _ ≤ c*(UniformAllAxisSeedPreparation.radix n j+1)^d:=count n hn j
    _ ≤ c*(129*(DFTModelCacheAsymptotics.scale n)^2)^d:=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
    _=(c*129^d)*(DFTModelCacheAsymptotics.scale n)^(2*d):=by
      rw [mul_pow,←pow_mul,Nat.mul_assoc]

end
end ExactFourierCircuits.DFTModelCacheBucketAsymptotics
