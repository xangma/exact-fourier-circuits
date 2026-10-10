import DFTModelCacheBudgetAbsorption
import DFTModelCacheHeightColorCallerCorrect
import DFTModelCacheTopologyPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBudgetAbsorption
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformWorkingLength
noncomputable section

theorem topology_size (a e : ℕ) :
 (DFTModelCacheHeightRaw.dag a e).size≤512*(a+e+1)^2 := by
 let K:=DFTModelCacheTopology.exponent a e
 let N:=UniformRadixTwoDAG.width K
 have hn:0<N:=UniformRadixTwoDAG.width_pos K
 have hk:K≤N:=UniformRadixTwoDAG.width_ge_height K
 have ha:a≤N:=(DFTModelCacheTopology.dimensions_fit a e).1
 have he:e≤N:=(DFTModelCacheTopology.dimensions_fit a e).2
 have hc:(DFTModelCacheHeightRaw.dag a e).size=DFTModelCacheTopology.C K a :=
  DFTModelCacheTopology.typed_count K a e ha he
 have count:DFTModelCacheTopology.C K a≤32*N^2 := by
  have product:=Nat.mul_le_mul_right N hk
  have square:N≤N*N := by nlinarith
  unfold DFTModelCacheTopology.C
  rw [DFTModelCacheTopology.G_formula]
  change 6*(3*K*N+2*N)+2*a≤32*N^2
  nlinarith
 have width:N≤4*(a+e+1) := by
  have h:=DFTModelCacheTopology.localWidth_bound a e
  change N≤4*(a+e)+1 at h
  omega
 have square:=Nat.pow_le_pow_left width 2
 rw [mul_pow] at square
 rw [hc]
 nlinarith

private theorem budget_arithmetic (s g e : ℕ) (pos:1≤ s)
 (hg:g≤512*s^2) (he:e≤ s) :
 DFTModelCacheDAGDepth.workBudget e g+57*g+
 DFTModelCacheBucket.workBudget g+29+1200*(2*g+1)^2+25+
 50002000*(e+1+g+2*g+1)^3+47≤1000000000000000000000000*s^8 := by
 unfold DFTModelCacheDAGDepth.workBudget DFTModelCacheBucket.workBudget
   DFTModelCacheBucket.selectBudget
 have s2:s≤ s^2:=le_self_pow (by omega) (by decide)
 have s4:s^2≤ s^4:=Nat.pow_le_pow_right (by omega) (by decide)
 have s6:s^6≤ s^8:=Nat.pow_le_pow_right (by omega) (by decide)
 have s8:s^4≤ s^8:=Nat.pow_le_pow_right (by omega) (by decide)
 have g2:=Nat.pow_le_pow_left hg 2
 have g3:=Nat.pow_le_pow_left hg 3
 have g4:=Nat.pow_le_pow_left hg 4
 have eg:=Nat.mul_le_mul he hg
 have eg2:=Nat.mul_le_mul he g2
 have eg3:=Nat.mul_le_mul he g3
 have e2:=Nat.pow_le_pow_left he 2
 have e3:=Nat.pow_le_pow_left he 3
 have e2g:=Nat.mul_le_mul e2 hg
 have s1:s≤ s^8:=le_self_pow (by omega) (by decide)
 have s3:s^3≤ s^8:=Nat.pow_le_pow_right (by omega) (by decide)
 have s5:s^5≤ s^8:=Nat.pow_le_pow_right (by omega) (by decide)
 have s7:s^7≤ s^8:=Nat.pow_le_pow_right (by omega) (by decide)
 have one:1≤ s^8:=Nat.succ_le_of_lt (Nat.pow_pos (by omega))
 rw [mul_pow] at g2 g3 g4
 ring_nf at *
 nlinarith

/-- The actual local caller budget, with its topology/height/color producers,
is polynomial solely in the genuine raw rectangle dimensions. -/
theorem height_color_polynomial (a e : ℕ) :
 DFTModelCacheHeightColorCaller.workBudget a e≤
 2000000000000000000000000*(a+e+1)^8 := by
 have top:=(DFTModelCacheTopology.polynomial_budgets a e).1
 have hlocal:=DFTModelCacheHeightRaw.localWorkBudget_polynomial a e
 have count:(DFTModelCacheHeightRaw.dag a e).size=DFTModelCacheBucketRaw.count a e :=
  DFTModelCacheTopology.typed_count _ _ _
   (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
 have budget:=budget_arithmetic (a+e+1) (DFTModelCacheHeightRaw.dag a e).size e
  (by omega) (topology_size a e) (by omega)
 unfold DFTModelCacheHeightColorCaller.workBudget DFTModelCacheHeightColorCaller.localBound
 unfold DFTModelCacheBucketRaw.workBudget at hlocal
 simp only [←count] at hlocal
 change DFTModelCacheHeightRaw.localWorkBudget a e+
  50002000*(e+1+(DFTModelCacheHeightRaw.dag a e).size+
   2*(DFTModelCacheHeightRaw.dag a e).size+1)^3+47≤_
 omega

/-- Ordinary rectangle-fit geometry discharges the local radix budget. -/
theorem height_color_radix (a e r : ℕ) (fit:a+e≤r) :
 DFTModelCacheHeightColorCaller.workBudget a e≤
 2000000000000000000000000*(r+1)^8 :=
 (height_color_polynomial a e).trans (Nat.mul_le_mul_left _
  (Nat.pow_le_pow_left (by omega) 8))

/-- Applied to the actual closed raw producer, without an initialized tape,
native execution, output, or cost premise. Height is ordinary request geometry. -/
theorem height_color_actual (c a e A C P d r : ℕ) (enabled : Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6) (fit:a+e≤r) :
 (run DFTModelCacheHeightColorCaller.program
   (DFTModelCacheHeightColorCaller.input c a e A C P d enabled)).valid ∧
 (run DFTModelCacheHeightColorCaller.program
   (DFTModelCacheHeightColorCaller.input c a e A C P d enabled)).work≤
 2000000000000000000000000*(r+1)^8 := by
 obtain ⟨_,_,_,valid,work,_⟩:=DFTModelCacheHeightColorCaller.specification
  c a e A C P d (A+DFTModelCacheHeightColorCaller.localBound a e) enabled height le_rfl
 exact ⟨valid,work.trans (height_color_radix a e r fit)⟩

theorem selected_height_color_sum {n : ℕ} (hn:0<n)
 (a e:Fin (axisCount n+1)→ℕ)
 (fit:∀i,a i+e i≤UniformSelectedCRT.radices n i) :
 (∑i,DFTModelCacheHeightColorCaller.workBudget (a i) (e i))≤
 (2000000000000000000000000*selectedFactor 8)*workingLength n := by
 calc
  _≤∑i,2000000000000000000000000*(UniformSelectedCRT.radices n i+1)^8 :=
   Finset.sum_le_sum (fun i _=>height_color_radix _ _ _ (fit i))
  _=2000000000000000000000000*
   (∑i,(UniformSelectedCRT.radices n i+1)^8) := by rw [Finset.mul_sum]
  _≤2000000000000000000000000*(selectedFactor 8*workingLength n) :=
   Nat.mul_le_mul_left _ (selected_sum hn 8)
  _=_ := by ring

end
end ExactFourierCircuits.DFTModelCacheBudgetAbsorption
