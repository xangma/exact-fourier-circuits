import DFTModelCacheMatchingFactorsProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] program scalar

/-- The pair tape contains an actually prepared coefficient and its conjugate. -/
def Paired (z : Tape (ℂ × ℂ)) : Prop :=
  ∀j,j<z.len→(z.look j (0,0)).2=starRingEnd ℂ (z.look j (0,0)).1

theorem scalar_at (r j : ℕ) (z : Tape (ℂ × ℂ)) (positive : 0<r) (limit : j<9*r)
    (paired : Paired z) (present : j%r/2<z.len) :
    (run scalar (pairArgs r z Complex.I ExactFourierCircuits.a⁻¹ j)).valid ∧
    (run scalar (pairArgs r z Complex.I ExactFourierCircuits.a⁻¹ j)).work≤200 ∧
    (run scalar (pairArgs r z Complex.I ExactFourierCircuits.a⁻¹ j)).peak≤9 := by
  let l : Fin 9:=⟨j/r,(Nat.div_lt_iff_lt_mul positive).mpr limit⟩
  let t : Fin 2:=⟨j%r%2,Nat.mod_lt _ (by decide)⟩
  let c:ℂ:=(z.look (j%r/2) (0,0)).1
  have pair:z.look (j%r/2) (0,0)=(c,starRingEnd ℂ c):=
    Prod.ext rfl (paired _ present)
  have eq:pairArgs r z Complex.I ExactFourierCircuits.a⁻¹ j=input l t c := by
    simp only [pairArgs,input,l,t]
    rw [pair]
  rw [eq]
  exact (scalar_correct l t c).2

theorem argumentPeak_bound (r j : ℕ) (z : Tape (ℂ × ℂ))
    (radix : 2≤r) (limit : j<9*r) (count : z.len≤r) : argumentPeak r z j≤9*r := by
  have div:j/r<9:=(Nat.div_lt_iff_lt_mul (by omega)).mpr limit
  have mod:j%r<r:=Nat.mod_lt _ (by omega)
  have row:j%r/2≤j%r:=Nat.div_le_self _ _
  simp only [argumentPeak,max_le_iff]
  omega

theorem packedCell_bounds (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ))
    (radix : 2≤r) (limit : j<9*r) (count : z.len≤r) (paired : Paired z) :
    (run packedCell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).valid ∧
    (run packedCell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).work≤274 ∧
    (run packedCell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).peak≤9*r := by
  have ap:=argumentPeak_bound r j z radix limit count
  by_cases h:j%r/2<z.len
  · have good:=scalar_at r j z (by omega) limit paired h
    simp only [packedCell_yes _ _ _ _ _ _ h,Bill.pay]
    exact ⟨good.1,by omega,max_le (good.2.2.trans (by omega)) ap⟩
  · simp only [packedCell_no _ _ _ _ _ _ h]
    exact ⟨trivial,by omega,(le_max_right (j/r) _).trans ap⟩

theorem destination_bounds (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ)
    (radix : 2≤r) (limit : j<9*r) (table : ∀a,a<r→p.look a 0<r) :
    (run destination (args r p z i ai,j)).peak≤9*r := by
  have div:j/r<9:=(Nat.div_lt_iff_lt_mul (by omega)).mpr limit
  have mod:j%r<r:=Nat.mod_lt _ (by omega)
  have dest:=table (j%r) mod
  have mul: j/r*r≤8*r:=Nat.mul_le_mul_right r (by omega)
  rw [destination_run]
  simp only [max_le_iff]
  omega

theorem cell_bounds (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ))
    (radix : 2≤r) (limit : j<9*r) (count : z.len≤r) (paired : Paired z)
    (table : ∀a,a<r→p.look a 0<r) :
    (run cell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).valid ∧
    (run cell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).work≤306 ∧
    (run cell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).peak≤9*r := by
  have pk:=packedCell_bounds r j p z radix limit count paired
  have dp:=destination_bounds r j p z Complex.I ExactFourierCircuits.a⁻¹ radix limit table
  rw [destination_run] at dp
  constructor
  · rw [cell_run]
    exact pk.1
  · constructor
    · rw [cell_run]
      change (run packedCell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).work+32≤306
      omega
    · rw [cell_run]
      exact max_le dp pk.2.2

/-- Work and Nat peak of the actual closed sow program, including all reads,
divisions, rational arithmetic, allocation and scatter writes. -/
theorem program_bounds (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ))
    (radix : 2≤r) (count : z.len≤r) (paired : Paired z)
    (table : ∀a,a<r→p.look a 0<r) :
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).valid ∧
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).work≤2781*r+13 ∧
    (run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).peak≤9*r := by
  have cells:=fun j hj=>cell_bounds r j p z radix hj count paired table
  refine ⟨?_,?_,?_⟩
  · rw [program_run]
    change (Bill.sow _ _ _ _).valid
    exact (DFTModelCRT.sow_valid _ _ _ _).mpr (fun j hj=>(cells j hj).1)
  · rw [program_run]
    change (Bill.sow _ _ _ _).work+11≤_
    rw [DFTModelCRT.sow_work]
    have sum:(∑j∈Finset.range (9*r),(run cell (args r p z Complex.I ExactFourierCircuits.a⁻¹,j)).work)≤306*(9*r) := by
      calc
        _≤∑_j∈Finset.range (9*r),306:=Finset.sum_le_sum (fun j hj=>(cells j (Finset.mem_range.mp hj)).2.1)
        _=306*(9*r):=by simp [Nat.mul_comm]
    omega
  · rw [program_run]
    change max (Bill.sow _ _ _ _).peak (max 9 (9*r))≤_
    rw [DFTModelCRT.sow_peak]
    refine max_le (max_le (le_refl _) (max_le (le_refl _) ?_)) (by omega)
    exact Finset.sup_le (fun j hj=>(cells j (Finset.mem_range.mp hj)).2.2)

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors
