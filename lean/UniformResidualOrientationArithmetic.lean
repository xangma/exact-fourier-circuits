import UniformResidualFibers
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualOrientationArithmetic
open scoped BigOperators
open BinaryFrames BinaryTensor
noncomputable section

def scannerWeight {n : ℕ} (v : Vec (Fin n)) : ℕ := ∑ j : Fin n, (v j).val

lemma scannerWeight_eq {n : ℕ} (v : Vec (Fin n)) : scannerWeight v=weight v := rfl
lemma scanner_mod_four {n : ℕ} (v : Vec (Fin n)) :
 scannerWeight v%4=(weightModFour v).val := by
 simp only [scannerWeight_eq,weightModFour,ZMod.val_natCast]
lemma scanner_cast {n : ℕ} (v : Vec (Fin n)) :
 ((scannerWeight v%4 : ℕ) : ZMod 4)=weightModFour v := by
 rw [scannerWeight_eq,ZMod.natCast_mod]
 rfl
lemma norm_one_scanner {n : ℕ} (v : Vec (Fin n)) (hv:dot v v=1) :
 scannerWeight v%4=1 ∨ scannerWeight v%4=3 :=
 norm_one_weight_mod_four v hv

lemma weight_one_of_scanner {n : ℕ} (v : Vec (Fin n))
 (hv:scannerWeight v%4=1) : weightModFour v=1 := by
 rw [← scanner_cast v,hv]
 rfl
lemma weight_three_of_scanner {n : ℕ} (v : Vec (Fin n))
 (hv:scannerWeight v%4=3) : weightModFour v=3 := by
 rw [← scanner_cast v,hv]
 rfl

def boolCode (b : Bool) : ℕ := if b then 1 else 0

lemma orientation_code {n : ℕ} (v : Vec (Fin n)) (hv:dot v v=1)
 (decreasing : Bool) :
 (boolCode decreasing+(if scannerWeight v%4=3 then 1 else 0))%2=
 boolCode (UniformResidualFibers.inverseOrientation v decreasing) := by
 rcases norm_one_scanner v hv with h | h
 · have orient:=UniformResidualFibers.inverseOrientation_weight_one v decreasing
    (weight_one_of_scanner v h)
   rw [orient,h]
   cases decreasing <;> norm_num [boolCode]
 · have orient:=UniformResidualFibers.inverseOrientation_weight_three v decreasing
    (weight_three_of_scanner v h)
   rw [orient,h]
   cases decreasing <;> norm_num [boolCode]

lemma orientation_is_one {n : ℕ} (v : Vec (Fin n)) (hv:dot v v=1)
 (decreasing : Bool) :
 ((boolCode decreasing+(if scannerWeight v%4=3 then 1 else 0))%2=1) ↔
 UniformResidualFibers.inverseOrientation v decreasing=true := by
 rw [orientation_code v hv decreasing]
 cases UniformResidualFibers.inverseOrientation v decreasing <;> simp [boolCode]

lemma orientation_code_of_matching_nat {n : ℕ} (v : Vec (Fin n))
 (hv:dot v v=1) (decreasing : Bool) (code : ℕ) (hc:code=boolCode decreasing) :
 (code+(if scannerWeight v%4=3 then 1 else 0))%2=
 boolCode (UniformResidualFibers.inverseOrientation v decreasing) := by
 rw [hc]
 exact orientation_code v hv decreasing
end
end ExactFourierCircuits.UniformResidualOrientationArithmetic
