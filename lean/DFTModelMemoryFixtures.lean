import DFTModelMemoryAffinePointwise

set_option autoImplicit false

/-! Exact focused reductions of both compiled programs, including dirty tags and
zero coefficients. These fixtures do not claim the complete DFT translation. -/
namespace ExactFourierCircuits.DFTModelMemoryFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def dirty : Tape (ℕ × ℂ) := Tape.tab 3
  (fun j => if j = 0 then (1,2) else if j = 1 then (0,3) else (1,-4))

def coefficients : Tape ℂ := Tape.tab 3
  (fun j => if j = 0 then 0 else if j = 1 then 2 else Complex.I)

theorem pointwise_length :
    (run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.len = 3 := by rfl

theorem pointwise_work :
    (run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).work = 109 := by rfl

theorem pointwise_peak :
    (run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).peak = 3 := by rfl

theorem zero_product_retains_tag :
    ((run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 0 (0,0)).1 = 1 := by rfl

theorem zero_product_value :
    ((run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 0 (0,0)).2 = 0 := by
  change (0:ℂ)*2 = 0
  ring

theorem prepared_tag_retained :
    ((run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 1 (0,0)).1 = 0 := by rfl

theorem prepared_product_value :
    ((run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 1 (0,0)).2 = 6 := by
  change (2:ℂ)*3 = 6
  norm_num

theorem complex_product_value :
    ((run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 2 (0,0)).2 =
      -4*Complex.I := by
  change Complex.I*(-4) = -4*Complex.I
  ring

theorem pointwise_empty_work :
    (run DFTModelMemoryPointwise.program (0,(dirty,coefficients))).work = 4 := by rfl

theorem pointwise_empty_peak :
    (run DFTModelMemoryPointwise.program (0,(dirty,coefficients))).peak = 0 := by rfl

theorem pointwise_single_work :
    (run DFTModelMemoryPointwise.program (1,(dirty,coefficients))).work = 39 := by rfl

theorem pointwise_outside_default :
    (run DFTModelMemoryPointwise.program (3,(dirty,coefficients))).val.look 3 (7,8) = (7,8) := by rfl

theorem copy_length :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (3,dirty)).val.len = 3 := by rfl

theorem copy_work :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (3,dirty)).work = 37 := by rfl

theorem copy_peak :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (3,dirty)).peak = 3 := by rfl

theorem copy_tag :
    ((run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (3,dirty)).val.look 2 (0,0)).1 = 1 := by rfl

theorem copy_value :
    ((run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (3,dirty)).val.look 2 (0,0)).2 = -4 := by rfl

theorem copy_empty_work :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (0,dirty)).work = 4 := by rfl

theorem copy_empty_peak :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (0,dirty)).peak = 0 := by rfl

theorem copy_single_work :
    (run (DFTModelMemoryCopy.program DFTModelMemoryPointwise.Datum) (1,dirty)).work = 15 := by rfl

theorem prepared_copy_work :
    (run (DFTModelMemoryCopy.program sc) (3,coefficients)).work = 37 := by rfl

theorem prepared_copy_value :
    (run (DFTModelMemoryCopy.program sc) (3,coefficients)).val.look 2 0 = Complex.I := by rfl

def affineDirty : Tape DFTModelAffine.Tagged.T := Tape.tab 3
  (fun j => if j = 0 then (1,(2,3)) else if j = 1 then (0,(3,0)) else (1,(4,-4)))

theorem affine_length :
    (run DFTModelMemoryAffinePointwise.program (3,(affineDirty,coefficients))).val.len = 3 := by rfl

theorem affine_work :
    (run DFTModelMemoryAffinePointwise.program (3,(affineDirty,coefficients))).work = 151 := by rfl

theorem affine_peak :
    (run DFTModelMemoryAffinePointwise.program (3,(affineDirty,coefficients))).peak = 3 := by rfl

theorem affine_zero_tag :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 0 (0,(0,0))).1 = 1 := by rfl

theorem affine_zero_offset :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 0 (0,(0,0))).2.1 = 0 := by
  change (0:ℂ)*2 = 0
  ring

theorem affine_zero_homogeneous :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 0 (0,(0,0))).2.2 = 0 := by
  change (0:ℂ)*3 = 0
  ring

theorem affine_prepared_offset :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 1 (0,(0,0))).2.1 = 6 := by
  change (2:ℂ)*3 = 6
  norm_num

theorem affine_prepared_homogeneous :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 1 (0,(0,0))).2.2 = 0 := by
  change (2:ℂ)*0 = 0
  ring

theorem affine_prepared_tag :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 1 (0,(0,0))).1 = 0 := by rfl

theorem affine_cancellation :
    let z := (run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 2 (0,(0,0))
    z.2.1+z.2.2 = 0 := by
  change Complex.I*4+Complex.I*(-4) = 0
  ring

theorem affine_cancellation_tag :
    ((run DFTModelMemoryAffinePointwise.program
      (3,(affineDirty,coefficients))).val.look 2 (0,(0,0))).1 = 1 := by rfl

theorem affine_empty_work :
    (run DFTModelMemoryAffinePointwise.program (0,(affineDirty,coefficients))).work = 4 := by rfl

theorem affine_single_work :
    (run DFTModelMemoryAffinePointwise.program (1,(affineDirty,coefficients))).work = 53 := by rfl

theorem affine_copy_tag :
    ((run (DFTModelMemoryCopy.program DFTModelAffine.Tagged)
      (3,affineDirty)).val.look 2 (0,(0,0))).1 = 1 := by rfl

theorem affine_copy_offset :
    ((run (DFTModelMemoryCopy.program DFTModelAffine.Tagged)
      (3,affineDirty)).val.look 2 (0,(0,0))).2.1 = 4 := by rfl

theorem affine_copy_homogeneous :
    ((run (DFTModelMemoryCopy.program DFTModelAffine.Tagged)
      (3,affineDirty)).val.look 2 (0,(0,0))).2.2 = -4 := by rfl

end
end ExactFourierCircuits.DFTModelMemoryFixtures
