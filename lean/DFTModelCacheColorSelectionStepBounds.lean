import DFTModelCacheColorSelectionValues
import DFTModelCacheHeightStepBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorSelection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheHeight (straight_work Words words_mono words_blank words_look degree literals degree_positive straight_words)
open DFTModelCacheColor (Row)
noncomputable section

theorem step_valid (x:Input.T) (q j:ℕ) (s:State.T) : (run step ((x,q),(j,s))).valid :=
 DFTModelCacheTraversal.indexCode_valid step (by decide) () _
theorem step_work (x:Input.T) (q j:ℕ) (s:State.T) : (run step ((x,q),(j,s))).work ≤ 1000 :=
 (straight_work step (by decide) () _).trans (by decide)
theorem count_work (x:Input.T) : (run count x).work ≤ 100 :=
 (straight_work count (by decide) () x).trans (by decide)
theorem count_valid (x:Input.T) : (run count x).valid :=
 DFTModelCacheTraversal.indexCode_valid count (by decide) () x
end
end ExactFourierCircuits.DFTModelCacheColorSelection
