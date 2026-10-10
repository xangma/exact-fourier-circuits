import DFTModelGlobalSectorPreparationAxisBounds
import DFTModelGlobalSectorPreparationLocalCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

theorem sumPeak_le (k i H : ℕ) (ws : Tape ℕ) (positions:i+k≤H)
 (values:sumValue k i ws≤H) : sumPeak k i ws≤H := by
 induction k generalizing i with
 | zero=>simp [sumPeak]
 | succ k ih=>
   have hv:sumValue k (i+1) ws≤H:=by simp only [sumValue] at values;omega
   have ht:=ih (i+1) (by omega) hv
   simp only [sumPeak]
   omega

theorem list_get_le_sum (xs : List ℕ) (j : Fin xs.length) : xs.get j≤xs.sum := by
 induction xs with
 | nil=>exact Fin.elim0 j
 | cons x xs ih=>
   refine Fin.cases ?_ (fun i=>?_) j
   · simp
   · have h:=ih i
     simp only [List.get_eq_getElem,List.sum_cons]
     exact le_trans h (by omega)

theorem sum_take_le (xs : List ℕ) (j : ℕ) : (xs.take j).sum≤xs.sum := by
 have h:=congrArg List.sum (List.take_append_drop j xs)
 rw [List.sum_append] at h
 omega

theorem native_blocks_bound (a : UniformSectorPacking.Axis) : a.widths.length≤a.widths.sum :=
 List.length_le_sum_of_one_le a.widths (by
   intro w hw
   rcases a.widths_one_two w hw with h|h <;> omega)

theorem blockCell_peak (a : UniformSectorPacking.Axis) (j : Fin a.widths.length) :
 (run blockCell (encodeAxis a,j.val)).peak≤a.widths.sum+1 := by
 have hb:=native_blocks_bound a
 have hj:=j.isLt
 have hw:=list_get_le_sum a.widths j
 have hs:sumValue j.val 0 (ofList a.widths)≤a.widths.sum := by
   rw [sumValue_take a.widths j.val hj.le]
   exact sum_take_le _ _
 have hp:=sumPeak_le j.val 0 a.widths.sum (ofList a.widths) (by omega) hs
 have look:(ofList a.widths).look j.val 0=a.widths.get j:=by simp [ofList,Tape.look,hj]
 rw [blockCell_run]
 change max 1 (max ((ofList a.widths).look j.val 0-1)
   (max j.val (sumPeak j.val 0 (ofList a.widths))))≤_
 rw [look]
 omega

theorem digitCell_peak (x : Axis.T) (j : ℕ) :
 (run digitCell (x,j)).peak≤ max x.2.1.len j := by
 rw [digitCell_run,findProgram_run]
 simp only [Bill.pass,Bill.pay]
 rw [digitFinish_run]
 have hp:=find_depth_peak x.2.1.len 0 j x.2.1
 dsimp only [Bill.peak] at *
 omega

attribute [local irreducible] blockCell digitCell blockProgram digitProgram

theorem prepareAxis_peak (a : UniformSectorPacking.Axis) :
 (run prepareAxis (encodeAxis a)).peak≤a.widths.sum+1 := by
 have hb:(run blockProgram (encodeAxis a)).peak≤a.widths.sum+1 := by
   rw [blockProgram_run]
   change max (Bill.tab a.widths.length Block.blank
     (fun j=>run blockCell (encodeAxis a,j))).peak a.widths.length≤_
   rw [ModelEquivalenceInterpreter.tab_peak]
   apply max_le (max_le ?_ ?_) ?_
   · exact le_trans (native_blocks_bound a) (Nat.le_succ _)
   · apply Finset.sup_le
     intro j hj
     exact blockCell_peak a ⟨j,Finset.mem_range.mp hj⟩
   · exact le_trans (native_blocks_bound a) (Nat.le_succ _)
 have hd:(run digitProgram (encodeAxis a)).peak≤a.widths.sum+1 := by
   rw [digitProgram_run]
   change max (Bill.tab a.widths.sum Digit.blank
     (fun j=>run digitCell (encodeAxis a,j))).peak 0≤_
   rw [ModelEquivalenceInterpreter.tab_peak]
   apply max_le (max_le (by omega) ?_) (by omega)
   apply Finset.sup_le
   intro j hj
   have hp:=digitCell_peak (encodeAxis a) j
   have hj:=Finset.mem_range.mp hj
   have hw:=native_blocks_bound a
   change (run digitCell (encodeAxis a,j)).peak≤_
   change (run digitCell (encodeAxis a,j)).peak≤ max a.widths.length j at hp
   omega
 change max 0 (max (max (run blockProgram (encodeAxis a)).peak
   (max (run digitProgram (encodeAxis a)).peak 0)) 0)≤_
 omega

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
