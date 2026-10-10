import DFTModelCacheCalendarSequence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming
open DFTModelCacheTraversal (ofList rectangleEncode)
open scoped BigOperators
noncomputable section
attribute [local irreducible] prefixProgram eventCell Bill.tab sequenceTotal eventTable

def sequenceBudget (r n : ℕ) : ℕ :=
  n*(1000*(2*r+1)+17)+4*n+n*(n*(1000*(2*r+1)+17)+26)+17

theorem sequenceCount_run (t : ℕ) (L : List Row) :
    run sequenceCount (t,ofList (L.map rectangleEncode))=⟨L.length,3,L.length,True⟩ := by
  simp [sequenceCount,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,ofList]

theorem eventTable_run (t : ℕ) (L : List Row) :
    run eventTable (t,ofList (L.map rectangleEncode))=
      (Bill.tab L.length Event9.blank (fun j=>run eventCell ((t,ofList (L.map rectangleEncode)),j))).pay 4 L.length := by
  rw [eventTable]
  change ((run sequenceCount (t,ofList (L.map rectangleEncode))).pass (fun n=>
    Bill.tab n Event9.blank (fun j=>run eventCell ((t,ofList (L.map rectangleEncode)),j)))).pay 1 0=_
  rw [sequenceCount_run]
  simp only [Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;>omega

theorem eventTable_work (t : ℕ) (L : List Row) (r : ℕ)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run eventTable (t,ofList (L.map rectangleEncode))).work≤
      6+4*L.length+L.length*(L.length*(1000*(2*r+1)+17)+26) := by
  rw [eventTable_run]
  change (Bill.tab L.length Event9.blank (fun j=>run eventCell ((t,ofList (L.map rectangleEncode)),j))).work+4≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hb:(∑j∈Finset.range L.length,(run eventCell ((t,ofList (L.map rectangleEncode)),j)).work)≤
      L.length*(L.length*(1000*(2*r+1)+17)+26) := by
    calc
      _≤∑_j∈Finset.range L.length,(L.length*(1000*(2*r+1)+17)+26) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj:=Finset.mem_range.mp hj
        rw [eventCell_run t L j hj]
        have hw:=prefix_work L r j (by omega) h
        have hm:=Nat.mul_le_mul_right (1000*(2*r+1)+17) (show j≤L.length by omega)
        dsimp only [Bill.work]
        omega
      _=_ := by simp [Nat.mul_comm]
  omega

theorem sequence_work (t : ℕ) (L : List Row) (r : ℕ)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run sequence (t,ofList (L.map rectangleEncode))).work ≤ sequenceBudget r L.length := by
  rw [sequence,DFTModelCacheTraversal.fork_work,sequenceTotal_run]
  have hw:=prefix_work L r L.length le_rfl h
  have ht:=eventTable_work t L r h
  dsimp only [Bill.pay]
  unfold sequenceBudget
  omega

theorem eventCell_peak (t : ℕ) (L : List Row) (r j : ℕ) (hj:j<L.length)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run eventCell ((t,ofList (L.map rectangleEncode)),j)).peak≤t+(L.length+1)*(100000*(2*r+1)) := by
  have pp:=prefix_peak L r j (by omega) h
  have pv:=prefix_value L j (by omega)
  have db:∀q∈L,rectangleDuration q≤100000*(2*r+1) := by
    intro q hq
    exact (rectangleDuration_bound q).trans (Nat.mul_le_mul_left _ (by have :=h q hq;omega))
  have sum:=duration_prefix_bound L (100000*(2*r+1)) j db
  have jm:=Nat.mul_le_mul_right (100000*(2*r+1)) (show j≤L.length+1 by omega)
  rw [eventCell_run t L j hj,pv]
  dsimp only [Bill.peak]
  exact max_le (max_le (by omega) (by omega)) (by nlinarith)

theorem eventTable_peak (t : ℕ) (L : List Row) (r : ℕ)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run eventTable (t,ofList (L.map rectangleEncode))).peak≤t+(L.length+1)*(100000*(2*r+1)) := by
  rw [eventTable_run]
  change max (Bill.tab L.length Event9.blank
    (fun j=>run eventCell ((t,ofList (L.map rectangleEncode)),j))).peak L.length≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le ?_ ?_) ?_
  · nlinarith
  · apply Finset.sup_le
    intro j hj
    exact eventCell_peak t L r j (Finset.mem_range.mp hj) h
  · nlinarith

theorem sequence_peak (t : ℕ) (L : List Row) (r : ℕ)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run sequence (t,ofList (L.map rectangleEncode))).peak≤t+(L.length+1)*(100000*(2*r+1)) := by
  rw [sequence,DFTModelCacheTraversal.fork_peak,sequenceTotal_run]
  have hp:=prefix_peak L r L.length le_rfl h
  apply max_le
  · dsimp only [Bill.pay]
    exact max_le (by nlinarith) (by nlinarith)
  · exact eventTable_peak t L r h

end
end ExactFourierCircuits.DFTModelCacheCalendar
