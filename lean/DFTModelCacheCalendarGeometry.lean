import DFTModelCacheCalendarCorrect
import DFTModelCacheCalendarSequenceBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section

def nodeWeight (v : ℕ) : ℕ := if v=0 then 1 else 2*v-1
def eventBudget (r : ℕ) : ℕ := r^2+2*r+1
def localDurationBudget (r : ℕ) : ℕ := 15*(r+1)^2+r^2*(100000*(2*r+1))
def durationBudget (r : ℕ) : ℕ := (2*r+1)*localDurationBudget r

theorem nodeWeight_pos (v : ℕ) : 1≤nodeWeight v := by unfold nodeWeight;split <;>omega

theorem nodeWeight_split (v : ℕ) (hv:2≤v) : nodeWeight (v/2)+nodeWeight (v-v/2)+1=nodeWeight v := by
  have hl:0<v/2:=by omega
  have hr:0<v-v/2:=by omega
  simp only [nodeWeight,ite_eq_right (by omega:v/2≠0),ite_eq_right (by omega:v-v/2≠0),ite_eq_right (by omega:v≠0)]
  omega

theorem rows_ab (v o b : ℕ) (q : Row) (hq:q∈rows v o b) : q.a+q.e≤2*v := by
  simp only [rows,List.mem_flatMap,List.mem_range,List.mem_map] at hq
  obtain ⟨i,_,j,_,rfl⟩:=hq
  simp only [row]
  omega

theorem currentRows_ab (v o : ℕ) (q : Row) (hq:q∈currentRows (⟨v,o,0,0⟩:Task)) : q.a+q.e≤2*v := by
  unfold currentRows at hq
  split at hq
  · simp at hq
  · exact rows_ab v o _ q hq

theorem timed_length (T : Tree) (t : ℕ) : (treeTimed t T).length≤T.nodeCount+T.rectangles.length := by
  induction T generalizing t with
  | direct v o => simp [treeTimed,Tree.nodeCount,Tree.rectangles]
  | split v o b L R hl hr =>
    have hL:=hl t
    have hR:=hr t
    simp only [treeTimed,List.length_append,sequenceRows_length,Tree.nodeCount,Tree.rectangles]
    omega

theorem source_events_bound (v o t : ℕ) : (treeTimed t (sourceTree v o)).length≤eventBudget v := by
  have h:=timed_length (sourceTree v o) t
  have hr:=ofPlan_rectangles_length (UniformBalancedToeplitz.plan v) o
  by_cases hv:v=0
  · subst v
    rw [sourceTree_eq,ite_eq_left (by omega)]
    simp [eventBudget,treeTimed]
  · have hn:=ofPlan_nodeCount_tight (UniformBalancedToeplitz.plan v) o (by omega)
    change (sourceTree v o).rectangles.length≤v^2 at hr
    change (sourceTree v o).nodeCount≤2*v-1 at hn
    unfold eventBudget
    omega

theorem currentRows_duration (v o r : ℕ) (hv:v≤r) :
    rectanglesDuration (currentRows (⟨v,o,0,0⟩:Task))≤r^2*(100000*(2*r+1)) := by
  have len:=DFTModelCacheTraversal.currentRows_bound (⟨v,o,0,0⟩:Task)
  have sq: v^2≤r^2:=Nat.pow_le_pow_left hv 2
  have h:=duration_list_bound (currentRows (⟨v,o,0,0⟩:Task)) (100000*(2*r+1)) (by
    intro q hq
    exact (rectangleDuration_bound q).trans (Nat.mul_le_mul_left _ (by have :=currentRows_ab v o q hq;omega)))
  exact h.trans (Nat.mul_le_mul_right _ (len.trans sq))

theorem source_duration_weight (v o r : ℕ) (hv:v≤r) :
    treeDuration (sourceTree v o)≤nodeWeight v*localDurationBudget r := by
  induction v using Nat.strong_induction_on generalizing o with
  | h v ih =>
    rw [sourceTree_eq]
    split
    · change directDuration v≤_
      have sq:(v+1)^2≤(r+1)^2:=Nat.pow_le_pow_left (by omega) 2
      have direct:directDuration v≤15*(r+1)^2:=by unfold directDuration;nlinarith [Nat.sub_le v 1]
      have wt:=nodeWeight_pos v
      have mul:=Nat.mul_le_mul_right (localDurationBudget r) wt
      simp only [Nat.one_mul] at mul
      exact direct.trans ((by unfold localDurationBudget;omega :15*(r+1)^2≤localDurationBudget r).trans mul)
    · rename_i hd
      have hl:=ih (v/2) (by omega) o (by omega)
      have hr:=ih (v-v/2) (by omega) (o+v/2) (by omega)
      have sum:=currentRows_duration v o r hv
      simp only [currentRows,hd,ite_false] at sum
      have cor:rectanglesDuration (rows v o (selected v))≤localDurationBudget r:=by
        unfold localDurationBudget;omega
      change max (treeDuration (sourceTree (v/2) o)) (treeDuration (sourceTree (v-v/2) (o+v/2)))+
        rectanglesDuration (rows v o (selected v))≤_
      calc
        _≤nodeWeight (v/2)*localDurationBudget r+nodeWeight (v-v/2)*localDurationBudget r+localDurationBudget r := by omega
        _=(nodeWeight (v/2)+nodeWeight (v-v/2)+1)*localDurationBudget r := by ring
        _=nodeWeight v*localDurationBudget r := by rw [nodeWeight_split v (by omega)]

theorem source_duration_bound (v o r : ℕ) (hv:v≤r) :
    treeDuration (sourceTree v o)≤durationBudget r := by
  have hn:nodeWeight v≤2*r+1:=by unfold nodeWeight;split <;>omega
  exact (source_duration_weight v o r hv).trans (Nat.mul_le_mul_right _ hn)

end
end ExactFourierCircuits.DFTModelCacheCalendar
