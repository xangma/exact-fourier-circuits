import DFTModelCacheCalendarBodyCharges

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node body finish prepare result sequence

def localWorkBudget (r : ℕ) : ℕ :=
  4000*(r+1)^4+sequenceBudget r (r^2)+116*eventBudget r+29*r^2+500

def workBudget (r : ℕ) : ℕ := (2*r+1)*localWorkBudget r+9

theorem sequenceBudget_mono (r n m : ℕ) (hn:n ≤ m) : sequenceBudget r n ≤ sequenceBudget r m := by
  let U:=1000*(2*r+1)+17
  have h1:=Nat.mul_le_mul_right U hn
  have h2:=Nat.mul_le_mul_right 4 hn
  have h3:=Nat.mul_le_mul hn (Nat.add_le_add_right h1 26)
  change n*U+4*n+n*(n*U+26)+17 ≤ m*U+4*m+m*(m*U+26)+17
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add h1 (by simpa only [Nat.mul_comm] using h2)) h3) 17

theorem eventBudget_mono (v r : ℕ) (hv:v ≤ r) : eventBudget v ≤ eventBudget r := by
  have sq:=Nat.pow_le_pow_left hv 2
  unfold eventBudget
  omega

theorem expected_events_bound (v o t r : ℕ) (hv:v ≤ r) : (expected v o t).2.len ≤ eventBudget r := by
  change ((treeTimed t (sourceTree v o)).map eventEncode).length ≤ _
  rw [List.length_map]
  exact (source_events_bound v o t).trans (eventBudget_mono v r hv)

theorem finish_source_work (v o t r : ℕ) (hv:v ≤ r) :
    (run finish (((v,(o,t)),(selected v,ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode))),
      (expected (v/2) o t,expected (v-v/2) (o+v/2) t))).work ≤
      sequenceBudget r (r^2)+116*eventBudget r+29*r^2+150 := by
  have hs:=finish_work v o t (selected v) (currentRows (⟨v,o,0,0⟩:Task))
    (expected (v/2) o t) (expected (v-v/2) (o+v/2) t)
  have hw:=sequence_work
    (t+max (expected (v/2) o t).1 (expected (v-v/2) (o+v/2) t).1)
    (currentRows (⟨v,o,0,0⟩:Task)) r (by intro q hq;have :=currentRows_ab v o q hq;omega)
  have len:(currentRows (⟨v,o,0,0⟩:Task)).length ≤ r^2:=
    (DFTModelCacheTraversal.currentRows_bound _).trans (Nat.pow_le_pow_left hv 2)
  have sm:=sequenceBudget_mono r _ _ len
  have hl:=expected_events_bound (v/2) o t r (by omega)
  have hr:=expected_events_bound (v-v/2) (o+v/2) t r (by omega)
  omega

theorem result_work (fuel v o t r : ℕ) (hv:v<fuel) (hr:v ≤ r) :
    (result fuel v o t).work ≤ nodeWeight v*localWorkBudget r := by
  induction fuel generalizing v o t with
  | zero => omega
  | succ fuel ih =>
    have nd:=DFTModelCacheDescriptor.node_work v o
    have pw:(v+1)^4 ≤ (r+1)^4:=Nat.pow_le_pow_left (by omega) 4
    have nm:=Nat.mul_le_mul_left 4000 pw
    rw [result_succ]
    change (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).work+1 ≤ _
    by_cases hd:v<2 ∨ selected v=0
    · have hw:=body_direct_work (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) v o t hd
      have one: (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).work+1 ≤ localWorkBudget r := by
        unfold localWorkBudget;omega
      exact one.trans (by have :=Nat.mul_le_mul_right (localWorkBudget r) (nodeWeight_pos v);simpa using this)
    · have hlv:v/2<fuel:=by omega
      have hrv:v-v/2<fuel:=by omega
      have hl:=ih (v/2) o t hlv (by omega)
      have hrr:=ih (v-v/2) (o+v/2) t hrv (by omega)
      have hb:=body_split_work (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) v o t hd
      have hs:=finish_source_work v o t r hr
      simp only [currentRows,hd,ite_false] at hs
      change (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).work ≤
        (run DFTModelCacheDescriptor.node (v,o)).work+(result fuel (v/2) o t).work+
        (result fuel (v-v/2) (o+v/2) t).work+_+100 at hb
      rw [result_value fuel (v/2) o t hlv,result_value fuel (v-v/2) (o+v/2) t hrv] at hb
      have hw:(body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).work+1 ≤
          nodeWeight (v/2)*localWorkBudget r+nodeWeight (v-v/2)*localWorkBudget r+localWorkBudget r := by
        unfold localWorkBudget at *
        omega
      calc
        _ ≤ _:=hw
        _=(nodeWeight (v/2)+nodeWeight (v-v/2)+1)*localWorkBudget r:=by ring
        _=nodeWeight v*localWorkBudget r:=by rw [nodeWeight_split v (by omega)]

theorem program_work (v o t : ℕ) : (run program (v,(o,t))).work ≤ workBudget v := by
  have h:=result_work (v+1) v o t v (by omega) le_rfl
  have hw:nodeWeight v ≤ 2*v+1:=by unfold nodeWeight;split <;>omega
  have hm:=Nat.mul_le_mul_right (localWorkBudget v) hw
  rw [program_run]
  change (result (v+1) v o t).work+9 ≤ _
  unfold workBudget
  omega

end
end ExactFourierCircuits.DFTModelCacheCalendar
