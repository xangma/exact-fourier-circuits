import DFTModelCacheCalendarBodyPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode comp_peak fork_peak)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node result direct prepare finish sequence correction

def peakBudget (r : ℕ) : ℕ :=
  4000*(r+1)^2+durationBudget r+(r^2+1)*(100000*(2*r+1))+4*eventBudget r+
  15*(r+1)^2+r+50

theorem peakBudget_linear (r : ℕ) : r+15 ≤ peakBudget r := by unfold peakBudget;omega

theorem finish_source_peak (v o t R : ℕ) (hv:v ≤ R) :
    (run finish (((v,(o,t)),(selected v,ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode))),
      (expected (v/2) o t,expected (v-v/2) (o+v/2) t))).peak ≤ t+peakBudget R := by
  let L:=currentRows (⟨v,o,0,0⟩:Task)
  let l:=expected (v/2) o t
  let r:=expected (v-v/2) (o+v/2) t
  have len:L.length ≤ R^2:=
    (DFTModelCacheTraversal.currentRows_bound _).trans (Nat.pow_le_pow_left hv 2)
  have ha:∀q∈L,q.a+q.e ≤ 2*R:=by intro q hq;have :=currentRows_ab v o q hq;omega
  have lc:l.1 ≤ durationBudget R:=source_duration_bound (v/2) o R (by omega)
  have rc:r.1 ≤ durationBudget R:=source_duration_bound (v-v/2) (o+v/2) R (by omega)
  have le:l.2.len ≤ eventBudget R:=expected_events_bound (v/2) o t R (by omega)
  have re:r.2.len ≤ eventBudget R:=expected_events_bound (v-v/2) (o+v/2) t R (by omega)
  have cd:rectanglesDuration L ≤ R^2*(100000*(2*R+1)):=currentRows_duration v o R hv
  have cp:=correction_peak v o t (selected v) R L l r ha
  have fd:=finishedDuration_peak ((v,(o,t)),(selected v,ofList (L.map rectangleEncode))) l r
    (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode))
  have fe:=finishedEvents_peak
    ((((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))
  change (run finishedEvents
    ((((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))).peak ≤
      l.2.len+r.2.len+((sequenceRows (t+max l.1 r.1) L).map eventEncode).length at fe
  rw [List.length_map,sequenceRows_length] at fe
  change (run finish (((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r))).peak ≤ _
  rw [finish,comp_peak,fork_peak,fork_peak]
  have arg:(run (.fork (.atom .id) correction)
    (((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r))).val=
    ((((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode))):=by
    change (_, (run correction _).val)=_
    rw [correction_value]
    rfl
  rw [arg]
  change max (max 0 (run correction _).peak) (max (run finishedDuration _).peak (run finishedEvents _).peak) ≤ _
  have lm:=Nat.mul_le_mul_right (100000*(2*R+1)) (Nat.add_le_add_right len 1)
  have child:=max_le lc rc
  have corCap:=Nat.add_le_add (Nat.add_le_add_left child t) lm
  have corB:=cp.trans corCap
  have corFinal:(run correction (((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r))).peak ≤ t+peakBudget R :=
    corB.trans (by unfold peakBudget;omega)
  change (run finishedDuration
    ((((v,(o,t)),(selected v,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))).peak ≤
      max 1 (max l.1 r.1+rectanglesDuration L) at fd
  have durationCap:=Nat.add_le_add child cd
  have durationBound:max 1 (max l.1 r.1+rectanglesDuration L) ≤ t+peakBudget R:=by
    apply max_le
    · change (1:ℕ) ≤ t+peakBudget R
      have :=peakBudget_linear R
      omega
    · apply durationCap.trans
      have lift:=Nat.mul_le_mul_right (100000*(2*R+1)) (Nat.le_succ (R^2))
      change R^2*(100000*(2*R+1)) ≤ (R^2+1)*(100000*(2*R+1)) at lift
      change durationBudget R+R^2*(100000*(2*R+1)) ≤ t+peakBudget R
      unfold peakBudget
      omega
  have durationFinal:=fd.trans durationBound
  have countCap:=Nat.add_le_add (Nat.add_le_add le re) len
  have eventBound:eventBudget R+eventBudget R+R^2 ≤ t+peakBudget R:=by unfold peakBudget eventBudget;omega
  have eventsFinal:=fe.trans (countCap.trans eventBound)
  exact max_le (max_le (Nat.zero_le _) corFinal) (max_le durationFinal eventsFinal)

 theorem result_peak (fuel v o t R E : ℕ) (hv:v<fuel) (hr:v ≤ R) (he:o+v ≤ E) (hf:fuel ≤ R+1) :
    (result fuel v o t).peak ≤ E+t+peakBudget R := by
  induction fuel generalizing v o t with
  | zero => omega
  | succ fuel ih =>
    have hb:2 ≤ E+t+peakBudget R:=by have :=peakBudget_linear R;omega
    have ds:=direct_peak v o t
    have sq:(v+1)^2 ≤ (R+1)^2:=Nat.pow_le_pow_left (by omega) 2
    have dm:=Nat.mul_le_mul_left 15 sq
    have dd:(run direct (v,(o,t))).peak ≤ E+t+peakBudget R:=by unfold peakBudget;omega
    have np:=DFTModelCacheDescriptor.node_peak v o
    have nm:=Nat.mul_le_mul_left 4000 sq
    have nn:(run DFTModelCacheDescriptor.node (v,o)).peak ≤ E+t+peakBudget R:=by unfold peakBudget;omega
    rw [result_succ]
    change max (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).peak (fuel+1) ≤ _
    refine max_le ?_ (by have :=peakBudget_linear R;omega)
    rw [body,code_comp_peak]
    change max (max (run prepare (v,(o,t))).peak 0) _ ≤ _
    rw [prepare_peak,code_import_value,prepare_value]
    refine max_le (max_le nn (by omega)) ?_
    apply branch_peak _ v o t _ _ _ hb dd
    intro hd
    have hlv:v/2<fuel:=by omega
    have hrv:v-v/2<fuel:=by omega
    have hl:=ih (v/2) o t hlv (by omega) (by omega) (by omega)
    have rr:=ih (v-v/2) (o+v/2) t hrv (by omega) (by omega) (by omega)
    apply splitCode_peak _ _ _ hb (by change o+v ≤ E+t+peakBudget R;omega) hl rr
    have fs:=finish_source_peak v o t R hr
    rw [result_value fuel (v/2) o t hlv,result_value fuel (v-v/2) (o+v/2) t hrv]
    simp only [currentRows,hd,ite_false] at *
    exact fs.trans (by omega)

/-- The largest integer created is polynomial in the raw radix, plus the supplied offset/start. -/
theorem program_peak (v o t : ℕ) : (run program (v,(o,t))).peak ≤ o+v+t+peakBudget v := by
  have hp:=result_peak (v+1) v o t v (o+v) (by omega) le_rfl le_rfl le_rfl
  rw [program_run]
  change max (result (v+1) v o t).peak (v+1) ≤ _
  exact max_le hp (by have :=peakBudget_linear v;omega)

/-- Closed timestamp preparation from integers alone, with all construction work charged. -/
theorem specification (v o t : ℕ) :
    (run program (v,(o,t))).val=
      (treeDuration (ofPlan (UniformBalancedToeplitz.plan v) o),
        ofList ((treeTimed t (ofPlan (UniformBalancedToeplitz.plan v) o)).map eventEncode)) ∧
    (run program (v,(o,t))).valid ∧
    (run program (v,(o,t))).work ≤ workBudget v ∧
    (run program (v,(o,t))).peak ≤ o+v+t+peakBudget v :=
  ⟨program_value v o t,program_valid v o t,program_work v o t,program_peak v o t⟩

end
end ExactFourierCircuits.DFTModelCacheCalendar
