import DFTModelAdmissibilityControl
import DFTModelCacheRecords
import UniformMachineRuns

set_option autoImplicit false

/-! Operational pairing for finite segments of the actual saving RAM program.
Record tapes represent only their original cells, including when adjacent
source heap cells are populated. -/
namespace ExactFourierCircuits.DFTModelSavingNativeControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

theorem boundedRuns_match {p : Program} {n B ticks : ℕ} {x y : Fin n → ℂ}
    {s z u : State} (actual : BoundedRuns p n x B s ticks u) (same : StateMatch s z) :
    ∃uz,BoundedRuns p n y B z ticks uz ∧ StateMatch u uz := by
  induction actual generalizing z with
  | refl bound=>exact ⟨z,.refl (same.wordBound bound),same⟩
  | next bound step tail ih=>
    obtain ⟨mid,midRun,midSame⟩:=step_match same step
    obtain ⟨uz,rest,last⟩:=ih midSame
    exact ⟨uz,.next (same.wordBound bound) midRun rest,last⟩

theorem runs_deterministic {p : Program} {n ticks : ℕ} {x : Fin n → ℂ}
    {s u v : State} (left : Runs p n x s ticks u) (right : Runs p n x s ticks v) : u=v := by
  induction left generalizing v with
  | refl s=>cases right;rfl
  | next first tail ih=>
    cases right with
    | next other rest=>
      have eq:=(StepResult.running.inj (first.symm.trans other))
      subst eq
      exact ih rest

theorem paired_runs {p : Program} {n B ticks : ℕ} {x y : Fin n → ℂ}
    {s z u uz : State} (actual : BoundedRuns p n x B s ticks u)
    (baseline : BoundedRuns p n y B z ticks uz) (same : StateMatch s z) : StateMatch u uz := by
  obtain ⟨u0,run0,last⟩:=boundedRuns_match (y:=y) actual same
  have eq:=runs_deterministic run0.runs baseline.runs
  subst u0
  exact last

theorem dataTape_lookup (vs : List ℕ) (j : ℕ) (live : j<vs.length) :
    (DFTModelCacheRecords.dataTape vs).look j 0=vs[j] := by
  rw [Tape.look_of_lt _ _ live]
  simp [DFTModelCacheRecords.dataTape,Tape.tab,List.getElem?_eq_getElem live]

theorem printed_dataTape {T : ℕ} {vs : List ℕ} {s : State}
    (printed : UniformFixedNetworkScheduleMachine.Printed T vs s) :
    ∀j,j<vs.length → ∀z,s.natHeap (T+j)=some z →
      (DFTModelCacheRecords.dataTape vs).look j 0=z := by
  intro j live z present
  have equal:=Option.some.inj ((printed j live).symm.trans present)
  rw [dataTape_lookup vs j live,equal]

theorem recordTape_lookup (rs : List UniformFixedNetworkScheduleMachine.Record)
    (j : ℕ) (live : j<rs.length) :
    (DFTModelCacheRecords.recordTape rs).look j (Tape.empty ℕ)=
      DFTModelCacheRecords.dataTape rs[j].data := by
  rw [Tape.look_of_lt _ _ live]
  simp [DFTModelCacheRecords.recordTape,Tape.tab,List.getElem?_eq_getElem live]

end
end ExactFourierCircuits.DFTModelSavingNativeControl
