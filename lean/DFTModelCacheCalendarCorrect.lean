import DFTModelCacheCalendarValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section
attribute [local irreducible] direct body finish prepare

theorem result_succ (fuel v o t : ℕ) : result (fuel+1) v o t=
    (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).pay 1 (fuel+1) := rfl

attribute [local irreducible] result

theorem result_value (fuel v o t : ℕ) (hv:v<fuel) : (result fuel v o t).val=expected v o t := by
  induction fuel generalizing v o t with
  | zero => omega
  | succ fuel ih =>
    rw [result_succ]
    change (body.run (fun x : Input.T=>result fuel x.1 x.2.1 x.2.2) (v,(o,t))).val=_
    by_cases hd:v<2 ∨ selected v=0
    · rw [body_direct _ v o t hd,direct_value,expected_direct v o t hd]
    · have hl:v/2<fuel:=by omega
      have hr:v-v/2<fuel:=by omega
      rw [body_split _ v o t hd]
      change (run finish (((v,(o,t)),(selected v,ofList ((rows v o (selected v)).map rectangleEncode))),
        ((result fuel (v/2) o t).val,(result fuel (v-v/2) (o+v/2) t).val))).val=_
      rw [ih _ _ _ hl,ih _ _ _ hr,finish_value]
      exact (expected_split v o t hd).symm

theorem header_run (v o t : ℕ) : run header (v,(o,t))=⟨(v+1,(v,(o,t))),7,v+1,True⟩ := by
  simp [header,nat,width,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem program_run (v o t : ℕ) : run program (v,(o,t))=(result (v+1) v o t).pay 9 (v+1) := by
  rw [program]
  unfold result
  change ((run header (v,(o,t))).pass (fun z=>
    (depthRun (run direct) body.run z.1 z.2).pay 1 z.1)).pay 1 0=_
  rw [header_run]
  simp only [Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;>omega

/-- Exact native synchronized calendar from the raw integer input alone. -/
theorem program_value (v o t : ℕ) : (run program (v,(o,t))).val=
    (treeDuration (ofPlan (UniformBalancedToeplitz.plan v) o),
      ofList ((treeTimed t (ofPlan (UniformBalancedToeplitz.plan v) o)).map eventEncode)) := by
  rw [program_run]
  exact result_value (v+1) v o t (by omega)

end
end ExactFourierCircuits.DFTModelCacheCalendar
