import UniformCacheLowRequestIteration
import UniformLocalStoredRequestLoopExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformTensorMonomialMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl UniformLocalRequestGeometry
noncomputable section

/-- Every physically stored request is visited, with its own genuine timing
cell. The invariant carries earlier actual cache entries through later writes. -/
theorem loop_low {constants n j qs R T}(hn:0<n)
 (g:UniformLocalRequestGeometry.Geometry constants n j qs R T)(x:Fin n → ℂ)
 (f i:ℕ)(remaining:i+f=qs.length)(s:State)(ready:Ready constants n j qs R T g x i s)
 (code:3776 ≤ envelope constants n)(pc:s.pc=21)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedExecution program n x (envelope constants n) s ticks u ∧
 ticks+costPrefix n j qs i ≤ costPrefix n j qs qs.length+2 ∧u.pc=3775 ∧
 Ready constants n j qs R T g x qs.length u ∧LoopFrame constants n j s u ∧ UniformCacheLowRetention.Frame n s u:=by
 induction f generalizing i s with
 | zero=>
  have eq:i=qs.length:=by omega
  subst i
  refine ⟨setPC s 3775,2,stop (x:=x) ready.control pc wb code,by omega,rfl,
   ready.withPC 3775,?_,⟨fun _ _=>rfl,fun _ _=>rfl⟩⟩
  exact ⟨by intros;rfl,by intros;rfl,by intros;rfl,rfl,rfl⟩
 | succ f ih=>
  have hi:i < qs.length:=by omega
  obtain ⟨a,t,first,cheap,ap,afterFirst,frame,firstLow⟩:=iteration_low hn g x i hi s ready code pc wb
  obtain ⟨u,ticks,tail,cost,up,final,lastFrame,lastLow⟩:=ih (i+1) (by omega) a afterFirst ap first.final_bound
  refine ⟨u,t+ticks,first.executes tail,?_,up,final,frame.trans lastFrame,firstLow.trans lastLow⟩
  rw[costPrefix_step n j qs i hi] at cost
  omega

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
