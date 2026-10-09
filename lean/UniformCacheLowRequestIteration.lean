import UniformCacheLowRequestBody
import UniformLocalStoredRequestIteration
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl UniformLocalRequestGeometry
open UniformLocalCacheSlotConductorMachine
noncomputable section

/-- One actual request test, axis installation, complete3738 producer and
measured13 advance. Earlier physical cache entries survive every instruction. -/
theorem iteration_low {constants n j qs R T}(hn:0<n)
 (g:UniformLocalRequestGeometry.Geometry constants n j qs R T)(x:Fin n → ℂ)
 (i:ℕ)(hi:i < qs.length)(s:State)(ready:Ready constants n j qs R T g x i s)
 (code:3776 ≤ envelope constants n)(pc:s.pc=21)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedRuns program n x (envelope constants n) s ticks u ∧
 ticks ≤ requestCharge n j (qs[i]'hi).row ∧u.pc=21 ∧
 Ready constants n j qs R T g x (i+1) u ∧LoopFrame constants n j s u ∧ UniformCacheLowRetention.Frame n s u:=by
 have first:=enter (x:=x) ready.control hi pc wb code
 have eh:=entered_heaps s
 have er:Ready constants n j qs R T g x i (entered s):=ready.transport (entered_control ready.control)
  eh.1 eh.2.1 (fun q lo up=>entered_keeps s q (by omega) (by omega)) eh.2.2.2.1 eh.2.2.2.2
 obtain ⟨b,bt,second,cheap,bp,post,bodyLow⟩:=body_low hn g x i hi (entered s) er
  ((entered_axis s).trans ready.control.axis) code (entered_pc s) first.final_bound
 let start:=setPC b 0
 have sr:=post.ready.withPC 0
 have bounds:=changePC_bound (envelope constants n) b 0 second.final_bound (by omega)
 have pp:start.natReg 6173+7 ≤ envelope constants n:=by
  rw[sr.control.live.pointer]
  have:=g.rowsBound
  omega
 have pi:start.natReg 6174+1 ≤ envelope constants n:=by
  rw[sr.control.live.index]
  have:=g.timesBound
  omega
 have pt:start.natReg 6161+1 ≤ envelope constants n:=by
  rw[sr.control.live.timePointer]
  have:=g.timesBound
  omega
 obtain ⟨last,advance,lp,copied,pointer,index,time,nh,sh,regs,out,roots⟩:=
  UniformLocalRequestAdvanceMachine.execution x start (by omega) rfl bounds pp pi pt
 have third:=UniformBoundedAssembly.boundedExecution_placed advance_code
  (by rw[UniformLocalRequestAdvanceMachine.program_length];omega) (by omega) advance
 rw[UniformSeedRankCrossPreparation.placed_zero b 3762 bp] at third
 let u:=setPC last 21
 have control:Control constants n j qs R T (i+1) u:=by
  exact (UniformLocalRequestControl.advance sr.control hi (post.measured.withPC 0)
   advance copied pointer index time).withPC 21
 have preservation:UniformSeedRankCrossPreparation.PreservedFrame n b u:=
  ⟨fun q _=>congrFun nh q,fun q _=>congrFun sh q,
   fun q lo up=>UniformLocalRequestFrames.advance_nat advance q (by simp[UniformLocalRequestFrames.advanceWrites];omega),out,roots⟩
 have conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=
  UniformLocalRectangleCoefficientMachine.conjugate_retained post.ready.conjugate
   (fun q _=>congrFun sh q) (fun q _=>congrFun nh q)
 have source:Source R T qs u:=post.ready.source.transport (fun _ _ _=>congrFun nh _) (fun _ _=>congrFun nh _)
 have completed:∀k (hk:k < qs.length),k < i+1 → Complete constants n j qs R T g k hk u:=by
  intro k hk old
  by_cases prior:k < i
  · exact (post.ready.completed k hk prior).heaps nh sh
  · have same:k=i:=by omega
    subst k
    exact post.current.heaps nh sh
 have final:Ready constants n j qs R T g x (i+1) u:=
  ⟨control,source,preservation.retained post.ready.original,conjugate,
   preservation.protected.metadata post.ready.metadata,preservation.protected.operands post.ready.operands,completed⟩
 have eframe:LoopFrame constants n j s (entered s):=
  ⟨fun q _ _=>congrFun eh.1 q,fun q _ _=>congrFun eh.2.1 q,
   fun q lo=>entered_keeps s q (by omega) (by omega),eh.2.2.2.1,eh.2.2.2.2⟩
 have aframe:LoopFrame constants n j b u:=
  ⟨fun q _ _=>congrFun nh q,fun q _ _=>congrFun sh q,
   fun q lo=>UniformLocalRequestFrames.advance_high advance q lo,out,roots⟩
 refine ⟨u,3+bt+13,(first.trans second).trans third,?_,rfl,final,(eframe.trans post.frame).trans aframe,?_⟩
 · change 3+bt+13 ≤ bodyCharge n j (qs[i]'hi).row+16
   omega
 · exact ⟨fun a ha=>(congrFun nh a).trans ((bodyLow.nat a ha).trans (congrFun eh.1 a)),
    fun a ha=>(congrFun sh a).trans ((bodyLow.scalar a ha).trans (congrFun eh.2.1 a))⟩

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
