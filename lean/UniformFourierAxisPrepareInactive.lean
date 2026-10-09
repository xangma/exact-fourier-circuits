import UniformFourierAxisPrepareControl
import UniformFourierAxisPrepareHead

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareInactive
open UniformMachine UniformNatBlockMachine
open UniformJointAllocation (Constants envelope)
open UniformJointCacheAllocation (ell)
open UniformAxisCacheSelectedPreparation (natAt scalarAt)
namespace H
export UniformFourierAxisPrepareHead (freshNat freshScalar Protected Frame)
end H
namespace C
export UniformFourierAxisPrepareControl (Frame decisionState footerWrites)
end C
noncomputable section

lemma inactive_values {d g:Nat}{s:State}(h:UniformEpochSelectorMachine.Selected d g s)
 (inactive:2*d+5≤g):s.natReg 7080=2 ∧s.natReg 6702=0 ∧s.natReg 6705=0:=by
 rcases h with h|h|h|h|h|h <;>rcases h with ⟨a,b,c⟩ <;>omega

lemma frame_trans {writes:List Nat}{s t u:State}(h:H.Frame s t)(f:C.Frame writes t u)
 (away:∀q,H.Protected q→q∉writes):H.Frame s u:=
 ⟨f.natHeap.trans h.natHeap,f.scalarHeap.trans h.scalarHeap,f.scalarReg.trans h.scalarReg,
  f.outputs.trans h.outputs,f.roots.trans h.roots,fun q hq=>(f.natReg q (away q hq)).trans (h.natReg q hq)⟩

lemma decision_away(q:Nat)(h:H.Protected q):q∉[7081]:=by
 simp only[List.mem_cons,List.not_mem_nil,or_false]
 unfold H.Protected at h
 omega
lemma footer_away(q:Nat)(h:H.Protected q):q∉C.footerWrites:=by
 simp only[C.footerWrites,UniformFourierAxisPrepareControl.footerWrites,List.mem_cons,List.not_mem_nil,or_false]
 unfold H.Protected at h
 omega

lemma footer_inputs {r N S count j physical directory cacheN cacheS:Nat}{s:State}
 (h:UniformFourierAxisPrepareFooter.Result r N S count j physical directory cacheN cacheS s):
 UniformGlobalCalendarDispatch.Inputs (UniformFourierAxisWorkspace.axisBank r N S).selected
 count r (UniformFourierAxisWorkspace.axisBank r N S).pool
 (UniformFourierAxisWorkspace.axisBank r N S).rawRows
 (UniformFourierAxisWorkspace.axisBank r N S).phase s:=
 ⟨h.selected,h.count,h.radix,h.pool,h.rows,h.phase⟩

/-- The actual retained selected-axis cache allocator's addresses. -/
def cache(c:Constants)(n:Nat)(j:Fin (ell n)):UniformJointCacheAllocation.AxisAddresses:=
 UniformJointCacheAllocation.axisBank (UniformAllAxisSeedPreparation.radix n j)
 (natAt c n j.val) (scalarAt c n j.val)

structure Result(c:Constants)(n d g:Nat)(j:Fin (ell n))(x:Fin n→ℂ)(s u:State):Prop where
 pc:u.pc=388
 footer:UniformFourierAxisPrepareFooter.Result (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) 0 j.val (s.natReg 6028) (s.natReg 5923)
  (cache c n j).endNat (cache c n j).endScalar u
 workspace:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) u
 allocation:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u
 seed:u.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val
 mode:u.natReg 7080=2
 count:u.natReg 6705=0
 selected:UniformEpochSelectorMachine.Selected d g u
 inputs:UniformAxisCacheInputs.Inputs n x u
 frame:H.Frame s u

lemma Result.dispatch {c:Constants}{n d g:Nat}{j:Fin (ell n)}{x:Fin n→ℂ}{s u:State}
 (h:Result c n d g j x s u):
 UniformGlobalCalendarDispatch.Inputs
  (UniformFourierAxisWorkspace.axisBank (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j)).selected
  0 (UniformAllAxisSeedPreparation.radix n j)
  (UniformFourierAxisWorkspace.axisBank (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j)).pool
  (UniformFourierAxisWorkspace.axisBank (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j)).rawRows
  (UniformFourierAxisWorkspace.axisBank (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j)).phase u:=
 footer_inputs h.footer

/-- Actual program entry0 through lookup, workspace allocator, duration read,
INACTIVE decision and the common genuine halt. No produced phase is an input. -/
theorem execution(c:Constants){n d g:Nat}(hn:0<n)(j:Fin (ell n))(x:Fin n→ℂ)(s:State)
 (head:UniformAxisCacheClockLookup.Header c n j.val s)
 (later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s)
 (input:UniformAxisCacheInputs.Inputs n x s)
 (natFrontier:s.natReg 5924=H.freshNat c n j)
 (scalarFrontier:s.natReg 5925=H.freshScalar c n j)
 (epoch:s.natReg 5920=g)
 (duration:s.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d)
 (fit:2*d+5≤envelope c n)(code:389≤envelope c n)(pc:s.pc=0)(bound:WordBound (envelope c n) s)
 (inactive:2*d+5≤g)(physicalFit:s.natReg 6028+4*j.val≤envelope c n):
 ∃u ticks,BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u ∧
 ticks≤4*Nat.clog 2 (4*UniformAllAxisSeedPreparation.radix n j)+140 ∧Result c n d g j x s u:=by
 obtain ⟨a,t,run,time,ap,workspace,allocation,radix,seed,selected,inputA,frames⟩:=
  UniformFourierAxisPrepareHead.execution c hn j x s head later input natFrontier scalarFrontier
   epoch duration fit code pc bound
 have active:=inactive_values selected inactive
 let b:=C.decisionState 2 a
 have decision:=UniformFourierAxisPrepareControl.decision_execution n (envelope c n) 2 x a ap active.1 run.final_bound code
 change BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) a 4 b at decision
 have bp:b.pc=370:=UniformFourierAxisPrepareControl.decision_pc 2 a
 have df:C.Frame [7081] a b:=UniformFourierAxisPrepareControl.decision_frame 2 a
 have workB:=UniformFourierAxisPrepareControl.decision_workspace (mode:=2) workspace
 have allocB:=UniformFourierAxisPrepareHead.allocation_transfer allocation (u:=b) (by
  intro q lo hi;exact df.natReg q (by simp only[List.mem_cons,List.not_mem_nil,or_false];omega))
 have framesB:H.Frame s b:=frame_trans frames df decision_away
 have args:UniformFourierAxisPrepareFooter.Args (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) 0 j.val (s.natReg 6028) (s.natReg 5923)
  (cache c n j).endNat (cache c n j).endScalar b:=by
  constructor
  · exact workB
  · exact (df.natReg 6705 (by decide)).trans active.2.2
  · exact (df.natReg 6800 (by decide)).trans radix
  · exact (framesB.natReg 5922 (by unfold H.Protected;omega)).trans head.axis
  · exact framesB.natReg 6028 (by unfold H.Protected;omega)
  · exact framesB.natReg 5923 (by unfold H.Protected;omega)
  · exact allocB.endNat
  · exact allocB.endScalar
 obtain ⟨done,result,ff⟩:=UniformFourierAxisPrepareControl.footer_execution n (envelope c n)
  (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j) 0 j.val
  (s.natReg 6028) (s.natReg 5923) (cache c n j).endNat (cache c n j).endScalar
  x b args bp decision.final_bound code physicalFit
 let u:=applyBlock UniformFourierAxisPrepareFooter.block b
 have framesU:H.Frame s u:=frame_trans framesB ff footer_away
 have inputU:UniformAxisCacheInputs.Inputs n x u:=UniformAxisCacheInputs.transport c n j.val hn x s u input
  ⟨framesU.scalarHeap,framesU.scalarReg,framesU.outputs,framesU.roots⟩ (fun q _=>congrFun framesU.natHeap q)
  (fun q lo hi=>framesU.natReg q (by unfold H.Protected;omega))
 have selB:=UniformFourierAxisPrepareControl.decision_selected (mode:=2) selected
 have selU:=UniformFourierAxisPrepareControl.footer_selected selB
 have allocU:=UniformFourierAxisPrepareHead.allocation_transfer allocB (u:=u) (by
  intro q lo hi;apply ff.natReg q
  simp only[C.footerWrites,UniformFourierAxisPrepareControl.footerWrites,List.mem_cons,List.not_mem_nil,or_false];omega)
 have up:u.pc=388:=by rw[UniformFourierAxisPrepareControl.block_pc,UniformFourierAxisPrepareFooter.block_length,bp]
 refine ⟨u,_,(run.trans decision).executes done,by omega,up,result,
  UniformFourierAxisPrepareControl.footer_workspace args,allocU,?_,?_,?_,selU,inputU,framesU⟩
 · exact (ff.natReg 7000 (by decide)).trans ((df.natReg 7000 (by decide)).trans seed)
 · exact (ff.natReg 7080 (by decide)).trans ((df.natReg 7080 (by decide)).trans active.1)
 · exact (ff.natReg 6705 (by decide)).trans ((df.natReg 6705 (by decide)).trans active.2.2)
end
end ExactFourierCircuits.UniformFourierAxisPrepareInactive
