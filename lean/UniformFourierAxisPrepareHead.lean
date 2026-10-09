import UniformFourierAxisPrepareEpoch
import UniformFourierAxisWorkspaceBindings
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareHead
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
open UniformJointAllocation (Constants envelope)
open UniformJointCacheAllocation (ell)
open UniformAxisCacheSelectedPreparation (natAt scalarAt)
noncomputable section

def freshNat(c:Constants)(n:ℕ)(j:Fin (ell n)):ℕ:=
 UniformGlobalCalendarArena.natBase c n+UniformFourierAxisWorkspace.natPrefix n j.val
def freshScalar(c:Constants)(n:ℕ)(j:Fin (ell n)):ℕ:=
 UniformGlobalCalendarArena.scalarBase c n+9*UniformAllAxisSeedPreparation.prefixSum n j.val

def Protected(q:ℕ):Prop:=(100≤q∧q≤106)∨(5920≤q∧q≤5925)∨(5936≤q∧q≤5939)∨
 (6000≤q∧q≤6199)∨q=6904∨q=6909∨q=6910
structure Frame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,Protected q→u.natReg q=s.natReg q

lemma allocation_transfer{r N S:ℕ}{s u:State}
 (a:UniformAxisCacheAllocationMachine.Result r N S s)
 (keep:∀q,6810≤q→q≤6821→u.natReg q=s.natReg q):
 UniformAxisCacheAllocationMachine.Result r N S u:=by
 exact ⟨(keep _ (by omega) (by omega)).trans a.tasks,
 (keep _ (by omega) (by omega)).trans a.nodes,
 (keep _ (by omega) (by omega)).trans a.requests,
 (keep _ (by omega) (by omega)).trans a.control,
 (keep _ (by omega) (by omega)).trans a.leafForward,
 (keep _ (by omega) (by omega)).trans a.leafTranspose,
 (keep _ (by omega) (by omega)).trans a.durations,
 (keep _ (by omega) (by omega)).trans a.nodeStarts,
 (keep _ (by omega) (by omega)).trans a.requestStarts,
 (keep _ (by omega) (by omega)).trans a.endNat,
 (keep _ (by omega) (by omega)).trans a.pool,
 (keep _ (by omega) (by omega)).trans a.endScalar⟩

lemma workspace_transfer{r N S:ℕ}{s u:State}
 (a:UniformFourierAxisWorkspaceHeader.Header r N S s)
 (keep:∀q,(7050≤q∧q≤7059)∨q=5934∨q=5935→u.natReg q=s.natReg q):
 UniformFourierAxisWorkspaceHeader.Header r N S u:=by
 exact ⟨(keep _ (by omega)).trans a.selected,(keep _ (by omega)).trans a.boundary,
 (keep _ (by omega)).trans a.phase,(keep _ (by omega)).trans a.rows,
 (keep _ (by omega)).trans a.permutation,(keep _ (by omega)).trans a.widths,
 (keep _ (by omega)).trans a.markers,(keep _ (by omega)).trans a.pool,
 (keep _ (by omega)).trans a.endNat,(keep _ (by omega)).trans a.endScalar,
 (keep _ (by omega)).trans a.nextNat,(keep _ (by omega)).trans a.nextScalar⟩

lemma block_pc(b:List Op)(s:State):(applyBlock b s).pc=s.pc+b.length:=by
 induction b generalizing s with
 | nil=>rfl
 | cons o b ih=>rw[applyBlock,ih,Op.apply_pc,List.length_cons];omega

/-- Existential boundary keeps the produced workspace state abstract for later helpers. -/
lemma workspace_execution(c:Constants){n:ℕ}(hn:0<n)(j:Fin (ell n))(x:Fin n→ℂ)(a:State)
 (radix:a.natReg 6800=UniformAllAxisSeedPreparation.radix n j)
 (aN:a.natReg 5924=freshNat c n j)(aS:a.natReg 5925=freshScalar c n j)
 (result:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) a)(pc:a.pc=69)(code:389≤envelope c n)(bound:WordBound (envelope c n) a):
 ∃b,BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) a 28 b∧b.pc=97∧
 UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j) (freshNat c n j) (freshScalar c n j) b∧
 b.natHeap=a.natHeap∧b.scalarHeap=a.scalarHeap∧b.scalarReg=a.scalarReg∧b.outputs=a.outputs∧b.rootOrders=a.rootOrders∧
 (∀q,(q<7050∨7068≤q)→q≠5934→q≠5935→b.natReg q=a.natReg q):=by
 obtain ⟨run,workspace⟩:=UniformFourierAxisWorkspaceBindings.execution c hn j
  UniformFourierAxisPrepareMachine.program x a radix aN aS (natAt c n j.val) (scalarAt c n j.val)
  result UniformFourierAxisPrepareMachine.workspace_code pc (by omega) bound
 refine ⟨applyBlock UniformFourierAxisWorkspaceHeader.block a,run,?_,workspace,UniformFourierAxisWorkspaceHeader.frame a⟩
 rw[block_pc,UniformFourierAxisWorkspaceHeader.block_length,pc]

/-- The literal389 executes its real69 lookup, real28 workspace arithmetic,
and real41 duration/epoch selector. The duration is ordinary retained heap data. -/
theorem execution(c:Constants){n d g:ℕ}(hn:0<n)(j:Fin (ell n))(x:Fin n→ℂ)(s:State)
 (head:UniformAxisCacheClockLookup.Header c n j.val s)
 (later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s)
 (input:UniformAxisCacheInputs.Inputs n x s)
 (natFrontier:s.natReg 5924=freshNat c n j)
 (scalarFrontier:s.natReg 5925=freshScalar c n j)
 (epoch:s.natReg 5920=g)
 (duration:s.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d)
 (fit:2*d+5≤envelope c n)(code:389≤envelope c n)(pc:s.pc=0)(bound:WordBound (envelope c n) s):
 ∃u ticks,BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u ∧
 ticks≤4*Nat.clog 2 (4*UniformAllAxisSeedPreparation.radix n j)+117 ∧u.pc=138 ∧
 UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (freshNat c n j) (freshScalar c n j) u ∧
 UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u ∧
 u.natReg 6800=UniformAllAxisSeedPreparation.radix n j ∧
 u.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val ∧
 UniformEpochSelectorMachine.Selected d g u ∧UniformAxisCacheInputs.Inputs n x u ∧Frame s u:=by
 obtain ⟨a0,lookup,ap,result,seedcell,radix,_front,_header,_input,lf⟩:=
  UniformAxisCacheClockLookup.execution c n hn j x s head later input pc bound
 have first:=UniformBoundedAssembly.boundedExecution_placed UniformFourierAxisPrepareMachine.lookup_code
  (by rw[UniformAxisCacheClockLookup.program_length];omega) (by omega) lookup
 rw[show placed 0 s=s by cases s;simp[placed]] at first
 let a:=setPC a0 69
 change BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) s _ a at first
 have keepA(q:ℕ)(h:Protected q):a.natReg q=s.natReg q:=by
  apply lf.natReg q<;>unfold Protected at h<;>omega
 have aN:a.natReg 5924=freshNat c n j:=(keepA _ (by unfold Protected;omega)).trans natFrontier
 have aS:a.natReg 5925=freshScalar c n j:=(keepA _ (by unfold Protected;omega)).trans scalarFrontier
 have resultA:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) a:=allocation_transfer result (fun _ _ _=>rfl)
 obtain ⟨b,second,bp,workspace,wf⟩:=workspace_execution c hn j x a radix aN aS resultA rfl code first.final_bound
 have keepB(q:ℕ)(h:q<7050∨7068≤q)(n:q≠5934)(s:q≠5935):b.natReg q=a.natReg q:=wf.2.2.2.2.2 q h n s
 have resultB:UniformAxisCacheAllocationMachine.Result (UniformAllAxisSeedPreparation.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) b:=allocation_transfer resultA (by
   intro q lo hi;exact keepB q (by omega) (by omega) (by omega))
 have epochB:b.natReg 5920=g:=(keepB _ (by omega) (by omega) (by omega)).trans
  ((keepA _ (by unfold Protected;omega)).trans epoch)
 have durationB:b.natHeap (b.natReg 6816)=some d:=by
  rw[resultB.durations]
  change b.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d
  rw[wf.1]
  change a0.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d
  rw[lf.natHeap]
  exact duration
 obtain ⟨u,t,third,time,up,selected,ef⟩:=UniformFourierAxisPrepareEpoch.execution x b bp epochB durationB
  second.final_bound code fit
 have keepEpoch(q:ℕ)(away:q∉UniformEpochSelectorMachine.modified):u.natReg q=b.natReg q:=ef.natReg q away
 have keepU(q:ℕ)(h:Protected q):u.natReg q=s.natReg q:=by
  have ep:u.natReg q=b.natReg q:=keepEpoch q (by
   simp only[UniformEpochSelectorMachine.modified,List.mem_cons,List.not_mem_nil,or_false] at *
   unfold Protected at h;omega)
  exact ep.trans ((keepB q (by unfold Protected at h;omega) (by unfold Protected at h;omega)
   (by unfold Protected at h;omega)).trans (keepA q h))
 have frames:Frame s u:=⟨ef.natHeap.trans (wf.1.trans lf.natHeap),
  ef.scalarHeap.trans (wf.2.1.trans lf.scalarHeap),ef.scalarReg.trans (wf.2.2.1.trans lf.scalarReg),
  ef.outputs.trans (wf.2.2.2.1.trans lf.outputs),ef.roots.trans (wf.2.2.2.2.1.trans lf.roots),keepU⟩
 have finalInput:UniformAxisCacheInputs.Inputs n x u:=UniformAxisCacheInputs.transport c n j.val hn x s u input
  ⟨frames.scalarHeap,frames.scalarReg,frames.outputs,frames.roots⟩ (fun q _=>congrFun frames.natHeap q)
  (fun q lo hi=>keepU q (by unfold Protected;omega))
 have workU:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (freshNat c n j) (freshScalar c n j) u:=workspace_transfer workspace (by
   intro q h;apply keepEpoch q
   simp only[UniformEpochSelectorMachine.modified,List.mem_cons,List.not_mem_nil,or_false] at *;omega)
 have allocU:=allocation_transfer resultB (u:=u) (by
  intro q lo hi;apply keepEpoch q
  simp only[UniformEpochSelectorMachine.modified,List.mem_cons,List.not_mem_nil,or_false] at *;omega)
 have radixU:u.natReg 6800=UniformAllAxisSeedPreparation.radix n j:=
  (keepEpoch _ (by simp[UniformEpochSelectorMachine.modified])).trans
   ((keepB _ (by omega) (by omega) (by omega)).trans radix)
 have seedU:u.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val:=
  (keepEpoch _ (by simp[UniformEpochSelectorMachine.modified])).trans
   ((keepB _ (by omega) (by omega) (by omega)).trans seedcell)
 refine ⟨u,_,
  first.trans (second.trans third),?_,up,workU,allocU,radixU,seedU,selected,finalInput,frames⟩
 split_ifs<;>omega
end
end ExactFourierCircuits.UniformFourierAxisPrepareHead
