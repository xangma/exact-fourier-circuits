import UniformCacheLowRequestCanonical
import UniformAxisCacheRectangleExecution
import UniformLocalStoredRequestCanonical
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRectangleExecution
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs UniformAxisCacheForestHeader
open UniformAxisCacheCanonicalRequests
open UniformTensorMonomialMachine (setPC)
/-- Places the actual finite3776 request program in its caller. All outputs
are genuine measured request-cache facts and physical endpoint registers. -/
theorem execution_low (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (p:Program) (base finish:ℕ) (code:CodeAt Q.program p base finish)
 (room:base+3776≤A.envelope c n) (exitBound:finish≤A.envelope c n)
 (x:Fin n→ℂ) (s:State)
 (ready:UniformAxisCacheTimingExecution.Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) s)
 (selected:Selected c n j.val s) (prepared:Prepared c n j s)
 (input:Inputs n x s) (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=base) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedRuns p n x (A.envelope c n) s ticks u∧
 ticks≤Q.costPrefix n j (canonical c n j) (canonical c n j).length+23∧u.pc=finish∧
 Q.Ready c n j (canonical c n j) (UniformJointCacheAllocation.axis c n j).requests
  (UniformJointCacheAllocation.axis c n j).requestStarts (geometry c n hn j) x (canonical c n j).length u∧
 Q.Endpoints c n j (canonical c n j) (UniformJointCacheAllocation.axis c n j).requests
  (UniformJointCacheAllocation.axis c n j).requestStarts u∧Q.LoopFrame c n j s u∧
 Control n j.val u∧UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u∧Prepared c n j u∧Inputs n x u∧
 UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=s.natReg 5921∧u.natReg 6909=s.natReg 6909∧u.natReg 6910=s.natReg 6910∧u.natReg 6800=Seed.radix n j ∧ UniformCacheLowRetention.Frame n s u:=by
 let start:=setPC s 0
 have startReady:UniformAxisCacheTimingExecution.Ready (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) start:=
  UniformAxisCacheHorizon.ready_transport ready rfl (fun _ _=>rfl)
 have startBank:UniformLocalRectangleWorkspaceHeaders.Bank n start:=bank
 have startBound:WordBound (A.envelope c n) start:=⟨by change 0≤A.envelope c n;omega,wb.2⟩
 obtain ⟨a,ticks,run,cost,ap,result,ends,frame,clock,low⟩:=
  UniformLocalStoredRequestLoop.canonical_execution_low c n hn j x start startReady startBank
   selected.source selected.control.index input.original.withPC input.conjugate.withPC
   (input.withPC).metadata (input.withPC).operands (by omega) rfl startBound
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed code
  (by simpa only [UniformLocalStoredRequestLoop.program_length] using room) exitBound run
 change BoundedRuns p n x (A.envelope c n) (placed base (setPC s 0)) ticks (setPC a finish) at placedRun
 rw [UniformSeedRankCrossPreparation.placed_zero s base pc] at placedRun
 let u:=setPC a finish
 have finalFrame:Q.LoopFrame c n j s u:=
  ⟨frame.nat,frame.scalar,frame.driver,frame.outputs,frame.roots⟩
 have control:Control n j.val u:=
  ⟨(frame.driver _ (by omega)).trans selected.control.zero,
   (frame.driver _ (by omega)).trans selected.control.one,
   (frame.driver _ (by omega)).trans selected.control.two,
   (frame.driver _ (by omega)).trans selected.control.nine,
   (frame.driver _ (by omega)).trans selected.control.source,
   (frame.driver _ (by omega)).trans selected.control.count,
   (frame.driver _ (by omega)).trans selected.control.index⟩
 have alloc:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u:=by
  constructor
  all_goals first
  | exact (frame.driver _ (by omega)).trans ready.result.tasks
  | exact (frame.driver _ (by omega)).trans ready.result.nodes
  | exact (frame.driver _ (by omega)).trans ready.result.requests
  | exact (frame.driver _ (by omega)).trans ready.result.control
  | exact (frame.driver _ (by omega)).trans ready.result.leafForward
  | exact (frame.driver _ (by omega)).trans ready.result.leafTranspose
  | exact (frame.driver _ (by omega)).trans ready.result.durations
  | exact (frame.driver _ (by omega)).trans ready.result.nodeStarts
  | exact (frame.driver _ (by omega)).trans ready.result.requestStarts
  | exact (frame.driver _ (by omega)).trans ready.result.endNat
  | exact (frame.driver _ (by omega)).trans ready.result.pool
  | exact (frame.driver _ (by omega)).trans ready.result.endScalar
 have finalPrepared:Prepared c n j u:=
  ⟨(frame.driver _ (by omega)).trans prepared.nodes,(frame.driver _ (by omega)).trans prepared.count,
   (frame.driver _ (by omega)).trans prepared.starts,(frame.driver _ (by omega)).trans prepared.durations,
   (frame.driver _ (by omega)).trans prepared.original,(frame.driver _ (by omega)).trans prepared.conjugate,
   (frame.driver _ (by omega)).trans prepared.rows⟩
 have finalResult:=result.withPC finish
 have finalEnds:Q.Endpoints c n j (canonical c n j) (UniformJointCacheAllocation.axis c n j).requests
  (UniformJointCacheAllocation.axis c n j).requestStarts u:=
  ⟨ends.pool,ends.permutation,ends.widths,ends.markers,ends.physicalAxis,ends.abi,
   ends.pointer,ends.timePointer,ends.index,ends.count⟩
 refine ⟨u,ticks,placedRun,cost,rfl,finalResult,finalEnds,finalFrame,control,alloc,finalPrepared,
  ⟨finalResult.metadata,finalResult.operands,finalResult.original,finalResult.conjugate⟩,
  finalResult.control.bank,clock _ (by omega) (by omega),frame.driver _ (by omega),frame.driver _ (by omega),
  (frame.driver _ (by omega)).trans ready.radix,⟨low.nat,low.scalar⟩⟩

end ExactFourierCircuits.UniformAxisCacheRectangleExecution
