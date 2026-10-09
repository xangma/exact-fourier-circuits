import UniformCacheLowFrame
import UniformAxisCacheForestExecution
import UniformActualCacheRectangleRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestExecution
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheForestEntry UniformAxisCacheForestGeometry UniformAxisCacheForestRetention
open UniformAxisCacheForestHeader UniformAxisCacheCanonicalRequests UniformJointCacheAllocation
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestExecution
noncomputable section

/-- Places the actual461 leaf scan after the real request phase. All entry
layouts and sources are derived from actual producer outputs. -/
theorem execution_low (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (p:Program) (base finish:ℕ) (code:CodeAt UniformDirectLeafForestProgram.program p base finish)
 (room:base+461≤A.envelope c n) (exitBound:finish≤A.envelope c n)
 (x:Fin n→ℂ) (s:State) (prepared:Prepared c n j s)
 (ends:UniformLocalStoredRequestLoop.Endpoints c n j (canonical c n j)
  (axis c n j).requests (axis c n j).requestStarts s)
 (source:UniformAxisCacheForestSource.Source c n j s)
 (control:Control n j.val s)
 (result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) s)
 (input:Inputs n x s) (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (rectangles:∀i (hi:i<(canonical c n j).length),UniformLocalRequestGeometry.Complete c n j
  (canonical c n j) (axis c n j).requests (axis c n j).requestStarts (geometry c n hn j) i hi s)
 (radix:s.natReg 6800=Seed.radix n j) (pc:s.pc=base) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedRuns p n x (A.envelope c n) s ticks u∧
 ticks≤(62*Seed.radix n j+246)*UniformDirectLeafForestModel.demand (visits c n j)+
  93*(visits c n j).length+40∧u.pc=finish∧Outcome c n hn j x s u ∧ UniformCacheLowRetention.Frame n s u:=by
 let start:=setPC s 0
 have h:=header prepared ends result source radix
 have startBound:WordBound (A.envelope c n) start:=⟨by change 0≤A.envelope c n;omega,wb.2⟩
 obtain ⟨a,ticks,run,cost,post,frame⟩:=UniformDirectLeafForestExecution.execution j x start
  (header_withPC h 0) ((sources input source).withPC (pc:=0)) (facts c n j) (seed_bounds c n hn j)
  rfl (positive c n hn j) rfl rfl (placement c n hn j) rfl rfl startBound
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed code
  (by simpa only[UniformDirectLeafForestProgram.program_length] using room) exitBound run
 change BoundedRuns p n x (A.envelope c n) (placed base (setPC s 0)) ticks (setPC a finish) at placedRun
 rw [UniformSeedRankCrossPreparation.placed_zero s base pc] at placedRun
 let u:=setPC a finish
 have finalFrame:Frame (parameters c n j) (visits c n j) s u:=
  ⟨frame.scalarOutside,frame.natBefore,frame.natHigh,frame.outputs,frame.roots⟩
 have keep(q:ℕ)(hi:6700≤q):u.natReg q=s.natReg q:=
  UniformDirectLeafForestFrames.execution_nat run q (Or.inl hi)
 have saved(q:ℕ)(lo:100≤q)(hi:q≤106):u.natReg q=s.natReg q:=
  UniformDirectLeafForestFrames.execution_nat run q (Or.inr (Or.inl ⟨lo,hi⟩))
 have outControl:Control n j.val u:=
  ⟨(keep _ (by omega)).trans control.zero,(keep _ (by omega)).trans control.one,
   (keep _ (by omega)).trans control.two,(keep _ (by omega)).trans control.nine,
   (keep _ (by omega)).trans control.source,(keep _ (by omega)).trans control.count,
   (keep _ (by omega)).trans control.index⟩
 have outResult:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u:=by
  constructor
  all_goals first
  | exact (keep _ (by omega)).trans result.tasks
  | exact (keep _ (by omega)).trans result.nodes
  | exact (keep _ (by omega)).trans result.requests
  | exact (keep _ (by omega)).trans result.control
  | exact (keep _ (by omega)).trans result.leafForward
  | exact (keep _ (by omega)).trans result.leafTranspose
  | exact (keep _ (by omega)).trans result.durations
  | exact (keep _ (by omega)).trans result.nodeStarts
  | exact (keep _ (by omega)).trans result.requestStarts
  | exact (keep _ (by omega)).trans result.endNat
  | exact (keep _ (by omega)).trans result.pool
  | exact (keep _ (by omega)).trans result.endScalar
 have outBank:UniformLocalRectangleWorkspaceHeaders.Bank n u:=by
  intro f
  exact (UniformDirectLeafForestBankFrame.execution_bank run _ (by omega) (by have:=f.isLt;omega)).trans (bank f)
 have allRects:=UniformActualCacheRectangleRetention.all_completed (geometry c n hn j)
  (before c n hn j) finalFrame rectangles
 refine ⟨u,ticks,placedRun,cost,rfl,?_,?_⟩
 · exact ⟨contents_withPC (UniformDirectLeafForestContents.ofPost post) finish,allRects,
  endpoints_withPC post.endpoints finish,
  inputs hn input (post.sources.withPC (pc:=finish)) finalFrame saved,outControl,outResult,outBank,
  UniformDirectLeafForestFrames.execution_nat run _ (Or.inr (Or.inr ⟨by omega,by omega⟩)),
  keep _ (by omega),keep _ (by omega),frame.outputs,frame.roots,
  fun i old=>earlier hn old finalFrame⟩

 · have l:=placement c n hn j
   have b:=bounds c n hn j
   have rows:(parameters c n j).start.rows≤(parameters c n j).ranges:=by
    change UniformLocalRectangleWorkspaceHeaders.z n≤(axis c n j).tasks
    have h:=b.rows;omega
   have nat:=low_nat finalFrame rows (by have h:=l.rows;omega)
   have lower:UniformCacheLowRetention.z n≤(parameters c n j).start.pool:=by
    change UniformCacheLowRetention.z n≤(axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
    have h:=(UniformAxisCachePhysical.axis_lower c n j).2
    have low:=UniformAxisCachePreparationRetention.slab_above_seed_word c n
    change UniformCacheLowRetention.z n≤UniformJointAllocation.slab c n at low
    omega
   exact ⟨nat,fun a ha=>finalFrame.scalarOutside a (Or.inl (ha.trans_le lower))⟩

end
end ExactFourierCircuits.UniformAxisCacheForestExecution
