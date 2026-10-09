import UniformAxisCacheClockLookup
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheClockLookup
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformTensorMonomialMachine (setPC)
noncomputable section

structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,q≠6800→q≠6801→q≠6802→q≠7000→q≠7096→q≠7097→q≠7098→q≠7099→
   (q<6540∨6551<q)→(q<6803∨6828<q)→u.natReg q=s.natReg q

/-- One genuine69-cell lookup. The selected radix is physically loaded, all
allocator arithmetic executes, and the last cell genuinely halts. -/
theorem execution (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (x:Fin n→ℂ) (s:State) (head:Header c n j.val s)
 (later:0<j.val→Frontiers c n j.val s) (input:Inputs n x s)
 (pc:s.pc=0) (wb:WordBound (A.envelope c n) s):
 ∃u,BoundedExecution program n x (A.envelope c n) s
   ((if j.val=0 then 10 else 8)+(4*Nat.clog 2 (4*Seed.radix n j)+55)+1) u∧
 u.pc=68∧UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
  (natAt c n j.val) (scalarAt c n j.val) u∧
 u.natReg 7000=Seed.directoryBase n+2*j.val∧u.natReg 6800=Seed.radix n j∧
 Frontiers c n j.val u∧Header c n j.val u∧Inputs n x u∧Frame s u:=by
 have bounds:=arithmetic c n hn
 obtain ⟨a,first,ap,args,seedcell,hf⟩:=head_execution c n hn j x s head later input pc wb
 let start:=setPC a 0
 have startBound:WordBound (A.envelope c n) start:=⟨by change 0≤A.envelope c n;omega,first.final_bound.2⟩
 have startArgs:UniformAxisCacheAllocationMachine.Arguments (Seed.radix n j)
   (natAt c n j.val) (scalarAt c n j.val) start:=⟨args.radix,args.natFrontier,args.scalarFrontier⟩
 obtain ⟨b,allocate,bp,result,af⟩:=UniformAxisCacheAllocationMachine.execution
  (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) (A.envelope c n) n x
  start startArgs rfl startBound (UniformAxisCacheAllocationMachine.selected_wordBudget c n hn j)
 have middle:BoundedRuns program n x (A.envelope c n) a
  (4*Nat.clog 2 (4*Seed.radix n j)+55) (setPC b 68):=by
  have h:=UniformBoundedAssembly.boundedExecution_placed allocator_code
   (by rw [UniformAxisCacheAllocationMachine.program_length];omega) (by omega) allocate
  change BoundedRuns program n x (A.envelope c n) (placed 10 (setPC a 0)) _ (setPC b 68) at h
  rw [UniformSeedRankCrossPreparation.placed_zero a 10 ap] at h
  exact h
 let u:=setPC b 68
 have halt:BoundedExecution program n x (A.envelope c n) u 1 u:=
  .halt middle.final_bound (by simp [UniformMachine.step,u,setPC,halt_at])
 have frame:Frame s u:=by
  refine ⟨af.natHeap.trans hf.natHeap,af.scalarHeap.trans hf.scalarHeap,
    af.scalarReg.trans hf.scalarReg,af.outputs.trans hf.outputs,af.roots.trans hf.roots,?_⟩
  intro q a b c d e f g h i j
  exact (af.natReg q i j).trans (hf.natReg q a b c d e f g h)
 have keep:∀q,q=5922∨q=6904∨q=6909∨q=6910∨(100≤q∧q≤106)→u.natReg q=s.natReg q:=by
  intro q hq
  apply frame.natReg q<;>omega
 have header:Header c n j.val u:=
  ⟨(keep _ (by omega)).trans head.axis,(keep _ (by omega)).trans head.directory,
   (keep _ (by omega)).trans head.initialNat,(keep _ (by omega)).trans head.initialScalar⟩
 have finalInput:Inputs n x u:=UniformAxisCacheInputs.transport c n j.val hn x s u input
  ⟨frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
  (fun q _=>congrFun frame.natHeap q) (fun q lo hi=>keep q (by omega))
 have front:Frontiers c n j.val u:=
  ⟨(af.natReg 6801 (by omega) (by omega)).trans args.natFrontier,
   (af.natReg 6802 (by omega) (by omega)).trans args.scalarFrontier⟩
 refine ⟨u,first.executes (middle.executes halt),rfl,?_,?_,?_,front,header,finalInput,frame⟩
 · exact ⟨result.tasks,result.nodes,result.requests,result.control,result.leafForward,
    result.leafTranspose,result.durations,result.nodeStarts,result.requestStarts,result.endNat,
    result.pool,result.endScalar⟩
 · exact (af.natReg 7000 (by omega) (by omega)).trans seedcell
 · exact (af.natReg 6800 (by omega) (by omega)).trans args.radix

end
end ExactFourierCircuits.UniformAxisCacheClockLookup
