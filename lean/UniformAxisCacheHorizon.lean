import UniformAxisCacheHorizonBounds
import UniformAxisCachePreparationRetention
import UniformGlobalClockHorizon
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheHorizon
open UniformMachine UniformAssembly UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCachePreparationRetention
open UniformLocalCacheTreeExecution UniformLocalCacheTreeIteration
open UniformAxisCacheTimingExecution (Ready)

lemma ready_transport {r N S:ℕ}{s u:State}(h:Ready r N S s)
 (heap:u.natHeap=s.natHeap)
 (regs:∀q,q<5921∨5937≤q→u.natReg q=s.natReg q):Ready r N S u:=by
 have directory:∀D k visits,Directory D k visits s→Directory D k visits u:=by
  intro D k visits hd
  induction visits generalizing k with
  | nil=>trivial
  | cons q qs ih=>
   refine ⟨?_,ih (k+1) hd.2⟩
   intro f
   rw [heap]
   exact hd.1 f
 have result:UniformAxisCacheAllocationMachine.Result r N S u:=by
  constructor
  all_goals first
  | exact (regs _ (by omega)).trans h.result.tasks
  | exact (regs _ (by omega)).trans h.result.nodes
  | exact (regs _ (by omega)).trans h.result.requests
  | exact (regs _ (by omega)).trans h.result.control
  | exact (regs _ (by omega)).trans h.result.leafForward
  | exact (regs _ (by omega)).trans h.result.leafTranspose
  | exact (regs _ (by omega)).trans h.result.durations
  | exact (regs _ (by omega)).trans h.result.nodeStarts
  | exact (regs _ (by omega)).trans h.result.requestStarts
  | exact (regs _ (by omega)).trans h.result.endNat
  | exact (regs _ (by omega)).trans h.result.pool
  | exact (regs _ (by omega)).trans h.result.endScalar
 refine ⟨?_,directory _ _ _ h.directory,?_,
  (regs _ (by omega)).trans h.requestBase,(regs _ (by omega)).trans h.nodeCount,
  (regs _ (by omega)).trans h.requestEnd,?_,result,
  (regs _ (by omega)).trans h.pool,(regs _ (by omega)).trans h.radix,
  (regs _ (by omega)).trans h.natFrontier,(regs _ (by omega)).trans h.scalarFrontier⟩
 · refine ⟨?_,?_,?_⟩
   · intro k hk;rw [heap];exact h.printed.durations k hk
   · intro k hk;rw [heap];exact h.printed.nodes k hk
   · intro k hk j hj;rw [heap];exact h.printed.requests k hk j hj
 · intro q hq large positive i j hij f
   rw [heap]
   exact h.tables q hq large positive i j hij f
 · exact ⟨(regs _ (by omega)).trans h.timing.durations,
   (regs _ (by omega)).trans h.timing.starts,(regs _ (by omega)).trans h.timing.requests⟩

lemma selected_transport {c:A.Constants}{n j:ℕ}{s u:State}(h:Selected c n j s)
 (regs:∀q,q<5921∨5937≤q→u.natReg q=s.natReg q):Selected c n j u:=by
 refine ⟨?_,?_,(regs _ (by omega)).trans h.radix,
  (regs _ (by omega)).trans h.source,(regs _ (by omega)).trans h.axisIndex⟩
 · exact ⟨(regs _ (by omega)).trans h.control.zero,(regs _ (by omega)).trans h.control.one,
   (regs _ (by omega)).trans h.control.two,(regs _ (by omega)).trans h.control.nine,
   (regs _ (by omega)).trans h.control.source,(regs _ (by omega)).trans h.control.count,
   (regs _ (by omega)).trans h.control.index⟩
 · exact ⟨(regs _ (by omega)).trans h.frontiers.natFrontier,
   (regs _ (by omega)).trans h.frontiers.scalarFrontier⟩

/-- Real root-duration memory supplies the seven charged horizon instructions;
the selected allocator geometry derives their numerical bound internally. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (p:Program)(base:ℕ)(x:Fin n→ℂ)(s:State)
 (ready:Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) s)
 (selected:Selected c n j.val s)(core:Core n x s)
 (code:UniformTensorMonomialMachine.BlockAt UniformGlobalClockHorizon.block p base)
 (pc:s.pc=base)(room:base+7≤A.envelope c n)(wb:WordBound (A.envelope c n) s):
 let u:=UniformTensorMonomialMachine.applyBlock UniformGlobalClockHorizon.block s
 BoundedRuns p n x (A.envelope c n) s 7 u∧u.pc=base+7∧
 Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Selected c n j.val u∧Core n x u∧
 u.natReg 5921=max (s.natReg 5921)
  (2*UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan (Seed.radix n j))+5)∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.scalarReg=s.scalarReg∧
 u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀q,q≠5921→(q<5934∨5937≤q)→u.natReg q=s.natReg q):=by
 have root:=UniformAxisCacheRootDuration.root_duration ready
 have bound:=UniformAxisCacheHorizonBounds.selected_horizon_fits c n hn j
 obtain ⟨run,value,heap,scalars,sregs,outputs,roots,regs⟩:=
  UniformGlobalClockHorizon.execution p x s _ root bound code pc room wb
 have retained:Core n x (UniformTensorMonomialMachine.applyBlock UniformGlobalClockHorizon.block s):=
  transport c n j.val hn x s _ core ⟨scalars,sregs,outputs,roots⟩
   (fun q _=>congrFun heap q) (fun q hq=>regs q (by omega) (Or.inl (by omega)))
 have frame:∀q,q<5921∨5937≤q→
  (UniformTensorMonomialMachine.applyBlock UniformGlobalClockHorizon.block s).natReg q=s.natReg q:=
  fun q hq=>regs q (by omega) (by omega)
 refine ⟨run,?_,ready_transport ready heap frame,selected_transport selected frame,
  retained,value,heap,scalars,sregs,outputs,roots,regs⟩
 rw [UniformTensorMonomialMachine.applyBlock_pc,pc,UniformGlobalClockHorizon.block_length]

end ExactFourierCircuits.UniformAxisCacheHorizon
