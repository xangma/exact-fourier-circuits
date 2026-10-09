import UniformAxisCacheTimingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTimingExecution
open UniformMachine UniformAssembly UniformLocalCacheTimingPlacement
open UniformTensorMonomialMachine (setPC)
open UniformAxisCacheTimingGeometry UniformJointCacheAllocation
open UniformLocalCacheTimingMetadata UniformLocalCacheTreeExecution
namespace P
export UniformAxisCacheTimingProgram (program changed)
end P
namespace A
export UniformAxisCacheAllocationMachine (Arguments Result wordBudget)
end A
noncomputable section

structure Ready(r N S:ℕ)(s:State):Prop where
 printed:UniformLocalCacheTimingExecution.Printed r 0 (axisBank r N S).requests
  (axisBank r N S).durations (axisBank r N S).nodeStarts (axisBank r N S).requestStarts s
 directory:Directory (axisBank r N S).nodes 0 (rootVisits r 0 (axisBank r N S).requests) s
 tables:RequestTables (rootVisits r 0 (axisBank r N S).requests) s
 requestBase:s.natReg 4274=(axisBank r N S).requests
 nodeCount:s.natReg 4281=UniformLocalCacheTimingMetadata.nodeCount r 0 (axisBank r N S).requests
 requestEnd:s.natReg 4282=(axisBank r N S).requests+7*requestCount r 0 (axisBank r N S).requests
 timing:UniformLocalCacheTimingConductor.Allocation (axisBank r N S).durations
  (axisBank r N S).nodeStarts (axisBank r N S).requestStarts s
 result:A.Result r N S s
 pool:s.natReg 6160=(axisBank r N S).pool
 radix:s.natReg 6800=r
 natFrontier:s.natReg 6801=N
 scalarFrontier:s.natReg 6802=S

/-- Ordinary allocator inputs produce all forest/timing headers, literal source
records and max-child timings in one actual370-cell execution. -/
theorem execution(r N S B n:ℕ)(x:Fin n→ℂ)(s:State)
 (args:A.Arguments r N S s)(radix:2≤r)(pc:s.pc=0)(wb:WordBound B s)(budget:A.wordBudget r N S≤B):
 ∃ta t u,BoundedExecution P.program n x B s (4*Nat.clog 2 (4*r)+66+ta+6+t) u∧
 ta≤(2*r+1)*nodeBudget r+18∧t≤UniformLocalCacheTimingExecution.printerBudget r 0 (axisBank r N S).requests∧
 Ready r N S u∧UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀q,q<N→u.natHeap q=s.natHeap q)∧
 (∀q,¬P.changed q→u.natReg q=s.natReg q):=by
 have layout:=producer_layout r N S B radix budget
 have timingLayout:=timing_layout r N S B budget
 have source:=source_gap r N S radix
 have duration:=(duration_fits r N S radix).trans budget
 have rowWord:=row_fits r N S B budget
 have code:370≤B:=by omega
 obtain ⟨a,prepare,ap,ready,prepareScalars,prepareHeap,prepareRegs⟩:=
  UniformAxisCachePrepareExecution.execution r N S B n x s args pc wb budget
 have placedPrepare:BoundedRuns P.program n x B s (4*Nat.clog 2 (4*r)+66) (setPC a 69):=by
  simpa only[placed,Nat.zero_add,setPC] using
   UniformAssembly.BoundedExecution.placed UniformAxisCacheTimingProgram.prepare_code (by omega) (by omega) prepare
 have awb:WordBound B (setPC a 0):=⟨by simp[setPC],prepare.final_bound.2⟩
 have aheader:UniformLocalCacheTreeIteration.Header r 0 (axisBank r N S).tasks (axisBank r N S).nodes
  (axisBank r N S).requests (setPC a 0):=
  ⟨ready.forest.width,ready.forest.offset,ready.forest.stack,ready.forest.directory,ready.forest.requests⟩
 have aalloc:UniformLocalCacheTimingConductor.Allocation (axisBank r N S).durations
  (axisBank r N S).nodeStarts (axisBank r N S).requestStarts (setPC a 0):=
  ⟨ready.timing.durations,ready.timing.starts,ready.timing.requests⟩
 obtain ⟨ta,t,b,conductor,time,timingCost,printed,dir,tables,base,nodes,requestEnd,scalars,regs,heap⟩:=
  UniformAxisCacheTimingConductor.execution n r 0 (axisBank r N S).tasks (axisBank r N S).nodes
   (axisBank r N S).requests (axisBank r N S).durations (axisBank r N S).nodeStarts
   (axisBank r N S).requestStarts B x (setPC a 0) aheader layout aalloc timingLayout source duration rowWord rfl awb
 have placedConductor:BoundedExecution P.program n x B (setPC a 69) (ta+6+t) (placed 69 b):=by
  have run:=terminal_execution UniformAxisCacheTimingProgram.conductor_code
   (by rw[UniformLocalCacheTimingConductor.program_length];omega) conductor
  simpa only[placed,setPC,Nat.add_zero] using run
 have whole:=placedPrepare.executes placedConductor
 have result:A.Result r N S (placed 69 b):=by
  constructor
  all_goals first
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.tasks
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.nodes
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.requests
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.control
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.leafForward
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.leafTranspose
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.durations
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.nodeStarts
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.requestStarts
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.endNat
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.pool
  | exact (regs _ (Or.inr (by omega)) (Or.inr (by omega))).trans ready.result.endScalar
 have out:Ready r N S (placed 69 b):=by
  refine ⟨⟨printed.durations,printed.nodes,printed.requests⟩,dir.withPC (69+b.pc),tables.withPC (69+b.pc),
   base,nodes,requestEnd,?_,result,?_,?_,?_,?_⟩
  · exact ⟨(regs 6175 (Or.inr (by omega)) (Or.inl (by omega))).trans ready.timing.durations,
    (regs 6176 (Or.inr (by omega)) (Or.inl (by omega))).trans ready.timing.starts,
    (regs 6177 (Or.inr (by omega)) (Or.inl (by omega))).trans ready.timing.requests⟩
  · exact (regs 6160 (Or.inr (by omega)) (Or.inl (by omega))).trans ready.pool
  · exact (regs 6800 (Or.inr (by omega)) (Or.inr (by omega))).trans
     ((prepareRegs 6800 (by unfold UniformAxisCachePrepareProgram.destination;omega)).trans args.radix)
  · exact (regs 6801 (Or.inr (by omega)) (Or.inr (by omega))).trans ready.natFrontier
  · exact (regs 6802 (Or.inr (by omega)) (Or.inr (by omega))).trans ready.scalarFrontier
 refine ⟨ta,t,placed 69 b,?_,time,timingCost,out,
  UniformLocalRectangleDescriptors.natOnly_execution UniformAxisCacheTimingProgram.program_natOnly whole.executes,?_,?_⟩
 · simpa only[Nat.add_assoc] using whole
 · intro q hq
   have lower:N≤(axisBank r N S).durations:=by dsimp[axisBank];omega
   have starts:N≤(axisBank r N S).nodeStarts:=by dsimp[axisBank];omega
   have requests:N≤(axisBank r N S).requestStarts:=by dsimp[axisBank];omega
   exact (heap q hq (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (congrFun prepareHeap q)
 · intro q hq
   exact UniformNewtonTableMachine.Executes.keeps_nat whole.executes
    (UniformAxisCacheTimingProgram.program_keeps q hq)
end
end ExactFourierCircuits.UniformAxisCacheTimingExecution
