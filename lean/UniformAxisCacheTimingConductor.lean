import UniformAxisCacheTimingGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTimingConductor
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheTreeExecution UniformLocalCacheTimingMetadata
open UniformLocalCacheTimingInitialization UniformLocalCacheTimingExecution
open UniformLocalCacheTimingPlacement UniformLocalCacheTimingConductor
noncomputable section

lemma directory_transport (D U:ℕ)(L:List UniformLocalCacheTreeMachine.Visit)(s u:State)(k:ℕ)
 (dir:Directory D k L s)(extent:D+7*(k+L.length)≤U)
 (same:∀q,q<U→u.natHeap q=s.natHeap q):Directory D k L u:=by
 induction L generalizing k with
 | nil=>trivial
 | cons q qs ih=>
  refine ⟨?_,ih (k+1) dir.2 (by simpa only[List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using extent)⟩
  intro f
  have hf:=f.isLt
  rw[same _ (by simp only[List.length_cons] at extent;omega)]
  exact dir.1 f

lemma sources_transport (D U:ℕ)(L:List UniformLocalCacheTreeMachine.Visit)(s u:State)
 (dir:Directory D 0 L s)(rows:RequestTables L s)(same:∀q,q<U→u.natHeap q=s.natHeap q)
 (dirEnd:D+7*L.length≤U)
 (source:∀q∈L,q.rectangleBase+7*UniformLocalRectangleDescriptors.emittedCount q.task.width+4≤U):
 Directory D 0 L u∧RequestTables L u:=by
 refine ⟨directory_transport D U L s u 0 dir (by simpa only[Nat.zero_add] using dirEnd) same,?_⟩
 intro q hq big positive i j bound f
 have endRow:=source q hq
 have count:UniformLocalRectangleDescriptors.emittedCount q.task.width=
  UniformWorkspacePlanner.chunkCount (q.task.width-q.task.width/2) (UniformWorkspacePlanner.selected q.task.width)*
   UniformWorkspacePlanner.chunkCount (q.task.width/2) (UniformWorkspacePlanner.selected q.task.width):=by
  simp [UniformLocalRectangleDescriptors.emittedCount,show ¬q.task.width<2 by omega,show UniformWorkspacePlanner.selected q.task.width≠0 by omega]
 have hf:=f.isLt
 rw[same _ (by rw[count] at endRow;omega)]
 exact rows q hq big positive i j bound f

theorem execution (n v o W D R U V T B:ℕ)(x:Fin n→ℂ)(s:State)
 (header:UniformLocalCacheTreeIteration.Header v o W D R s)
 (producerLayout:UniformLocalCacheTreeExecution.Layout v o W D R B)
 (allocation:Allocation U V T s)
 (timingLayout:UniformCacheTimingReverseData.Layout D U V T (nodeCount v o R) (requestCount v o R) B)
 (source:R+7*requestCount v o R+4≤U)
 (duration:UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v)≤B)
 (rowWord:20000*(v+1)≤B)(hp:s.pc=0)(hs:WordBound B s):∃ta t u,
 BoundedExecution UniformLocalCacheTimingConductor.program n x B s (ta+6+t) u∧
 ta≤(2*v+1)*nodeBudget v+18∧t≤printerBudget v o R∧Printed v o R U V T u∧
 Directory D 0 (rootVisits v o R) u∧RequestTables (rootVisits v o R) u∧
 u.natReg 4274=R∧u.natReg 4281=nodeCount v o R∧u.natReg 4282=R+7*requestCount v o R∧
 UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀r,(r<290∨4295≤r)→(r<6500∨6600≤r)→u.natReg r=s.natReg r)∧
 (∀q,q<W→(q<U∨U+nodeCount v o R≤q)→(q<V∨V+nodeCount v o R≤q)→
  (q<T∨T+requestCount v o R≤q)→u.natHeap q=s.natHeap q):=by
 have code:301≤B:=by nlinarith [Nat.zero_le v]
 obtain ⟨a,ta,producer,time,ap,dir,rows,nodes,requests,low⟩:=
  UniformLocalCacheTreeExecution.execution n v o W D R B x s header producerLayout hp hs
 have placedProducer:BoundedRuns UniformLocalCacheTimingConductor.program n x B s ta (setPC a 173):=by
  simpa only [placed,Nat.zero_add,setPC] using UniformAssembly.BoundedExecution.placed producer_code (by omega) (by omega) producer
 have da:a.natReg 4273=D:=
  (UniformNewtonTableMachine.Executes.keeps_nat producer.executes (producer_keeps_sources 4273 (Or.inl rfl))).trans header.directory
 have ra:a.natReg 4274=R:=
  (UniformNewtonTableMachine.Executes.keeps_nat producer.executes (producer_keeps_sources 4274 (Or.inr rfl))).trans header.requests
 have aa:Allocation U V T (setPC a 173):=
  ⟨(execution_natFrame producer 6175 (by omega)).trans allocation.durations,
   (execution_natFrame producer 6176 (by omega)).trans allocation.starts,
   (execution_natFrame producer 6177 (by omega)).trans allocation.requests⟩
 have installing:=block_runs installer UniformLocalCacheTimingConductor.program 173 n B x (setPC a 173) installer_code rfl
  placedProducer.final_bound (by change 173+6≤B;omega)
  (by simp [installer,readable,Op.readable]) (by
   have h0:=producer.final_bound.2.1 4273
   have h1:=producer.final_bound.2.1 4274
   have h2:=producer.final_bound.2.1 6175
   have h3:=producer.final_bound.2.1 6176
   have h4:=producer.final_bound.2.1 6177
   simp [installer,peak,Op.peak,Op.apply,writeNat,next,setPC]
   all_goals omega)
 let b:=applyBlock installer (setPC a 173)
 have bp:b.pc=179:=by rw [applyBlock_pc];rfl
 have bdir:=installer_source_tables (dir.withPC 173) (rows.withPC 173)
 have bb:WordBound B (setPC b 0):=⟨by simp [setPC],installing.final_bound.2⟩
 obtain ⟨t,u,timing,budget,printed,frame,scalars,registers⟩:=execute_from_printed n v o D R U V T B x (setPC b 0)
  ((installer_addresses D R U V T (setPC a 173) da ra aa).withPC 0)
  (bdir.1.withPC 0) (bdir.2.withPC 0) nodes requests timingLayout source duration rowWord rfl bb
 have placedTiming:BoundedExecution UniformLocalCacheTimingConductor.program n x B b t (placed 179 u):=by
  have hh:=terminal_execution timing_code (by rw [UniformCacheTimingProgram.program_length];omega) timing
  have start:placed 179 (setPC b 0)=b:=by simp [placed,setPC,←bp]
  rw [start] at hh
  exact hh
 have whole:=placedProducer.executes (installing.executes placedTiming)
 have lowU:∀q,q<U→u.natHeap q=b.natHeap q:=by
  intro q hq
  exact frame q (Or.inl hq) (Or.inl (by have h:=timingLayout.durations;omega))
   (Or.inl (by have h:=timingLayout.durations;have h':=timingLayout.starts;omega))
 have sources:=sources_transport D U (rootVisits v o R) b u bdir.1 bdir.2 lowU
  timingLayout.directory (root_source v o R U source)
 have ur:u.natReg 4274=R:=(registers 4274 (Or.inl (by omega))).trans ra
 have un:u.natReg 4281=nodeCount v o R:=(registers 4281 (Or.inl (by omega))).trans nodes
 have ue:u.natReg 4282=R+7*requestCount v o R:=(registers 4282 (Or.inl (by omega))).trans requests
 refine ⟨ta,t,placed 179 u,?_,time,budget,?_,sources.1.withPC (179+u.pc),
  sources.2.withPC (179+u.pc),ur,un,ue,
  UniformLocalRectangleDescriptors.natOnly_execution UniformLocalCacheTimingConductor.program_natOnly whole.executes,?_,?_⟩
 · have length:installer.length=6:=rfl
   simpa only [length,Nat.add_assoc] using whole
 · exact ⟨printed.durations,printed.nodes,printed.requests⟩
 · intro r producerReg timingReg
   exact UniformNewtonTableMachine.Executes.keeps_nat whole.executes (program_keeps r producerReg timingReg)
 · intro q hq hU hV hT
   exact (frame q hU hV hT).trans (low q hq)
end
end ExactFourierCircuits.UniformAxisCacheTimingConductor
