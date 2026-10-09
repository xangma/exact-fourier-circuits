import UniformAxisCacheHorizon
import UniformAxisCacheInputs
import UniformLocalRectangleWorkspaceHeaders
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestHeader
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheTimingExecution (Ready)

/-- All immutable forest registers are installed before requests. The request
program's checked high-register frame retains these real writes. -/
def ops:List Op:=[.binary .add 6660 6811 6900,.binary .add 6661 4281 6900,
 .binary .add 6664 6817 6900,.binary .add 6665 6816 6900,
 .binary .add 6690 6167 6900,.binary .mul 6691 6905 6902,
 .binary .add 6691 6167 6691,.binary .add 6692 6400 6900]
lemma ops_length:ops.length=8:=rfl
def changed:List ℕ:=[6660,6661,6664,6665,6690,6691,6692]

structure Prepared (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)) (s:State):Prop where
 nodes:s.natReg 6660=(UniformJointCacheAllocation.axis c n j).nodes
 count:s.natReg 6661=UniformLocalCacheTimingMetadata.nodeCount (Seed.radix n j) 0
   (UniformJointCacheAllocation.axis c n j).requests
 starts:s.natReg 6664=(UniformJointCacheAllocation.axis c n j).nodeStarts
 durations:s.natReg 6665=(UniformJointCacheAllocation.axis c n j).durations
 original:s.natReg 6690=Seed.directoryBase n+2*j.val
 conjugate:s.natReg 6691=UniformAllAxisConjugatePreparation.directoryBase n+2*j.val
 rows:s.natReg 6692=UniformLocalRectangleWorkspaceHeaders.z n

lemma registers (s:State) (q:ℕ) (hq:q∉changed):
 (applyBlock ops s).natReg q=s.natReg q:=by
 simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
 simp [ops,applyBlock,Op.apply,writeNat,next,hq.1,hq.2.1,hq.2.2.1,
  hq.2.2.2.1,hq.2.2.2.2.1,hq.2.2.2.2.2.1,hq.2.2.2.2.2.2]

/-- Eight charged copies/arithmetic operations derive the forest's immutable
header from actual370 outputs and the real startup/workspace banks. -/
theorem execution (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n))
 (p:Program) (base:ℕ) (code:BlockAt ops p base) (room:base+8≤A.envelope c n)
 (x:Fin n→ℂ) (s:State)
 (ready:Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) s)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (pc:s.pc=base) (wb:WordBound (A.envelope c n) s):
 let u:=applyBlock ops s
 BoundedRuns p n x (A.envelope c n) s 8 u∧u.pc=base+8∧Prepared c n j u∧
 Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Selected c n j.val u∧Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.scalarReg=s.scalarReg∧
 u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀q,q∉changed→u.natReg q=s.natReg q):=by
 let u:=applyBlock ops s
 have fit:=arithmetic c n hn
 have directoryFit:Seed.directoryBase n+2*C.ell n+2*C.ell n≤A.envelope c n:=by
  have small:=(UniformAllAxisConjugatePreparation.word_setup hn).2.2
  have slab:=UniformAxisCachePreparationRetention.slab_above_seed_word c n
  have before:UniformJointAllocation.slab c n≤A.envelope c n:=by unfold A.envelope;omega
  simpa only [UniformAllAxisConjugatePreparation.directoryBase,C.ell,UniformJointCacheAllocation.ell,
    Seed.axisCount] using small.trans (slab.trans before)
 have nodes:=wb.2.1 6811
 have count:=wb.2.1 4281
 have starts:=wb.2.1 6817
 have durations:=wb.2.1 6816
 have rows:=wb.2.1 6400
 have safe:readable ops s∧peak ops s≤A.envelope c n:=by
  constructor
  · simp [ops,readable,Op.readable,evalNat]
  · simp [ops,peak,Op.peak,Op.apply,evalNat,writeNat,next,selected.control.zero,
     selected.source,selected.control.count,selected.control.two]
    omega
 have run:=block_runs ops p base n (A.envelope c n) x s code pc wb
  (by rw [ops_length];exact room) safe.1 safe.2
 have frame:=registers s
 have out:Prepared c n j u:=by
  constructor
  · simpa [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero,UniformJointCacheAllocation.axis,natAt,scalarAt]
      using ready.result.nodes
  · simpa [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero,UniformJointCacheAllocation.axis,natAt,scalarAt]
      using ready.nodeCount
  · simpa [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero,UniformJointCacheAllocation.axis,natAt,scalarAt]
      using ready.result.nodeStarts
  · simpa [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero,UniformJointCacheAllocation.axis,natAt,scalarAt]
      using ready.result.durations
  · simp [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero,selected.source]
  · simp [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.source,
      selected.control.count,selected.control.two,UniformAllAxisConjugatePreparation.directoryBase,
      C.ell,UniformJointCacheAllocation.ell,Seed.axisCount,Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  · simpa [u,ops,applyBlock,Op.apply,evalNat,writeNat,next,selected.control.zero]
      using bank ⟨0,by decide⟩
 have result:UniformAxisCacheAllocationMachine.Result (Seed.radix n j)
   (natAt c n j.val) (scalarAt c n j.val) u:=by
  constructor
  all_goals first
  | exact (frame _ (by simp [changed])).trans ready.result.tasks
  | exact (frame _ (by simp [changed])).trans ready.result.nodes
  | exact (frame _ (by simp [changed])).trans ready.result.requests
  | exact (frame _ (by simp [changed])).trans ready.result.control
  | exact (frame _ (by simp [changed])).trans ready.result.leafForward
  | exact (frame _ (by simp [changed])).trans ready.result.leafTranspose
  | exact (frame _ (by simp [changed])).trans ready.result.durations
  | exact (frame _ (by simp [changed])).trans ready.result.nodeStarts
  | exact (frame _ (by simp [changed])).trans ready.result.requestStarts
  | exact (frame _ (by simp [changed])).trans ready.result.endNat
  | exact (frame _ (by simp [changed])).trans ready.result.pool
  | exact (frame _ (by simp [changed])).trans ready.result.endScalar
 have directory:∀D k visits,UniformLocalCacheTreeExecution.Directory D k visits s→
   UniformLocalCacheTreeExecution.Directory D k visits u:=by
  intro D k visits hd
  induction visits generalizing k with
  | nil=>trivial
  | cons q qs ih=>
   refine ⟨?_,ih (k+1) hd.2⟩
   intro f
   exact hd.1 f
 have finalReady:Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u:=
  ⟨⟨fun k hk=>ready.printed.durations k hk,fun k hk=>ready.printed.nodes k hk,
     fun k hk i hi=>ready.printed.requests k hk i hi⟩,
   directory _ _ _ ready.directory,
   (fun q hq large positive i j h f=>ready.tables q hq large positive i j h f),
   (frame _ (by simp [changed])).trans ready.requestBase,
   (frame _ (by simp [changed])).trans ready.nodeCount,
   (frame _ (by simp [changed])).trans ready.requestEnd,
   ⟨(frame _ (by simp [changed])).trans ready.timing.durations,
    (frame _ (by simp [changed])).trans ready.timing.starts,
    (frame _ (by simp [changed])).trans ready.timing.requests⟩,result,
   (frame _ (by simp [changed])).trans ready.pool,
   (frame _ (by simp [changed])).trans ready.radix,
   (frame _ (by simp [changed])).trans ready.natFrontier,
   (frame _ (by simp [changed])).trans ready.scalarFrontier⟩
 have finalSelected:Selected c n j.val u:=by
  refine ⟨?_,?_,(frame _ (by simp [changed])).trans selected.radix,
   (frame _ (by simp [changed])).trans selected.source,
   (frame _ (by simp [changed])).trans selected.axisIndex⟩
  · exact ⟨(frame _ (by simp [changed])).trans selected.control.zero,
    (frame _ (by simp [changed])).trans selected.control.one,
    (frame _ (by simp [changed])).trans selected.control.two,
    (frame _ (by simp [changed])).trans selected.control.nine,
    (frame _ (by simp [changed])).trans selected.control.source,
    (frame _ (by simp [changed])).trans selected.control.count,
    (frame _ (by simp [changed])).trans selected.control.index⟩
  · exact ⟨(frame _ (by simp [changed])).trans selected.frontiers.natFrontier,
    (frame _ (by simp [changed])).trans selected.frontiers.scalarFrontier⟩
 refine ⟨?_,?_,out,finalReady,finalSelected,?_,?_,rfl,rfl,rfl,rfl,rfl,frame⟩
 · simpa only [ops_length] using run
 · rw [UniformAxisCacheAllocationMachine.block_pc,pc,ops_length]
 · exact UniformAxisCacheInputs.transport c n j.val hn x s u input ⟨rfl,rfl,rfl,rfl⟩
    (fun _ _=>rfl) (fun q lo hi=>frame q (by simp only [changed,List.mem_cons,List.not_mem_nil,or_false];omega))
 · intro f
   exact (frame _ (by have h:=f.isLt;simp only [changed,List.mem_cons,List.not_mem_nil,or_false];omega)).trans (bank f)

end ExactFourierCircuits.UniformAxisCacheForestHeader
