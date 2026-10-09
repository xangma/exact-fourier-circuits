import UniformAxisCacheAdvanceMachine
import UniformAxisCacheTimingExecution
import UniformMultiAxisSectorMetadataPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheSelectedPreparation
open UniformMachine UniformAxisCacheStartupMachine
open UniformAxisCacheTimingExecution (Ready)

def natAt (c:A.Constants)(n j:ℕ):ℕ:=
 C.natStart c n+C.offsetSum
  (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j
def scalarAt (c:A.Constants)(n j:ℕ):ℕ:=
 C.scalarStart c n+C.offsetSum
  (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j

structure Selected (c:A.Constants)(n j:ℕ)(s:State):Prop where
 control:Control n j s
 frontiers:Frontiers c n j s
 radix:s.natReg 6800=UniformAllAxisSeedPreparation.radixAt n j
 source:s.natReg 6167=Seed.directoryBase n+2*j
 axisIndex:s.natReg 4200=j

lemma Selected.withPC {c:A.Constants}{n j pc:ℕ}{s:State}(h:Selected c n j s):
 Selected c n j (UniformTensorMonomialMachine.setPC s pc):=
 ⟨⟨h.control.zero,h.control.one,h.control.two,h.control.nine,h.control.source,h.control.count,h.control.index⟩,
  ⟨h.frontiers.natFrontier,h.frontiers.scalarFrontier⟩,h.radix,h.source,h.axisIndex⟩

lemma control_transport {n j:ℕ}{s u:State}(h:Control n j s)
 (frame:∀q,¬UniformAxisCacheTimingProgram.changed q→u.natReg q=s.natReg q):
 Control n j u:=by
 constructor
 all_goals first
 | exact (frame 6900 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.zero
 | exact (frame 6901 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.one
 | exact (frame 6902 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.two
 | exact (frame 6903 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.nine
 | exact (frame 6904 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.source
 | exact (frame 6905 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.count
 | exact (frame 6906 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans h.index

/-- The physically selected positive-length axis supplies the ordinary inputs
to literal370. The global envelope and actual radix lower bound are derived. -/
theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(j:Fin (C.ell n))
 (x:Fin n→ℂ)(s:State)(selected:Selected c n j.val s)
 (pc:s.pc=0)(wb:WordBound (A.envelope c n) s):
 ∃ta t u,BoundedExecution UniformAxisCacheTimingProgram.program n x (A.envelope c n) s
  (4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t) u∧
 ta≤(2*Seed.radix n j+1)*UniformLocalCacheTreeExecution.nodeBudget (Seed.radix n j)+18∧
 t≤UniformLocalCacheTimingExecution.printerBudget (Seed.radix n j) 0
  (UniformJointCacheAllocation.axis c n j).requests∧
 Ready (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 Selected c n j.val u∧UniformLocalRectangleDescriptors.ScalarFrame s u∧
 (∀q,q<natAt c n j.val→u.natHeap q=s.natHeap q)∧
 (∀q,¬UniformAxisCacheTimingProgram.changed q→u.natReg q=s.natReg q):=by
 have radix:2≤Seed.radix n j:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 have budget:=UniformAxisCacheAllocationMachine.selected_wordBudget c n hn j
 have args:UniformAxisCacheAllocationMachine.Arguments (Seed.radix n j)
   (natAt c n j.val) (scalarAt c n j.val) s:=
  ⟨selected.radix.trans (UniformAllAxisSeedPreparation.radixAt_eq n j),
   selected.frontiers.natFrontier,selected.frontiers.scalarFrontier⟩
 obtain ⟨ta,t,u,run,time,cost,ready,scalars,heap,regs⟩:=
  UniformAxisCacheTimingExecution.execution (Seed.radix n j) (natAt c n j.val)
   (scalarAt c n j.val) (A.envelope c n) n x s args radix pc wb budget
 have out:Selected c n j.val u:=by
  refine ⟨control_transport selected.control regs,⟨ready.natFrontier,ready.scalarFrontier⟩,
   ready.radix.trans (UniformAllAxisSeedPreparation.radixAt_eq n j).symm,?_,?_⟩
  · exact (regs 6167 (by unfold UniformAxisCacheTimingProgram.changed;omega)).trans selected.source
  · exact (UniformAxisCacheTimingProgram.axis_index_frame run).trans selected.axisIndex
 exact ⟨ta,t,u,run,time,cost,ready,out,scalars,heap,regs⟩

end ExactFourierCircuits.UniformAxisCacheSelectedPreparation
