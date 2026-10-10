import DFTModelGlobalKernelSourceCore
set_option autoImplicit false
/-! Strengthen the original372 proof by exposing its charged all-gather lower
bound. Literal code, placements and all execution witnesses are unchanged. -/
namespace ExactFourierCircuits.DFTModelGlobalKernelSourceLower
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
open UniformGlobalPackingChildPreparation (programFor packedValues produced_source rows_withPC)
noncomputable section

def gatherCost (W : ℕ) (xs : List UniformSectorPacking.BlockState) : ℕ :=
 (xs.map (fun st=>W*(7*st.width+12)+17)).sum
lemma gatherCost_sum (W : ℕ) (xs : List UniformSectorPacking.BlockState) :
 gatherCost W xs=7*W*(xs.map UniformSectorPacking.BlockState.width).sum+(12*W+17)*xs.length := by
 induction xs with
 | nil=>simp[gatherCost]
 | cons st xs ih=>simp only[gatherCost,List.map_cons,List.sum_cons,List.length_cons] at *;nlinarith[ih]

lemma lower_arith (W V M ell t tree : ℕ) :
 7*W*V+(12*W+17)*M≤t+(tree+43*ell+(12*W+44)*M+7*W*V+66+1) := by nlinarith

theorem execution {W n i frontier : ℕ}
 (gp : UniformGlobalRolePackingMachine.Geometry W) (as : List PhysicalAxis)
 (physicalVolume : UniformSectorPackingMachine.physicalVolume as=gp.volume)
 (physicalLength : as.length=gp.ell) (L : UniformSectorMetadataMachine.Layout)
 (gt : UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states as))
 (v : ℕ → Fin gp.volume → Scalar) (x : Fin n → ℂ) (s : State)
 (sameB : gp.B=L.B) (sameTransposeB : gt.B=L.B)
 (sameVolume : gp.volume=L.total) (sameTransposeVolume : gt.volume=L.total)
 (native : gt.native=gp.destination) (length : as.length=L.ell)
 (header : UniformGlobalRolePackingMachine.Header gp s)
 (banks : UniformGlobalRolePackingMachine.Banks gp as s)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ gp.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ gp.suffix)
 (sectorBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ L.rows)
 (rowsBelow : gp.rows+4*L.ell ≤ L.rows)
 (entry : gt.directory+5*L.total ≤ L.B)
 (directory : L.directory+3*L.total ≤ gt.directory) (code : 372 ≤ L.B)
 (count : s.natReg 102+1=L.ell) (ha : s.natReg 3201=gp.rows) (hd : s.natReg 3202=L.rows)
 (hs : s.natReg 3213=L.suffix) (ht : s.natReg 3214=L.stack) (hq : s.natReg 3215=L.directory)
 (he : s.natReg 4441=gt.directory) (hb : s.natReg 4442=gt.buffer)
 (hn : s.natReg 4531=gt.native) (hv : s.natReg 4530=gt.volume)
 (source : UniformGlobalRolePackingMachine.Source gp v s)
 (hi : i < (UniformProducedSectorChildABI.states as).length)
 (index : s.natReg 5800=i) (fresh : s.natReg 5801=frontier)
 (pc : s.pc=0) (wb : WordBound L.B s) :
 ∃ u ticks,BoundedExecution (programFor W) n x L.B s ticks u ∧
 ticks ≤ W*(213*gp.volume+31)+
  UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
  43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+73 ∧
 u.pc=371 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((UniformProducedSectorChildABI.states as)[i]'hi).pairs
  (gt.buffer+W*((UniformProducedSectorChildABI.states as)[i]'hi).start)
  ((UniformProducedSectorChildABI.states as)[i]'hi).width frontier u ∧
 u.natReg 4122=2^(u.natReg 4120) ∧
 UniformProducedSectorChildABI.GroupedSource W
  (gt.buffer+W*((UniformProducedSectorChildABI.states as)[i]'hi).start)
  ((UniformProducedSectorChildABI.states as)[i]'hi).width
  (UniformAllSectorTransposeMachine.slice
   (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v)
   ((UniformProducedSectorChildABI.states as)[i]'hi)) u ∧
 UniformAllSectorTransposeMachine.Filled gt
  (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v)
  (UniformProducedSectorChildABI.states as).length u ∧
 UniformAllSectorTransposeMachine.Table gt u ∧
 u.natReg 464=(UniformProducedSectorChildABI.states as).length ∧
 u.natReg 4441=gt.directory ∧u.natReg 5801=frontier ∧
 (∀ q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,q < gp.destination → q < gt.buffer → u.scalarHeap q=s.scalarHeap q) ∧
 (∀q,q < gp.suffix → q < L.rows → u.natHeap q=s.natHeap q) ∧
 (∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q) ∧
 gatherCost W (UniformProducedSectorChildABI.states as) ≤ ticks := by
 have firstBound : WordBound gp.B s := by rw [sameB];exact wb
 obtain ⟨t,ticks,packing,packingCost,tp,packed,frame,nat,out⟩ :=
  UniformGlobalRolePackingMachine.execution gp as physicalVolume physicalLength v x s header banks
   widthsBelow permutationsBelow source pc firstBound
 have packing' : BoundedExecution (UniformGlobalRolePackingMachine.programFor W) n x L.B s ticks t := by
  simpa only [sameB] using packing
 have firstLink := UniformGlobalMovementAssembly.first_code
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W) []
 simp only [UniformGlobalRolePackingMachine.program_length] at firstLink
 have placedFirst := UniformBoundedAssembly.boundedExecution_placed firstLink
  (by rw [UniformGlobalRolePackingMachine.program_length];omega) (by omega) packing'
 rw [show placed 0 s=s by cases s;simp [placed]] at placedFirst
 let ready := setPC t 0
 have readyBound := changePC_bound L.B t 0 packing'.final_bound (by omega)
 have retained := UniformGlobalRolePackingMachine.banks_transfer gp as physicalLength banks nat widthsBelow permutationsBelow
 have rawSource : UniformAllSectorTransposeMachine.Source gt
  (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v) ready :=
  produced_source gp as gt _ v ready native (sameTransposeVolume.trans sameVolume.symm) packed
 have keepsArguments : ∀ q,UniformGlobalRolePackingMachine.Protected q → ready.natReg q=s.natReg q := frame.2.2.1
 have rawCount : ready.natReg 102+1=L.ell := by rw [keepsArguments 102 (by unfold UniformGlobalRolePackingMachine.Protected;omega)];exact count
 have arg3201 : ready.natReg 3201=gp.rows := (keepsArguments 3201 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans ha
 have arg3202 : ready.natReg 3202=L.rows := (keepsArguments 3202 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hd
 have arg3213 : ready.natReg 3213=L.suffix := (keepsArguments 3213 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hs
 have arg3214 : ready.natReg 3214=L.stack := (keepsArguments 3214 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans ht
 have arg3215 : ready.natReg 3215=L.directory := (keepsArguments 3215 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hq
 have arg4441 : ready.natReg 4441=gt.directory := (keepsArguments 4441 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans he
 have arg4442 : ready.natReg 4442=gt.buffer := (keepsArguments 4442 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hb
 have arg4531 : ready.natReg 4531=gt.native := (keepsArguments 4531 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hn
 have arg4530 : ready.natReg 4530=gt.volume := (keepsArguments 4530 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hv
 have arg5800 : ready.natReg 5800=i := (keepsArguments 5800 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans index
 have arg5801 : ready.natReg 5801=frontier := (keepsArguments 5801 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans fresh
 have realRows : UniformSectorPackingMachine.Rows as 0 gp.rows ready :=
  rows_withPC as 0 gp.rows t 0 retained.1
 have realWidths : UniformSectorPackingMachine.Widths as ready := by
  intro a ha j;exact retained.2.1 a ha j
 obtain ⟨z,second,zp,child,pow,grouped,filled,table,num,directoryKept,freshKept,start,width,saved,outputs,roots,low,scalar⟩ :=
  UniformProducedSectorChildABI.execution_directory as L gt
   (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v) x ready
   sameTransposeB sameTransposeVolume length (physicalVolume.trans sameVolume) realRows realWidths sectorBelow rowsBelow
   entry directory (by omega) rfl rawCount arg3201 arg3202 arg3213 arg3214 arg3215 arg4441 arg4442
   arg4531 arg4530 rawSource hi arg5800 arg5801 readyBound
 have secondLink := UniformGlobalMovementAssembly.second_code
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W) []
 simp only [UniformGlobalRolePackingMachine.program_length,UniformProducedSectorChildABI.program_length,
  show 153+218=371 by rfl] at secondLink
 have placedSecond := UniformBoundedAssembly.boundedExecution_placed secondLink
  (by rw [UniformProducedSectorChildABI.program_length];omega) (by omega) second
 rw [show placed 153 ready=setPC t 153 by cases t;rfl] at placedSecond
 let u := setPC z 371
 have stop : BoundedExecution (programFor W) n x L.B u 1 u :=
  .halt placedSecond.final_bound (by simp [step,u,setPC,UniformGlobalPackingChildPreparation.halt_at])
 have actual : BoundedExecution (programFor W) n x L.B s
  (ticks+(UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+66+1)) u := by
  convert placedFirst.executes (placedSecond.executes stop) using 1
  rfl
 refine ⟨u,ticks+(UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+66+1),?_,?_,rfl,
  ⟨child.exponent,child.base,child.width,child.frontier⟩,pow,grouped,filled,table,num,directoryKept,freshKept,?_,
  outputs.trans frame.1,roots.trans frame.2.1,?_,?_,UniformKernelPreparationRetention.keeps_args actual,?_⟩
 · exact actual
 · omega
 · intro q hlo hhi
   exact (saved q hlo hhi).trans (keepsArguments q (by unfold UniformGlobalRolePackingMachine.Protected;omega))
 · intro q hp hb
   exact (scalar q (Or.inl hb)).trans (out q (Or.inl hp))

 · intro q first second
   exact (low q second).trans (nat.prefix q first)

 · have widths : ((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum=L.total := by
    rw[UniformProducedSectorChildABI.states,UniformSectorBatchDirectoryMachine.sector_width_sum]
    exact physicalVolume.trans sameVolume
   rw[gatherCost_sum,widths]
   exact lower_arith _ _ _ _ _ _

end
end ExactFourierCircuits.DFTModelGlobalKernelSourceLower
