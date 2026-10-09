import UniformGlobalSectorDirectoryRetention
import UniformConditionalSectorReturn
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelPreparationRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
open UniformGlobalPackingChildPreparation (programFor packedValues produced_source rows_withPC)
noncomputable section

def writesArgs:Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => decide (5900 ≤ d ∧d ≤ 5910)
 | _ => false
lemma writes_relocate (b ret:ℕ) (i:Instruction):writesArgs (relocate b ret i)=writesArgs i:=by
 cases i <;>rfl
lemma program_free (W:ℕ):(programFor W).all (fun i=> !writesArgs i)=true:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly,List.all_append,List.all_map,
  Function.comp_def,writes_relocate,
  UniformGlobalRolePackingMachine.programFor,UniformProducedSectorChildABI.programFor,UniformAssembly.embed,
  UniformProducedSectorTransposePreparation.programFor,UniformProducedSectorBatchPreparation.programFor,
  UniformMultiAxisSectorMetadataPreparation.program,UniformSectorBatchDirectoryMachine.programFor,
  UniformAllSectorTransposeMachine.programFor,List.all_cons,List.all_nil]
 rfl
lemma keeps_args {W B n ticks:ℕ} {x:Fin n → ℂ} {s u:State}
 (run:BoundedExecution (programFor W) n x B s ticks u):
 ∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q:=by
 intro q low high
 apply UniformNewtonTableMachine.Executes.keeps_nat run.executes
 intro i hi
 have free:=List.all_eq_true.mp (program_free W) i hi
 cases i <;>simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals intro equal;subst_vars
 all_goals simp[writesArgs,low,high] at free

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
 (∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q) := by
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
  outputs.trans frame.1,roots.trans frame.2.1,?_,?_,keeps_args actual⟩
 · exact actual
 · omega
 · intro q hlo hhi
   exact (saved q hlo hhi).trans (keepsArguments q (by unfold UniformGlobalRolePackingMachine.Protected;omega))
 · intro q hp hb
   exact (scalar q (Or.inl hb)).trans (out q (Or.inl hp))

 · intro q first second
   exact (low q second).trans (nat.prefix q first)

end
end ExactFourierCircuits.UniformKernelPreparationRetention
