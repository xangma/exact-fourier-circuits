import UniformGlobalMovementAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalPackingChildPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section

def programFor (W : ℕ) : Program := UniformGlobalMovementAssembly.assembly
 (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W) []
def program : Program := programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W : ℕ) : (programFor W).length=372 := by
 simp only [programFor,UniformGlobalMovementAssembly.assembly_length,
  UniformGlobalRolePackingMachine.program_length,UniformProducedSectorChildABI.program_length,List.length_nil]
lemma halt_at (W : ℕ) : (programFor W)[371]?=some .halt := by
 have h := UniformGlobalMovementAssembly.halt_at (UniformGlobalRolePackingMachine.programFor W)
  (UniformProducedSectorChildABI.programFor W) []
 simpa only [programFor,UniformGlobalRolePackingMachine.program_length,
  UniformProducedSectorChildABI.program_length,List.length_nil,Nat.add_zero,show 153+218=371 by rfl] using h

def packedValues {W : ℕ} (g : UniformGlobalRolePackingMachine.Geometry W)
 (p : Equiv.Perm (Fin g.volume)) (v : ℕ → Fin g.volume → Scalar) (r j : ℕ) : Scalar :=
 if h:j < g.volume then v r (p ⟨j,h⟩) else Scalar.zero

lemma produced_source {W : ℕ} (gp : UniformGlobalRolePackingMachine.Geometry W)
 (as : List PhysicalAxis) (gt : UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states as))
 (p : Equiv.Perm (Fin gp.volume)) (v : ℕ → Fin gp.volume → Scalar) (s : State)
 (native : gt.native=gp.destination) (volume : gt.volume=gp.volume)
 (done : UniformGlobalRolePackingMachine.Filled gp p v W s) :
 UniformAllSectorTransposeMachine.Source gt (packedValues gp p v) s := by
 intro i hi r hr j hj
 have fit := gt.fits i hi
 change j < ((UniformProducedSectorChildABI.states as)[i]'hi).width at hj
 have bound : ((UniformProducedSectorChildABI.states as)[i]'hi).start+j < gp.volume := by
  rw [volume] at fit
  omega
 have val := done r hr ⟨((UniformProducedSectorChildABI.states as)[i]'hi).start+j,bound⟩
 simpa only [UniformSectorTransposeMachine.sourceAddress,UniformAllSectorTransposeMachine.Geometry.local,
  Bool.false_eq_true,ite_false,UniformAllSectorTransposeMachine.slice,packedValues,dite_eq_left bound,
  native,volume,Nat.add_assoc] using val

lemma rows_withPC (as : List PhysicalAxis) (depth base : ℕ) (s : State) (pc : ℕ)
 (h : UniformSectorPackingMachine.Rows as depth base s) :
 UniformSectorPackingMachine.Rows as depth base (setPC s pc) := by
 induction as generalizing depth with
 | nil => trivial
 | cons a as ih =>
  rcases h with ⟨h0,h1,h2,h3,rest⟩
  exact ⟨h0,h1,h2,h3,ih (depth+1) rest⟩

/-- Actual all-W packing153 followed by actual produced gather/ABI218.
The latter's source bank, generated directory and four child arguments are
derived from the real first execution. Its next recursive child remains open. -/
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
 (∀ q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,q < gp.destination → q < gt.buffer → u.scalarHeap q=s.scalarHeap q) := by
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
 obtain ⟨z,second,zp,child,pow,grouped,filled,table,start,width,saved,outputs,roots,low,scalar⟩ :=
  UniformProducedSectorChildABI.execution as L gt
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
  .halt placedSecond.final_bound (by simp [step,u,setPC,halt_at])
 refine ⟨u,ticks+(UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+66+1),?_,?_,rfl,
  ⟨child.exponent,child.base,child.width,child.frontier⟩,pow,grouped,filled,table,?_,
  outputs.trans frame.1,roots.trans frame.2.1,?_⟩
 · convert placedFirst.executes (placedSecond.executes stop) using 1
   rfl
 · omega
 · intro q hlo hhi
   exact (saved q hlo hhi).trans (keepsArguments q (by unfold UniformGlobalRolePackingMachine.Protected;omega))
 · intro q hp hb
   exact (scalar q (Or.inl hb)).trans (out q (Or.inl hp))

end
end ExactFourierCircuits.UniformGlobalPackingChildPreparation
