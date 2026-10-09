import UniformProducedSectorTransposePreparation
import UniformSectorChildEntryPreparation
import UniformSectorPhysicalBinaryAction

/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.2, Lemma 4.1, PDF p. 19, and §4.3, proof of Proposition 4.2, p. 20; recursive batching is §2.6, Theorem 2.6, pp. 11–12 (`net:tensor-bound`).

Literal producer, gather and argument-loader instructions implement contiguous sector/role batches. Register numbers and the child ABI are implementation bookkeeping without a separate paper lemma; this theorem ends at child entry and does not assume the child transform.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedSectorChildABI
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- Runtime ordinal, fresh frontier and the original generated-directory
address are ordinary arguments. The actual five-word row is loaded here. -/
def setup : List Op := [.literal 5802 0,.literal 5803 1,.literal 5804 5,
 .mul 5805 5800 5804,.add 5805 4441 5805,.getNat 4120 5805,
 .add 5805 5805 5803,.getNat 4122 5805,.add 5805 5805 5803,
 .getNat 4121 5805,.add 5805 5805 5803,.getNat 5807 5805,
 .add 5805 5805 5803,.getNat 5808 5805,.add 4123 5801 5802]

def programFor (W : ℕ) : Program := UniformAssembly.embed []
 (UniformProducedSectorTransposePreparation.programFor W) (setup.map Op.code ++ [.halt]) 202
def program : Program := programFor ExplicitSeedBudget.paddedRoles
lemma setup_length : setup.length = 15 := rfl
lemma program_length (W : ℕ) : (programFor W).length = 218 := by
 simp only [programFor,UniformAssembly.embed,List.length_append,List.length_map,List.length_nil,Nat.zero_add,
  UniformProducedSectorTransposePreparation.program_length,setup_length,List.length_singleton]
lemma setup_code (W : ℕ) : BlockAt setup (programFor W) 202 := by
 intro i hi
 unfold programFor UniformAssembly.embed
 simp only [List.nil_append,List.length_nil]
 rw [List.getElem?_append_right (by rw [List.length_map,
  UniformProducedSectorTransposePreparation.program_length];omega)]
 simp only [List.length_map,UniformProducedSectorTransposePreparation.program_length]
 rw [show 202+i-202=i by omega,List.getElem?_append_left (by simpa using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma halt_at (W : ℕ) : (programFor W)[217]? = some .halt := by
 unfold programFor
 unfold UniformAssembly.embed
 simp only [List.nil_append,List.length_nil]
 rw [List.getElem?_append_right (by rw [List.length_map,
  UniformProducedSectorTransposePreparation.program_length];omega)]
 simp only [List.length_map,UniformProducedSectorTransposePreparation.program_length]
 simp only [show 217-202=15 by omega]
 rw [List.getElem?_append_right (by rw [List.length_map,setup_length]) ]
 rfl

def writesArguments : Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
   [5800,5801,4441].contains d
 | _ => false
lemma relocate_arguments (b ret : ℕ) (i : Instruction) :
 writesArguments (relocate b ret i) = writesArguments i := by cases i <;> rfl
lemma producer_free (W : ℕ) :
 (UniformProducedSectorTransposePreparation.programFor W).all (fun i => !writesArguments i) = true := by
 simp only [UniformProducedSectorTransposePreparation.programFor,
  UniformProducedSectorBatchPreparation.programFor,List.all_append,List.all_map,
  Function.comp_def,relocate_arguments,List.all_cons,List.all_nil]
 rfl
lemma producer_keeps (W q : ℕ) (hq : q ∈ ([5800,5801,4441] : List ℕ)) :
 ∀ i ∈ UniformProducedSectorTransposePreparation.programFor W,
  UniformNewtonTableMachine.KeepsNat q i := by
 intro i hi
 have free := List.all_eq_true.mp (producer_free W) i hi
 cases i <;> simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals intro equal;subst_vars
 all_goals simp [writesArguments,hq] at free
lemma execution_keeps {W B n t : ℕ} {x : Fin n → ℂ} {s u : State}
 (h : BoundedExecution (UniformProducedSectorTransposePreparation.programFor W) n x B s t u) :
 ∀ q ∈ ([5800,5801,4441] : List ℕ),u.natReg q = s.natReg q := by
 intro q hq
 exact UniformNewtonTableMachine.Executes.keeps_nat h.executes (producer_keeps W q hq)

structure Args (ordinal frontier directory : ℕ) (s : State) : Prop where
 index : s.natReg 5800 = ordinal
 frontier : s.natReg 5801 = frontier
 directory : s.natReg 4441 = directory

lemma setup_header {W E A i frontier : ℕ} {st : UniformSectorPacking.BlockState} {s : State}
 (h : Args i frontier E s) (cell : UniformSectorBatchDirectoryMachine.BatchCell W E A i st s) :
 UniformSectorChildEntryPreparation.ChildHeader st.pairs (A+W*st.start) st.width frontier (applyBlock setup s) ∧
 (applyBlock setup s).natReg 5807 = st.start ∧
 (applyBlock setup s).natReg 5808 = W*st.width := by
 rcases cell with ⟨q,w,b,start,batch⟩
 simp only [Nat.add_assoc] at q w b start batch
 refine ⟨?_,?_,?_⟩
 · constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h.index,h.frontier,h.directory,
    q,w,b,start,batch,Nat.mul_comm i 5,Nat.add_assoc]
 all_goals simp [setup,applyBlock,Op.apply,writeNat,next,h.index,h.frontier,h.directory,
  q,w,b,start,batch,Nat.mul_comm i 5,Nat.add_assoc]

lemma setup_safe {W E A i frontier B : ℕ} {st : UniformSectorPacking.BlockState} {s : State}
 (h : Args i frontier E s) (cell : UniformSectorBatchDirectoryMachine.BatchCell W E A i st s)
 (row : E+5*(i+1) ≤ B) (five : 5 ≤ B) (wb : WordBound B s) :
 readable setup s ∧ peak setup s ≤ B := by
 have qB := (wb.2.2.1 _ _ cell.1).2
 have wB := (wb.2.2.1 _ _ cell.2.1).2
 have bB := (wb.2.2.1 _ _ cell.2.2.1).2
 have sB := (wb.2.2.1 _ _ cell.2.2.2.1).2
 have batchB := (wb.2.2.1 _ _ cell.2.2.2.2).2
 have fB : frontier ≤ B := by simpa only [h.frontier] using wb.2.1 5801
 rcases cell with ⟨q,w,b,start,batch⟩
 simp only [Nat.add_assoc] at q w b start batch
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.index,h.frontier,h.directory,q,w,b,start,batch,Nat.mul_comm i 5,Nat.add_assoc]
 omega

lemma setup_frame (s : State) :
 (applyBlock setup s).natHeap = s.natHeap ∧
 (applyBlock setup s).scalarHeap = s.scalarHeap ∧
 (applyBlock setup s).scalarReg = s.scalarReg ∧
 (applyBlock setup s).outputs = s.outputs ∧
 (applyBlock setup s).rootOrders = s.rootOrders ∧
 ∀ q,(q < 4120 ∨ 4124 ≤ q) → (q < 5802 ∨ 5809 ≤ q) →
  (applyBlock setup s).natReg q = s.natReg q := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q h0 h1
 simp (disch := omega) [setup,applyBlock,Op.apply,writeNat,next]

def states (as : List UniformSectorPackingMachine.PhysicalAxis) :=
 UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)

/-- Raw numeric role-major arrays, including dependency tags. This is a data
ABI, not an assumed transform or recursive execution. -/
def GroupedSource (W base width : ℕ) (v : ℕ → ℕ → Scalar) (s : State) : Prop :=
 ∀ r,r < W → ∀ j,j < width → s.scalarHeap (base+r*width+j) = some (v r j)

/-- The literal202 producer/gather and the literal15 loader execute
continuously. No generated sector table, child header or contiguous child
array is an entry premise. The recursive child is the next open obligation. -/
theorem execution {W n a i frontier : ℕ}
 (as : List UniformSectorPackingMachine.PhysicalAxis) (L : UniformSectorMetadataMachine.Layout)
 (g : UniformAllSectorTransposeMachine.Geometry W false (states as))
 (v : ℕ → ℕ → Scalar) (x : Fin n → ℂ) (s : State)
 (sameB : g.B=L.B) (sameVolume : g.volume=L.total)
 (hlen : as.length=L.ell) (hvolume : UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows : UniformSectorPackingMachine.Rows as 0 a s) (widths : UniformSectorPackingMachine.Widths as s)
 (below : ∀ ax ∈ as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep : a+4*L.ell ≤ L.rows) (entry : g.directory+5*L.total ≤ L.B)
 (directory : L.directory+3*L.total ≤ g.directory) (code : 218 ≤ L.B) (pc : s.pc=0)
 (count : s.natReg 102+1=L.ell) (ha : s.natReg 3201=a) (hd : s.natReg 3202=L.rows)
 (hs : s.natReg 3213=L.suffix) (ht : s.natReg 3214=L.stack) (hq : s.natReg 3215=L.directory)
 (he : s.natReg 4441=g.directory) (hb : s.natReg 4442=g.buffer)
 (native : s.natReg 4531=g.native) (volume : s.natReg 4530=g.volume)
 (source : UniformAllSectorTransposeMachine.Source g v s)
 (hi : i < (states as).length) (index : s.natReg 5800=i) (fresh : s.natReg 5801=frontier)
 (wb : WordBound L.B s) :
 ∃ u,BoundedExecution (programFor W) n x L.B s
  (UniformSectorMetadataMachine.treeCost
    (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(states as).length+7*W*L.total+66) u ∧ u.pc=217 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((states as)[i]'hi).pairs
  (g.buffer+W*((states as)[i]'hi).start) ((states as)[i]'hi).width frontier u ∧
 u.natReg 4122=2^(u.natReg 4120) ∧
 GroupedSource W (g.buffer+W*((states as)[i]'hi).start) ((states as)[i]'hi).width
  (UniformAllSectorTransposeMachine.slice v ((states as)[i]'hi)) u ∧
 UniformAllSectorTransposeMachine.Filled g v (states as).length u ∧
 UniformAllSectorTransposeMachine.Table g u ∧
 u.natReg 5807=((states as)[i]'hi).start ∧
 u.natReg 5808=W*((states as)[i]'hi).width ∧
 (∀ q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,q < L.rows → u.natHeap q=s.natHeap q) ∧
 UniformScalarCopyMachine.Outside g.buffer (W*g.volume) s.scalarHeap u := by
 obtain ⟨t,run,tp,filled,table,num,saved,outputs,roots,low,out⟩ :=
  UniformProducedSectorTransposePreparation.execution as L g v x s sameB sameVolume hlen hvolume
   rows widths below sep entry directory (by omega) pc count ha hd hs ht hq he hb native volume source wb
 have link := UniformAssembly.embed_code []
  (UniformProducedSectorTransposePreparation.programFor W) (setup.map Op.code ++ [.halt]) 202
 simp only [List.length_nil] at link
 have moved := UniformBoundedAssembly.boundedExecution_placed link
  (by rw [UniformProducedSectorTransposePreparation.program_length];omega) (by omega) run
 rw [show placed 0 s=s by cases s;simp [placed]] at moved
 let ready := setPC t 202
 have kept := execution_keeps run
 have args : Args i frontier g.directory ready :=
  ⟨(kept 5800 (by simp)).trans index,(kept 5801 (by simp)).trans fresh,
   (kept 4441 (by simp)).trans he⟩
 have cell : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer i ((states as)[i]'hi) ready :=
  table i hi
 have row : g.directory+5*(i+1) ≤ L.B := by
  have bound := g.entry
  rw [sameB] at bound
  nlinarith
 have safe := setup_safe args cell row (by omega) moved.final_bound
 have second := block_runs setup (programFor W) 202 n L.B x ready (setup_code W) rfl moved.final_bound
  (by rw [setup_length];omega) safe.1 safe.2
 let u := applyBlock setup ready
 have up : u.pc=217 := by rw [applyBlock_pc,setup_length];rfl
 have stop : BoundedExecution (programFor W) n x L.B u 1 u :=
  .halt second.final_bound (by rw [step,up,halt_at])
 have head := setup_header args cell
 have width := UniformSectorBatchDirectoryMachine.sector_width
  (UniformSectorPackingMachine.physicalAxes as) i hi
 have hw : u.natReg 4122=2^(u.natReg 4120) := by
  rw [head.1.width,head.1.exponent]
  exact width
 refine ⟨u,?_,up,head.1,hw,?_,
  filled,table,head.2.1,head.2.2,?_,outputs,roots,low,out⟩
 · convert moved.executes (second.executes stop) using 1
   · rfl
   · simp only [setup_length,states]
 · intro r hr j hj
   exact filled i hi hi r hr j hj
 · intro q hlo hhi
   exact ((setup_frame ready).2.2.2.2.2 q (by omega) (by omega)).trans (saved q hlo hhi)

end
end ExactFourierCircuits.UniformProducedSectorChildABI
