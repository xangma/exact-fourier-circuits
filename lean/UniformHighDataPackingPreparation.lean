import UniformConjugatePackedMatchingPreparation
import UniformScalarCopyMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformHighDataPackingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformAllAxisSeedPreparation (axisCount)

def setup : List Op := [.literal 2241 0,.add 147 1180 2241,.add 148 2240 2241,.add 149 1453 2241]
def program : Program := setup.map Op.code ++ UniformScalarCopyMachine.program.map (relocate 4 14) ++
 UniformSeedChunkPackingPreparation.continuation.map (relocate 14 166) ++ [.halt]
lemma setup_length : setup.length=4:=rfl
lemma program_length : program.length=167:=by simp only [program,List.length_append,List.length_map,
 setup_length,UniformScalarCopyMachine.program_length,UniformSeedChunkPackingPreparation.continuation_length,List.length_singleton]
lemma setup_code : BlockAt setup program 0:=by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma copy_code : CodeAt UniformScalarCopyMachine.program program 4 14:=
 UniformRankCrossPreparationMachine.segment_code (setup.map Op.code)
  (UniformSeedChunkPackingPreparation.continuation.map (relocate 14 166)++[.halt]) _ 4 14 (by rw [List.length_map,setup_length])
lemma packing_code : CodeAt UniformSeedChunkPackingPreparation.continuation program 14 166:=by
 have eq:program=(setup.map Op.code++UniformScalarCopyMachine.program.map (relocate 4 14))++
  UniformSeedChunkPackingPreparation.continuation.map (relocate 14 166)++[.halt]:=by simp only [program,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code _ [.halt] _ 14 166 (by
  simp only [List.length_append,List.length_map,setup_length,UniformScalarCopyMachine.program_length])
lemma halt_at : program[166]?=some .halt:=by
 let before:=setup.map Op.code++UniformScalarCopyMachine.program.map (relocate 4 14)++
  UniformSeedChunkPackingPreparation.continuation.map (relocate 14 166)
 have len:before.length=166:=by simp only [before,List.length_append,List.length_map,setup_length,
  UniformScalarCopyMachine.program_length,UniformSeedChunkPackingPreparation.continuation_length]
 change (before++[.halt])[166]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
variable {n B : ℕ} {j : Fin (axisCount n)} {seed : UniformSeedChunkPreparation.Config}

/-- Read-footprint transport only. The scalar view is never an execution start;
actual prepared banks are transported separately by their physical frame. -/
lemma seed_result_transport (hn : 0<n) (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 {s u : State} (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed s)
 (nat : u.natHeap=s.natHeap)
 (regs : ∀q,q<147 ∨ (154 ≤ q ∧ q ≠ 2241) → u.natReg q=s.natReg q)
 (scalars : ∀i,i<p.packing.source → u.scalarHeap i=s.scalarHeap i)
 (positive : seed.seed.C+7*seed.seed.width+1 ≤ p.packing.source)
 (negative : seed.seed.negative+7*seed.seed.width ≤ p.packing.source)
 (constants : seed.seed.constants+6 ≤ p.packing.source) :
 UniformSeedChunkPreparation.Result n j seed B hn p.seed u := by
 let view:State:={u with scalarHeap:=s.scalarHeap}
 have old:=UniformSeedChunkPreparation.seedResult_transport hn p.seed post.prepared
  (u:=view) (fun q _=>congrFun nat q) rfl (fun q h0 h1=>regs q (Or.inr ⟨by omega,by omega⟩))
 have prep:UniformSeedHeightPreparation.Result n j seed.seed B (p.seed.seed.replay hn j seed.seed B) u:=by
  refine ⟨⟨old.source.bank,old.source.directory,old.source.tape⟩,
   post.prepared.cursor.transport_register
    (fun q h0 h1=>regs q (Or.inr ⟨by omega,by omega⟩)),?_,?_,?_,?_,?_⟩
  · intro d hd
    obtain ⟨table,col,rec⟩:=old.processed d hd
    refine ⟨?_,col,rec⟩
    intro i hi
    exact table i hi
  · intro i
    have hi:i.val<7*seed.seed.width+1:=by
     have:=i.isLt;change i.val<seed.seed.width+6*seed.seed.width at this;omega
    exact (scalars _ (by omega)).trans (post.prepared.positive i)
  · exact (scalars _ (by omega)).trans post.prepared.root
  · intro i hi;exact (scalars _ (by omega)).trans (post.prepared.negative i hi)
  · intro i hi;exact (scalars _ (by omega)).trans (post.prepared.constants i hi)
 have header:UniformChunkMatchingPreparation.Header (seed.chunk n j) u:=by
  refine ⟨post.header.height.transport_register
   (fun q h0 h1=>regs q (Or.inr ⟨by omega,by omega⟩)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [regs _ (by omega)];first
   | exact post.header.radix | exact post.header.source | exact post.header.target
   | exact post.header.borrowed | exact post.header.selected | exact post.header.ordinals
   | exact post.header.mapped | exact post.header.permutation | exact post.header.widths
   | exact post.header.markers | exact post.header.axis | exact post.header.depth
   | exact post.header.color
 refine ⟨prep,header,?_,?_,?_,?_,?_⟩
 · rw [regs _ (by omega)];exact post.count
 · change _ ∧ _ ∧ _ ∧ _ ∧ True
   rw [nat];exact post.rows
 · intro a ha k;rw [nat];exact post.widths a ha k
 · intro a ha k;rw [nat];exact post.permutations a ha k
 · intro i hi;change _ ∧ _ ∧ _;rw [nat];exact post.mapped i hi

/-- Only ordinary placement of the already-produced coefficient banks. -/
structure BankPlacement (p : UniformSeedChunkPackingPreparation.Layout n j seed B) : Prop where
 positive : seed.seed.C+7*seed.seed.width+1 ≤ p.packing.source
 negative : seed.seed.negative+7*seed.seed.width ≤ p.packing.source
 constants : seed.seed.constants+6 ≤ p.packing.source

def Protected (q : ℕ) : Prop :=
 (q<147 ∨ 154 ≤ q) ∧ q ≠ 2241 ∧ ((q<600 ∨ 650 ≤ q) ∧ q ≠ 1405 ∧ (q<1400 ∨ 1405 ≤ q) ∧ q ≠ 1455)

def Frame (s u : State) : Prop := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ (∀q,Protected q → u.natReg q=s.natReg q) ∧ (∀q,q ≠ 32 → q ≠ 70 → u.scalarReg q=s.scalarReg q)

lemma setup_frame (s : State) :
 (applyBlock setup s).natHeap=s.natHeap ∧ (applyBlock setup s).scalarHeap=s.scalarHeap ∧ (applyBlock setup s).scalarReg=s.scalarReg ∧ (applyBlock setup s).outputs=s.outputs ∧ (applyBlock setup s).rootOrders=s.rootOrders ∧ (∀q,q<147 ∨ (154 ≤ q ∧ q ≠ 2241) → (applyBlock setup s).natReg q=s.natReg q) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]

lemma setup_safe (s : State) (hs : WordBound B s) : readable setup s ∧ peak setup s ≤ B := by
 refine ⟨by simp [setup,readable,Op.readable],?_⟩
 simp only [setup,peak,Op.peak,Op.apply,writeNat,next]
 simp
 exact ⟨hs.2.1 1180,hs.2.1 2240,hs.2.1 1453⟩

/-- A real copy and a real generated-axis packing, with no host phase writes.
The low input is present; the high destination may be dirty. Both its exact
values and dependency tags are copied and then permuted by the printed DFS. -/
theorem execution (hn : 0<n) (x : Fin n → ℂ)
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (low : ℕ)
 (original : Fin p.packing.total → Scalar) (s : State)
 (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed s)
 (args : UniformSeedChunkPackingPreparation.Args p s) (lowArg : s.natReg 2240=low)
 (present : ∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated : low+p.packing.total ≤ p.packing.source) (banks : BankPlacement p)
 (pc : s.pc=0) (bound : WordBound B s) : ∃u ticks origin,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ 220*p.packing.total+44 ∧ u.pc=166 ∧ UniformSeedChunkPreparation.Result n j seed B hn p.seed origin ∧ UniformSeedChunkPackingPreparation.Packed p original origin u ∧ (∀i,origin.scalarHeap (p.packing.source+i.val)=some (original i)) ∧ (∀i,u.scalarHeap (low+i.val)=some (original i)) ∧ UniformSectorPackingMachine.OutsideAllocation p.packing s u ∧ (∀ i : ℕ, (i < p.packing.source ∨ p.packing.source+p.packing.total ≤ i) → (i < p.packing.destination ∨ p.packing.destination+p.packing.total ≤ i) → u.scalarHeap i=s.scalarHeap i) ∧ Frame s u := by
 have code:=p.code
 have safe:=setup_safe s bound
 have first:=block_runs setup program 0 n B x s setup_code pc bound
  (by rw [setup_length];omega) safe.1 safe.2
 let a:=applyBlock setup s
 have af:=setup_frame s
 have ap:a.pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,setup_length]
 have radix:s.natReg 1180=p.packing.total:=by
  rw [post.header.radix]
  exact p.volume.symm
 have h147:a.natReg 147=p.packing.total:=by
  simp [a,setup,applyBlock,Op.apply,writeNat,next,radix]
 have h148:a.natReg 148=low:=by simp [a,setup,applyBlock,Op.apply,writeNat,next,lowArg]
 have h149:a.natReg 149=p.packing.source:=by
  simp [a,setup,applyBlock,Op.apply,writeNat,next,args.2.2.2.1]
 have src:UniformScalarCopyMachine.Source p.packing.total low (setPC a 0).scalarHeap:=by
  intro i hi
  exact ⟨original ⟨i,hi⟩,present ⟨i,hi⟩⟩
 obtain ⟨v,copy,copied,_,outside,cf,nf⟩:=UniformScalarCopyMachine.execution n x
  p.packing.total low p.packing.source B (setPC a 0) src separated
  (by have:=p.packing.sourceBelow;have fit:=p.packing.destinationBound;rw [p.bound] at fit;omega) (by omega) rfl h147 h148 h149
  (changePC_bound B a 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed copy_code
  (by rw [UniformScalarCopyMachine.program_length];omega) (by omega) copy
 rw [UniformSeedRankCrossPreparation.placed_zero a 4 ap] at moved
 let origin:=setPC v 14
 have nat:origin.natHeap=s.natHeap:=cf.1.trans af.1
 have regs:∀q,q<147 ∨ (154 ≤ q ∧ q ≠ 2241) → origin.natReg q=s.natReg q:=by
  intro q hq
  exact (nf q (by omega)).trans (af.2.2.2.2.2 q hq)
 have scalar:∀i,i<p.packing.source → origin.scalarHeap i=s.scalarHeap i:=by
  intro i hi
  exact (outside i (Or.inl hi)).trans (congrFun af.2.1 i)
 have genuine:=seed_result_transport hn p post nat regs scalar banks.positive banks.negative banks.constants
 have args':UniformSeedChunkPackingPreparation.Args p origin:=by
  rcases args with ⟨h0,h1,h2,h3,h4⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [regs _ (by omega)];assumption
 have source:UniformSectorPackingMachine.SourceReady p.packing original origin:=by
  intro i
  exact (copied i.val i.isLt).trans (present i)
 obtain ⟨z,t,last,cost,zpc,packed⟩:=UniformSeedChunkPackingPreparation.continuation_execution
  hn p original x (setPC origin 0)
  (seed_result_transport hn p genuine rfl (fun _ _=>rfl) (fun _ _=>rfl)
   banks.positive banks.negative banks.constants)
  args' source rfl (changePC_bound B origin 0 moved.final_bound (by omega))
 have placedLast:=UniformBoundedAssembly.boundedExecution_placed packing_code (by
  rw [UniformSeedChunkPackingPreparation.continuation_length];omega) (by omega) last
 rw [UniformSeedRankCrossPreparation.placed_zero origin 14 rfl] at placedLast
 let u:=setPC z 166
 have stop:BoundedExecution program n x B u 1 u:=.halt placedLast.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:=first.executes (moved.executes (placedLast.executes stop))
 refine ⟨u,4+(7*p.packing.total+4)+t+1,origin,?_,by omega,rfl,genuine,?_,source,?_,?_,?_,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using all
 · exact ⟨packed.inverse,packed.values,packed.scalarOutside,packed.natOutside,packed.frame⟩
 · intro i
   exact (packed.scalarOutside _ (Or.inl (by have:=i.isLt;have:=p.packing.sourceBelow;omega))).trans
    ((outside _ (Or.inl (by have:=i.isLt;omega))).trans (present i))
 · intro i h0 h1 h2
   exact (packed.natOutside i h0 h1 h2).trans (congrFun nat i)
 · intro i h0 h1
   exact (packed.scalarOutside i h1).trans ((outside i h0).trans (congrFun af.2.1 i))
 · refine ⟨packed.frame.1.trans (cf.2.1.trans af.2.2.2.1),
   packed.frame.2.1.trans (cf.2.2.1.trans af.2.2.2.2.1),?_,?_⟩
   · intro q hq
     exact (packed.frame.2.2.1 q hq.2.2).trans (regs q (by rcases hq with ⟨h0,h1,h2⟩;omega))
   · intro q h0 h1
     exact (packed.frame.2.2.2 q h1).trans ((cf.2.2.2 q h0).trans (congrFun af.2.2.1 q))


/-- The existing six-C placement already puts the high source above the old
coefficient banks; it is enough for the real-copy seed transport. -/
lemma BankPlacement.of_matching {work : UniformRankCrossPreparationMachine.Parameters} {V mu bar : ℕ}
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (a : UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar) : BankPlacement p := by
 have chain:=a.spectrum.scalar_chain
 have c:=a.matching.coefficient.conjugatesBelow
 have mb:=a.matching.coefficient.destinations
 have fresh:=a.matching.destinationFresh
 dsimp only [UniformConjugatePackedMatchingPreparation.workParameters,
  UniformConjugateRankSpectrumPreparation.relocated] at chain
 change V+UniformToeplitzCrossDAG.bankSize seed.seed.exponent ≤ mu at c
 change mu<bar at mb
 change bar<p.packing.source at fresh
 exact ⟨by have:=a.positiveBefore;omega,by have:=a.negativeBefore;omega,by have:=a.constantsBefore;omega⟩

/-- These extra facts describe only the fresh data placement, not its contents. -/
structure RetentionPlacement (p : UniformSeedChunkPackingPreparation.Layout n j seed B) : Prop where
 original : UniformAllAxisSeedPreparation.axisBase n (axisCount n) ≤ p.packing.source
 conjugate : UniformAllAxisConjugatePreparation.axisBase n (axisCount n) ≤ p.packing.source
 directory : UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n ≤ p.packing.suffix

lemma Frame.saved {s u : State} (f : Frame s u) (q : ℕ) (h0 : 100 ≤ q) (h1 : q ≤ 106) :
 u.natReg q=s.natReg q := f.2.2.1 q (by unfold Protected;omega)

/-- Exact protected banks are retained through the charged relocation and DFS.
The original low source remains available. No conjugate spectrum or matching
operator certificate enters this theorem. -/
theorem execution_retained (hn : 0<n) (x : Fin n → ℂ)
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (low : ℕ)
 (original : Fin p.packing.total → Scalar) (s : State)
 (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed s)
 (args : UniformSeedChunkPackingPreparation.Args p s) (lowArg : s.natReg 2240=low)
 (present : ∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated : low+p.packing.total ≤ p.packing.source) (banks : BankPlacement p)
 (placement : RetentionPlacement p)
 (retained : UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate : UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (metadata : UniformPermutationInversePreparation.Metadata n s)
 (ops : UniformInitialPreparation.Operands n x s)
 (pc : s.pc=0) (bound : WordBound B s) : ∃u ticks origin,
 BoundedExecution program n x B s ticks u ∧ ticks ≤ 220*p.packing.total+44 ∧ u.pc=166 ∧ UniformSeedChunkPreparation.Result n j seed B hn p.seed origin ∧ UniformSeedChunkPackingPreparation.Packed p original origin u ∧ UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧ UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧ UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧ (∀i,u.scalarHeap (low+i.val)=some (original i)) ∧ Frame s u := by
 obtain ⟨u,t,origin,run,cost,up,genuine,packed,_,lowKeep,nat,scalar,frame⟩:=
  execution hn x p low original s post args lowArg present separated banks pc bound
 have before:∀i,i<p.packing.source → u.scalarHeap i=s.scalarHeap i:=by
  intro i hi
  exact scalar i (Or.inl hi) (Or.inl (by have:=p.packing.sourceBelow;omega))
 have nh:∀i,i<p.packing.suffix → u.natHeap i=s.natHeap i:=by
  intro i hi
  apply UniformSectorPackingMachine.protected_prefix p.packing s u nat i hi
 have directory:UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n ≤ p.packing.suffix:=by
  have:=placement.directory
  unfold UniformAllAxisConjugatePreparation.directoryBase at this
  omega
 have f:UniformSeedRankCrossPreparation.PreservedFrame n s u:=
  ⟨fun i hi=>nh i (hi.trans_le directory),fun i hi=>before i (hi.trans_le placement.original),
   fun q h0 h1=>frame.saved q h0 h1,frame.1,frame.2.1⟩
 have cj:UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=by
  refine ⟨?_,?_,?_⟩
  · intro a ha q l
    exact (before _ ((UniformAllAxisConjugatePreparation.compact_address_before a ha q l).trans_le placement.conjugate)).trans
     (conjugate.coefficients a ha q l)
  · intro a ha
    exact (nh _ (by have:=a.isLt;have:=placement.directory;omega)).trans (conjugate.address a ha)
  · intro a ha
    exact (nh _ (by have:=a.isLt;have:=placement.directory;omega)).trans (conjugate.width a ha)
 exact ⟨u,t,origin,run,cost,up,genuine,packed,f.retained retained,cj,
  f.protected.metadata metadata,f.protected.operands ops,lowKeep,frame⟩

/-- Canonical caller-budget specialization. A compatible allocator and the
actual low bank must still be supplied; this is not a global allocator theorem. -/
theorem canonical_execution (hn : 0<n) (x : Fin n → ℂ)
 (p : UniformSeedChunkPackingPreparation.Layout n j seed ((n+2)^19)) (low : ℕ)
 (original : Fin p.packing.total → Scalar) (s : State)
 (post : UniformSeedChunkPreparation.Result n j seed ((n+2)^19) hn p.seed s)
 (args : UniformSeedChunkPackingPreparation.Args p s) (lowArg : s.natReg 2240=low)
 (present : ∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated : low+p.packing.total ≤ p.packing.source) (banks : BankPlacement p)
 (pc : s.pc=0) (bound : WordBound ((n+2)^19) s) : ∃u ticks origin,
 BoundedExecution program n x ((n+2)^19) s ticks u ∧ ticks ≤ 220*p.packing.total+44 ∧ u.pc=166 ∧ UniformSeedChunkPreparation.Result n j seed ((n+2)^19) hn p.seed origin ∧ UniformSeedChunkPackingPreparation.Packed p original origin u ∧ (∀i,origin.scalarHeap (p.packing.source+i.val)=some (original i)) ∧ (∀i,u.scalarHeap (low+i.val)=some (original i)) ∧ UniformSectorPackingMachine.OutsideAllocation p.packing s u ∧ (∀i:ℕ,(i<p.packing.source ∨ p.packing.source+p.packing.total ≤ i) → (i<p.packing.destination ∨ p.packing.destination+p.packing.total ≤ i) → u.scalarHeap i=s.scalarHeap i) ∧ Frame s u :=
 execution hn x p low original s post args lowArg present separated banks pc bound

end
end ExactFourierCircuits.UniformHighDataPackingPreparation
