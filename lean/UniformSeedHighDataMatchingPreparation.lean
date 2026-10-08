import UniformSeedConjugatePreservation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedHighDataMatchingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformAllAxisSeedPreparation (axisCount)

/-- Only ordinary allocation headers are copied. No populated coefficient,
matching, permutation or generated table is installed here. -/
def setup : List Op := [.literal 2265 0,
 .add 1820 2250 2265,
 .add 1821 2251 2265,
 .add 484 2252 2265,
 .add 485 2253 2265,
 .add 486 2254 2265,
 .add 487 2255 2265,
 .add 488 2256 2265,
 .add 490 2257 2265,
 .add 525 2258 2265,
 .add 527 2259 2265,
 .add 528 2260 2265,
 .add 529 2261 2265,
 .add 563 2262 2265,
 .add 564 2263 2265,
 .add 675 2264 2265]
def program : Program := UniformSeedChunkPreparation.program.map (relocate 0 1286) ++
 setup.map Op.code ++ UniformHighDataConjugateMatchingPreparation.program.map (relocate 1302 2668) ++ [.halt]
lemma setup_length : setup.length=16:=rfl
lemma program_length : program.length=2669:=by
 simp only [program,List.length_append,List.length_map,UniformSeedChunkPreparation.program_length,
 setup_length,UniformHighDataConjugateMatchingPreparation.program_length,List.length_singleton]
attribute [local irreducible] UniformSeedChunkPreparation.program UniformHighDataConjugateMatchingPreparation.program
lemma seed_code : CodeAt UniformSeedChunkPreparation.program program 0 1286:=by
 have eq:program=[]++UniformSeedChunkPreparation.program.map (relocate 0 1286)++
  (setup.map Op.code++UniformHighDataConjugateMatchingPreparation.program.map (relocate 1302 2668)++[.halt]):=by
  simp only [program,List.nil_append,List.append_assoc]
 rw [eq];exact UniformRankCrossPreparationMachine.segment_code [] _ _ _ _ rfl
lemma setup_code : BlockAt setup program 1286:=by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformSeedChunkPreparation.program.map (relocate 0 1286)) (setup.map Op.code)
  (UniformHighDataConjugateMatchingPreparation.program.map (relocate 1302 2668)++[.halt]) i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_map,UniformSeedChunkPreparation.program_length,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using lookup
lemma matching_code : CodeAt UniformHighDataConjugateMatchingPreparation.program program 1302 2668:=by
 let before:=UniformSeedChunkPreparation.program.map (relocate 0 1286)++setup.map Op.code
 have eq:program=before++UniformHighDataConjugateMatchingPreparation.program.map (relocate 1302 2668)++[.halt]:=by
  simp only [program,before,List.append_assoc]
 rw [eq];exact UniformRankCrossPreparationMachine.segment_code before [.halt] _ _ _ (by
  simp only [before,List.length_append,List.length_map,UniformSeedChunkPreparation.program_length,setup_length])
lemma halt_at : program[2668]?=some .halt:=by
 let before:=UniformSeedChunkPreparation.program.map (relocate 0 1286)++setup.map Op.code++
  UniformHighDataConjugateMatchingPreparation.program.map (relocate 1302 2668)
 have len:before.length=2668:=by
  simp only [before,List.length_append,List.length_map,UniformSeedChunkPreparation.program_length,
   setup_length,UniformHighDataConjugateMatchingPreparation.program_length]
 change (before++[.halt])[2668]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
attribute [local irreducible] UniformToeplitzCrossDAG.crossDAG UniformChunkMatchingPreparation.crossWord UniformChunkMatchingPreparation.colors
variable {n B:ℕ} {j:Fin (axisCount n)} {seed:UniformSeedChunkPreparation.Config}
structure FutureArgs (wp:UniformRankCrossPreparationMachine.Parameters) (V:ℕ)
 (j:Fin (axisCount n)) (s:State) : Prop where
 V : s.natReg 2250=V
 axis : s.natReg 2251=j.val
 a : s.natReg 2252=wp.a
 e : s.natReg 2253=wp.e
 i0 : s.natReg 2254=wp.i0
 j0 : s.natReg 2255=wp.j0
 split : s.natReg 2256=wp.split
 S : s.natReg 2257=wp.S
 K : s.natReg 2258=wp.K
 A : s.natReg 2259=wp.A
 d : s.natReg 2260=wp.d
 C : s.natReg 2261=wp.C
 conv : s.natReg 2262=wp.conv
 tape : s.natReg 2263=wp.tape
 depth : s.natReg 2264=wp.depth

lemma FutureArgs.transport {wp:UniformRankCrossPreparationMachine.Parameters} {V:ℕ}
 {s u:State} (h:FutureArgs wp V j s) (f:∀q,2250≤q→q≤2264→u.natReg q=s.natReg q) : FutureArgs wp V j u:=by
 constructor
 · exact (f 2250 (by omega) (by omega)).trans h.V
 · exact (f 2251 (by omega) (by omega)).trans h.axis
 · exact (f 2252 (by omega) (by omega)).trans h.a
 · exact (f 2253 (by omega) (by omega)).trans h.e
 · exact (f 2254 (by omega) (by omega)).trans h.i0
 · exact (f 2255 (by omega) (by omega)).trans h.j0
 · exact (f 2256 (by omega) (by omega)).trans h.split
 · exact (f 2257 (by omega) (by omega)).trans h.S
 · exact (f 2258 (by omega) (by omega)).trans h.K
 · exact (f 2259 (by omega) (by omega)).trans h.A
 · exact (f 2260 (by omega) (by omega)).trans h.d
 · exact (f 2261 (by omega) (by omega)).trans h.C
 · exact (f 2262 (by omega) (by omega)).trans h.conv
 · exact (f 2263 (by omega) (by omega)).trans h.tape
 · exact (f 2264 (by omega) (by omega)).trans h.depth

def Protected (q:ℕ):Prop:=q≠2265 ∧ q≠1820 ∧ q≠1821 ∧ (q<484∨489≤q) ∧ q≠490 ∧ q≠525 ∧
 (q<527∨530≤q) ∧ q≠563 ∧ q≠564 ∧ q≠675
lemma setup_frame (s:State) : (applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧ (applyBlock setup s).outputs=s.outputs ∧
 (applyBlock setup s).rootOrders=s.rootOrders ∧ (∀q,Protected q→(applyBlock setup s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro q h;unfold Protected at h
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_preserved (s:State) : UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock setup s):=by
 have f:=setup_frame s
 exact ⟨fun _ _=>congrFun f.1 _,fun _ _=>congrFun f.2.1 _,
  fun q lo hi=>f.2.2.2.2 q (by unfold Protected;omega),f.2.2.1,f.2.2.2.1⟩
lemma setup_safe {s:State} (bound:WordBound B s) : readable setup s ∧ peak setup s≤B:=by
 constructor
 · simp [setup,readable,Op.readable]
 · simp [setup,peak,Op.peak,Op.apply,writeNat,next]
   repeat' constructor
   all_goals exact bound.2.1 _
lemma setup_spectrum {wp:UniformRankCrossPreparationMachine.Parameters} {V:ℕ} {s:State}
 (h:FutureArgs wp V j s) (D:s.natReg 104=UniformMasterRootMachine.order n) :
 UniformConjugateRankSpectrumPreparation.Arguments n j wp V (applyBlock setup s):=by
 refine ⟨?_,?_,?_⟩
 · simp [setup,applyBlock,Op.apply,writeNat,next,h.V]
 · simp [setup,applyBlock,Op.apply,writeNat,next,h.axis]
 · intro q hq h0 h1 h2 h3
   simp only [UniformRankCrossPreparationMachine.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp_all [setup,applyBlock,Op.apply,writeNat,next,UniformRankCrossPreparationMachine.Parameters.register,
    UniformConjugateRankSpectrumPreparation.selected,h.a,h.e,h.i0,h.j0,h.split,h.S,h.K,h.A,h.d,h.C,h.conv,h.tape,h.depth]

lemma setup_result (hn:0<n) (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 {s:State} (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed s) :
 UniformSeedChunkPreparation.Result n j seed B hn p.seed (applyBlock setup s):=by
 have f:=setup_frame s
 have prepared:=UniformSeedChunkPreparation.seedResult_transport hn p.seed post.prepared
  (fun _ _=>congrFun f.1 _) f.2.1
  (fun q lo hi=>f.2.2.2.2 q (by unfold Protected;omega))
 have header:UniformChunkMatchingPreparation.Header (seed.chunk n j) (applyBlock setup s):=by
  constructor
  · exact post.header.height.transport_register (fun q lo hi=>f.2.2.2.2 q (by unfold Protected;omega))
  all_goals rw [f.2.2.2.2 _ (by unfold Protected;omega)];first
   | exact post.header.radix | exact post.header.source | exact post.header.target
   | exact post.header.borrowed | exact post.header.selected | exact post.header.ordinals
   | exact post.header.mapped | exact post.header.permutation | exact post.header.widths
   | exact post.header.markers | exact post.header.axis | exact post.header.depth
   | exact post.header.color
 refine ⟨prepared,header,?_,?_,?_,?_,?_⟩
 · rw [f.2.2.2.2 894 (by unfold Protected;omega)];exact post.count
 · change _∧_∧_∧_∧True;rw [f.1];exact post.rows
 · intro a ha k;rw [f.1];exact post.widths a ha k
 · intro a ha k;rw [f.1];exact post.permutations a ha k
 · intro i hi;change _∧_∧_;rw [f.1];exact post.mapped i hi

lemma result_withPC (hn:0<n) (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 {s:State} (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed s) (pc:ℕ) :
 UniformSeedChunkPreparation.Result n j seed B hn p.seed (setPC s pc):=by
 refine ⟨?_,post.header.withPC pc,post.count,post.rows,post.widths,post.permutations,post.mapped⟩
 exact ⟨post.prepared.source.withPC,post.prepared.cursor.withPC,post.prepared.processed,
  post.prepared.positive,post.prepared.root,post.prepared.negative,post.prepared.constants⟩

attribute [local irreducible] setup

structure Boundary (x:Fin n→ℂ) (hn:0<n) (p:UniformSeedChunkPackingPreparation.Layout n j seed B)
 (low:ℕ) (original:Fin p.packing.total→Scalar)
 (work:UniformRankCrossPreparationMachine.Parameters) (V mu bar:ℕ) (s u:State):Prop where
 genuine : UniformSeedChunkPreparation.Result n j seed B hn p.seed u
 packing : UniformSeedChunkPackingPreparation.Args p u
 lowArg : u.natReg 2240=low
 present : ∀i,u.scalarHeap (low+i.val)=some (original i)
 spectrum : UniformConjugateRankSpectrumPreparation.Arguments n j
  (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V u
 matching : UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) u
 metadata : UniformPermutationInversePreparation.Metadata n u
 operands : UniformInitialPreparation.Operands n x u
 original : UniformAllAxisSeedPreparation.Retained n (axisCount n) u
 conjugate : UniformAllAxisConjugatePreparation.Retained n (axisCount n) u
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders

theorem boundary_setup (hn:0<n) (x:Fin n→ℂ)
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B) (low:ℕ)
 (original:Fin p.packing.total→Scalar) (s:State)
 (_args:UniformSeedChunkPreparation.Args n j seed s)
 (packingArgs:UniformSeedChunkPackingPreparation.Args p s) (lowArg:s.natReg 2240=low)
 (present:∀i,s.scalarHeap (low+i.val)=some (original i))
 (_separated:low+p.packing.total≤p.packing.source)
 (_placement:UniformHighDataPackingPreparation.RetentionPlacement p)
 (work:UniformRankCrossPreparationMachine.Parameters) (V mu bar:ℕ)
 (_allocation:UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar)
 (future:FutureArgs (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V j s)
 (matchingArgs:UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ops:UniformInitialPreparation.Operands n x s)
 (retained:UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (_fresh:UniformSeedConjugatePreservation.Fresh
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n)) (low+p.packing.total))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) seed.seed.seed)
 (v:State)
 (post:UniformSeedChunkPreparation.Result n j seed B hn p.seed v)
 (old:UniformSeedRankCrossPreparation.PreservedFrame n s v)
 (pref:UniformSeedConjugatePreservation.PrefixFrame
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n)) (low+p.packing.total))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) s v)
 (kept:∀q,1450≤q→v.natReg q=s.natReg q) :
 Boundary x hn p low original work V mu bar s
  (setPC (applyBlock setup (setPC v 1286)) 0):=by
 let afterSeed:=setPC v 1286
 have future':FutureArgs (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V j afterSeed:=
  future.transport (fun q lo _=>kept q (by omega))
 let installed:=applyBlock setup afterSeed
 let entry:=setPC installed 0
 have ef:=setup_frame afterSeed
 have eold:UniformSeedRankCrossPreparation.PreservedFrame n s entry:=old.trans (setup_preserved afterSeed)
 have cv:UniformAllAxisConjugatePreparation.Retained n (axisCount n) entry:=by
  apply UniformSeedConjugatePreservation.PrefixFrame.conjugate (s:=s) _ conjugate
  refine ⟨fun i hi=>?_,fun i hi=>?_⟩
  · exact (congrFun ef.2.1 i).trans (pref.scalar i (lt_of_lt_of_le hi (Nat.le_max_left _ _)))
  · exact (congrFun ef.1 i).trans (pref.nat i hi)
 have ereg (q:ℕ) (hp:Protected q) (hq:1450≤q):entry.natReg q=s.natReg q:=
  (ef.2.2.2.2 q hp).trans (kept q hq)
 have packing':UniformSeedChunkPackingPreparation.Args p entry:=by
  rcases packingArgs with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨(ereg _ (by unfold Protected;omega) (by omega)).trans h0,
   (ereg _ (by unfold Protected;omega) (by omega)).trans h1,
   (ereg _ (by unfold Protected;omega) (by omega)).trans h2,
   (ereg _ (by unfold Protected;omega) (by omega)).trans h3,
   (ereg _ (by unfold Protected;omega) (by omega)).trans h4⟩
 have low':entry.natReg 2240=low:=(ereg _ (by unfold Protected;omega) (by omega)).trans lowArg
 have present':∀i,entry.scalarHeap (low+i.val)=some (original i):=by
  intro i
  have hi:=i.isLt
  exact ((congrFun ef.2.1 _).trans (pref.scalar _ (lt_of_lt_of_le (by omega) (Nat.le_max_right _ _)))).trans (present i)
 have matching':UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) entry:=by
  intro q lo hi
  exact ((ef.2.2.2.2 q (by unfold Protected;omega)).trans (kept q (by omega))).trans (matchingArgs q lo hi)
 have genuine:UniformSeedChunkPreparation.Result n j seed B hn p.seed entry:=by
  exact result_withPC hn p (setup_result hn p (result_withPC hn p post 1286)) 0
 have spectrum:=setup_spectrum future' (old.protected.metadata metadata).saved.masterRoot
 exact ⟨genuine,packing',low',present',spectrum,matching',eold.protected.metadata metadata,
  eold.protected.operands ops,eold.retained retained,cv,ef.2.2.1.trans old.2.2.2.1,
  ef.2.2.2.1.trans old.2.2.2.2⟩

theorem preparation (hn:0<n) (x:Fin n→ℂ)
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B) (low:ℕ)
 (original:Fin p.packing.total→Scalar) (s:State)
 (args:UniformSeedChunkPreparation.Args n j seed s)
 (packingArgs:UniformSeedChunkPackingPreparation.Args p s) (lowArg:s.natReg 2240=low)
 (present:∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated:low+p.packing.total≤p.packing.source)
 (placement:UniformHighDataPackingPreparation.RetentionPlacement p)
 (work:UniformRankCrossPreparationMachine.Parameters) (V mu bar:ℕ)
 (allocation:UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar)
 (future:FutureArgs (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V j s)
 (matchingArgs:UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ops:UniformInitialPreparation.Operands n x s)
 (retained:UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (fresh:UniformSeedConjugatePreservation.Fresh
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n)) (low+p.packing.total))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) seed.seed.seed)
 (code:2669≤B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedRuns program n x B s ticks (setPC u 1302) ∧
 ticks≤UniformSeedChunkPreparation.runtimeBudget n j seed+16 ∧
 u.pc=0 ∧ WordBound B u ∧ Boundary x hn p low original work V mu bar s u:=by
 obtain ⟨v,t,first,cost,vp,post,rv,mv,ov,old,pref⟩:=UniformSeedConjugatePreservation.Chunk.execution
  hn j seed B x s args metadata retained ops p.seed _ _ fresh pc bound
 have firstPlaced:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedChunkPreparation.program_length];omega) (by omega) first
 rw [show placed 0 s=s by cases s;simp [placed]] at firstPlaced
 let afterSeed:=setPC v 1286
 have kept (q:ℕ) (hq:1450≤q):v.natReg q=s.natReg q:=
  UniformNewtonTableMachine.Executes.keeps_nat first.executes (UniformSeedChunkPackingPreparation.seed_keeps q hq)
 have safe:=setup_safe firstPlaced.final_bound
 have installedRun:=block_runs setup program 1286 n B x afterSeed setup_code rfl
  firstPlaced.final_bound (by rw [setup_length];omega) safe.1 safe.2
 let installed:=applyBlock setup afterSeed
 have ip:installed.pc=1302:=by rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
 let entry:=setPC installed 0
 have ready:Boundary x hn p low original work V mu bar s entry:=
  boundary_setup hn x p low original s args packingArgs lowArg present separated placement work V mu bar
   allocation future matchingArgs metadata ops retained conjugate fresh v post old pref kept
 have whole:=firstPlaced.trans installedRun
 have placedEntry:setPC entry 1302=installed:=by
  change placed 1302 (setPC installed 0)=installed
  exact UniformSeedRankCrossPreparation.placed_zero installed 1302 ip
 refine ⟨entry,t+16,?_,by omega,rfl,
  changePC_bound B installed 0 installedRun.final_bound (by omega),ready⟩
 rw [placedEntry];simpa only [setup_length] using whole

/-- A single fixed stored program generates the actual selected chunk first,
then installs ordinary future headers, relocates/pack data, prepares the
conjugate spectrum, and performs six-C matching and native scatter. No Result,
Packed, spectrum, permutation, scale or action is an entry premise. -/
theorem execution (hn:0<n) (x:Fin n→ℂ)
 (p:UniformSeedChunkPackingPreparation.Layout n j seed B) (low:ℕ)
 (original:Fin p.packing.total→Scalar) (s:State)
 (args:UniformSeedChunkPreparation.Args n j seed s)
 (packingArgs:UniformSeedChunkPackingPreparation.Args p s) (lowArg:s.natReg 2240=low)
 (present:∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated:low+p.packing.total≤p.packing.source)
 (placement:UniformHighDataPackingPreparation.RetentionPlacement p)
 (work:UniformRankCrossPreparationMachine.Parameters) (V mu bar:ℕ)
 (allocation:UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar)
 (future:FutureArgs (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V j s)
 (matchingArgs:UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ops:UniformInitialPreparation.Operands n x s)
 (retained:UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (fresh:UniformSeedConjugatePreservation.Fresh
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n)) (low+p.packing.total))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) seed.seed.seed)
 (code:2669≤B) (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks≤UniformSeedChunkPreparation.runtimeBudget n j seed+
  UniformConjugatePackedMatchingPreparation.runtimeBudget p work+220*p.packing.total+62 ∧
 u.pc=2668 ∧ UniformHighDataConjugateMatchingPreparation.FullAction p original u ∧
 UniformHighDataConjugateMatchingPreparation.LogicalPairs p allocation.matching.capacity original u ∧
 UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders :=by
 obtain ⟨entry,t,first,cost,ep,eb,ready⟩:=preparation hn x p low original s args packingArgs lowArg present
  separated placement work V mu bar allocation future matchingArgs metadata ops retained conjugate fresh code pc bound
 obtain ⟨z,tm,last,mcost,zp,action,logical,rz,cz,mz,oz,out,roots⟩:=
  UniformHighDataConjugateMatchingPreparation.execution hn x p low original entry ready.genuine ready.packing ready.lowArg ready.present
   separated placement work V mu bar allocation ready.spectrum ready.matching ready.metadata ready.operands ready.original ready.conjugate ep eb
 have matchingPlaced:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformHighDataConjugateMatchingPreparation.program_length];omega) (by omega) last
 have pe:placed 1302 entry=setPC entry 1302:=by
  simp only [placed,setPC,ep,Nat.add_zero]
 rw [pe] at matchingPlaced
 let u:=setPC z 2668
 have stop:BoundedExecution program n x B u 1 u:=.halt matchingPlaced.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:=first.executes (matchingPlaced.executes stop)
 refine ⟨u,t+tm+1,?_,by omega,rfl,action,logical,rz.withPC,cz.withPC,
  mz.transport (fun _ _=>rfl) (fun _ _=>rfl),oz.transport rfl,?_,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using all
 · exact out.trans ready.outputs
 · exact roots.trans ready.roots

lemma canonical_code {n:ℕ} (hn:0<n) : 2669≤(n+2)^19:=by
 have base:3≤n+2:=by omega
 exact (show 2669≤3^19 by decide).trans (Nat.pow_le_pow_left base 19)

/-- Explicit same canonical B19. Ordinary allocation/shape bounds remain
premises; this specialization does not construct the global allocator. -/
theorem canonical_execution (hn:0<n) (x:Fin n→ℂ)
 (p:UniformSeedChunkPackingPreparation.Layout n j seed ((n+2)^19)) (low:ℕ)
 (original:Fin p.packing.total→Scalar) (s:State)
 (args:UniformSeedChunkPreparation.Args n j seed s)
 (packingArgs:UniformSeedChunkPackingPreparation.Args p s) (lowArg:s.natReg 2240=low)
 (present:∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated:low+p.packing.total≤p.packing.source)
 (placement:UniformHighDataPackingPreparation.RetentionPlacement p)
 (work:UniformRankCrossPreparationMachine.Parameters) (V mu bar:ℕ)
 (allocation:UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar)
 (future:FutureArgs (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V j s)
 (matchingArgs:UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ops:UniformInitialPreparation.Operands n x s)
 (retained:UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (fresh:UniformSeedConjugatePreservation.Fresh
  (max (UniformAllAxisConjugatePreparation.axisBase n (axisCount n)) (low+p.packing.total))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) seed.seed.seed)
 (pc:s.pc=0) (bound:WordBound ((n+2)^19) s) : ∃u ticks,
 BoundedExecution program n x ((n+2)^19) s ticks u ∧
 ticks≤UniformSeedChunkPreparation.runtimeBudget n j seed+
  UniformConjugatePackedMatchingPreparation.runtimeBudget p work+220*p.packing.total+62 ∧
 u.pc=2668 ∧ UniformHighDataConjugateMatchingPreparation.FullAction p original u ∧
 UniformHighDataConjugateMatchingPreparation.LogicalPairs p allocation.matching.capacity original u ∧
 UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders :=by
 exact execution hn x p low original s args packingArgs lowArg present separated placement work V mu bar
  allocation future matchingArgs metadata ops retained conjugate fresh (canonical_code hn) pc bound

end
end ExactFourierCircuits.UniformSeedHighDataMatchingPreparation
