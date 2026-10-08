import UniformSeedChunkPreparation
import UniformMatchingPackingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedChunkPackingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformAllAxisSeedPreparation (axisCount radix Retained axisBase directoryBase)
abbrev Config := UniformSeedChunkPreparation.Config

/-- Five ordinary allocation arguments are copied by charged instructions.
The zero is initialized here: no undeclared zero-register readiness is used. -/
def install : List Op := [.literal 1455 0,.add 1400 1450 1455,.add 1401 1451 1455,
 .add 1402 1452 1455,.add 1403 1453 1455,.add 1404 1454 1455]
def headers : List Op := install ++ UniformMatchingPackingPreparation.setup
def beforePacking : Program := headers.map Op.code
/-- This continuation consumes the actual SeedChunk result, not another
Matching215 run. Six header copies, eight packing setup instructions,137+halt. -/
def continuation : Program := beforePacking ++
 UniformSectorPackingMachine.program.map (relocate 14 151) ++ [.halt]
def program : Program := UniformSeedChunkPreparation.program.map (relocate 0 1286) ++
 beforePacking ++ UniformSectorPackingMachine.program.map (relocate 1300 1437) ++ [.halt]
lemma install_length : install.length=6 := rfl
lemma headers_length : headers.length=14 := by simp [headers,install_length,UniformMatchingPackingPreparation.setup_length]
lemma beforePacking_length : beforePacking.length=14 := by simp [beforePacking,headers_length]
lemma continuation_length : continuation.length=152 := by
 simp [continuation,beforePacking_length,UniformSectorPackingMachine.program_length]
lemma program_length : program.length=1438 := by
 simp [program,UniformSeedChunkPreparation.program_length,beforePacking_length,UniformSectorPackingMachine.program_length]
lemma headers_code : BlockAt headers continuation 0 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (headers.map Op.code)
  (UniformSectorPackingMachine.program.map (relocate 14 151) ++ [.halt]) i
  (by simpa using hi)
 simpa only [continuation,beforePacking,List.append_assoc,List.length_nil,Nat.zero_add,
  List.nil_append,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma packing_code : CodeAt UniformSectorPackingMachine.program continuation 14 151 :=
 UniformRankCrossPreparationMachine.segment_code beforePacking [.halt] _ 14 151 beforePacking_length
lemma continuation_halt : continuation[151]?=some .halt := by
 unfold continuation
 rw [List.getElem?_append_right (by simp [beforePacking_length,UniformSectorPackingMachine.program_length])]
 simp [beforePacking_length,UniformSectorPackingMachine.program_length]
lemma seed_code : CodeAt UniformSeedChunkPreparation.program program 0 1286 := by
 have he:program=[] ++ UniformSeedChunkPreparation.program.map (relocate 0 1286) ++
  (beforePacking ++ UniformSectorPackingMachine.program.map (relocate 1300 1437) ++ [.halt]) := by
  simp only [program,List.nil_append,List.append_assoc]
 rw [he]
 exact UniformRankCrossPreparationMachine.segment_code [] _ _ 0 1286 rfl
lemma full_headers_code : BlockAt headers program 1286 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformSeedChunkPreparation.program.map (relocate 0 1286)) (headers.map Op.code)
  (UniformSectorPackingMachine.program.map (relocate 1300 1437) ++ [.halt]) i
  (by simpa using hi)
 simpa only [program,beforePacking,List.append_assoc,List.length_map,
  UniformSeedChunkPreparation.program_length,List.getElem?_map,
  List.getElem?_eq_getElem hi,Option.map_some] using h
lemma full_packing_code : CodeAt UniformSectorPackingMachine.program program 1300 1437 :=
 UniformRankCrossPreparationMachine.segment_code
  (UniformSeedChunkPreparation.program.map (relocate 0 1286) ++ beforePacking) [.halt] _ 1300 1437
  (by simp [UniformSeedChunkPreparation.program_length,beforePacking_length])
lemma halt_at : program[1437]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simp [UniformSeedChunkPreparation.program_length,
  beforePacking_length,UniformSectorPackingMachine.program_length])]
 simp [UniformSeedChunkPreparation.program_length,beforePacking_length,
  UniformSectorPackingMachine.program_length]

noncomputable section
structure Layout (n:ℕ) (j:Fin (axisCount n)) (c:Config) (B:ℕ) where
 seed : UniformSeedChunkPreparation.Layout n j c B
 packing : UniformSectorPackingMachine.Layout
 bound : packing.B=B
 oneAxis : packing.ell=1
 axisRow : packing.rows=c.axis
 volume : packing.total=radix n j
 seedBelow : axisBase n (axisCount n)≤packing.destination
 positiveBelow : c.seed.C+7*c.seed.width+1≤packing.destination
 negativeBelow : c.seed.negative+7*c.seed.width≤packing.destination
 constantsBelow : c.seed.constants+6≤packing.destination
 code : 1438≤B

def Layout.bridge {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) :
 UniformMatchingPackingPreparation.Layout (c.chunk n j) B :=
 ⟨l.seed.chunk,l.packing,l.bound,l.oneAxis,l.axisRow,l.volume,l.code.trans' (by decide)⟩

abbrev word (n:ℕ) (j:Fin (axisCount n)) (c:Config) :=
 UniformChunkMatchingPreparation.crossWord (c.chunk n j)
  (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2

abbrev axes {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) :=
 [UniformChunkMatchingPreparation.axis l.seed.chunk (word n j c)
  (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
  (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)]
lemma volume {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) :
 UniformSectorPackingMachine.physicalVolume (axes l)=l.packing.total :=
 UniformMatchingPackingPreparation.axis_volume l.bridge (word n j c)
  (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
  (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)

def Args {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) (s:State) : Prop :=
 s.natReg 1450=l.packing.suffix ∧ s.natReg 1451=l.packing.stack ∧
 s.natReg 1452=l.packing.inverse ∧ s.natReg 1453=l.packing.source ∧
 s.natReg 1454=l.packing.destination
lemma headers_spec {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) (s:State)
 (args:Args l s) (head:UniformChunkMatchingPreparation.Header (c.chunk n j) s) :
 UniformSectorPackingMachine.Header l.packing (applyBlock headers s) := by
 constructor
 all_goals simp (disch:=omega) [headers,install,UniformMatchingPackingPreparation.setup,applyBlock,
  Op.apply,writeNat,next,args.1,args.2.1,args.2.2.1,args.2.2.2.1,args.2.2.2.2,
  head.axis,l.oneAxis,l.axisRow,UniformSeedChunkPreparation.Config.chunk]
lemma headers_safe {s:State} {B:ℕ} (hs:WordBound B s) (hc:1≤B) :
 readable headers s ∧ peak headers s≤B := by
 constructor
 · simp [headers,install,UniformMatchingPackingPreparation.setup,readable,Op.readable]
 · simp [headers,install,UniformMatchingPackingPreparation.setup,peak,Op.peak,Op.apply,writeNat,next]
   exact ⟨hc,hs.2.1 1190,hs.2.1 1450,hs.2.1 1451,hs.2.1 1452,hs.2.1 1453,hs.2.1 1454⟩
def Frame (s u:State) := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,((q<600 ∨ 650≤q) ∧ q≠1405 ∧ (q<1400 ∨ 1405≤q) ∧ q≠1455)→u.natReg q=s.natReg q) ∧
 (∀q,q≠70→u.scalarReg q=s.scalarReg q)
lemma headers_frame (s:State) : Frame s (applyBlock headers s) := by
 refine ⟨rfl,rfl,?_,fun _ _=>rfl⟩
 intro q hq
 simp (disch:=omega) [headers,install,UniformMatchingPackingPreparation.setup,applyBlock,Op.apply,writeNat,next]
lemma packing_frame {s u:State} (h:UniformSectorPackingMachine.FinalFrame s u) : Frame s u :=
 ⟨h.1,h.2.1,fun q hq=>h.2.2.1 q (by omega),h.2.2.2⟩
lemma Frame.trans {s u v:State} (a:Frame s u) (b:Frame u v) : Frame s v :=
 ⟨b.1.trans a.1,b.2.1.trans a.2.1,fun q h=>(b.2.2.1 q h).trans (a.2.2.1 q h),
 fun q h=>(b.2.2.2 q h).trans (a.2.2.2 q h)⟩

/-- The actual generated inverse-address permutation, with a proved length cast. -/
def unpacking {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B) :=
 UniformSectorPackingMachine.physicalUnpacking (axes l) l.packing (volume l)

structure Packed {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B)
 (v:Fin l.packing.total→Scalar) (s u:State) : Prop where
 inverse : UniformSectorPackingMachine.InverseReady l.packing (unpacking l) u
 values : ∀i,u.scalarHeap (l.packing.destination+i.val)=some (v (unpacking l i))
 scalarOutside : ∀q,(q<l.packing.destination ∨ l.packing.destination+l.packing.total≤q)→u.scalarHeap q=s.scalarHeap q
 natOutside : UniformSectorPackingMachine.OutsideAllocation l.packing s u
 frame : Frame s u

/-- Shared charged continuation proof. It consumes the genuine SeedChunk
postcondition and physical input scalars, then executes14 setup+Packing137+halt.
No new generated table or ready packing header is supplied. -/
theorem packing_stage {n B:ℕ} (hn:0<n) {j:Fin (axisCount n)} {c:Config}
 (l:Layout n j c B) (v:Fin l.packing.total→Scalar) (x:Fin n→ℂ) (s:State)
 (post:UniformSeedChunkPreparation.Result n j c B hn l.seed s)
 (args:Args l s) (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (q:Program) (base ret:ℕ) (headerCode:BlockAt headers q base)
 (packingCode:CodeAt UniformSectorPackingMachine.program q (base+14) ret)
 (halt:q[ret]?=some .halt) (fit:base+151≤B) (retFit:ret≤B)
 (pc:s.pc=base) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution q n x B s ticks u ∧ ticks≤213*l.packing.total+35 ∧
 u.pc=ret ∧ Packed l v s u := by
 have safe:=headers_safe bound (by omega)
 have first:=block_runs headers q base n B x s headerCode pc bound
  (by rw [headers_length];omega) safe.1 safe.2
 let b:=applyBlock headers s
 have bp:b.pc=base+14:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,headers_length]
 have head:=headers_spec l s args post.header
 have below:=UniformMatchingPackingPreparation.axis_below l.bridge (word n j c)
  (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
  (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)
 have rows:UniformSectorPackingMachine.Rows (axes l) 0 l.packing.rows (setPC b 0):=by
  rw [l.axisRow];exact post.rows
 obtain ⟨z,t,cost,run,zpc,inv,values,out,natOut,frame⟩:=
  UniformSectorPackingMachine.execution (axes l) l.packing n x v (setPC b 0)
   (by simp [axes,l.oneAxis]) (volume l)
   (UniformSectorPackingMachine.header_setPC _ b 0 head) rows post.widths post.permutations
   below.1 below.2 source rfl (by rw [l.bound];exact changePC_bound B b 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed packingCode
  (by rw [UniformSectorPackingMachine.program_length];omega) retFit (by rw [l.bound] at run;exact run)
 rw [UniformSeedRankCrossPreparation.placed_zero b (base+14) bp] at moved
 let u:=setPC z ret
 have stop:BoundedExecution q n x B u 1 u:=.halt moved.final_bound
  (by simp [step,u,setPC,halt])
 refine ⟨u,14+t+1,?_,by omega,rfl,?_,?_,?_,?_,?_⟩
 · simpa only [headers_length,Nat.add_assoc] using first.executes (moved.executes stop)
 · exact inv
 · exact values
 · exact out
 · exact natOut
 · exact (headers_frame s).trans (packing_frame frame)

/-- Standalone152-instruction continuation from a genuine generated SeedChunk
result. Its original contiguous data source remains an honest physical premise. -/
theorem continuation_execution {n B:ℕ} (hn:0<n) {j:Fin (axisCount n)} {c:Config}
 (l:Layout n j c B) (v:Fin l.packing.total→Scalar) (x:Fin n→ℂ) (s:State)
 (post:UniformSeedChunkPreparation.Result n j c B hn l.seed s)
 (args:Args l s) (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution continuation n x B s ticks u ∧ ticks≤213*l.packing.total+35 ∧
 u.pc=151 ∧ Packed l v s u :=
 packing_stage hn l v x s post args source continuation 0 151 headers_code packing_code
  continuation_halt (by have:=l.code;omega) (by have:=l.code;omega) pc bound

/-- Exact tags of every produced positive, negative and normalization constant
are retained by the actual packing stores under the ordinary disjoint layout. -/
theorem coefficients_retained {n B:ℕ} {j:Fin (axisCount n)} {c:Config}
 (l:Layout n j c B) {v:Fin l.packing.total→Scalar} {s u:State} (h:Packed l v s u) :
 (∀i,i<7*c.seed.width+1→u.scalarHeap (c.seed.C+i)=s.scalarHeap (c.seed.C+i)) ∧
 (∀i,i<7*c.seed.width→u.scalarHeap (c.seed.negative+i)=s.scalarHeap (c.seed.negative+i)) ∧
 (∀i,i<6→u.scalarHeap (c.seed.constants+i)=s.scalarHeap (c.seed.constants+i)) := by
 refine ⟨fun i hi=>h.scalarOutside _ (Or.inl (by have:=l.positiveBelow;omega)),
  fun i hi=>h.scalarOutside _ (Or.inl (by have:=l.negativeBelow;omega)),
  fun i hi=>h.scalarOutside _ (Or.inl (by have:=l.constantsBelow;omega))⟩

/-- The complete1286-instruction seed/chunk helper preserves new caller1450+.
This finite footprint is verified on actual instruction constructors. -/
def below (p:Program) := p.all (fun i=>decide (UniformSeedHeightPreparation.natCeiling i≤1450))
lemma below_append (p q:Program) : below (p++q)=(below p && below q) := List.all_append
lemma below_relocate (p:Program) (base ret:ℕ) : below (p.map (relocate base ret))=below p := by
 simp [below,List.all_map,Function.comp_def,UniformSeedHeightPreparation.natCeiling_relocate]
lemma seed_ceiling : ∀i∈UniformSeedChunkPreparation.program,
 UniformSeedHeightPreparation.natCeiling i≤1450 := by
 have seed:below UniformSeedHeightPreparation.program=true:=by
  apply List.all_eq_true.mpr
  intro i hi;exact decide_eq_true (by have:=UniformSeedChunkPreparation.seedHeight_ceiling i hi;omega)
 have chunk:below UniformChunkMatchingPreparation.program=true:=by decide
 have all:below UniformSeedChunkPreparation.program=true:=by
  simp only [UniformSeedChunkPreparation.program,UniformSeedChunkPreparation.beforeChunk,
   UniformSeedChunkPreparation.beforeSetup,below_append,below_relocate,seed,chunk,Bool.and_eq_true]
  repeat' apply And.intro
  all_goals decide
 simpa only [below,List.all_eq_true,decide_eq_true_eq] using all
lemma seed_keeps (q:ℕ) (hq:1450≤q) : ∀i∈UniformSeedChunkPreparation.program,
 UniformNewtonTableMachine.KeepsNat q i := by
 intro i hi
 have h:=seed_ceiling i hi
 cases i <;> simp only [UniformSeedHeightPreparation.natCeiling] at h
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega

lemma Packed.preserved {n B:ℕ} {j:Fin (axisCount n)} {c:Config} (l:Layout n j c B)
 {v:Fin l.packing.total→Scalar} {s u:State} (h:Packed l v s u) :
 UniformSeedRankCrossPreparation.PreservedFrame n s u := by
 have lo:=UniformMatchingPackingPreparation.layout_order l.bridge
 have old:=l.seed.oldRows
 refine ⟨?_,fun q hq=>h.scalarOutside q (Or.inl (hq.trans_le l.seedBelow)),
  fun q lo hi=>h.frame.2.2.1 q (by omega),h.frame.1,h.frame.2.1⟩
 intro q hq
 apply UniformSectorPackingMachine.protected_prefix l.packing s u h.natOutside q
 have f:=l.seed.seed.oldBanks.directory
 have fd:=l.seed.seed.heightLayout.directory
 have b:=l.seed.borrowFresh;have z:=l.seed.selectedFresh;have t:=l.seed.ordinalFresh
 have a:=l.seed.mappedFresh;have p:=l.seed.permutationFresh;have w:=l.seed.widthsFresh
 have m:=l.seed.markersFresh
 change directoryBase n+2*axisCount n≤c.seed.directory at f
 change c.seed.directory+c.seed.gates+2≤c.seed.rows at fd
 change c.seed.rows+6*c.seed.gates*(8*c.seed.exponent+7)≤c.borrowed at old
 have order:c.axis+4≤l.packing.suffix:=lo.1
 omega

/-- One continuously charged1438-instruction program. Seed/height/matching
and packing-address banks are derived internally. The contiguous input bank
is supplied honestly; producing a tensor-fiber gather is a separate obligation. -/
theorem execution {n B:ℕ} (hn:0<n) (j:Fin (axisCount n)) (c:Config)
 (l:Layout n j c B) (v:Fin l.packing.total→Scalar) (x:Fin n→ℂ) (s:State)
 (args:UniformSeedChunkPreparation.Args n j c s) (packingArgs:Args l s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
 (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (sourceLow:l.packing.source+l.packing.total≤axisBase n (axisCount n))
 (pc:s.pc=0) (bound:WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks≤UniformSeedChunkPreparation.runtimeBudget n j c+213*l.packing.total+35 ∧ u.pc=1437 ∧
 (∃z,UniformSeedChunkPreparation.Result n j c B hn l.seed z ∧ Packed l v z u) ∧
 Retained n (axisCount n) u ∧ UniformPermutationInversePreparation.Metadata n u ∧
 UniformInitialPreparation.Operands n x u := by
 obtain ⟨z,t,run,cost,zpc,post,_,_,_,frame⟩:=
  UniformSeedChunkPreparation.execution hn j c B x s args metadata ret ops l.seed pc bound
 have moved:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedChunkPreparation.program_length];have:=l.code;omega)
  (by have:=l.code;omega) run
 rw [show placed 0 s=s by cases s;simp [placed]] at moved
 let a:=setPC z 1286
 have postA:UniformSeedChunkPreparation.Result n j c B hn l.seed a:=
  ⟨UniformSeedChunkPreparation.seedResult_transport hn l.seed post.prepared (fun _ _=>rfl) rfl
    (fun _ _ _=>rfl),post.header.withPC _,post.count,post.rows,post.widths,post.permutations,post.mapped⟩
 have copied:Args l a:=by
  rcases packingArgs with ⟨h0,h1,h2,h3,h4⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals first
  | exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (seed_keeps 1450 (by decide))).trans h0
  | exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (seed_keeps 1451 (by decide))).trans h1
  | exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (seed_keeps 1452 (by decide))).trans h2
  | exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (seed_keeps 1453 (by decide))).trans h3
  | exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (seed_keeps 1454 (by decide))).trans h4
 have src:UniformSectorPackingMachine.SourceReady l.packing v a:=by
  intro i
  change z.scalarHeap (l.packing.source+i.val)=some (v i)
  rw [frame.2.1 (l.packing.source+i.val) (by have:=i.isLt;omega)]
  exact source i
 obtain ⟨u,tp,last,cp,up,packed⟩:=packing_stage hn l v x a postA copied src program 1286 1437
  full_headers_code full_packing_code halt_at (by have:=l.code;omega) (by have:=l.code;omega)
  rfl moved.final_bound
 have finalFrame:=frame.trans (packed.preserved l)
 refine ⟨u,t+tp,moved.executes last,by omega,up,⟨a,postA,packed⟩,
  finalFrame.retained ret,finalFrame.protected.metadata metadata,finalFrame.protected.operands ops⟩

/-- The produced array is exactly the canonical sector packing, with no
assumed generated permutation or host coordinate writes. -/
theorem Packed.sectorCoordinates {n B:ℕ} {j:Fin (axisCount n)} {c:Config}
 {l:Layout n j c B} {v:Fin l.packing.total→Scalar} {s u:State} (h:Packed l v s u)
 (z:UniformSectorPacking.SectorPosition (UniformSectorPackingMachine.physicalAxes (axes l))) :
 u.scalarHeap (l.packing.destination+
  (finCongr (volume l) (UniformSectorPacking.packedEquiv _ z)).val)=some
  (v (finCongr (volume l) (UniformSectorPacking.originalEquiv _ z))) := by
 rw [←UniformMatchingPackingPreparation.physicalUnpacking_coordinate]
 exact h.values _

/-- Actual prepared scalar banks produced by SeedHeight/Chunk are preserved,
including all dependency flags. This does not execute a six-C matching round. -/
theorem Packed.coefficientBanks {n B:ℕ} (hn:0<n) {j:Fin (axisCount n)} {c:Config}
 (l:Layout n j c B) {v:Fin l.packing.total→Scalar} {s u:State}
 (post:UniformSeedChunkPreparation.Result n j c B hn l.seed s) (h:Packed l v s u) :
 UniformKernelSpectrumMachine.Result c.seed.exponent c.seed.C
  (UniformRankCrossPreparationMachine.kernelValues (UniformSeedHeightPreparation.parameters n j c.seed).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) u ∧
 u.scalarHeap (c.seed.C+7*c.seed.width)=some (UniformPairMachine.prepared (OAI.ExactFourier.zeta c.seed.width)) ∧
 UniformReplayCoefficientMachine.NegativeBank c.seed.negative (7*c.seed.width)
  (UniformRankCrossReplayPreparationMachine.bankValues (UniformSeedHeightPreparation.parameters n j c.seed)
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j)) u ∧
 UniformReplayCoefficientMachine.Constants c.seed.exponent c.seed.constants u := by
 have keep:=coefficients_retained l h
 refine ⟨?_,?_,?_,?_⟩
 · intro i
   have hi:i.val<7*c.seed.width+1:=by
    have ht:=i.isLt
    change i.val<UniformRadixTwoDAG.width c.seed.exponent+6*UniformRadixTwoDAG.width c.seed.exponent at ht
    change i.val<7*UniformRadixTwoDAG.width c.seed.exponent+1
    omega
   rw [keep.1 i.val hi]
   exact post.prepared.positive i
 · rw [keep.1 (7*c.seed.width) (by omega)]
   exact post.prepared.root
 · intro i hi;rw [keep.2.1 i hi];exact post.prepared.negative i hi
 · intro i hi;rw [keep.2.2 i hi];exact post.prepared.constants i hi

lemma runtime_bound {n B:ℕ} (j:Fin (axisCount n)) (c:Config) (l:Layout n j c B) :
 UniformSeedChunkPreparation.runtimeBudget n j c+213*l.packing.total+35≤
 100000600*(8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2)^5 := by
 have prior:=l.seed.runtime_bound j c B
 rw [l.volume]
 let z:=8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2
 have hz:1≤z:=by dsimp [z];omega
 have pow:z≤z^5:=le_self_pow hz (by decide)
 change UniformSeedChunkPreparation.runtimeBudget n j c≤100000300*z^5 at prior
 change _≤100000600*z^5
 have rz:radix n j+1≤z:=by dsimp [z];omega
 nlinarith

end
end ExactFourierCircuits.UniformSeedChunkPackingPreparation
