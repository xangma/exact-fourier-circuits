import UniformChunkMatchingPreparation
import UniformMultiAxisSectorMetadataPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisEdgeProducer
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformAllAxisSeedPreparation (axisCount)
open UniformPermutationInversePreparation (Metadata)
open UniformToeplitzCrossDAG (crossDAG)

/-- Readonly4200 axis index,4201..4212 ordinary chunk source/target/work/depth/color,
4219 output edge directory. No generated count, edge, color or matching enters. -/
def rootRead : List Op := [.literal 4213 0,.literal 4214 1,.literal 4215 2,.literal 4216 4,
 .mul 4217 4200 4216,.add 4217 102 4217,.add 4217 105 4217,.getNat 1180 4217]
def copyHeaders : List Op :=[.add 1181 4201 4213,.add 1182 4202 4213,.add 1183 4203 4213,.add 1184 4204 4213,.add 1185 4205 4213,.add 1186 4206 4213,.add 1187 4207 4213,.add 1188 4208 4213,.add 1189 4209 4213,.add 1190 4210 4213,.add 1191 4211 4213,.add 1192 4212 4213]
def setup : List Op :=rootRead++copyHeaders
def emit : List Op := [.mul 4218 4200 4215,.add 4218 4219 4218,
 .putNat 4218 894,.add 4218 4218 4214,.putNat 4218 1186]
def beforeChunk : Program :=UniformCrossHeightPreparationMachine.program.map (relocate 0 186) ++setup.map Op.code
def beforeEmit : Program :=beforeChunk++UniformChunkMatchingPreparation.program.map (relocate 206 421)
def program : Program := beforeEmit ++emit.map Op.code ++ [.halt]
lemma setup_length : setup.length=20 :=rfl
lemma emit_length : emit.length=5 :=rfl
lemma beforeChunk_length : beforeChunk.length=206 :=by
 simp only [beforeChunk,List.length_append,List.length_map,UniformCrossHeightPreparationMachine.program_length,setup_length]
lemma beforeEmit_length : beforeEmit.length=421 :=by
 simp only [beforeEmit,List.length_append,List.length_map,beforeChunk_length,UniformChunkMatchingPreparation.program_length]
lemma program_length : program.length=427 :=by
 simp only [program,List.length_append,List.length_map,beforeEmit_length,emit_length];rfl
lemma height_code : CodeAt UniformCrossHeightPreparationMachine.program program 0 186 :=by
 let after:=setup.map Op.code++UniformChunkMatchingPreparation.program.map (relocate 206 421)++emit.map Op.code++[.halt]
 have eq:program=[]++UniformCrossHeightPreparationMachine.program.map (relocate 0 186)++after:=by
  simp only [program,beforeEmit,beforeChunk,after,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] after _ 0 186 rfl
lemma chunk_code : CodeAt UniformChunkMatchingPreparation.program program 206 421 :=by
 intro i hi
 have il:i<215:=by simpa only [UniformChunkMatchingPreparation.program_length] using hi
 rw [program,List.getElem?_append_left (by
  simp only [List.length_append,List.length_map,beforeEmit_length,emit_length];omega)]
 rw [List.getElem?_append_left (by rw [beforeEmit_length];omega)]
 rw [beforeEmit,List.getElem?_append_right (by rw [beforeChunk_length];omega)]
 simp only [beforeChunk_length,show 206+i-206=i by omega,List.getElem?_map]
lemma setup_code : BlockAt setup program 186 :=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformCrossHeightPreparationMachine.program.map (relocate 0 186)) (setup.map Op.code)
  (UniformChunkMatchingPreparation.program.map (relocate 206 421)++emit.map Op.code++[.halt]) i (by simpa using hi)
 simpa only [program,beforeEmit,beforeChunk,List.append_assoc,List.length_map,UniformCrossHeightPreparationMachine.program_length,
 List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma emit_code : BlockAt emit program 421 :=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment beforeEmit (emit.map Op.code) [.halt] i (by simpa using hi)
 simpa only [program,beforeEmit_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma halt_at : program[426]?=some .halt :=by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,beforeEmit_length,emit_length];omega)]
 simp only [List.length_append,List.length_map,beforeEmit_length,emit_length];rfl

noncomputable section

def register (p:UniformChunkMatchingPreparation.Parameters) : ℕ→ℕ
 | 4201=>p.source | 4202=>p.target | 4203=>p.borrowed | 4204=>p.selected | 4205=>p.ordinals
 | 4206=>p.mapped | 4207=>p.permutation | 4208=>p.widths | 4209=>p.markers | 4210=>p.axis
 | 4211=>p.depth | 4212=>p.color | _=>0
structure Header {n:ℕ} (j:Fin (axisCount n)) (p:UniformChunkMatchingPreparation.Parameters) (directory:ℕ) (s:State):Prop where
 height : UniformCrossHeightPreparationMachine.Header p.height s
 index : s.natReg 4200=j.val
 args : ∀q,4201≤q→q≤4212→s.natReg q=register p q
 directory : s.natReg 4219=directory

structure Layout {n:ℕ} (j:Fin (axisCount n)) (p:UniformChunkMatchingPreparation.Parameters) (directory B:ℕ):Prop where
 radix : p.radix=UniformSelectedCRT.radices n j
 chunk : UniformChunkMatchingPreparation.Layout p B
 height : UniformCrossHeightPreparationMachine.Layout p.height
 words : UniformCrossHeightPreparationMachine.wordBudget p.height≤B
 protectedRows : copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)≤p.height.D
 protectedColors : copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)≤p.height.F
 protectedPalette : copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)≤p.height.U
 protectedDirectory : copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)≤p.height.J
 directoryFresh : p.axis+4≤directory
 directoryBound : directory+2*axisCount n≤B
 code : 427≤B

/-- Only honest original typed Cross271, Depth35/Bucket24 banks are accepted.
Height rows/colors, selected/mapped edges and matching are generated internally. -/
structure Original (p:UniformChunkMatchingPreparation.Parameters)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) (s:State):Prop where
 bank : UniformDAGBucketMachine.Bank p.height.Q
  (UniformDAGBucketMachine.order (crossDAG p.height.K p.height.a p.height.e ha he).size
   (UniformDAGBucketMachine.typedDepth (crossDAG p.height.K p.height.a p.height.e ha he).program)) s
 directory : UniformDAGBucketMachine.Directory p.height.R
  (crossDAG p.height.K p.height.a p.height.e ha he).size
  ((crossDAG p.height.K p.height.a p.height.e ha he).size+2)
  (UniformDAGBucketMachine.typedDepth (crossDAG p.height.K p.height.a p.height.e ha he).program) s
 tape : UniformToeplitzCrossTopologyMachine.RowTable
  (UniformToeplitzCrossTopologyMachine.crossRows p.height.K p.height.a p.height.e) p.height.T s

lemma root_cell {n:ℕ} (j:Fin (axisCount n)) (s:State) (hm:Metadata n s):
 s.natHeap (copyBase n+ell n+4*j.val)=some (UniformSelectedCRT.radices n j):=by
 have h:=(hm.crt j).1
 simpa only [UniformCRTHeaderMachine.tableAddress,UniformInitialPreparation.protectedView,
  UniformSelectedCRT.radices,UniformInitialPreparation.ell,UniformInitialPreparation.len,
  Nat.add_assoc,Nat.add_zero] using h


lemma root_keeps (s:State) (q:ℕ) (hq:q≠1180) (lo:q<4213 ∨4218≤q):
 (applyBlock rootRead s).natReg q=s.natReg q :=by
 simp (disch:=omega) [rootRead,applyBlock,Op.apply,writeNat,next]
lemma copy_keeps (s:State) (q:ℕ) (lo:q<1181 ∨1193≤q):
 (applyBlock copyHeaders s).natReg q=s.natReg q :=by
 simp (disch:=omega) [copyHeaders,applyBlock,Op.apply,writeNat,next]
lemma root_height {p:UniformChunkMatchingPreparation.Parameters} {s:State}
 (h:UniformCrossHeightPreparationMachine.Header p.height s):
 UniformCrossHeightPreparationMachine.Header p.height (applyBlock rootRead s) :=by
 constructor
 all_goals first
 | exact (root_keeps s _ (by omega) (by omega)).trans h.exponent
 | exact (root_keeps s _ (by omega) (by omega)).trans h.targets
 | exact (root_keeps s _ (by omega) (by omega)).trans h.inputs
 | exact (root_keeps s _ (by omega) (by omega)).trans h.tape
 | exact (root_keeps s _ (by omega) (by omega)).trans h.order
 | exact (root_keeps s _ (by omega) (by omega)).trans h.sourceDirectory
 | exact (root_keeps s _ (by omega) (by omega)).trans h.rows
 | exact (root_keeps s _ (by omega) (by omega)).trans h.colors
 | exact (root_keeps s _ (by omega) (by omega)).trans h.palette
 | exact (root_keeps s _ (by omega) (by omega)).trans h.directory
 | exact (root_keeps s _ (by omega) (by omega)).trans h.coefficients
 | exact (root_keeps s _ (by omega) (by omega)).trans h.enabled
 | exact (root_keeps s _ (by omega) (by omega)).trans h.constants
lemma copy_height {p:UniformChunkMatchingPreparation.Parameters} {s:State}
 (h:UniformCrossHeightPreparationMachine.Header p.height s):
 UniformCrossHeightPreparationMachine.Header p.height (applyBlock copyHeaders s) :=by
 constructor
 all_goals first
 | exact (copy_keeps s _ (by omega)).trans h.exponent
 | exact (copy_keeps s _ (by omega)).trans h.targets
 | exact (copy_keeps s _ (by omega)).trans h.inputs
 | exact (copy_keeps s _ (by omega)).trans h.tape
 | exact (copy_keeps s _ (by omega)).trans h.order
 | exact (copy_keeps s _ (by omega)).trans h.sourceDirectory
 | exact (copy_keeps s _ (by omega)).trans h.rows
 | exact (copy_keeps s _ (by omega)).trans h.colors
 | exact (copy_keeps s _ (by omega)).trans h.palette
 | exact (copy_keeps s _ (by omega)).trans h.directory
 | exact (copy_keeps s _ (by omega)).trans h.coefficients
 | exact (copy_keeps s _ (by omega)).trans h.enabled
 | exact (copy_keeps s _ (by omega)).trans h.constants
lemma root_radix {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B) (s:State) (hm:Metadata n s) (h:Header j p directory s):
 (applyBlock rootRead s).natReg 1180=p.radix :=by
 have root:=root_cell j s hm
 have cell:s.natHeap (s.natReg 105+(s.natReg 102+s.natReg 4200*4))=some p.radix:=by
  rw [hm.saved.copyAddress,hm.saved.count,h.index,l.radix]
  simpa only [Nat.mul_comm,Nat.add_assoc] using root
 simp [rootRead,applyBlock,Op.apply,writeNat,next,cell]

lemma apply_append (a b:List Op) (s:State):applyBlock (a++b) s=applyBlock b (applyBlock a s) :=by
 induction a generalizing s with
 | nil=>rfl
 | cons op a ih=>simp only [List.cons_append,applyBlock,ih]

lemma copied_header (p:UniformChunkMatchingPreparation.Parameters) (s:State)
 (height:UniformCrossHeightPreparationMachine.Header p.height s)
 (radix:s.natReg 1180=p.radix) (zero:s.natReg 4213=0)
 (args:∀q,4201≤q→q≤4212→s.natReg q=register p q):
 UniformChunkMatchingPreparation.Header p (applyBlock copyHeaders s) :=by
 constructor
 · exact copy_height height
 · exact (copy_keeps s 1180 (by omega)).trans radix
 all_goals simp (disch:=omega) [copyHeaders,applyBlock,Op.apply,writeNat,next,zero,register,args]

lemma setup_header {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B) (s:State) (hm:Metadata n s) (h:Header j p directory s):
 UniformChunkMatchingPreparation.Header p (applyBlock setup s) :=by
 have height:=root_height h.height
 have radix:=root_radix l s hm h
 have zero:(applyBlock rootRead s).natReg 4213=0:=by simp [rootRead,applyBlock,Op.apply,writeNat,next]
 have args:∀q,4201≤q→q≤4212→(applyBlock rootRead s).natReg q=register p q:=by
  intro q lo hi;exact (root_keeps s q (by omega) (by omega)).trans (h.args q lo hi)
 have done:=copied_header p (applyBlock rootRead s) height radix zero args
 simpa only [setup,apply_append] using done

lemma rootRead_length : rootRead.length=8 :=rfl
lemma copyHeaders_length : copyHeaders.length=12 :=rfl
lemma root_code : BlockAt rootRead program 186 :=by
 intro i hi
 have h:=setup_code i (by rw [setup_length];rw [rootRead_length] at hi;omega)
 have eq:(setup[i]'(by rw [setup_length];rw [rootRead_length] at hi;omega))=rootRead[i]'hi:=by
  simp only [setup,List.getElem_append_left hi]
 simpa only [eq] using h
lemma copy_code : BlockAt copyHeaders program 194 :=by
 intro i hi
 have h:=setup_code (8+i) (by rw [setup_length];rw [copyHeaders_length] at hi;omega)
 have eq:(setup[8+i]'(by rw [setup_length];rw [copyHeaders_length] at hi;omega))=copyHeaders[i]'hi:=by
  unfold setup
  have ge:rootRead.length≤8+i:=by have h:=rootRead_length;omega
  rw [List.getElem_append_right ge]
  simp only [rootRead_length,show 8+i-8=i by omega]
 simpa only [eq,show 186+(8+i)=194+i by omega] using h

def Frame (s u:State):Prop:=u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧(∀q,100≤q→q≤106→u.natReg q=s.natReg q) ∧
 (∀q,4200≤q→(q<4213 ∨4219≤q)→u.natReg q=s.natReg q)
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.1.trans h.2.2.2.1,
 fun q lo hi=>(k.2.2.2.2.1 q lo hi).trans (h.2.2.2.2.1 q lo hi),
 fun q lo hi=>(k.2.2.2.2.2 q lo hi).trans (h.2.2.2.2.2 q lo hi)⟩
lemma Frame.withPC {s u:State} (h:Frame s u) (pc:ℕ):Frame s (setPC u pc):=h
lemma Frame.metadataFrame {s u:State} (h:Frame s u):UniformMultiAxisSectorMetadataPreparation.Retention s u:=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
lemma height_frame {s u:State} (f:UniformCrossHeightPreparationMachine.Frame s u):Frame s u:=by
 refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,?_,?_⟩
 all_goals intro q lo hi;apply f.2.2.2.2 q
 all_goals unfold UniformCrossHeightPreparationMachine.Protected UniformCrossDepthReplayPreparation.Protected
 all_goals omega
lemma chunk_frame {s u:State} (f:UniformChunkMatchingPreparation.Frame s u):Frame s u:=by
 refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,?_,?_⟩
 all_goals intro q lo hi;apply f.2.2.2.2 q
 all_goals unfold UniformChunkMatchingPreparation.Protected;omega
lemma root_frame (s:State):Frame s (applyBlock rootRead s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
 all_goals intro q lo hi;exact root_keeps s q (by omega) (by omega)
lemma copy_frame (s:State):Frame s (applyBlock copyHeaders s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
 all_goals intro q lo hi;exact copy_keeps s q (by omega)
lemma emit_frame (s:State):Frame s (applyBlock emit s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
 all_goals intro q lo hi;simp (disch:=omega) [emit,applyBlock,Op.apply,writeNat,next]
lemma Header.transport {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory:ℕ} {s u:State} (h:Header j p directory s) (f:Frame s u)
 (height:UniformCrossHeightPreparationMachine.Header p.height u):Header j p directory u:=
 ⟨height,(f.2.2.2.2.2 4200 (by omega) (by omega)).trans h.index,
 fun q lo hi=>(f.2.2.2.2.2 q (by omega) (by omega)).trans (h.args q lo hi),
 (f.2.2.2.2.2 4219 (by omega) (by omega)).trans h.directory⟩
lemma Header.withPC {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory:ℕ} {s:State} (h:Header j p directory s) (pc:ℕ):Header j p directory (setPC s pc):=
 ⟨h.height.withPC _,h.index,h.args,h.directory⟩

lemma root_safe {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B) (s:State) (hm:Metadata n s) (h:Header j p directory s):
 readable rootRead s ∧peak rootRead s≤B:=by
 have q:=j.isLt
 unfold axisCount at q
 have jBound:j.val≤ell n:=by omega
 have span:=l.protectedRows
 have code:=l.code
 unfold UniformGlobalNatPreparation.amount at span
 have db:p.height.D≤B:=by
  have b:=l.words
  unfold UniformCrossHeightPreparationMachine.wordBudget UniformCrossHeightPreparationMachine.rowBase at b
  omega
 have r:p.radix≤B:=by
  have c:=l.chunk.permutationFresh
  have d:=l.chunk.widthsFresh
  have e:=l.chunk.markersFresh
  have f:=l.chunk.finalBound
  omega
 have root:=root_cell j s hm
 have cell:s.natHeap (UniformGlobalNatPreparation.destination (ell n) (len n)+(ell n+j.val*4))=some p.radix:=by
  simpa only [copyBase,Nat.mul_comm,Nat.add_assoc,←l.radix] using root
 simp [rootRead,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.index,hm.saved.copyAddress,hm.saved.count,cell]
 unfold copyBase at span
 omega

lemma copy_safe (s:State) (B:ℕ) (zero:s.natReg 4213=0) (wb:WordBound B s):
 readable copyHeaders s ∧peak copyHeaders s≤B:=by
 have args:∀q,s.natReg q≤B:=wb.2.1
 simp [copyHeaders,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero]
 repeat' constructor
 all_goals exact args _
lemma setup_heap (s:State):(applyBlock setup s).natHeap=s.natHeap:=rfl
lemma emit_below (s:State) (directory:ℕ) (hd:s.natReg 4219=directory) (two:s.natReg 4215=2)
 (one:s.natReg 4214=1) (q:ℕ) (lo:q<directory):
 (applyBlock emit s).natHeap q=s.natHeap q:=by
 simp (disch:=omega) [emit,applyBlock,Op.apply,writeNat,next,hd,two,one]

def edgeCount (p:UniformChunkMatchingPreparation.Parameters)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height):ℕ:=
 (UniformChunkMatchingPreparation.indices p (UniformChunkMatchingPreparation.crossWord p ha he)).length
def edges {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height):Fin (edgeCount p ha he)→UniformColoring.Edge:=
 UniformChunkMatchingPreparation.physicalEdges l.chunk
  (UniformChunkMatchingPreparation.crossWord p ha he) (UniformChunkMatchingPreparation.cross_domain p ha he)
lemma edges_matching {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height):
 UniformMatchingAxisTableMachine.Matching (edges l ha he):=
 UniformChunkMatchingPreparation.physical_matching l.chunk
  (UniformChunkMatchingPreparation.cross_domain p ha he) (UniformChunkMatchingPreparation.cross_degree p ha he)
lemma edges_range {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height):
 UniformMatchingAxisTableMachine.InRange (UniformSelectedCRT.radices n j) (edges l ha he):=by
 rw [←l.radix]
 exact UniformChunkMatchingPreparation.physical_range l.chunk (UniformChunkMatchingPreparation.cross_domain p ha he)


lemma processed_sameHeap {v:UniformCrossHeightPreparationMachine.Parameters} {Z G d:ℕ}
 {p:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize v.K) v.e G} {s u:State}
 (h:UniformCrossHeightPreparationMachine.Processed v Z p d s) (same:u.natHeap=s.natHeap):
 UniformCrossHeightPreparationMachine.Processed v Z p d u:=by
 simpa only [UniformCrossHeightPreparationMachine.Processed,UniformCrossHeightPreparationMachine.Slice,
  UniformCrossShearTableMachine.Table,UniformCrossShearTableMachine.RowFields,
  UniformCrossHeightPreparationMachine.Record,same] using h
lemma height_metadata {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B) {s u:State} (hm:Metadata n s)
 (outside:UniformCrossHeightPreparationMachine.Outside p.height s u)
 (frame:UniformCrossHeightPreparationMachine.Frame s u):Metadata n u:=by
 apply UniformMultiAxisSectorMetadataPreparation.retained_metadata hm (height_frame frame).metadataFrame
  (copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)) (le_refl _)
 intro q lo
 exact outside q (Or.inl (lt_of_lt_of_le lo l.protectedRows))
  (Or.inl (lt_of_lt_of_le lo l.protectedColors)) (Or.inl (lt_of_lt_of_le lo l.protectedPalette))
  (Or.inl (lt_of_lt_of_le lo l.protectedDirectory))
lemma root_heap (s:State):(applyBlock rootRead s).natHeap=s.natHeap:=rfl
lemma copy_heap (s:State):(applyBlock copyHeaders s).natHeap=s.natHeap:=rfl
lemma root_constants (s:State):
 (applyBlock rootRead s).natReg 4213=0 ∧(applyBlock rootRead s).natReg 4214=1 ∧
 (applyBlock rootRead s).natReg 4215=2:=by
 simp [rootRead,applyBlock,Op.apply,writeNat,next]
lemma copy_constants (s:State):
 (applyBlock copyHeaders s).natReg 4214=s.natReg 4214 ∧
 (applyBlock copyHeaders s).natReg 4215=s.natReg 4215:=
 ⟨copy_keeps s _ (by omega),copy_keeps s _ (by omega)⟩
lemma emit_index (s:State) (j:ℕ) (directory:ℕ) (hi:s.natReg 4200=j) (hd:s.natReg 4219=directory)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 (applyBlock emit s).natHeap (directory+2*j)=some (s.natReg 894) ∧
 (applyBlock emit s).natHeap (directory+2*j+1)=some (s.natReg 1186):=by
 simp [emit,applyBlock,Op.apply,writeNat,next,hi,hd,one,two,Nat.mul_comm]
lemma emit_safe {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B) (s:State) (hi:s.natReg 4200=j.val)
 (hd:s.natReg 4219=directory) (one:s.natReg 4214=1) (two:s.natReg 4215=2) (wb:WordBound B s):
 readable emit s ∧peak emit s≤B:=by
 have ji:=j.isLt
 have fit:=l.directoryBound
 have count:=wb.2.1 894
 have mapped:=wb.2.1 1186
 simp [emit,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,hi,hd,one,two]
 omega
lemma chunk_emit_constants {s u:State} (frame:UniformChunkMatchingPreparation.Frame s u):
 u.natReg 4214=s.natReg 4214 ∧u.natReg 4215=s.natReg 4215:=by
 constructor
 all_goals apply frame.2.2.2.2;unfold UniformChunkMatchingPreparation.Protected;omega
lemma mapped_edges_closed {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) {Z:ℕ} {s:State}
 (table:UniformCrossShearTableMachine.Table p.mapped
  (UniformChunkMatchingPreparation.mappedRows p l.chunk.capacity
   (UniformChunkMatchingPreparation.crossWord p ha he) (UniformChunkMatchingPreparation.crossLocations p Z)) s):
 UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped s:=by
 have size:(UniformChunkMatchingPreparation.crossWord p ha he).length≤2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [UniformChunkMatchingPreparation.crossWord,UniformCrossHeightPreparationMachine.cross_size p.height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled p.depth
 have selected:(UniformChunkMatchingPreparation.selectedRows p (UniformChunkMatchingPreparation.crossWord p ha he)
  (UniformChunkMatchingPreparation.crossLocations p Z)).length≤2*UniformCrossHeightPreparationMachine.gates p.height:=by
  rw [UniformChunkMatchingPreparation.selectedRows,List.length_map]
  exact (UniformChunkMatchingPreparation.selected_count p _).trans size
 exact UniformChunkMatchingPreparation.mapped_edges l.chunk
  (UniformChunkMatchingPreparation.cross_domain p ha he) (UniformChunkMatchingPreparation.row_geometry l.chunk selected) table


/-- Charged generation of all depth/color rows, followed by the actual CRT
radix read and ordinary chunk-header installation. No generated table premise. -/
theorem prepare_execution {n:ℕ} (j:Fin (axisCount n)) (p:UniformChunkMatchingPreparation.Parameters)
 (directory Z B m:ℕ) (x:Fin m→ℂ) (s:State)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (l:Layout j p directory B) (h:Header j p directory s) (hm:Metadata n s)
 (orig:Original p ha he s) (pc:s.pc=0) (wb:WordBound B s):
 ∃u ticks,BoundedRuns program m x B s ticks u ∧
 ticks≤4*p.height.K+47+(8*p.height.K+7)*(64*UniformCrossHeightPreparationMachine.gates p.height+
  200*(2*UniformCrossHeightPreparationMachine.gates p.height+1)^2+56) ∧u.pc=206 ∧
 UniformChunkMatchingPreparation.Header p u ∧
 UniformCrossHeightPreparationMachine.Processed p.height Z (crossDAG p.height.K p.height.a p.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height p.height) u ∧
 u.natReg 4214=1 ∧u.natReg 4215=2 ∧
 UniformCrossHeightPreparationMachine.Outside p.height s u ∧Frame s u:=by
 obtain ⟨a,t,run,cost,apc,cursor,_,done,out,frame⟩:=UniformCrossHeightPreparationMachine.cross_execution
  p.height Z B m ha he x s h.height pc wb l.height l.words orig.bank orig.directory orig.tape
 have code:=l.code
 let e:=setPC a 186
 have first:BoundedRuns program m x B s t e:=by
  have q:=UniformBoundedAssembly.boundedExecution_placed height_code
   (by rw [UniformCrossHeightPreparationMachine.program_length];omega) (by omega) run
  change BoundedRuns program m x B (UniformAssembly.placed 0 s) t e at q
  have eq:UniformAssembly.placed 0 s=s:=by cases s;simp [UniformAssembly.placed]
  rw [eq] at q
  exact q
 have fe:Frame s e:=(height_frame frame).withPC _
 have eh:Header j p directory e:=h.transport fe (cursor.header.withPC 186)
 have em:Metadata n e:=height_metadata l hm out frame
 have esafe:=root_safe l e em eh
 let r:State:=applyBlock rootRead e
 have second:BoundedRuns program m x B e 8 r:=by
  simpa only [rootRead_length] using block_runs rootRead program 186 m B x e root_code rfl
   first.final_bound (by rw [rootRead_length];omega) esafe.1 esafe.2
 have rpc:r.pc=194:=by dsimp only [r];rw [UniformTensorMonomialMachine.applyBlock_pc,rootRead_length];rfl
 have rh:UniformCrossHeightPreparationMachine.Header p.height r:=root_height eh.height
 have rad:r.natReg 1180=p.radix:=root_radix l e em eh
 have rc:r.natReg 4213=0 ∧r.natReg 4214=1 ∧r.natReg 4215=2:=root_constants e
 have args:∀(q:ℕ),4201≤q→q≤4212→State.natReg r q=register p q:=by
  intro q lo hi
  exact (root_keeps e q (by omega) (by omega)).trans (eh.args q lo hi)
 have rsafe:=copy_safe r B rc.1 second.final_bound
 let u:=applyBlock copyHeaders r
 have third:BoundedRuns program m x B r 12 u:=by
  simpa only [copyHeaders_length] using block_runs copyHeaders program 194 m B x r copy_code rpc
   second.final_bound (by rw [copyHeaders_length];omega) rsafe.1 rsafe.2
 have upc:u.pc=206:=by dsimp only [u];rw [UniformTensorMonomialMachine.applyBlock_pc,copyHeaders_length,rpc]
 have head:UniformChunkMatchingPreparation.Header p u:=copied_header p r rh rad rc.1 args
 have constants:=copy_constants r
 have fu:Frame s u:=fe.trans ((root_frame e).trans (copy_frame r))
 have udone:UniformCrossHeightPreparationMachine.Processed p.height Z
  (crossDAG p.height.K p.height.a p.height.e ha he).program (UniformCrossHeightPreparationMachine.height p.height) u:=
  processed_sameHeap done rfl
 exact ⟨u,t+8+12,first.trans (second.trans third),by omega,upc,head,udone,
  constants.1.trans rc.2.1,constants.2.trans rc.2.2,fun q h1 h2 h3 h4=>out q h1 h2 h3 h4,fu⟩


lemma layout_low {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B):
 p.height.D≤p.height.F ∧p.height.D≤p.height.U ∧p.height.D≤p.height.J ∧
 p.height.D≤p.borrowed ∧p.height.D≤directory:=by
 have rows:=l.height.rows
 have colors:=l.height.colors
 have palette:=l.height.palette
 have br:=l.chunk.oldRows
 have bf:=l.chunk.borrowFresh
 have sf:=l.chunk.selectedFresh
 have ofr:=l.chunk.ordinalFresh
 have mf:=l.chunk.mappedFresh
 have pf:=l.chunk.permutationFresh
 have wf:=l.chunk.widthsFresh
 have mk:=l.chunk.markersFresh
 have df:=l.directoryFresh
 unfold UniformCrossHeightPreparationMachine.rowBase at rows br
 unfold UniformCrossHeightPreparationMachine.colorBase at colors
 omega
lemma edgeCount_bound (p:UniformChunkMatchingPreparation.Parameters)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height):
 edgeCount p ha he≤2*UniformCrossHeightPreparationMachine.gates p.height:=by
 have size:(UniformChunkMatchingPreparation.crossWord p ha he).length≤2*UniformCrossHeightPreparationMachine.gates p.height:=by
  simpa only [UniformChunkMatchingPreparation.crossWord,UniformCrossHeightPreparationMachine.cross_size p.height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length (crossDAG p.height.K p.height.a p.height.e ha he).program p.height.enabled p.depth
 exact (UniformChunkMatchingPreparation.selected_count p _).trans size
lemma emit_edges {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) {s:State}
 (h:UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped s)
 (hd:s.natReg 4219=directory) (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped (applyBlock emit s):=by
 intro i
 have ib:=i.isLt
 have bound:=edgeCount_bound p ha he
 have m:=l.chunk.mappedFresh
 have pf:=l.chunk.permutationFresh
 have wf:=l.chunk.widthsFresh
 have mk:=l.chunk.markersFresh
 have df:=l.directoryFresh
 exact ⟨(emit_below s directory hd two one _ (by omega)).trans (h i).1,
  (emit_below s directory hd two one _ (by omega)).trans (h i).2⟩

def Result {n:ℕ} {j:Fin (axisCount n)} {p:UniformChunkMatchingPreparation.Parameters}
 {directory B:ℕ} (l:Layout j p directory B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) (s:State):Prop:=
 s.natHeap (directory+2*j.val)=some (edgeCount p ha he) ∧
 s.natHeap (directory+2*j.val+1)=some p.mapped ∧
 UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped s
/-- The literal427 realizes a selected axis edge directory continuously from
original Cross/Bucket physical banks. Matching/range are derived, not inputs.
This is geometry preparation; it asserts no Fourier action for the axis. -/
theorem execution {n:ℕ} (j:Fin (axisCount n)) (p:UniformChunkMatchingPreparation.Parameters)
 (directory Z B m:ℕ) (x:Fin m→ℂ) (s:State)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (l:Layout j p directory B) (h:Header j p directory s) (hm:Metadata n s)
 (orig:Original p ha he s) (pc:s.pc=0) (wb:WordBound B s):
 ∃u ticks,BoundedExecution program m x B s ticks u ∧
 ticks≤8*p.height.K+180*p.radix+145+(8*p.height.K+7)*(64*UniformCrossHeightPreparationMachine.gates p.height+
  200*(2*UniformCrossHeightPreparationMachine.gates p.height+1)^2+56) ∧u.pc=426 ∧
 Result l ha he u ∧Metadata n u ∧Frame s u ∧
 (∀q,q<p.height.D→q<directory→u.natHeap q=s.natHeap q):=by
 obtain ⟨a,t,run,cost,apc,header,done,one,two,out,frame⟩:=prepare_execution j p directory Z B m x s ha he l h hm orig pc wb
 have code:=l.code
 let a0:=setPC a 0
 obtain ⟨v,c,ccost,crun,chead,count,_,_,_,table,_,cout,cframe⟩:=UniformChunkMatchingPreparation.cross_execution
  p Z B m x a0 ha he l.chunk (header.withPC 0) (processed_sameHeap done rfl) rfl
  (changePC_bound B a 0 run.final_bound (by omega))
 let e:=setPC c 421
 have second:BoundedRuns program m x B a v e:=by
  have q:=UniformBoundedAssembly.boundedExecution_placed chunk_code
   (by rw [UniformChunkMatchingPreparation.program_length];omega) (by omega) crun
  rw [UniformMultiAxisSectorMetadataPreparation.placed_zero a 206 apc] at q
  exact q
 have fe:Frame s e:=frame.trans (chunk_frame cframe)
 have driver:(e.natReg 4200=j.val) ∧(e.natReg 4219=directory):=
  ⟨(fe.2.2.2.2.2 4200 (by omega) (by omega)).trans h.index,
  (fe.2.2.2.2.2 4219 (by omega) (by omega)).trans h.directory⟩
 have constants:=chunk_emit_constants cframe
 have eone:e.natReg 4214=1:=constants.1.trans one
 have etwo:e.natReg 4215=2:=constants.2.trans two
 have safe:=emit_safe l e driver.1 driver.2 eone etwo second.final_bound
 let u:=applyBlock emit e
 have third:BoundedRuns program m x B e 5 u:=by
  simpa only [emit_length] using block_runs emit program 421 m B x e emit_code rfl
   second.final_bound (by rw [emit_length];omega) safe.1 safe.2
 have upc:u.pc=426:=by dsimp only [u];rw [UniformTensorMonomialMachine.applyBlock_pc,emit_length];rfl
 have uf:Frame s u:=fe.trans (emit_frame e)
 have count':e.natReg 894=edgeCount p ha he:=count
 have records:=emit_index e j.val directory driver.1 driver.2 eone etwo
 have mapped:e.natReg 1186=p.mapped:=chead.mapped
 have bank:UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped e:=mapped_edges_closed l ha he table
 have ubank:UniformMatchingAxisTableMachine.Edges (edges l ha he) p.mapped u:=emit_edges l ha he bank driver.2 eone etwo
 have low:=layout_low l
 have below:∀q,q<p.height.D→q<directory→u.natHeap q=s.natHeap q:=by
  intro q hd hdir
  have aheap:=out q (Or.inl hd) (Or.inl (lt_of_lt_of_le hd low.1))
   (Or.inl (lt_of_lt_of_le hd low.2.1)) (Or.inl (lt_of_lt_of_le hd low.2.2.1))
  have cheap:=cout q (Or.inl (lt_of_lt_of_le hd low.2.2.2.1))
  exact (emit_below e directory driver.2 etwo eone q hdir).trans (cheap.trans aheap)
 have um:Metadata n u:=by
  apply UniformMultiAxisSectorMetadataPreparation.retained_metadata hm uf.metadataFrame
   (copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)) (le_refl _)
  intro q hq
  exact below q (lt_of_lt_of_le hq l.protectedRows) (lt_of_lt_of_le hq (l.protectedRows.trans low.2.2.2.2))
 have finish:BoundedExecution program m x B u 1 u:=.halt third.final_bound (by simp [step,upc,halt_at])
 refine ⟨u,t+v+5+1,run.executes (second.executes (third.executes finish)),by omega,upc,?_,um,uf,below⟩
 exact ⟨by simpa only [count'] using records.1,
  by simpa only [mapped] using records.2,ubank⟩

end
end ExactFourierCircuits.UniformAxisEdgeProducer
