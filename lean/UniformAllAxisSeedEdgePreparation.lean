import UniformSeedEdgeRetention
import UniformAxisEdgeProducer
import UniformAllAxisMatchingTablePreparation
import UniformEmptyStartupMatchingPreparation
import UniformSeedChunkPackingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisSeedEdgePreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformAllAxisSeedPreparation (axisCount radix Retained)
open UniformPermutationInversePreparation (Metadata)

def boot : List Op := [.literal 4253 0,.literal 4254 1,.literal 4255 2,.literal 4256 4,
 .literal 4257 196,.literal 4259 100000,.literal 4260 40,
 .add 4250 101 4255,.mul 4250 4250 4250,.mul 4250 4250 4259,
 .add 4251 102 4254,.literal 4252 0,
 .add 4270 4251 4254,.mul 4270 4270 4260,.mul 4270 4270 4250]
def rootRead : List Op :=[.add 4200 4252 4253,.add 4219 4270 4253]++UniformAxisEdgeProducer.rootRead
def emptyEmit : List Op :=[.literal 894 0,.literal 1186 0]++UniformAxisEdgeProducer.emit
/-- Every pointer is physically formed from the current axis's fresh arena.
No coefficient, typed tape, depth/order, or mapped edge is supplied. -/
def positions : List (ℕ×ℕ):=[(1127,1),(1128,2),(1129,1),(1130,3),(1131,2),(1132,3),
 (1133,4),(1134,5),(1135,6),(1136,4),(1137,5),(1220,7),(1221,8),(1222,9),(1223,10),
 (1230,30),(1231,31),(1232,32),(1233,33),(1234,34),(1235,35),(1236,36),(1237,37)]
def pointer (d k:ℕ):List Op :=[.literal 4263 k,.mul d 4250 4263,.add d 4262 d]
def installStart : List Op :=[.add 4262 4252 4254,.mul 4262 4262 4260,.mul 4262 4262 4250,
 .add 1120 4252 4253,.literal 1122 1,.literal 1123 1,.literal 1124 1,.literal 1125 0,
 .literal 1126 1,.literal 1224 1,.literal 1238 1,.literal 1239 0]
def pointers (ps:List (ℕ×ℕ)):List Op:=ps.flatMap (fun p=>pointer p.1 p.2)
def install : List Op:=installStart++pointers positions
def head : Program:=boot.map Op.code++[.branchLT 4252 4251 16 1409]++rootRead.map Op.code++
 [.branchLT 1180 4257 27 35]++emptyEmit.map Op.code++[.jump 1407]++install.map Op.code
def beforeEmit : Program:=head++UniformSeedChunkPreparation.program.map (relocate 116 1402)
def program : Program:=beforeEmit++UniformAxisEdgeProducer.emit.map Op.code++
 [.natBinary .add 4252 4252 4254,.jump 15,.halt]
lemma boot_length : boot.length=15:=rfl
lemma rootRead_length : rootRead.length=10:=rfl
lemma emptyEmit_length : emptyEmit.length=7:=rfl
lemma install_length : install.length=81:=rfl
lemma head_length : head.length=116:=by
 simp only [head,List.length_append,List.length_map,boot_length,rootRead_length,emptyEmit_length,install_length]
 rfl
lemma beforeEmit_length : beforeEmit.length=1402:=by
 simp only [beforeEmit,List.length_append,List.length_map,head_length,UniformSeedChunkPreparation.program_length]
lemma program_length : program.length=1410:=by
 simp only [program,List.length_append,List.length_map,beforeEmit_length,UniformAxisEdgeProducer.emit_length];rfl
lemma seed_code : CodeAt UniformSeedChunkPreparation.program program 116 1402:=by
 let tail:=UniformAxisEdgeProducer.emit.map Op.code++[.natBinary .add 4252 4252 4254,.jump 15,.halt]
 have eq:program=head++UniformSeedChunkPreparation.program.map (relocate 116 1402)++tail:=by
  simp only [program,beforeEmit,tail,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code head tail _ _ _ head_length
lemma boot_code : BlockAt boot program 0:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (boot.map Op.code)
  ([.branchLT 4252 4251 16 1409]++rootRead.map Op.code++[.branchLT 1180 4257 27 35]++emptyEmit.map Op.code++
   [.jump 1407]++install.map Op.code++UniformSeedChunkPreparation.program.map (relocate 116 1402)++
   UniformAxisEdgeProducer.emit.map Op.code++[.natBinary .add 4252 4252 4254,.jump 15,.halt]) i (by simpa using hi)
 simpa only [program,beforeEmit,head,List.append_assoc,List.nil_append,List.length_nil,Nat.zero_add,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma branch_at : program[15]?=some (.branchLT 4252 4251 16 1409):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment (boot.map Op.code)
  [.branchLT 4252 4251 16 1409]
  (rootRead.map Op.code++[.branchLT 1180 4257 27 35]++emptyEmit.map Op.code++[.jump 1407]++install.map Op.code++
   UniformSeedChunkPreparation.program.map (relocate 116 1402)++UniformAxisEdgeProducer.emit.map Op.code++
   [.natBinary .add 4252 4252 4254,.jump 15,.halt]) 0 (by decide)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_map,boot_length,Nat.add_zero,List.getElem?_cons_zero] using h

noncomputable section

def base (n j:ℕ):ℕ:=40*UniformSeedChunkAllocation.slot n*(j+1)
def directory (n:ℕ):ℕ:=40*UniformSeedChunkAllocation.slot n*(axisCount n+1)
def config (n j:ℕ):UniformSeedChunkPreparation.Config where
 seed:=⟨1,1,1,0,1,
  base n j+UniformSeedChunkAllocation.slot n,base n j+2*UniformSeedChunkAllocation.slot n,
  base n j+UniformSeedChunkAllocation.slot n,base n j+3*UniformSeedChunkAllocation.slot n,
  base n j+2*UniformSeedChunkAllocation.slot n,base n j+3*UniformSeedChunkAllocation.slot n,
  base n j+4*UniformSeedChunkAllocation.slot n,base n j+5*UniformSeedChunkAllocation.slot n,
  base n j+6*UniformSeedChunkAllocation.slot n,base n j+4*UniformSeedChunkAllocation.slot n,
  base n j+5*UniformSeedChunkAllocation.slot n,base n j+7*UniformSeedChunkAllocation.slot n,
  base n j+8*UniformSeedChunkAllocation.slot n,base n j+9*UniformSeedChunkAllocation.slot n,
  base n j+10*UniformSeedChunkAllocation.slot n,true⟩
 borrowed:=base n j+30*UniformSeedChunkAllocation.slot n
 selected:=base n j+31*UniformSeedChunkAllocation.slot n
 ordinals:=base n j+32*UniformSeedChunkAllocation.slot n
 mapped:=base n j+33*UniformSeedChunkAllocation.slot n
 permutation:=base n j+34*UniformSeedChunkAllocation.slot n
 widths:=base n j+35*UniformSeedChunkAllocation.slot n
 markers:=base n j+36*UniformSeedChunkAllocation.slot n
 axis:=base n j+37*UniformSeedChunkAllocation.slot n
 layer:=1
 color:=0
lemma exponent (n j:ℕ):(config n j).seed.exponent=2:=by
 change UniformWorkspacePlanner.exponent 1 1=2;decide
lemma width (n j:ℕ):(config n j).seed.width=4:=by
 rw [UniformSeedHeightPreparation.Config.width,exponent];rfl
lemma gates (n j:ℕ):(config n j).seed.gates=194:=by
 rw [UniformSeedHeightPreparation.Config.gates,exponent,width];rfl
lemma capacity (n j:ℕ):(config n j).seed.gates+(config n j).seed.e+(config n j).seed.a=196:=by
 rw [gates];rfl

/-- Physical all-axis inputs are original retained seed/metadata/operands.
These ordinary placement inequalities contain no produced/matching/action field.
The canonical B19 instance will close these arithmetic fields separately. -/
structure Layout (n B:ℕ):Prop where
 active:∀j:Fin (axisCount n),196≤radix n j→UniformSeedChunkPreparation.Layout n j (config n j.val) B
 directory:directory n+2*axisCount n≤B
 code:1410≤B

structure Driver (n j:ℕ) (s:State):Prop where
 slot:s.natReg 4250=UniformSeedChunkAllocation.slot n
 count:s.natReg 4251=axisCount n
 index:s.natReg 4252=j
 zero:s.natReg 4253=0
 one:s.natReg 4254=1
 two:s.natReg 4255=2
 four:s.natReg 4256=4
 threshold:s.natReg 4257=196
 forty:s.natReg 4260=40
 directory:s.natReg 4270=directory n

lemma Driver.withPC {n j:ℕ} {s:State} (d:Driver n j s) (pc:ℕ):Driver n j (setPC s pc):=by
 cases d;constructor <;> assumption
lemma boot_driver {n:ℕ} (s:State) (m:Metadata n s):Driver n 0 (applyBlock boot s):=by
 constructor
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,m.saved.inputLength,m.saved.count,
  UniformSeedChunkAllocation.slot,axisCount,directory]
 all_goals ring

def registerWrites : List (ℕ×ℕ)→ℕ→ℕ→(ℕ→ℕ)→(ℕ→ℕ)
 | [],_,_,r=>r
 | (d,k)::ps,b,w,r=>registerWrites ps b w (Function.update r d (b+w*k))
lemma registerWrites_pointwise (ps:List (ℕ×ℕ)) (b w:ℕ) (r v:ℕ→ℕ) (q:ℕ) (same:r q=v q):
 registerWrites ps b w r q=registerWrites ps b w v q:=by
 induction ps generalizing r v with
 | nil=>exact same
 | cons dk ps ih=>
  apply ih
  by_cases h:q=dk.1
  · simp [h]
  · simp [h,same]
lemma pointer_reg (s:State) (d k q:ℕ) (dst:d≠4250 ∧d≠4262 ∧d≠4263) (h:q≠4263):
 (applyBlock (pointer d k) s).natReg q=Function.update s.natReg d (s.natReg 4262+s.natReg 4250*k) q:=by
 rcases dst with ⟨h0,h2,h3⟩
 by_cases eq:q=d
 · subst q
   simp (disch:=omega) [pointer,applyBlock,Op.apply,writeNat,next]
 · simp (disch:=omega) [pointer,applyBlock,Op.apply,writeNat,next]
lemma pointers_reg (ps:List (ℕ×ℕ)) (s:State)
 (valid:∀p∈ps,p.1≠4250 ∧p.1≠4262 ∧p.1≠4263) (q:ℕ) (hq:q≠4263):
 (applyBlock (pointers ps) s).natReg q=registerWrites ps (s.natReg 4262) (s.natReg 4250) s.natReg q:=by
 induction ps generalizing s with
 | nil=>rfl
 | cons dk ps ih=>
  have dst:=valid dk (by simp)
  have root: (applyBlock (pointer dk.1 dk.2) s).natReg 4262=s.natReg 4262:=by
   rw [pointer_reg s dk.1 dk.2 4262 dst (by omega)]
   simp [Ne.symm dst.2.1]
  have slot: (applyBlock (pointer dk.1 dk.2) s).natReg 4250=s.natReg 4250:=by
   rw [pointer_reg s dk.1 dk.2 4250 dst (by omega)]
   simp [Ne.symm dst.1]
  simp only [pointers,List.flatMap_cons,UniformAxisEdgeProducer.apply_append]
  change (applyBlock (pointers ps) (applyBlock (pointer dk.1 dk.2) s)).natReg q=_
  rw [ih _ (fun p hp=>valid p (by simp [hp])),root,slot]
  simp only [registerWrites]
  exact registerWrites_pointwise ps _ _ _ _ q (pointer_reg s dk.1 dk.2 q dst hq)
lemma positions_valid:∀p∈positions,p.1≠4250 ∧p.1≠4262 ∧p.1≠4263:=by decide
lemma install_args {n:ℕ} (j:Fin (axisCount n)) (s:State) (d:Driver n j.val s):
 UniformSeedChunkPreparation.Args n j (config n j.val) (applyBlock install s):=by
 have reg:∀q,q≠4263→(applyBlock install s).natReg q=
  registerWrites positions ((applyBlock installStart s).natReg 4262) ((applyBlock installStart s).natReg 4250)
   (applyBlock installStart s).natReg q:=by
  intro q hq
  simp only [install,UniformAxisEdgeProducer.apply_append]
  exact pointers_reg positions _ positions_valid q hq
 refine ⟨⟨?_,?_,?_⟩,?_⟩
 · rw [reg 1120 (by omega)]
   simp [positions,registerWrites,installStart,applyBlock,Op.apply,writeNat,next,d.zero,d.index]
 · intro q lo hi
   interval_cases q
   all_goals rw [reg _ (by omega)]
   all_goals simp [positions,registerWrites,installStart,applyBlock,Op.apply,writeNat,next,d.zero,d.one,d.forty,d.index,d.slot,
    config,base,UniformSeedHeightPreparation.Config.register,UniformSeedHeightPreparation.Config.seed,
    UniformSeedRankCrossPreparation.Config.register,Nat.mul_comm,Nat.mul_assoc]
 · intro q lo hi
   interval_cases q
   all_goals rw [reg _ (by omega)]
   all_goals simp [positions,registerWrites,installStart,applyBlock,Op.apply,writeNat,next,d.zero,d.one,d.forty,d.index,d.slot,
    config,base,UniformSeedHeightPreparation.Config.register,Nat.mul_comm,Nat.mul_assoc]
 · intro q lo hi
   interval_cases q
   all_goals rw [reg _ (by omega)]
   all_goals simp [positions,registerWrites,installStart,applyBlock,Op.apply,writeNat,next,d.zero,d.one,d.forty,d.index,d.slot,
    config,base,UniformSeedChunkPreparation.Config.register,Nat.mul_comm,Nat.mul_assoc]


lemma install_heap (s:State):(applyBlock install s).natHeap=s.natHeap:=by
 apply (UniformEmptyStartupMatchingPreparation.natOnly_frame install (by decide) s).1
lemma install_scalar (s:State):(applyBlock install s).scalarHeap=s.scalarHeap:=by
 exact (UniformEmptyStartupMatchingPreparation.natOnly_frame install (by decide) s).2.1
lemma install_keeps (s:State) (q:ℕ) (hi:4250≤q) (h2:q≠4262) (h3:q≠4263):
 (applyBlock install s).natReg q=s.natReg q:=by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [install,installStart,pointers,positions,pointer,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma root_keeps (s:State) (q:ℕ) (hi:4250≤q):
 (applyBlock rootRead s).natReg q=s.natReg q:=by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [rootRead,UniformAxisEdgeProducer.rootRead,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma emit_keeps (s:State) (q:ℕ) (hi:4250≤q):
 (applyBlock UniformAxisEdgeProducer.emit s).natReg q=s.natReg q:=by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [UniformAxisEdgeProducer.emit,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma empty_keeps (s:State) (q:ℕ) (hi:4250≤q):
 (applyBlock emptyEmit s).natReg q=s.natReg q:=by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 simp [emptyEmit,UniformAxisEdgeProducer.emit,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma Driver.transport {n j:ℕ} {s u:State} (d:Driver n j s)
 (keep:∀q,4250≤q→q≠4262→q≠4263→u.natReg q=s.natReg q):Driver n j u:=by
 constructor
 all_goals first
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.slot
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.count
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.index
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.zero
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.one
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.two
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.four
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.threshold
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.forty
 | exact (keep _ (by omega) (by omega) (by omega)).trans d.directory
lemma base_step (n j:ℕ):base n (j+1)=base n j+40*UniformSeedChunkAllocation.slot n:=by
 unfold base;ring
lemma base_mono (n:ℕ) {i j:ℕ} (h:i≤j):base n i≤base n j:=
 Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)
lemma slot_positive (n:ℕ):100000≤UniformSeedChunkAllocation.slot n:=by
 unfold UniformSeedChunkAllocation.slot
 have hp:1≤(n+2)^2:=Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
 omega
lemma axis_end_before_directory (n:ℕ) (j:Fin (axisCount n)):
 (config n j.val).axis+4≤directory n:=by
 have b:=base_mono n (show j.val+1≤axisCount n by omega)
 have s:=slot_positive n
 rw [base_step] at b
 change base n j.val+37*UniformSeedChunkAllocation.slot n+4≤base n (axisCount n)
 omega
lemma before_next (n:ℕ) {i j:ℕ} (h:i<j):
 (config n i).axis+4≤(config n j).seed.d:=by
 have b:=base_mono n (show i+1≤j by omega)
 have s:=slot_positive n
 rw [base_step] at b
 change base n i+37*UniformSeedChunkAllocation.slot n+4≤base n j+UniformSeedChunkAllocation.slot n
 omega

structure Payload (r:ℕ) where
 count:ℕ
 source:ℕ
 edges:Fin count→UniformColoring.Edge
 matching:UniformMatchingAxisTableMachine.Matching edges
 range:UniformMatchingAxisTableMachine.InRange r edges

def activePayload {n B:ℕ} (l:Layout n B) (j:Fin (axisCount n)) (cap:196≤radix n j):Payload (radix n j):=
 let c:=config n j.val
 let lay:=(l.active j cap).chunk
 let ha:=(UniformSeedHeightPreparation.widths c.seed).1
 let he:=(UniformSeedHeightPreparation.widths c.seed).2
 let W:=UniformChunkMatchingPreparation.crossWord (c.chunk n j) ha he
 let dom:=UniformChunkMatchingPreparation.cross_domain (c.chunk n j) ha he
 ⟨(UniformChunkMatchingPreparation.indices (c.chunk n j) W).length,c.mapped,
  UniformChunkMatchingPreparation.physicalEdges lay W dom,
  UniformChunkMatchingPreparation.physical_matching lay dom (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) ha he),
  UniformChunkMatchingPreparation.physical_range lay dom⟩
def payload {n B:ℕ} (_hn:0<n) (l:Layout n B) (j:Fin (axisCount n)):Payload (radix n j):=
 if cap:196≤radix n j then activePayload l j cap
 else ⟨0,0,Fin.elim0,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
lemma payload_active {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)) (cap:196≤radix n j):
 payload hn l j=activePayload l j cap:=dite_eq_left cap

def family {n B:ℕ} (hn:0<n) (l:Layout n B):UniformAllAxisMatchingTablePreparation.Family n where
 count:=fun j=>(payload hn l j).count
 source:=fun j=>(payload hn l j).source
 edges:=fun j=>(payload hn l j).edges
 matching:=fun j=>(payload hn l j).matching
 range:=fun j=>(payload hn l j).range
/-- Algebraic matching/range of every actual emitted axis. The physical source
banks still require the loop execution theorem; no result is assumed here. -/
lemma family_capacity {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)):
 2*(family hn l).count j≤radix n j:=
 UniformMatchingAxisTableMachine.matching_capacity (radix n j) ((family hn l).edges j)
  ((family hn l).matching j) ((family hn l).range j)

lemma seed_high {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformSeedChunkPreparation.program n x B s t u)
 (q:ℕ) (hi:4250≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes
  (UniformSeedChunkPackingPreparation.seed_keeps q (by omega))
lemma Driver.seed {n j B t:ℕ} {x:Fin n→ℂ} {s u:State} (d:Driver n j s)
 (run:BoundedExecution UniformSeedChunkPreparation.program n x B s t u):Driver n j u:=
 d.transport (fun q hq _ _=>seed_high run q hq)
lemma install_driver {n j:ℕ} {s:State} (d:Driver n j s):
 Driver n j (applyBlock install s):=d.transport (fun q hq h2 h3=>install_keeps s q hq h2 h3)
lemma root_driver {n j:ℕ} {s:State} (d:Driver n j s):
 Driver n j (applyBlock rootRead s):=d.transport (fun q hq _ _=>root_keeps s q hq)
lemma emit_driver {n j:ℕ} {s:State} (d:Driver n j s):
 Driver n j (applyBlock UniformAxisEdgeProducer.emit s):=
 d.transport (fun q hq _ _=>emit_keeps s q hq)
lemma empty_driver {n j:ℕ} {s:State} (d:Driver n j s):
 Driver n j (applyBlock emptyEmit s):=d.transport (fun q hq _ _=>empty_keeps s q hq)

section
attribute [local irreducible] config
/-- The genuine1286 postcondition supplies the actual mapped edge endpoints.
The statement contains no assumed matching, range or final-bank premise. -/
lemma produced_edges {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n))
 (cap:196≤radix n j) {s:State}
 (post:UniformSeedChunkPreparation.Result n j (config n j.val) B hn (l.active j cap) s):
 s.natReg 894=(payload hn l j).count ∧
 s.natReg 1186=(payload hn l j).source ∧
 UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source s:=by
 let c:=config n j.val
 let lay:=(l.active j cap).chunk
 let ha:=(UniformSeedHeightPreparation.widths c.seed).1
 let he:=(UniformSeedHeightPreparation.widths c.seed).2
 let W:=UniformChunkMatchingPreparation.crossWord (c.chunk n j) ha he
 let dom:=UniformChunkMatchingPreparation.cross_domain (c.chunk n j) ha he
 have count:s.natReg 894=(UniformChunkMatchingPreparation.indices (c.chunk n j) W).length:=post.count
 have mapped:s.natReg 1186=c.mapped:=post.header.mapped
 have size:W.length≤2*UniformCrossHeightPreparationMachine.gates (c.chunk n j).height:=by
  simpa only [W,UniformChunkMatchingPreparation.crossWord,
   UniformCrossHeightPreparationMachine.cross_size (c.chunk n j).height ha he] using
   UniformCrossHeightPreparationMachine.bucket_length
    (UniformToeplitzCrossDAG.crossDAG (c.chunk n j).height.K (c.chunk n j).height.a (c.chunk n j).height.e ha he).program
    (c.chunk n j).height.enabled (c.chunk n j).depth
 have small:(UniformChunkMatchingPreparation.selectedRows (c.chunk n j) W
   (UniformChunkMatchingPreparation.crossLocations (c.chunk n j) c.seed.negative)).length≤
   2*UniformCrossHeightPreparationMachine.gates (c.chunk n j).height:=by
  rw [UniformChunkMatchingPreparation.selectedRows,List.length_map]
  exact (UniformChunkMatchingPreparation.selected_count (c.chunk n j) W).trans size
 have geo:=UniformChunkMatchingPreparation.row_geometry lay small
 have edges:=UniformChunkMatchingPreparation.mapped_edges lay dom geo post.mapped
 rw [payload_active hn l j cap]
 exact ⟨count,mapped,edges⟩

end
lemma root_constants (s:State):
 (applyBlock rootRead s).natReg 4214=1 ∧(applyBlock rootRead s).natReg 4215=2:=by
 simp [rootRead,UniformAxisEdgeProducer.rootRead,applyBlock,Op.apply,writeNat,next]
lemma seed_constants {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformSeedChunkPreparation.program n x B s t u):
 u.natReg 4214=s.natReg 4214 ∧u.natReg 4215=s.natReg 4215:=by
 constructor
 all_goals exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (UniformSeedChunkPackingPreparation.seed_keeps _ (by omega)))
lemma install_constants (s:State):
 (applyBlock install s).natReg 4214=s.natReg 4214 ∧(applyBlock install s).natReg 4215=s.natReg 4215:=by
 constructor
 all_goals apply UniformSeedRankCrossPreparation.block_register_keeps
 all_goals simp [install,installStart,pointers,positions,pointer,UniformSeedRankCrossPreparation.KeepsRegister]

lemma produced_low {n B:ℕ} (j:Fin (axisCount n)) (_cap:196≤radix n j) (_l:Layout n B)
 {s u:State} (outside:UniformSeedEdgeRetention.Chunk.Outside n j (config n j.val) s u):
 ∀q,q<base n j.val→u.natHeap q=s.natHeap q:=by
 intro q hq
 apply outside.1 q
 all_goals left
 all_goals change q<base n j.val+_
 all_goals omega

lemma produced_directory {n B:ℕ} (j:Fin (axisCount n)) (_cap:196≤radix n j) (_l:Layout n B)
 {s u:State} (outside:UniformSeedEdgeRetention.Chunk.Outside n j (config n j.val) s u):
 ∀q,directory n≤q→u.natHeap q=s.natHeap q:=by
 intro q hq
 have endAxis:=axis_end_before_directory n j
 have axis:(config n j.val).axis+4≤q:=endAxis.trans hq
 have slot:=slot_positive n
 change base n j.val+37*UniformSeedChunkAllocation.slot n+4≤q at axis
 apply outside.1 q
 all_goals right
 · change base n j.val+UniformSeedChunkAllocation.slot n+3*UniformRadixTwoDAG.count (config n j.val).seed.exponent≤q
   rw [exponent];norm_num [UniformRadixTwoDAG.count];omega
 · change base n j.val+2*UniformSeedChunkAllocation.slot n+5*UniformToeplitzCrossTopologyMachine.G (config n j.val).seed.exponent≤q
   rw [exponent];norm_num [UniformToeplitzCrossTopologyMachine.G,UniformConvolutionDAG.total,UniformRadixTwoDAG.count,UniformRadixTwoDAG.width];omega
 · rw [gates];change base n j.val+3*UniformSeedChunkAllocation.slot n+5*194≤q;omega
 · rw [gates];change base n j.val+4*UniformSeedChunkAllocation.slot n+1+1+194≤q;omega
 · rw [gates];change base n j.val+5*UniformSeedChunkAllocation.slot n+194*(194+1)≤q;omega
 · rw [gates];change base n j.val+6*UniformSeedChunkAllocation.slot n+194+2≤q;omega
 · change (config n j.val).seed.rows+6*(config n j.val).seed.gates*(8*(config n j.val).seed.exponent+7)≤q
   rw [gates,exponent];change base n j.val+7*UniformSeedChunkAllocation.slot n+6*194*(8*2+7)≤q;omega
 · change (config n j.val).seed.colors+2*(config n j.val).seed.gates*(8*(config n j.val).seed.exponent+7)≤q
   rw [gates,exponent];change base n j.val+8*UniformSeedChunkAllocation.slot n+2*194*(8*2+7)≤q;omega
 · change base n j.val+9*UniformSeedChunkAllocation.slot n+12≤q;omega
 · change (config n j.val).seed.heightDirectory+3*(8*(config n j.val).seed.exponent+7)≤q
   rw [exponent];change base n j.val+10*UniformSeedChunkAllocation.slot n+3*(8*2+7)≤q;omega
 · change base n j.val+37*UniformSeedChunkAllocation.slot n+4≤q;exact axis

lemma root_code : BlockAt rootRead program 16:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 4252 4251 16 1409]) (rootRead.map Op.code)
  ([.branchLT 1180 4257 27 35]++emptyEmit.map Op.code++[.jump 1407]++install.map Op.code++
   UniformSeedChunkPreparation.program.map (relocate 116 1402)++UniformAxisEdgeProducer.emit.map Op.code++
   [.natBinary .add 4252 4252 4254,.jump 15,.halt]) i (by simpa using hi)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_append,List.length_map,
  boot_length,List.length_singleton,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma install_code : BlockAt install program 35:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 4252 4251 16 1409]++rootRead.map Op.code++
   [.branchLT 1180 4257 27 35]++emptyEmit.map Op.code++[.jump 1407]) (install.map Op.code)
  (UniformSeedChunkPreparation.program.map (relocate 116 1402)++UniformAxisEdgeProducer.emit.map Op.code++
   [.natBinary .add 4252 4252 4254,.jump 15,.halt]) i (by simpa using hi)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_append,List.length_map,
  boot_length,rootRead_length,emptyEmit_length,List.length_singleton,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma empty_code : BlockAt emptyEmit program 27:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 4252 4251 16 1409]++rootRead.map Op.code++[.branchLT 1180 4257 27 35])
  (emptyEmit.map Op.code) ([.jump 1407]++install.map Op.code++
   UniformSeedChunkPreparation.program.map (relocate 116 1402)++UniformAxisEdgeProducer.emit.map Op.code++
   [.natBinary .add 4252 4252 4254,.jump 15,.halt]) i (by simpa using hi)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_append,List.length_map,
  boot_length,rootRead_length,List.length_singleton,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma emit_code : BlockAt UniformAxisEdgeProducer.emit program 1402:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment beforeEmit (UniformAxisEdgeProducer.emit.map Op.code)
  [.natBinary .add 4252 4252 4254,.jump 15,.halt] i (by simpa using hi)
 simpa only [program,beforeEmit_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma capacity_at : program[26]?=some (.branchLT 1180 4257 27 35):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 4252 4251 16 1409]++rootRead.map Op.code)
  [.branchLT 1180 4257 27 35]
  (emptyEmit.map Op.code++[.jump 1407]++install.map Op.code++
   UniformSeedChunkPreparation.program.map (relocate 116 1402)++UniformAxisEdgeProducer.emit.map Op.code++
   [.natBinary .add 4252 4252 4254,.jump 15,.halt]) 0 (by decide)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_append,List.length_map,
  boot_length,rootRead_length,List.length_singleton,Nat.add_zero,List.getElem?_cons_zero] using h

lemma readable_append (a b:List Op) (s:State):readable (a++b) s ↔readable a s ∧readable b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>simp [readable,applyBlock]
 | cons o a ih=>simp only [List.cons_append,readable,applyBlock,ih];tauto
lemma peak_append (a b:List Op) (s:State):peak (a++b) s=max (peak a s) (peak b (applyBlock a s)):=by
 induction a generalizing s with
 | nil=>simp [peak,applyBlock]
 | cons o a ih=>simp only [List.cons_append,peak,applyBlock,ih,max_assoc]

lemma pointer_safe (s:State) (d k B:ℕ) (dst:d≠4250 ∧d≠4262 ∧d≠4263)
 (hk:k≤B) (hv:s.natReg 4262+s.natReg 4250*k≤B):
 readable (pointer d k) s ∧peak (pointer d k) s≤B:=by
 rcases dst with ⟨h0,h2,h3⟩
 simp [pointer,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,Ne.symm h2]
 omega
lemma pointers_safe (ps:List (ℕ×ℕ)) (s:State) (B:ℕ)
 (valid:∀p∈ps,p.1≠4250 ∧p.1≠4262 ∧p.1≠4263)
 (safe:∀p∈ps,p.2≤B ∧s.natReg 4262+s.natReg 4250*p.2≤B):
 readable (pointers ps) s ∧peak (pointers ps) s≤B:=by
 induction ps generalizing s with
 | nil=>exact ⟨True.intro,Nat.zero_le _⟩
 | cons dk ps ih=>
  have dst:=valid dk (by simp)
  have ds:=safe dk (by simp)
  have first:=pointer_safe s dk.1 dk.2 B dst ds.1 ds.2
  have root:(applyBlock (pointer dk.1 dk.2) s).natReg 4262=s.natReg 4262:=by
   rw [pointer_reg s dk.1 dk.2 4262 dst (by omega)]
   simp [Ne.symm dst.2.1]
  have slot:(applyBlock (pointer dk.1 dk.2) s).natReg 4250=s.natReg 4250:=by
   rw [pointer_reg s dk.1 dk.2 4250 dst (by omega)]
   simp [Ne.symm dst.1]
  have rest:=ih (applyBlock (pointer dk.1 dk.2) s)
   (fun p hp=>valid p (by simp [hp])) (by intro p hp;simpa only [root,slot] using safe p (by simp [hp]))
  simpa only [pointers,List.flatMap_cons,readable_append,
   peak_append,max_le_iff] using And.intro (And.intro first.1 rest.1) (And.intro first.2 rest.2)

lemma install_safe {n B:ℕ} (j:Fin (axisCount n)) (s:State) (d:Driver n j.val s)
 (bound:(config n j.val).axis+4≤B) :readable install s ∧peak install s≤B:=by
 have slot:=slot_positive n
 change base n j.val+37*UniformSeedChunkAllocation.slot n+4≤B at bound
 have bas:base n j.val≤B:=by omega
 have start:readable installStart s ∧peak installStart s≤B:=by
  simp [installStart,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,d.index,d.one,d.forty,d.slot,d.zero]
  unfold base at bas bound
  simp only [Nat.mul_assoc,Nat.mul_comm] at bas bound ⊢
  have jbound:j.val≤40*UniformSeedChunkAllocation.slot n*(j.val+1):=by nlinarith
  have scaled:40*(j.val+1)≤40*UniformSeedChunkAllocation.slot n*(j.val+1):=by nlinarith
  repeat' constructor
  all_goals nlinarith
 have root:(applyBlock installStart s).natReg 4262=base n j.val:=by
  simp [installStart,applyBlock,Op.apply,writeNat,next,d.index,d.one,d.forty,d.slot,base,Nat.mul_assoc,Nat.mul_comm]
 have slot':(applyBlock installStart s).natReg 4250=UniformSeedChunkAllocation.slot n:=
  (UniformSeedRankCrossPreparation.block_register_keeps installStart s 4250 (by simp [installStart,UniformSeedRankCrossPreparation.KeepsRegister])).trans d.slot
 have coords:∀p∈positions,p.2≤B ∧(applyBlock installStart s).natReg 4262+
   (applyBlock installStart s).natReg 4250*p.2≤B:=by
  intro p hp
  have size:p.2≤37:=by rcases p with ⟨d,k⟩;simp [positions,Prod.mk.injEq] at hp;omega
  rw [root,slot']
  have mul:=Nat.mul_le_mul_left (UniformSeedChunkAllocation.slot n) size
  omega
 have tail:=pointers_safe positions (applyBlock installStart s) B positions_valid coords
 simpa only [install,readable_append,
  peak_append,max_le_iff] using
  And.intro (And.intro start.1 tail.1) (And.intro start.2 tail.2)

lemma root_radix {n:ℕ} (j:Fin (axisCount n)) (s:State) (m:Metadata n s) (d:Driver n j.val s):
 (applyBlock rootRead s).natReg 1180=radix n j:=by
 have root:=UniformAxisEdgeProducer.root_cell j s m
 have cell:s.natHeap (s.natReg 105+(s.natReg 102+j.val*4))=some (radix n j):=by
  rw [m.saved.copyAddress,m.saved.count]
  simpa only [Nat.mul_comm,Nat.add_assoc] using root
 simp [rootRead,UniformAxisEdgeProducer.rootRead,applyBlock,Op.apply,writeNat,next,d.index,d.zero,cell]
lemma root_safe {n B:ℕ} (j:Fin (axisCount n)) (s:State) (m:Metadata n s) (d:Driver n j.val s)
 (l:Layout n B) (hs:WordBound B s):readable rootRead s ∧peak rootRead s≤B:=by
 have root:=UniformAxisEdgeProducer.root_cell j s m
 let addr:=s.natReg 105+(s.natReg 102+j.val*4)
 have cell:s.natHeap addr=some (radix n j):=by
  dsimp only [addr];rw [m.saved.copyAddress,m.saved.count]
  simpa only [Nat.mul_comm,Nat.add_assoc] using root
 have bound:addr≤B ∧radix n j≤B:=hs.2.2.1 addr _ cell
 dsimp only [addr] at cell
 have dir:=l.directory
 have code:=l.code
 simp [rootRead,UniformAxisEdgeProducer.rootRead,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  d.index,d.directory,d.zero,cell]
 change s.natReg 105+(s.natReg 102+j.val*4)≤B ∧radix n j≤B at bound
 omega

lemma nat_block_preserved {n:ℕ} (ops:List Op) (s:State)
 (natOnly:ops.all UniformEmptyStartupMatchingPreparation.natOnly=true)
 (saved:∀q,100≤q→q≤106→∀o∈ops,UniformSeedRankCrossPreparation.KeepsRegister q o):
 UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock ops s):=by
 have frame:=UniformEmptyStartupMatchingPreparation.natOnly_frame ops natOnly s
 refine ⟨fun _ _=>congrFun frame.1 _,fun _ _=>congrFun frame.2.1 _,?_,frame.2.2.2.1,frame.2.2.2.2⟩
 intro q lo hi
 exact UniformSeedRankCrossPreparation.block_register_keeps ops s q (saved q lo hi)
lemma install_preserved (n:ℕ) (s:State):UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock install s):=by
 apply nat_block_preserved install s (by decide)
 intro q lo hi
 simp [install,installStart,pointers,positions,pointer,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma root_preserved (n:ℕ) (s:State):UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock rootRead s):=by
 apply nat_block_preserved rootRead s (by decide)
 intro q lo hi
 simp [rootRead,UniformAxisEdgeProducer.rootRead,UniformSeedRankCrossPreparation.KeepsRegister]
 omega
lemma boot_preserved (n:ℕ) (s:State):UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock boot s):=by
 apply nat_block_preserved boot s (by decide)
 intro q lo hi
 simp [boot,UniformSeedRankCrossPreparation.KeepsRegister]
 omega

lemma boot_safe {n B:ℕ} (s:State) (m:Metadata n s) (l:Layout n B):
 readable boot s ∧peak boot s≤B:=by
 have code:=l.code
 have slot:=slot_positive n
 have bound:=l.directory
 have count:axisCount n≤40*UniformSeedChunkAllocation.slot n*(axisCount n+1):=by nlinarith
 have pre:40*(axisCount n+1)≤40*UniformSeedChunkAllocation.slot n*(axisCount n+1):=by nlinarith
 have ns:n+2≤UniformSeedChunkAllocation.slot n:=by unfold UniformSeedChunkAllocation.slot;nlinarith
 have sq:(n+2)^2≤UniformSeedChunkAllocation.slot n:=by unfold UniformSeedChunkAllocation.slot;omega
 have more:UniformSeedChunkAllocation.slot n≤directory n:=by unfold directory;nlinarith
 simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,m.saved.inputLength,m.saved.count
  ]
 simp only [UniformSeedChunkAllocation.slot,directory,axisCount,pow_two] at ns sq bound count pre more
 ring_nf at ns sq bound count pre more ⊢
 omega
lemma root_index {n:ℕ} (j:Fin (axisCount n)) (s:State) (d:Driver n j.val s):
 (applyBlock rootRead s).natReg 4200=j.val ∧(applyBlock rootRead s).natReg 4219=directory n:=by
 simp [rootRead,UniformAxisEdgeProducer.rootRead,applyBlock,Op.apply,writeNat,next,d.index,d.zero,d.directory]
lemma install_index (s:State):
 (applyBlock install s).natReg 4200=s.natReg 4200 ∧(applyBlock install s).natReg 4219=s.natReg 4219:=by
 constructor
 all_goals apply UniformSeedRankCrossPreparation.block_register_keeps
 all_goals simp [install,installStart,pointers,positions,pointer,UniformSeedRankCrossPreparation.KeepsRegister]
lemma seed_index {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformSeedChunkPreparation.program n x B s t u):
 u.natReg 4200=s.natReg 4200 ∧u.natReg 4219=s.natReg 4219:=by
 constructor
 all_goals exact (UniformNewtonTableMachine.Executes.keeps_nat run.executes (UniformSeedChunkPackingPreparation.seed_keeps _ (by omega)))
lemma emit_safe {n B:ℕ} (j:Fin (axisCount n)) (s:State) (l:Layout n B)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (hs:WordBound B s):
 readable UniformAxisEdgeProducer.emit s ∧peak UniformAxisEdgeProducer.emit s≤B:=by
 have ib:=j.isLt
 have bd:=l.directory
 have c:=hs.2.1 894
 have m:=hs.2.1 1186
 simp [UniformAxisEdgeProducer.emit,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,index,dir,one,two]
 omega
lemma emitted_below {n:ℕ} (j:Fin (axisCount n)) (s:State)
 (_index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (q:ℕ) (lo:q<directory n):
 (applyBlock UniformAxisEdgeProducer.emit s).natHeap q=s.natHeap q:=by
 exact UniformAxisEdgeProducer.emit_below s (directory n) dir two one q lo
lemma emitted_other {n:ℕ} (j:Fin (axisCount n)) (s:State)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (q:ℕ)
 (h0:q≠directory n+2*j.val) (h1:q≠directory n+2*j.val+1):
 (applyBlock UniformAxisEdgeProducer.emit s).natHeap q=s.natHeap q:=by
 simp [UniformAxisEdgeProducer.emit,applyBlock,Op.apply,writeNat,next,index,dir,one,two,Function.update_apply]
 split_ifs <;> simp_all only [Nat.mul_comm] <;> omega
lemma empty_records {n:ℕ} (j:Fin (axisCount n)) (s:State)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 (applyBlock emptyEmit s).natHeap (directory n+2*j.val)=some 0 ∧
 (applyBlock emptyEmit s).natHeap (directory n+2*j.val+1)=some 0:=by
 simp [emptyEmit,UniformAxisEdgeProducer.emit,applyBlock,Op.apply,writeNat,next,index,dir,one,two,Nat.mul_comm]
lemma payload_count {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)):
 (payload hn l j).count≤388:=by
 by_cases cap:196≤radix n j
 · simp only [payload,dite_eq_left cap,activePayload]
   have size:=UniformChunkMatchingPreparation.selected_count ((config n j.val).chunk n j)
    (UniformChunkMatchingPreparation.crossWord ((config n j.val).chunk n j)
      (UniformSeedHeightPreparation.widths (config n j.val).seed).1 (UniformSeedHeightPreparation.widths (config n j.val).seed).2)
   have bound:=UniformCrossHeightPreparationMachine.bucket_length
    (UniformToeplitzCrossDAG.crossDAG (config n j.val).seed.exponent (config n j.val).seed.a (config n j.val).seed.e
      (UniformSeedHeightPreparation.widths (config n j.val).seed).1 (UniformSeedHeightPreparation.widths (config n j.val).seed).2).program
    (config n j.val).seed.enabled (config n j.val).layer
   conv at bound => rhs;rw [UniformToeplitzCrossDAG.crossDAG_size]
   have b: (UniformChunkMatchingPreparation.crossWord ((config n j.val).chunk n j)
      (UniformSeedHeightPreparation.widths (config n j.val).seed).1 (UniformSeedHeightPreparation.widths (config n j.val).seed).2).length≤
      2*(config n j.val).seed.gates:=by
    simpa only [UniformChunkMatchingPreparation.crossWord,UniformSeedHeightPreparation.Config.gates,
     UniformSeedHeightPreparation.Config.width,UniformRadixTwoDAG.width_eq,
     UniformSeedChunkPreparation.Config.chunk,UniformSeedHeightPreparation.Config.height] using bound
   rw [gates] at b
   exact size.trans b
 · simp [payload,cap]
lemma payload_below {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)):
 (payload hn l j).source+3*(payload hn l j).count≤(config n j.val).axis+4:=by
 have count:=payload_count hn l j
 have slot:=slot_positive n
 by_cases cap:196≤radix n j
 · change (payload hn l j).source+3*(payload hn l j).count≤base n j.val+37*UniformSeedChunkAllocation.slot n+4
   have source:(payload hn l j).source=base n j.val+33*UniformSeedChunkAllocation.slot n:=by simp [payload,cap,activePayload,config]
   rw [source];omega
 · simp only [payload,dite_eq_right cap];omega

def Complete {n B:ℕ} (hn:0<n) (l:Layout n B) (j:ℕ) (s:State):Prop:=
 ∀i:Fin (axisCount n),i.val<j→
 s.natHeap (directory n+2*i.val)=some (payload hn l i).count ∧
 s.natHeap (directory n+2*i.val+1)=some (payload hn l i).source ∧
 UniformMatchingAxisTableMachine.Edges (payload hn l i).edges (payload hn l i).source s
structure Invariant {n B:ℕ} (hn:0<n) (l:Layout n B) (j:ℕ) (x:Fin n→ℂ) (s:State):Prop where
 driver:Driver n j s
 metadata:Metadata n s
 retained:Retained n (axisCount n) s
 operands:UniformInitialPreparation.Operands n x s
 completed:Complete hn l j s

lemma emit_preserved {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (s:State)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock UniformAxisEdgeProducer.emit s):=by
 have old:UniformAllAxisSeedPreparation.directoryBase n+2*axisCount n≤directory n:=by
  have bound:=(UniformSeedChunkAllocation.slot_global hn).2
  have slot:=slot_positive n
  unfold directory
  nlinarith
 refine ⟨fun q hq=>emitted_below j s index dir one two q (hq.trans_le old),fun _ _=>rfl,?_,rfl,rfl⟩
 intro q lo hi
 simp (disch:=omega) [UniformAxisEdgeProducer.emit,applyBlock,Op.apply,writeNat,next]
lemma emitted_result {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n))
 {s:State} (count:s.natReg 894=(payload hn l j).count) (mapped:s.natReg 1186=(payload hn l j).source)
 (edges:UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source s)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 (applyBlock UniformAxisEdgeProducer.emit s).natHeap (directory n+2*j.val)=some (payload hn l j).count ∧
 (applyBlock UniformAxisEdgeProducer.emit s).natHeap (directory n+2*j.val+1)=some (payload hn l j).source ∧
 UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source
   (applyBlock UniformAxisEdgeProducer.emit s):=by
 have records:=UniformAxisEdgeProducer.emit_index s j.val (directory n) index dir one two
 refine ⟨by simpa only [count] using records.1,by simpa only [mapped] using records.2,?_⟩
 intro i
 have cb:=payload_below hn l j
 have db:=axis_end_before_directory n j
 have il:=i.isLt
 exact ⟨(emitted_below j s index dir one two _ (by omega)).trans (edges i).1,
  (emitted_below j s index dir one two _ (by omega)).trans (edges i).2⟩

lemma seedArgs_withPC {n:ℕ} {j:Fin (axisCount n)} {c:UniformSeedChunkPreparation.Config} {s:State}
 (h:UniformSeedChunkPreparation.Args n j c s) (pc:ℕ):UniformSeedChunkPreparation.Args n j c (setPC s pc):=
 ⟨⟨h.seed.1,h.seed.2.1,h.seed.2.2⟩,h.extra⟩

/-- Opaque actual intermediate state after the81 charged stores.
Clients consume its proved fields without unfolding the entire register-update tree. -/
theorem install_execution {n B:ℕ} (l:Layout n B) (j:Fin (axisCount n)) (cap:196≤radix n j)
 (x:Fin n→ℂ) (s:State) (d:Driver n j.val s) (pc:s.pc=35) (hs:WordBound B s):∃u,
 BoundedRuns program n x B s 81 u ∧u.pc=116 ∧UniformSeedChunkPreparation.Args n j (config n j.val) u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧
 Driver n j.val u ∧u.natReg 4200=s.natReg 4200 ∧u.natReg 4219=s.natReg 4219 ∧
 u.natReg 4214=s.natReg 4214 ∧u.natReg 4215=s.natReg 4215:=by
 have code:=l.code
 have safe:=install_safe j s d (l.active j cap).finalBound
 have first:=block_runs install program 35 n B x s install_code pc hs
  (by rw [install_length];omega) safe.1 safe.2
 refine ⟨applyBlock install s,?_,?_,install_args j s d,install_preserved n s,install_heap s,
  install_scalar s,install_driver d,(install_index s).1,(install_index s).2,(install_constants s).1,(install_constants s).2⟩
 · simpa only [install_length] using first
 · rw [UniformTensorMonomialMachine.applyBlock_pc,pc,install_length]

lemma seedResult_withPC {n B:ℕ} (hn:0<n) {j:Fin (axisCount n)} {c:UniformSeedChunkPreparation.Config}
 (h:UniformSeedChunkPreparation.Layout n j c B) {s:State}
 (post:UniformSeedChunkPreparation.Result n j c B hn h s) (pc:ℕ):
 UniformSeedChunkPreparation.Result n j c B hn h (setPC s pc):=by
 refine ⟨UniformSeedChunkPreparation.seedResult_transport hn h post.prepared (fun _ _=>rfl) rfl (fun _ _ _=>rfl),
  post.header.withPC pc,post.count,post.rows,post.widths,post.permutations,post.mapped⟩

section
attribute [local irreducible] config
/-- Opaque boundary after actual header synthesis and all835/1046/1286 phases.
This separates machine state transport from the later directory writes. -/
theorem active_seed {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)) (cap:196≤radix n j)
 (x:Fin n→ℂ) (s:State) (driver:Driver n j.val s)
 (metadata:Metadata n s) (retained:Retained n (axisCount n) s) (operands:UniformInitialPreparation.Operands n x s)
 (pc:s.pc=35) (hs:WordBound B s):∃u t,
 BoundedRuns program n x B s (81+t) u ∧t≤UniformSeedChunkPreparation.runtimeBudget n j (config n j.val) ∧
 u.pc=1402 ∧UniformSeedChunkPreparation.Result n j (config n j.val) B hn (l.active j cap) u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 UniformSeedEdgeRetention.Chunk.Outside n j (config n j.val) s u ∧Driver n j.val u ∧
 u.natReg 4200=s.natReg 4200 ∧u.natReg 4219=s.natReg 4219 ∧
 u.natReg 4214=s.natReg 4214 ∧u.natReg 4215=s.natReg 4215:=by
 have code:=l.code
 obtain ⟨installed,first,ip,args,installedFrame,installedHeap,installedScalar,installedDriver,installedIndex,installedDir,installedOne,installedTwo⟩:=
  install_execution l j cap x s driver pc hs
 let entry:=setPC installed 0
 have eb:=changePC_bound B installed 0 first.final_bound (by omega)
 have ef:UniformSeedRankCrossPreparation.PreservedFrame n s entry:=installedFrame
 obtain ⟨v,t,run,cost,vp,post,_,_,_,frame,outside⟩:=UniformSeedEdgeRetention.Chunk.execution hn j (config n j.val) B x entry
  (seedArgs_withPC args 0) (ef.protected.metadata metadata) (ef.retained retained) (ef.protected.operands operands)
  (l.active j cap) rfl eb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedChunkPreparation.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero installed 116 ip] at placedRun
 let e:=setPC v 1402
 have d:Driver n j.val e:=installedDriver.withPC 0 |>.seed run |>.withPC 1402
 refine ⟨e,t,?_,cost,rfl,?_,?_,?_,d,?_,?_,?_,?_⟩
 · simpa only [e,UniformTensorMonomialMachine.setPC] using first.trans placedRun
 · exact seedResult_withPC hn (l.active j cap) post 1402
 · exact ef.trans frame
 · constructor
   · intro q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
     exact (outside.1 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11).trans (congrFun installedHeap q)
   · intro q h1 h2 h3 h4 h5
     exact (outside.2 q h1 h2 h3 h4 h5).trans (congrFun installedScalar q)
 · exact (seed_index run).1.trans installedIndex
 · exact (seed_index run).2.trans installedDir
 · exact (seed_constants run).1.trans installedOne
 · exact (seed_constants run).2.trans installedTwo

end

section
attribute [local irreducible] config
/-- Actual charged active-axis body from ordinary state/bank/layout inputs.
All FFT spectra, Cross tape, depths, colors and selected rows are generated by
literal1286; only the loop's existing real-root/index fields are read. -/
theorem active_body {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)) (cap:196≤radix n j)
 (x:Fin n→ℂ) (s:State) (driver:Driver n j.val s)
 (metadata:Metadata n s) (retained:Retained n (axisCount n) s) (operands:UniformInitialPreparation.Operands n x s)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (pc:s.pc=35) (hs:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤UniformSeedChunkPreparation.runtimeBudget n j (config n j.val)+86 ∧
 u.pc=1407 ∧Driver n j.val u ∧Metadata n u ∧Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 (u.natHeap (directory n+2*j.val)=some (payload hn l j).count ∧
  u.natHeap (directory n+2*j.val+1)=some (payload hn l j).source ∧
  UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source u) ∧
 (∀q,q<base n j.val→u.natHeap q=s.natHeap q) ∧
 (∀q,q≠directory n+2*j.val→q≠directory n+2*j.val+1→directory n≤q→u.natHeap q=s.natHeap q):=by
 have code:=l.code
 obtain ⟨e,t,first,cost,ep,post,eframe,outside,d,ei,ed,eo,et⟩:=active_seed hn l j cap x s driver metadata retained operands pc hs
 have records:=produced_edges hn l j cap post
 have is:e.natReg 4200=j.val:=ei.trans index
 have ds:e.natReg 4219=directory n:=ed.trans dir
 have os:e.natReg 4214=1:=eo.trans one
 have ts:e.natReg 4215=2:=et.trans two
 have safeEmit:=emit_safe j e l is ds os ts first.final_bound
 let u:=applyBlock UniformAxisEdgeProducer.emit e
 have last:=block_runs UniformAxisEdgeProducer.emit program 1402 n B x e emit_code ep first.final_bound
  (by rw [UniformAxisEdgeProducer.emit_length];omega) safeEmit.1 safeEmit.2
 have up:u.pc=1407:=by dsimp only [u];rw [UniformTensorMonomialMachine.applyBlock_pc,ep,UniformAxisEdgeProducer.emit_length]
 have efinal:UniformSeedRankCrossPreparation.PreservedFrame n s u:=
  eframe.trans (emit_preserved hn j e is ds os ts)
 refine ⟨u,81+t+5,?_,by omega,up,emit_driver d,efinal.protected.metadata metadata,efinal.retained retained,
  efinal.protected.operands operands,efinal,emitted_result hn l j records.1 records.2.1 records.2.2 is ds os ts,?_,?_⟩
 · simpa only [install_length,UniformAxisEdgeProducer.emit_length] using first.trans last
 · intro q lo
   exact (emitted_below j e is ds os ts q (lt_of_lt_of_le lo (by unfold base directory;have ib:=j.isLt;nlinarith))).trans
    (produced_low j cap l outside q lo)
 · intro q h0 h1 lo
   exact (emitted_other j e is ds os ts q h0 h1).trans
    (produced_directory j cap l outside q lo)

end

lemma emptyJump_at : program[34]?=some (.jump 1407):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++[.branchLT 4252 4251 16 1409]++rootRead.map Op.code++
   [.branchLT 1180 4257 27 35]++emptyEmit.map Op.code) [.jump 1407]
  (install.map Op.code++UniformSeedChunkPreparation.program.map (relocate 116 1402)++
   UniformAxisEdgeProducer.emit.map Op.code++[.natBinary .add 4252 4252 4254,.jump 15,.halt]) 0 (by decide)
 simpa only [program,beforeEmit,head,List.append_assoc,List.length_append,List.length_map,
  boot_length,rootRead_length,emptyEmit_length,List.length_singleton,Nat.add_zero,List.getElem?_cons_zero] using h
lemma advance_at : program[1407]?=some (.natBinary .add 4252 4252 4254):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeEmit++UniformAxisEdgeProducer.emit.map Op.code)
  [.natBinary .add 4252 4252 4254,.jump 15,.halt] [] 0 (by decide)
 simpa only [program,List.append_nil,List.length_append,List.length_map,beforeEmit_length,
  UniformAxisEdgeProducer.emit_length,Nat.add_zero,List.getElem?_cons_zero] using h
lemma jump_at : program[1408]?=some (.jump 15):=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeEmit++UniformAxisEdgeProducer.emit.map Op.code)
  [.natBinary .add 4252 4252 4254,.jump 15,.halt] [] 1 (by decide)
 simpa only [program,List.append_nil,List.length_append,List.length_map,beforeEmit_length,
  UniformAxisEdgeProducer.emit_length,List.getElem?_cons_succ,List.getElem?_cons_zero] using h
lemma halt_at : program[1409]?=some .halt:=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (beforeEmit++UniformAxisEdgeProducer.emit.map Op.code)
  [.natBinary .add 4252 4252 4254,.jump 15,.halt] [] 2 (by decide)
 simpa only [program,List.append_nil,List.length_append,List.length_map,beforeEmit_length,
  UniformAxisEdgeProducer.emit_length,List.getElem?_cons_succ,List.getElem?_cons_zero] using h



/-- Both branches and the actual protected CRT read are charged. -/
theorem prepare_axis {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n))
 (x:Fin n→ℂ) (s:State) (inv:Invariant hn l j.val x s) (pc:s.pc=15) (hs:WordBound B s):∃u,
 BoundedRuns program n x B s 12 u ∧u.pc=(if 196≤radix n j then 35 else 27) ∧
 Driver n j.val u ∧Metadata n u ∧Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 u.natHeap=s.natHeap ∧UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 u.natReg 4200=j.val ∧u.natReg 4219=directory n ∧u.natReg 4214=1 ∧u.natReg 4215=2:=by
 have code:=l.code
 let a:=setPC s 16
 have ab:=changePC_bound B s 16 hs (by omega)
 have first:BoundedRuns program n x B s 1 a:=.next hs
  (by simp [step,pc,branch_at,inv.driver.index,inv.driver.count,j.isLt,a,setPC]) (.refl ab)
 have af:UniformSeedRankCrossPreparation.PreservedFrame n s a:=⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
 have am:=af.protected.metadata inv.metadata
 have safe:=root_safe j a am (inv.driver.withPC 16) l ab
 have middle:=block_runs rootRead program 16 n B x a root_code rfl ab
  (by rw[rootRead_length];omega) safe.1 safe.2
 have vp:(applyBlock rootRead a).pc=26:=by rw[UniformTensorMonomialMachine.applyBlock_pc,rootRead_length];rfl
 have dr:=root_driver (inv.driver.withPC 16)
 have frame:=root_preserved n a
 have radixEq:=root_radix j a am (inv.driver.withPC 16)
 have indx:=root_index j a (inv.driver.withPC 16)
 have constants:=root_constants a
 generalize hv:applyBlock rootRead a=v at middle vp dr frame radixEq indx constants
 let u:=setPC v (if 196≤radix n j then 35 else 27)
 have ub:=changePC_bound B v (if 196≤radix n j then 35 else 27) middle.final_bound (by split_ifs <;>omega)
 have last:BoundedRuns program n x B v 1 u:=.next middle.final_bound
  (by by_cases cap:196≤radix n j <;>
      simp [step,vp,capacity_at,radixEq,dr.threshold,u,setPC,cap]) (.refl ub)
 have full:UniformSeedRankCrossPreparation.PreservedFrame n s u:=frame
 refine ⟨u,?_,rfl,dr.withPC _,full.protected.metadata inv.metadata,full.retained inv.retained,
  full.protected.operands inv.operands,?_,full,indx.1,indx.2,?_,?_⟩
 · convert first.trans (middle.trans last) using 1; simp only[rootRead_length]
 · change v.natHeap=s.natHeap
   rw [←hv];rfl
 · exact constants.1
 · exact constants.2

lemma empty_preserved {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (s:State)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):
 UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock emptyEmit s):=by
 let v:=applyBlock ([.literal 894 0,.literal 1186 0]:List Op) s
 have first:UniformSeedRankCrossPreparation.PreservedFrame n s v:=by
  apply nat_block_preserved _ s (by decide)
  intro q lo hi
  simp [UniformSeedRankCrossPreparation.KeepsRegister];omega
 have second:=emit_preserved hn j v index dir one two
 simpa only[emptyEmit,UniformAxisEdgeProducer.apply_append] using first.trans second
lemma empty_below {n:ℕ} (j:Fin (axisCount n)) (s:State)
 (_index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (q:ℕ) (lo:q<directory n):
 (applyBlock emptyEmit s).natHeap q=s.natHeap q:=by
 exact UniformAxisEdgeProducer.emit_below (applyBlock [.literal 894 0,.literal 1186 0] s)
  (directory n) dir two one q lo
lemma empty_other {n:ℕ} (j:Fin (axisCount n)) (s:State)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (q:ℕ)
 (h0:q≠directory n+2*j.val) (h1:q≠directory n+2*j.val+1):
 (applyBlock emptyEmit s).natHeap q=s.natHeap q:=by
 exact emitted_other j (applyBlock [.literal 894 0,.literal 1186 0] s) index dir one two q h0 h1
lemma empty_safe {n B:ℕ} (j:Fin (axisCount n)) (s:State) (l:Layout n B)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2):readable emptyEmit s ∧peak emptyEmit s≤B:=by
 have code:=l.code
 have ib:=j.isLt
 have bd:=l.directory
 simp [emptyEmit,UniformAxisEdgeProducer.emit,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  index,dir,one,two]
 omega

/-- An unavailable unit-chunk layer emits actual zero matching geometry.
The axis's Fourier action is a separate small-axis/local-schedule obligation. -/
theorem empty_body {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n)) (cap:¬196≤radix n j)
 (x:Fin n→ℂ) (s:State) (driver:Driver n j.val s)
 (metadata:Metadata n s) (retained:Retained n (axisCount n) s) (operands:UniformInitialPreparation.Operands n x s)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2) (pc:s.pc=27) (hs:WordBound B s):∃u,
 BoundedRuns program n x B s 8 u ∧u.pc=1407 ∧Driver n j.val u ∧Metadata n u ∧
 Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 (u.natHeap (directory n+2*j.val)=some (payload hn l j).count ∧
  u.natHeap (directory n+2*j.val+1)=some (payload hn l j).source ∧
  UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source u) ∧
 (∀q,q<base n j.val→u.natHeap q=s.natHeap q) ∧
 (∀q,q≠directory n+2*j.val→q≠directory n+2*j.val+1→directory n≤q→u.natHeap q=s.natHeap q):=by
 have code:=l.code
 have safe:=empty_safe j s l index dir one two
 have run:=block_runs emptyEmit program 27 n B x s empty_code pc hs
  (by rw[emptyEmit_length];omega) safe.1 safe.2
 have vp:(applyBlock emptyEmit s).pc=34:=by rw[UniformTensorMonomialMachine.applyBlock_pc,pc,emptyEmit_length]
 have frame:=empty_preserved hn j s index dir one two
 have d:=empty_driver driver
 have records:=empty_records j s index dir one two
 let u:=setPC (applyBlock emptyEmit s) 1407
 have ub:=changePC_bound B _ 1407 run.final_bound (by omega)
 have uf:UniformSeedRankCrossPreparation.PreservedFrame n s u:=frame
 have jump:BoundedRuns program n x B (applyBlock emptyEmit s) 1 u:=.next run.final_bound
  (by simp[step,vp,emptyJump_at,u,setPC]) (.refl ub)
 refine ⟨u,?_,rfl,d.withPC _,uf.protected.metadata metadata,uf.retained retained,
  uf.protected.operands operands,uf,?_,?_,?_⟩
 · simpa only[emptyEmit_length] using run.trans jump
 · refine ⟨?_,?_,?_⟩
   · simpa only[u,setPC,payload,dite_eq_right cap] using records.1
   · simpa only[u,setPC,payload,dite_eq_right cap] using records.2
   · simp [payload,cap,UniformMatchingAxisTableMachine.Edges]
 · intro q hq
   exact empty_below j s index dir one two q (hq.trans_le (by unfold base directory;have jl:=j.isLt;nlinarith))
 · exact fun q h0 h1 _=>empty_other j s index dir one two q h0 h1


lemma Complete.transport {n B j:ℕ} {hn:0<n} {l:Layout n B} {s u:State}
 (c:Complete hn l j s) (eq:u.natHeap=s.natHeap):Complete hn l j u:=by
 intro i hi
 refine ⟨(congrFun eq _).trans (c i hi).1,(congrFun eq _).trans (c i hi).2.1,?_⟩
 intro k
 exact ⟨(congrFun eq _).trans ((c i hi).2.2 k).1,(congrFun eq _).trans ((c i hi).2.2 k).2⟩
lemma payload_prior {n B j:ℕ} (hn:0<n) (l:Layout n B) (i:Fin (axisCount n)) (hi:i.val<j):
 (payload hn l i).source+3*(payload hn l i).count≤base n j:=by
 have h:=payload_below hn l i
 have slot:=slot_positive n
 change (payload hn l i).source+3*(payload hn l i).count≤
  base n i.val+37*UniformSeedChunkAllocation.slot n+4 at h
 unfold base at *
 nlinarith
lemma Complete.extend {n B:ℕ} {hn:0<n} {l:Layout n B} {s u:State} (j:Fin (axisCount n))
 (old:Complete hn l j.val s)
 (new:u.natHeap (directory n+2*j.val)=some (payload hn l j).count ∧
  u.natHeap (directory n+2*j.val+1)=some (payload hn l j).source ∧
  UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source u)
 (low:∀q,q<base n j.val→u.natHeap q=s.natHeap q)
 (high:∀q,q≠directory n+2*j.val→q≠directory n+2*j.val+1→directory n≤q→u.natHeap q=s.natHeap q):
 Complete hn l (j.val+1) u:=by
 intro i hi
 by_cases eq:i=j
 · subst i;exact new
 · have ij:i.val<j.val:=by have ne:=Fin.val_injective.ne eq;omega
   have prev:=old i ij
   refine ⟨(high _ (by omega) (by omega) (by omega)).trans prev.1,
    (high _ (by omega) (by omega) (by omega)).trans prev.2.1,?_⟩
   intro k
   have bound:=payload_prior hn l i ij
   have kl:=k.isLt
   exact ⟨(low _ (by omega)).trans (prev.2.2 k).1,(low _ (by omega)).trans (prev.2.2 k).2⟩

lemma Driver.advance {n j:ℕ} {s:State} (h:Driver n j s):Driver n (j+1) (setPC (writeNat s 4252 (j+1)) 15):=by
 constructor
 all_goals simp [setPC,writeNat,next,h.slot,h.count,h.zero,h.one,h.two,h.four,h.threshold,h.forty,h.directory]
lemma advance_preserved (n:ℕ) (s:State) (j:ℕ):
 UniformSeedRankCrossPreparation.PreservedFrame n s (setPC (writeNat s 4252 j) 15):=by
 refine ⟨fun _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
 intro q lo hi;simp (disch:=omega) [setPC,writeNat,next]

def bodyBudget (n j:ℕ):ℕ:=if h:j<axisCount n then
 if 196≤radix n ⟨j,h⟩ then UniformSeedChunkPreparation.runtimeBudget n ⟨j,h⟩ (config n j)+86 else 8 else 0
lemma bodyBudget_eq {n:ℕ} (j:Fin (axisCount n)):
 bodyBudget n j.val=(if 196≤radix n j then UniformSeedChunkPreparation.runtimeBudget n j (config n j.val)+86 else 8):=by
 simp [bodyBudget,j.isLt]

theorem axis_body {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n))
 (x:Fin n→ℂ) (s:State) (driver:Driver n j.val s)
 (metadata:Metadata n s) (retained:Retained n (axisCount n) s) (operands:UniformInitialPreparation.Operands n x s)
 (index:s.natReg 4200=j.val) (dir:s.natReg 4219=directory n)
 (one:s.natReg 4214=1) (two:s.natReg 4215=2)
 (pc:s.pc=if 196≤radix n j then 35 else 27) (hs:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤bodyBudget n j.val ∧u.pc=1407 ∧Driver n j.val u ∧
 Metadata n u ∧Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 (u.natHeap (directory n+2*j.val)=some (payload hn l j).count ∧
  u.natHeap (directory n+2*j.val+1)=some (payload hn l j).source ∧
  UniformMatchingAxisTableMachine.Edges (payload hn l j).edges (payload hn l j).source u) ∧
 (∀q,q<base n j.val→u.natHeap q=s.natHeap q) ∧
 (∀q,q≠directory n+2*j.val→q≠directory n+2*j.val+1→directory n≤q→u.natHeap q=s.natHeap q):=by
 rw[bodyBudget_eq]
 by_cases cap:196≤radix n j
 · simp only[ite_eq_left cap] at pc ⊢
   exact active_body hn l j cap x s driver metadata retained operands index dir one two pc hs
 · simp only[ite_eq_right cap] at pc ⊢
   obtain ⟨u,run,up,d,m,r,o,f,records,low,high⟩:=empty_body hn l j cap x s driver metadata retained operands index dir one two pc hs
   exact ⟨u,8,run,le_rfl,up,d,m,r,o,f,records,low,high⟩

/-- One genuine iteration preserves every prior emitted edge and directory row. -/
theorem iteration {n B:ℕ} (hn:0<n) (l:Layout n B) (j:Fin (axisCount n))
 (x:Fin n→ℂ) (s:State) (inv:Invariant hn l j.val x s) (pc:s.pc=15) (hs:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤bodyBudget n j.val+14 ∧
 Invariant hn l (j.val+1) x u ∧u.pc=15 ∧UniformSeedRankCrossPreparation.PreservedFrame n s u:=by
 have code:=l.code
 obtain ⟨a,pre,ap,ad,am,ar,ao,ah,af,ai,adir,aone,atwo⟩:=prepare_axis hn l j x s inv pc hs
 obtain ⟨v,t,body,cost,vp,d,m,r,o,f,records,low,high⟩:=axis_body hn l j x a ad am ar ao ai adir aone atwo ap pre.final_bound
 have complete:Complete hn l (j.val+1) v:=
  (inv.completed.transport ah).extend j records low high
 let advanced:=writeNat v 4252 (j.val+1)
 have index:v.natReg 4252+v.natReg 4254=j.val+1:=by rw[d.index,d.one]
 have jb:j.val+1≤B:=by
  have bound:=l.directory;have slot:=slot_positive n;have il:=j.isLt
  unfold directory at bound;nlinarith
 have ab:=writeNat_bound B v 4252 (j.val+1) body.final_bound (by rw[vp];omega) jb
 have advance:BoundedRuns program n x B v 1 advanced:=.next body.final_bound
  (by simp only[step,vp,advance_at,evalNat,index];rfl) (.refl ab)
 let u:=setPC advanced 15
 have ub:=changePC_bound B advanced 15 ab (by omega)
 have jump:BoundedRuns program n x B advanced 1 u:=.next ab
  (by simp[step,advanced,writeNat,next,vp,jump_at,u,setPC]) (.refl ub)
 have finalFrame:UniformSeedRankCrossPreparation.PreservedFrame n s u:=af.trans (f.trans (advance_preserved n v (j.val+1)))
 refine ⟨u,12+t+2,?_,by omega,⟨d.advance,finalFrame.protected.metadata inv.metadata,
  finalFrame.retained inv.retained,finalFrame.protected.operands inv.operands,complete.transport rfl⟩,rfl,finalFrame⟩
 convert pre.trans (body.trans (advance.trans jump)) using 1


def loopBudget (n:ℕ):ℕ→ℕ→ℕ
 | _,0=>0
 | j,k+1=>bodyBudget n j+14+loopBudget n (j+1) k
/-- No axis-produced bank or helper-ready state is an input to this induction. -/
theorem loop {n B:ℕ} (hn:0<n) (l:Layout n B) (j fuel:ℕ) (x:Fin n→ℂ) (s:State)
 (inv:Invariant hn l j x s) (left:j+fuel=axisCount n) (pc:s.pc=15) (hs:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤loopBudget n j fuel ∧Invariant hn l (axisCount n) x u ∧
 u.pc=15 ∧UniformSeedRankCrossPreparation.PreservedFrame n s u:=by
 induction fuel generalizing j s with
 | zero=>
  have eq:j=axisCount n:=by omega
  subst j
  exact ⟨s,0,.refl hs,le_rfl,inv,pc,⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩⟩
 | succ fuel ih=>
  let index:Fin (axisCount n):=⟨j,by omega⟩
  obtain ⟨v,t,first,cost,vi,vp,vf⟩:=iteration hn l index x s inv pc hs
  obtain ⟨u,k,rest,bound,ui,up,uf⟩:=ih (j+1) v vi (by omega) vp first.final_bound
  refine ⟨u,t+k,first.trans rest,?_,ui,up,vf.trans uf⟩
  change t≤bodyBudget n j+14 at cost
  rw[loopBudget];omega

/-- Fixed literal1410: original retained coefficients and real CRT roots suffice
for every emitted matching layer. This is a selected-layer constructor only. -/
theorem execution {n B:ℕ} (hn:0<n) (l:Layout n B) (x:Fin n→ℂ) (s:State)
 (hm:Metadata n s) (hr:Retained n (axisCount n) s) (ho:UniformInitialPreparation.Operands n x s)
 (pc:s.pc=0) (hs:WordBound B s):∃u t,
 BoundedExecution program n x B s t u ∧t≤loopBudget n 0 (axisCount n)+17 ∧u.pc=1409 ∧
 UniformAllAxisMatchingTablePreparation.Source (family hn l) (directory n) u ∧
 Metadata n u ∧Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u:=by
 have code:=l.code
 have safe:=boot_safe s hm l
 have initialized:=block_runs boot program 0 n B x s boot_code pc hs
  (by rw[boot_length];omega) safe.1 safe.2
 have bf:=boot_preserved n s
 have inv:Invariant hn l 0 x (applyBlock boot s):=
  ⟨boot_driver s hm,bf.protected.metadata hm,bf.retained hr,bf.protected.operands ho,fun _ hi=>by omega⟩
 have bp:(applyBlock boot s).pc=15:=by rw[UniformTensorMonomialMachine.applyBlock_pc,boot_length,pc]
 generalize hv:applyBlock boot s=v at initialized bf inv bp
 obtain ⟨a,t,run,cost,ai,ap,af⟩:=loop hn l 0 (axisCount n) x v inv (by omega) bp initialized.final_bound
 let u:=setPC a 1409
 have ub:=changePC_bound B a 1409 run.final_bound (by omega)
 have stop:BoundedRuns program n x B a 1 u:=.next run.final_bound
  (by simp[step,ap,branch_at,ai.driver.index,ai.driver.count,u,setPC]) (.refl ub)
 have halt:BoundedExecution program n x B u 1 u:=.halt ub (by simp[step,u,setPC,halt_at])
 have frame:UniformSeedRankCrossPreparation.PreservedFrame n s u:=bf.trans af
 refine ⟨u,15+t+2,?_,by omega,rfl,?_,frame.protected.metadata hm,frame.retained hr,
  frame.protected.operands ho,frame⟩
 · convert initialized.executes (run.executes (stop.executes halt)) using 1
   simp only[boot_length];omega
 · intro j
   exact ai.completed j j.isLt


/-- Empty-startup continuation uses the unchanged actual935 producer. -/
def fullProgram:Program:=UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)++
 program.map (relocate 935 2345)++[.halt]
lemma fullProgram_length:fullProgram.length=2346:=by
 simp only[fullProgram,List.length_append,List.length_map,UniformAllAxisSeedPreparation.fullProgram_length,program_length];rfl
section
attribute [local irreducible] program UniformAllAxisSeedPreparation.fullProgram
lemma prefixCode (p q:Program) (ret:ℕ):CodeAt p (p.map (relocate 0 ret)++q) 0 ret:=by
 intro i hi
 rw[Nat.zero_add,List.getElem?_append_left (by simpa only[List.length_map] using hi),List.getElem?_map]
lemma full_startup_code:CodeAt UniformAllAxisSeedPreparation.fullProgram fullProgram 0 935:=by
 unfold fullProgram
 rw[List.append_assoc]
 exact prefixCode _ _ _
lemma full_driver_code:CodeAt program fullProgram 935 2345:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)) [.halt] program 935 2345
  (by simp only[List.length_map,UniformAllAxisSeedPreparation.fullProgram_length])
lemma full_halt:fullProgram[2345]?=some .halt:=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)++program.map (relocate 935 2345)) [.halt] [] 0 (by decide)
 simpa only[fullProgram,List.append_nil,List.length_append,List.length_map,
  UniformAllAxisSeedPreparation.fullProgram_length,program_length,Nat.add_zero,List.getElem?_cons_zero] using h

/-- One continuous literal2346 execution from empty heaps and one root request.
The ordinary allocation remains explicit; this constructs only a selected layer. -/
theorem initial_execution {n:ℕ} (hn:0<n) (l:Layout n ((n+2)^19)) (x:Fin n→ℂ):∃u t,
 BoundedExecution fullProgram n x ((n+2)^19) initial t u ∧
 t≤UniformAllAxisSeedPreparation.fullBudget n+loopBudget n 0 (axisCount n)+18 ∧u.pc=2345 ∧
 UniformAllAxisMatchingTablePreparation.Source (family hn l) (directory n) u ∧
 Metadata n u ∧Retained n (axisCount n) u ∧UniformInitialPreparation.Operands n x u ∧
 u.rootOrders=[UniformMasterRootMachine.order n] ∧u.outputs=initial.outputs:=by
 obtain ⟨p,s,start,_,ret,metadata,ops,_,_,roots,outputs,_,cost⟩:=UniformAllAxisSeedPreparation.initial_execution hn x
 have bound:=UniformAllAxisSeedPreparation.full_word_bound hn
 have hb:2346≤(n+2)^19:=by
  have pow:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
  norm_num at pow;omega
 have first:=UniformBoundedAssembly.boundedExecution_placed full_startup_code
  (by rw[UniformAllAxisSeedPreparation.fullProgram_length];omega) (by omega) start
 let e:=setPC s 0
 have em:Metadata n e:=metadata.transport (fun _ _=>rfl) (fun _ _=>rfl)
 have er:Retained n (axisCount n) e:=ret.withPC
 have eo:UniformInitialPreparation.Operands n x e:=ops.transport rfl
 obtain ⟨v,t,run,tc,vp,src,m,r,o,frame⟩:=execution hn l x e em er eo rfl
  (changePC_bound _ s 0 start.final_bound (by omega))
 have next:=UniformBoundedAssembly.boundedExecution_placed full_driver_code
  (by rw[program_length];omega) (by omega) run
 have he:placed 935 e=setPC s 935:=rfl
 rw[he] at next
 let u:=setPC v 2345
 have stop:BoundedExecution fullProgram n x ((n+2)^19) u 1 u:=.halt next.final_bound
  (by simp[step,u,setPC,full_halt])
 refine ⟨u,p+UniformAllAxisSeedPreparation.preparationRuntime n+1+t+1,?_,by omega,rfl,src,
  m.transport (fun _ _=>rfl) (fun _ _=>rfl),r.withPC,o.transport rfl,
  frame.2.2.2.2.trans roots,frame.2.2.2.1.trans outputs⟩
 exact first.executes (next.executes stop)

end

end
end ExactFourierCircuits.UniformAllAxisSeedEdgePreparation
