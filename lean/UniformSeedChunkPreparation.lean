import UniformSeedHeightPreparation
import UniformChunkMatchingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedChunkPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformAllAxisSeedPreparation (axisCount radix Retained directoryBase)

/-- Ordinary geometry/placement inputs. The selected axis, offsets and retained
    coefficient banks are inherited from SeedHeight; no generated table enters. -/
structure Config where
  seed : UniformSeedHeightPreparation.Config
  borrowed : ℕ
  selected : ℕ
  ordinals : ℕ
  mapped : ℕ
  permutation : ℕ
  widths : ℕ
  markers : ℕ
  axis : ℕ
  layer : ℕ
  color : ℕ

def Config.register (c : Config) : ℕ → ℕ
  | 1230=>c.borrowed | 1231=>c.selected | 1232=>c.ordinals | 1233=>c.mapped
  | 1234=>c.permutation | 1235=>c.widths | 1236=>c.markers | 1237=>c.axis
  | 1238=>c.layer | 1239=>c.color | _=>0

def Config.chunk (n : ℕ) (j : Fin (axisCount n)) (c : Config) : UniformChunkMatchingPreparation.Parameters :=
  ⟨c.seed.height,radix n j,c.seed.j0,c.seed.i0,c.borrowed,c.selected,c.ordinals,
    c.mapped,c.permutation,c.widths,c.markers,c.axis,c.layer,c.color⟩

/-- Capture ordinary inputs before helpers use their own scratch registers. -/
def boot : List Op := [.literal 1240 0,.add 1241 1120 1240,
  .add 1242 1124 1240,.add 1243 1125 1240]
/-- Read the true retained radix from the actual two-field directory. All
    helper headers are installed by charged instructions. -/
def directoryLoad : List Op := [.literal 1244 1,.literal 1245 2,
  .add 1246 105 106,.add 1246 1246 103,.mul 1247 1241 1245,
  .add 1246 1246 1247,.add 1246 1246 1244,.getNat 1180 1246]
def copyHeaders : List Op := [.add 1181 1243 1240,.add 1182 1242 1240,
  .add 1183 1230 1240,.add 1184 1231 1240,.add 1185 1232 1240,
  .add 1186 1233 1240,.add 1187 1234 1240,.add 1188 1235 1240,
  .add 1189 1236 1240,.add 1190 1237 1240,.add 1191 1238 1240,.add 1192 1239 1240]
def setup : List Op := directoryLoad ++ copyHeaders

def beforeSetup : Program := boot.map Op.code ++
  UniformSeedHeightPreparation.program.map (relocate 4 1050)
def beforeChunk : Program := beforeSetup ++ setup.map Op.code
def program : Program := beforeChunk ++
  UniformChunkMatchingPreparation.program.map (relocate 1070 1285) ++ [.halt]

lemma boot_length : boot.length=4 := rfl
lemma setup_length : setup.length=20 := rfl
lemma beforeSetup_length : beforeSetup.length=1050 := by
  simp [beforeSetup,boot_length,UniformSeedHeightPreparation.program_length]
lemma beforeChunk_length : beforeChunk.length=1070 := by
  simp [beforeChunk,beforeSetup_length,setup_length]
lemma program_length : program.length=1286 := by
  simp [program,beforeChunk_length,UniformChunkMatchingPreparation.program_length]
lemma boot_code : BlockAt boot program 0 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma seed_code : CodeAt UniformSeedHeightPreparation.program program 4 1050 := by
  let after:=setup.map Op.code ++ UniformChunkMatchingPreparation.program.map (relocate 1070 1285) ++ [.halt]
  have he:program=boot.map Op.code ++ UniformSeedHeightPreparation.program.map (relocate 4 1050) ++ after := by
    simp [program,beforeChunk,beforeSetup,after,List.append_assoc]
  rw [he]
  exact UniformRankCrossPreparationMachine.segment_code _ after _ 4 1050
    (by simp [boot_length])
lemma setup_code : BlockAt setup program 1050 := by
  intro i hi
  have h:=UniformAllAxisSeedPreparation.lookup_segment beforeSetup (setup.map Op.code)
    (UniformChunkMatchingPreparation.program.map (relocate 1070 1285) ++ [.halt]) i
    (by simpa using hi)
  simpa only [program,beforeChunk,List.append_assoc,beforeSetup_length,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some] using h

lemma directoryLoad_length : directoryLoad.length=8 := rfl
lemma copyHeaders_length : copyHeaders.length=12 := rfl
lemma directoryLoad_code : BlockAt directoryLoad program 1050 := by
  intro i hi
  change i<8 at hi
  have h:=setup_code i (by change i<20;omega)
  have sub:(setup[i]'(by change i<20;omega))=(directoryLoad[i]'hi):=by
    simp only [setup,List.getElem_append_left (show i<directoryLoad.length from hi)]
    rfl
  simpa only [sub] using h
lemma copyHeaders_code : BlockAt copyHeaders program 1058 := by
  intro i hi
  change i<12 at hi
  have h:=setup_code (8+i) (by change 8+i<20;omega)
  have sub:(setup[8+i]'(by change 8+i<20;omega))=(copyHeaders[i]'hi):=by
    simp only [setup,List.getElem_append_right (show directoryLoad.length≤8+i by change 8≤8+i;omega),
      directoryLoad_length,show 8+i-8=i by omega]
    rfl
  simpa only [sub,show 1050+(8+i)=1058+i by omega] using h
lemma chunk_code : CodeAt UniformChunkMatchingPreparation.program program 1070 1285 :=
  UniformRankCrossPreparationMachine.segment_code beforeChunk [.halt] _ 1070 1285 beforeChunk_length
lemma halt_at : program[1285]?=some .halt := by
  rw [program,List.getElem?_append_right (by simp [beforeChunk_length,UniformChunkMatchingPreparation.program_length])]
  simp [beforeChunk_length,UniformChunkMatchingPreparation.program_length]

/-- Explicit finite destination footprint for preservation of the new caller. -/
def below (p : Program) := p.all (fun ins=>decide (UniformSeedHeightPreparation.natCeiling ins≤1230))
lemma below_append (p q : Program) : below (p++q)=(below p && below q) := List.all_append
lemma below_relocate (p : Program) (base ret : ℕ) : below (p.map (relocate base ret))=below p := by
  simp [below,List.all_map,Function.comp_def,UniformSeedHeightPreparation.natCeiling_relocate]
lemma seedHeight_ceiling : ∀ins∈UniformSeedHeightPreparation.program,
    UniformSeedHeightPreparation.natCeiling ins≤1230 := by
  have seed:below UniformSeedRankCrossPreparation.program=true := by
    apply List.all_eq_true.mpr
    intro ins hi
    exact decide_eq_true (by have h:=UniformSeedHeightPreparation.seed_ceiling ins hi;omega)
  have height:below UniformCrossHeightPreparationMachine.program=true := by decide
  have h:below UniformSeedHeightPreparation.program=true := by
    simp only [UniformSeedHeightPreparation.program,UniformSeedHeightPreparation.beforeHeight,
      UniformSeedHeightPreparation.beforeSeed,below_append,below_relocate,seed,height,Bool.and_eq_true]
    repeat' apply And.intro
    all_goals decide
  simpa only [below,List.all_eq_true,decide_eq_true_eq] using h
lemma ceiling_keeps (q : ℕ) (hq:1230≤q) : ∀ins∈UniformSeedHeightPreparation.program,
    UniformNewtonTableMachine.KeepsNat q ins := by
  intro ins hi
  have h:=seedHeight_ceiling ins hi
  cases ins <;> simp only [UniformSeedHeightPreparation.natCeiling] at h
  all_goals simp only [UniformNewtonTableMachine.KeepsNat]
  all_goals omega

noncomputable section

structure Args (n : ℕ) (j : Fin (axisCount n)) (c : Config) (s : State) : Prop where
  seed : UniformSeedHeightPreparation.Args n j c.seed s
  extra : ∀q,1230≤q→q≤1239→s.natReg q=c.register q

structure Carried (n : ℕ) (j : Fin (axisCount n)) (c : Config) (s : State) : Prop where
  zero : s.natReg 1240=0
  index : s.natReg 1241=j.val
  target : s.natReg 1242=c.seed.i0
  source : s.natReg 1243=c.seed.j0
  extra : ∀q,1230≤q→q≤1239→s.natReg q=c.register q

/-- Nat-only caller frame, including every scalar and heap cell. -/
def SetupFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀q,(q<1180 ∨ (1193≤q ∧ q<1240) ∨ 1248≤q)→u.natReg q=s.natReg q)
lemma SetupFrame.preserved {n : ℕ} {s u : State} (f:SetupFrame s u) :
    UniformSeedRankCrossPreparation.PreservedFrame n s u :=
  ⟨fun _ _=>congrFun f.1 _,fun _ _=>congrFun f.2.1 _,
    fun q _ _=>f.2.2.2.2.2 q (by omega),f.2.2.2.1,f.2.2.2.2.1⟩
lemma boot_frame (s : State) : SetupFrame s (applyBlock boot s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma setup_frame (s : State) : SetupFrame s (applyBlock setup s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [setup,directoryLoad,copyHeaders,applyBlock,Op.apply,writeNat,next]
lemma boot_args {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (args:Args n j c s) : UniformSeedHeightPreparation.Args n j c.seed (setPC (applyBlock boot s) 0) := by
  obtain ⟨idx,core,extra⟩:=args.seed
  refine ⟨?_,?_,?_⟩
  · exact (boot_frame s).2.2.2.2.2 1120 (by omega) |>.trans idx
  · intro q lo hi
    exact ((boot_frame s).2.2.2.2.2 q (by omega)).trans (core q lo hi)
  · intro q lo hi
    exact ((boot_frame s).2.2.2.2.2 q (by omega)).trans (extra q lo hi)
lemma boot_carried {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (args:Args n j c s) : Carried n j c (setPC (applyBlock boot s) 0) := by
  have target:=args.seed.2.1 1124 (by omega) (by omega)
  have source:=args.seed.2.1 1125 (by omega) (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [boot,applyBlock,Op.apply,writeNat,next,setPC]
  · simp [boot,applyBlock,Op.apply,writeNat,next,setPC,args.seed.1]
  · simpa [boot,applyBlock,Op.apply,writeNat,next,setPC,
      UniformSeedHeightPreparation.Config.register,UniformSeedHeightPreparation.Config.seed,
      UniformSeedRankCrossPreparation.Config.register] using target
  · simpa [boot,applyBlock,Op.apply,writeNat,next,setPC,
      UniformSeedHeightPreparation.Config.register,UniformSeedHeightPreparation.Config.seed,
      UniformSeedRankCrossPreparation.Config.register] using source
  · intro q lo hi
    exact ((boot_frame s).2.2.2.2.2 q (by omega)).trans (args.extra q lo hi)
lemma Carried.transport {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s u : State}
    (h:Carried n j c s) (eq:∀q,1230≤q→q≤1243→u.natReg q=s.natReg q) : Carried n j c u :=
  ⟨(eq 1240 (by omega) (by omega)).trans h.zero,(eq 1241 (by omega) (by omega)).trans h.index,
    (eq 1242 (by omega) (by omega)).trans h.target,(eq 1243 (by omega) (by omega)).trans h.source,
    fun q lo hi=>(eq q lo (by omega)).trans (h.extra q lo hi)⟩

/-- SeedHeight's existing disjoint layout plus one fresh chunk output pool.
    Only capacity, depth/color choice and addresses are extra inputs. -/
structure Layout (n : ℕ) (j : Fin (axisCount n)) (c : Config) (B : ℕ) : Prop where
  seed : UniformSeedHeightPreparation.Layout n j c.seed B
  capacity : c.seed.gates+c.seed.e+c.seed.a≤radix n j
  oldRows : UniformCrossHeightPreparationMachine.rowBase c.seed.height (8*c.seed.exponent+7)≤c.borrowed
  oldColors : UniformCrossHeightPreparationMachine.colorBase c.seed.height (8*c.seed.exponent+7)≤c.borrowed
  oldDirectory : UniformCrossHeightPreparationMachine.recordBase c.seed.height (8*c.seed.exponent+7)≤c.borrowed
  borrowFresh : c.borrowed+c.seed.gates≤c.selected
  selectedFresh : c.selected+6*c.seed.gates≤c.ordinals
  ordinalFresh : c.ordinals+2*c.seed.gates≤c.mapped
  mappedFresh : c.mapped+6*c.seed.gates≤c.permutation
  permutationFresh : c.permutation+radix n j≤c.widths
  widthsFresh : c.widths+radix n j≤c.markers
  markersFresh : c.markers+radix n j≤c.axis
  finalBound : c.axis+4≤B
  depth : c.layer<8*c.seed.exponent+7
  color : c.color<11
  code : 1286≤B

lemma Layout.chunk {n : ℕ} {j : Fin (axisCount n)} {c : Config} {B : ℕ} (h:Layout n j c B) :
    UniformChunkMatchingPreparation.Layout (c.chunk n j) B := by
  refine ⟨by have :=h.code;omega,?_,?_,?_,?_,h.capacity,h.oldRows,h.oldColors,h.oldDirectory,
    h.borrowFresh,h.selectedFresh,h.ordinalFresh,h.mappedFresh,h.permutationFresh,h.widthsFresh,
    h.markersFresh,h.finalBound,h.depth,h.color⟩
  · change 2≤radix n j
    have :=h.seed.positiveA;have :=h.seed.positiveE
    have :=h.seed.hRows;have :=h.seed.interior;have :=h.seed.columns;omega
  · change c.seed.j0+c.seed.e≤radix n j
    have :=h.seed.columns;have :=h.seed.gSplit;omega
  · exact h.seed.hRows
  · exact Or.inl (h.seed.columns.trans h.seed.interior)

lemma directory_address {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (metadata:UniformPermutationInversePreparation.Metadata n s) (carry:Carried n j c s) :
    s.natReg 105+s.natReg 106+s.natReg 103+2*s.natReg 1241+1=directoryBase n+2*j.val+1 := by
  rw [metadata.saved.copyAddress,metadata.saved.copyLength,metadata.saved.workingLength,carry.index]
  rw [UniformAllAxisSeedPreparation.directory_after_protected]

lemma directoryLoad_frame (s : State) : SetupFrame s (applyBlock directoryLoad s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [directoryLoad,applyBlock,Op.apply,writeNat,next]
lemma copyHeaders_frame (s : State) : SetupFrame s (applyBlock copyHeaders s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq
  simp (disch:=omega) [copyHeaders,applyBlock,Op.apply,writeNat,next]
lemma applyBlock_append (a b : List Op) (s : State) : applyBlock (a++b) s=applyBlock b (applyBlock a s) := by
  induction a generalizing s with
  | nil=>rfl
  | cons o a ih=>exact ih (o.apply s)
lemma directoryLoad_radix {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (carry:Carried n j c s) :
    (applyBlock directoryLoad s).natReg 1180=radix n j := by
  have dir:=directory_address metadata carry
  have width:=ret.width j j.isLt
  simp only [directoryLoad,applyBlock,Op.apply,writeNat,next,Function.update_apply]
  simp
  rw [show s.natReg 105+s.natReg 106+s.natReg 103+s.natReg 1241*2+1=
      directoryBase n+2*j.val+1 by simpa [Nat.mul_comm] using dir,width]
  rfl
lemma copyHeaders_spec {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (carry:Carried n j c s) (width:s.natReg 1180=radix n j)
    (height:UniformCrossHeightPreparationMachine.Header c.seed.height s) :
    UniformChunkMatchingPreparation.Header (c.chunk n j) (setPC (applyBlock copyHeaders s) 0) := by
  constructor
  · apply height.transport_register
    intro q lo hi
    exact (copyHeaders_frame s).2.2.2.2.2 q (by omega)
  · simpa [copyHeaders,applyBlock,Op.apply,writeNat,next,setPC] using (show s.natReg 1180=(c.chunk n j).radix from width)
  all_goals simp (disch:=omega) [copyHeaders,applyBlock,Op.apply,writeNat,next,setPC,
    carry.zero,carry.target,carry.source,carry.extra,Config.register,Config.chunk]
lemma setup_spec {n : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (carry:Carried n j c s)
    (height:UniformCrossHeightPreparationMachine.Header c.seed.height s) :
    UniformChunkMatchingPreparation.Header (c.chunk n j) (setPC (applyBlock setup s) 0) := by
  have carried:Carried n j c (applyBlock directoryLoad s):=carry.transport
    (by
      intro q lo hi
      apply UniformSeedRankCrossPreparation.block_register_keeps
      simp [directoryLoad,UniformSeedRankCrossPreparation.KeepsRegister]
      omega)
  have hh:UniformCrossHeightPreparationMachine.Header c.seed.height (applyBlock directoryLoad s):=
    height.transport_register (fun q lo hi=>(directoryLoad_frame s).2.2.2.2.2 q (by omega))
  simpa only [setup,applyBlock_append] using copyHeaders_spec carried (directoryLoad_radix metadata ret carry) hh


lemma boot_safe {B : ℕ} {s : State} (hs:WordBound B s) : readable boot s ∧ peak boot s≤B := by
  constructor
  · simp [boot,readable,Op.readable]
  · simp [boot,peak,Op.peak,Op.apply,writeNat,next]
    exact ⟨hs.2.1 1120,hs.2.1 1124,hs.2.1 1125⟩
lemma directoryLoad_safe {n B : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (carry:Carried n j c s)
    (hs:WordBound B s) (hc:2≤B) : readable directoryLoad s ∧ peak directoryLoad s≤B := by
  have dir:=directory_address metadata carry
  have cell:=ret.width j j.isLt
  have pointer:directoryBase n+2*j.val+1≤B:=(hs.2.2.1 _ _ cell).1
  have value:radix n j≤B:=(hs.2.2.1 _ _ cell).2
  have addr:s.natReg 105+s.natReg 106+s.natReg 103+s.natReg 1241*2+1=directoryBase n+2*j.val+1:=by
    simpa [Nat.mul_comm] using dir
  constructor
  · simp [directoryLoad,readable,Op.readable,Op.apply,writeNat,next,addr,cell]
  · simp [directoryLoad,peak,Op.peak,Op.apply,writeNat,next,addr,cell]
    omega
lemma copyHeaders_safe {n B : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State}
    (carry:Carried n j c s) (hs:WordBound B s) : readable copyHeaders s ∧ peak copyHeaders s≤B := by
  constructor
  · simp [copyHeaders,readable,Op.readable]
  · simp [copyHeaders,peak,Op.peak,Op.apply,writeNat,next,carry.zero]
    repeat' apply And.intro
    all_goals exact hs.2.1 _

/-- The directory load and header copies execute, rather than appearing as a
    host-state update between the two physical producers. -/
lemma setup_runs {n B : ℕ} {j : Fin (axisCount n)} {c : Config} {s : State} (x : Fin n→ℂ)
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (carry:Carried n j c s)
    (pc:s.pc=1050) (hs:WordBound B s) (hc:1070≤B) :
    BoundedRuns program n x B s 20 (applyBlock setup s) := by
  have safe:=directoryLoad_safe metadata ret carry hs (by omega)
  have first:=block_runs directoryLoad program 1050 n B x s directoryLoad_code pc hs
    (by rw [directoryLoad_length];omega) safe.1 safe.2
  let v:=applyBlock directoryLoad s
  have vp:v.pc=1058:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,directoryLoad_length]
  have vc:Carried n j c v:=carry.transport (by
    intro q lo hi
    apply UniformSeedRankCrossPreparation.block_register_keeps
    simp [directoryLoad,UniformSeedRankCrossPreparation.KeepsRegister]
    omega)
  have safe2:=copyHeaders_safe vc first.final_bound
  have last:=block_runs copyHeaders program 1058 n B x v copyHeaders_code vp first.final_bound
    (by rw [copyHeaders_length];omega) safe2.1 safe2.2
  simpa only [directoryLoad_length,copyHeaders_length,setup,applyBlock_append] using first.trans last


/-- Later Nat-table preparation preserves every produced scalar bank, actual
    cross tape/order/directory, and all of its colored depth buckets. -/
lemma seedResult_transport {n B : ℕ} {j : Fin (axisCount n)} {c : Config} {s u : State}
    (hn:0<n) (h:Layout n j c B)
    (post:UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) s)
    (heap:∀q,q<c.borrowed→u.natHeap q=s.natHeap q)
    (scalar:u.scalarHeap=s.scalarHeap)
    (regs:∀q,1050≤q→q≤1079→u.natReg q=s.natReg q) :
    UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) u := by
  have size: (UniformRankCrossReplayPreparationMachine.cross
      (UniformSeedHeightPreparation.parameters n j c.seed) (h.seed.replay hn j c.seed B)).size =
      UniformCrossHeightPreparationMachine.gates c.seed.height := by
    exact UniformCrossHeightPreparationMachine.cross_size c.seed.height _ _
  have before: c.seed.height.D≤c.borrowed := by
    have hr:=h.oldRows
    change c.seed.height.D+6*UniformCrossHeightPreparationMachine.gates c.seed.height*
      (8*c.seed.exponent+7)≤c.borrowed at hr
    omega
  refine ⟨post.source.transport size h.seed.heightLayout (fun q hi=>heap q (hi.trans_le before)),
    post.cursor.transport_register regs,?_,?_,?_,?_,?_⟩
  · intro d hd
    obtain ⟨table,col,rec⟩:=post.processed d hd
    have len:=UniformCrossHeightPreparationMachine.bucket_length
      (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j c.seed)
        (h.seed.replay hn j c.seed B)).program c.seed.height.enabled d
    have len':(UniformCrossDepthReplayPreparation.bucket
      (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j c.seed)
        (h.seed.replay hn j c.seed B)).program c.seed.height.enabled d).length ≤
        2*UniformCrossHeightPreparationMachine.gates c.seed.height:=by simpa only [size] using len
    have rr:=h.oldRows
    have cc:=h.oldColors
    have dd:=h.oldDirectory
    have rh:UniformCrossHeightPreparationMachine.rowBase c.seed.height d+3*(UniformCrossDepthReplayPreparation.bucket
      (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j c.seed)
        (h.seed.replay hn j c.seed B)).program c.seed.height.enabled d).length≤c.borrowed:=by
      simp only [UniformCrossHeightPreparationMachine.rowBase] at rr ⊢;nlinarith [len']
    have ch:UniformCrossHeightPreparationMachine.colorBase c.seed.height d+(UniformCrossDepthReplayPreparation.bucket
      (UniformRankCrossReplayPreparationMachine.cross (UniformSeedHeightPreparation.parameters n j c.seed)
        (h.seed.replay hn j c.seed B)).program c.seed.height.enabled d).length≤c.borrowed:=by
      simp only [UniformCrossHeightPreparationMachine.colorBase] at cc ⊢;nlinarith [len']
    have dh:UniformCrossHeightPreparationMachine.recordBase c.seed.height d+3≤c.borrowed:=by
      simp only [UniformCrossHeightPreparationMachine.recordBase] at dd ⊢;omega
    refine ⟨?_,?_,?_⟩
    · apply UniformChunkMatchingPreparation.table_transport table
      intro q lo hi
      simp only [List.length_map] at hi
      exact heap q (lt_of_lt_of_le hi rh)
    · intro i
      rw [heap _ (lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) ch)]
      exact col i
    · unfold UniformCrossHeightPreparationMachine.Record
      rw [heap _ (by omega),heap _ (by omega),heap _ (by omega)]
      exact rec
  · intro i;rw [scalar];exact post.positive i
  · rw [scalar];exact post.root
  · intro i hi;rw [scalar];exact post.negative i hi
  · intro i hi;rw [scalar];exact post.constants i hi

lemma chunk_preserved {n B : ℕ} {j : Fin (axisCount n)} {c : Config} {s u : State}
    (h:Layout n j c B) (outside:UniformChunkMatchingPreparation.Outside (c.chunk n j) s u)
    (frame:UniformChunkMatchingPreparation.Frame s u) :
    UniformSeedRankCrossPreparation.PreservedFrame n s u := by
  refine ⟨?_,fun q _=>congrFun frame.1 q,
    fun q lo hi=>UniformChunkMatchingPreparation.saved_metadata_frame frame q lo hi,frame.2.2.1,frame.2.2.2.1⟩
  intro q hq
  have old:=h.seed.oldBanks.directory
  have hd:=h.seed.heightLayout.directory
  have hr:=h.oldRows
  change directoryBase n+2*axisCount n≤c.seed.directory at old
  change c.seed.directory+c.seed.gates+2≤c.seed.rows at hd
  change c.seed.rows+6*c.seed.gates*(8*c.seed.exponent+7)≤c.borrowed at hr
  exact outside q (Or.inl (by change q<c.borrowed;omega))

def runtimeBudget (n : ℕ) (j : Fin (axisCount n)) (c : Config) :=
  UniformSeedHeightPreparation.runtimeBudget n j c.seed+4*c.seed.exponent+180*radix n j+117

/-- Actual selected matching-axis outputs, including the mapped three-field
    coefficient-address rows. The earlier seed/height banks are retained. -/
structure Result (n : ℕ) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (hn:0<n) (h:Layout n j c B) (u : State) : Prop where
  prepared : UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) u
  header : UniformChunkMatchingPreparation.Header (c.chunk n j) u
  count : u.natReg 894=(UniformChunkMatchingPreparation.indices (c.chunk n j)
    (UniformChunkMatchingPreparation.crossWord (c.chunk n j)
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2)).length
  rows : UniformSectorPackingMachine.Rows [UniformChunkMatchingPreparation.axis h.chunk
    (UniformChunkMatchingPreparation.crossWord (c.chunk n j)
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2)
    (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
    (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)] 0 c.axis u
  widths : UniformSectorPackingMachine.Widths [UniformChunkMatchingPreparation.axis h.chunk
    (UniformChunkMatchingPreparation.crossWord (c.chunk n j)
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2)
    (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
    (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)] u
  permutations : UniformSectorPackingMachine.Permutations [UniformChunkMatchingPreparation.axis h.chunk
    (UniformChunkMatchingPreparation.crossWord (c.chunk n j)
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2)
    (UniformChunkMatchingPreparation.cross_domain (c.chunk n j) _ _)
    (UniformChunkMatchingPreparation.cross_degree (c.chunk n j) _ _)] u
  mapped : UniformCrossShearTableMachine.Table c.mapped
    (UniformChunkMatchingPreparation.mappedRows (c.chunk n j) h.chunk.capacity
      (UniformChunkMatchingPreparation.crossWord (c.chunk n j)
        (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2)
      (UniformChunkMatchingPreparation.crossLocations (c.chunk n j) c.seed.negative)) u

/-- From retained selected-axis coefficients to an actual physical matching
    axis in one finite program. No generated bank, color record, logical-row
    table, borrowed coordinate bank or helper-ready header is an input. -/
theorem execution {n : ℕ} (hn:0<n) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (x : Fin n→ℂ) (s : State) (args:Args n j c s)
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
    (h:Layout n j c B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤runtimeBudget n j c ∧ u.pc=1285 ∧
    Result n j c B hn h u ∧ Retained n (axisCount n) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    UniformSeedRankCrossPreparation.PreservedFrame n s u := by
  have code:=h.code
  have safe:=boot_safe hs
  have first:=block_runs boot program 0 n B x s boot_code pc hs
    (by rw [boot_length];omega) safe.1 safe.2
  let v:=applyBlock boot s
  have vp:v.pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,boot_length]
  let seedEntry:=setPC v 0
  have eb:WordBound B seedEntry:=changePC_bound B v 0 first.final_bound (by omega)
  have start:UniformSeedRankCrossPreparation.PreservedFrame n s seedEntry:=(boot_frame s).preserved
  obtain ⟨w,t,seedRun,seedCost,wp,post,_,_,_,seedFrame⟩:=
    UniformSeedHeightPreparation.execution hn j c.seed B x seedEntry (boot_args args)
      (start.protected.metadata metadata) (start.retained ret) (start.protected.operands ops)
      h.seed rfl eb
  have middle:=UniformBoundedAssembly.boundedExecution_placed seed_code
    (by rw [UniformSeedHeightPreparation.program_length];omega) (by omega) seedRun
  rw [UniformSeedRankCrossPreparation.placed_zero v 4 vp] at middle
  let afterSeed:=setPC w 1050
  have carry:Carried n j c afterSeed:=(boot_carried args).transport (by
    intro q lo _
    have eq : w.natReg q=seedEntry.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat seedRun.executes (ceiling_keeps q lo)
    exact eq)
  have old:UniformSeedRankCrossPreparation.PreservedFrame n s afterSeed:=start.trans seedFrame
  have carriedMeta:UniformPermutationInversePreparation.Metadata n afterSeed:=old.protected.metadata metadata
  have carriedRet:Retained n (axisCount n) afterSeed:=old.retained ret
  have install:=setup_runs (c:=c) (j:=j) x carriedMeta carriedRet carry rfl middle.final_bound (by omega)
  let installed:=applyBlock setup afterSeed
  have ip:installed.pc=1070:=by rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
  let chunkEntry:=setPC installed 0
  have ib:WordBound B chunkEntry:=changePC_bound B installed 0 install.final_bound (by omega)
  have head:=setup_spec carriedMeta carriedRet carry (post.cursor.header.withPC 1050)
  have transported:UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) chunkEntry:=
    seedResult_transport hn h post (fun _ _=>rfl) rfl
      (fun q lo hi=>(setup_frame afterSeed).2.2.2.2.2 q (by omega))
  obtain ⟨ticks,z,cost,last,header,count,rows,widths,perms,mapped,processed,outside,frame⟩:=
    UniformChunkMatchingPreparation.cross_execution (c.chunk n j) c.seed.negative B n x chunkEntry
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2
      h.chunk head transported.processed rfl ib
  have lastPlaced:=UniformBoundedAssembly.boundedExecution_placed chunk_code
    (by rw [UniformChunkMatchingPreparation.program_length];omega) (by omega) last
  rw [UniformSeedRankCrossPreparation.placed_zero installed 1070 ip] at lastPlaced
  let u:=setPC z 1285
  have stop:BoundedExecution program n x B u 1 u:=.halt lastPlaced.final_bound
    (by simp [step,u,setPC,halt_at])
  have all:BoundedExecution program n x B s (4+t+20+ticks+1) u:=by
    simpa only [boot_length,Nat.add_assoc] using first.executes (middle.executes (install.executes (lastPlaced.executes stop)))
  have pre:UniformSeedRankCrossPreparation.PreservedFrame n s chunkEntry:=
    old.trans (setup_frame afterSeed).preserved
  have full:UniformSeedRankCrossPreparation.PreservedFrame n s u:=pre.trans (chunk_preserved h outside frame)
  have prepared:UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) u:=
    seedResult_transport hn h transported (fun q hq=>outside q (Or.inl hq)) frame.1
      (fun q lo hi=>frame.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega))
  refine ⟨u,4+t+20+ticks+1,all,?_,rfl,⟨prepared,header.withPC 1285,count,rows,widths,perms,mapped⟩,
    full.retained ret,full.protected.metadata metadata,full.protected.operands ops,full⟩
  unfold runtimeBudget
  change ticks≤4*c.seed.exponent+180*radix n j+92 at cost
  omega


/-- Same ambient word budget; the number of executed instructions depends only
    polynomially on local widths and the logarithm of the original master order. -/
lemma Layout.runtime_bound {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (h:Layout n j c B) : runtimeBudget n j c≤
    100000300*(8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2)^5 := by
  have prior:=h.seed.runtime_bound j c.seed B
  let z:=8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2
  have hz:1≤z:=by dsimp [z];omega
  have hp:z≤z^5:=le_self_pow hz (by decide)
  have hw:c.seed.width≤8*radix n j:=by
    have b:=UniformWorkspacePlanner.width_bound (show 0<c.seed.a+c.seed.e by have :=h.seed.positiveA;omega)
    change 2^c.seed.exponent≤4*(c.seed.a+c.seed.e) at b
    have a:=h.seed.hRows;have e:=h.seed.columns;have g:=h.seed.gSplit
    rw [UniformSeedHeightPreparation.Config.width,UniformRadixTwoDAG.width_eq]
    omega
  have hk:c.seed.exponent≤c.seed.width:=by
    have b:=UniformCrossDepthReplayPreparation.power_ge_successor c.seed.exponent
    change c.seed.exponent+1≤2^c.seed.exponent at b
    rw [UniformSeedHeightPreparation.Config.width,UniformRadixTwoDAG.width_eq];omega
  change UniformSeedHeightPreparation.runtimeBudget n j c.seed+4*c.seed.exponent+180*radix n j+117≤100000300*z^5
  change UniformSeedHeightPreparation.runtimeBudget n j c.seed≤100000000*z^5 at prior
  have extra:4*c.seed.exponent+180*radix n j+117≤300*z:=by dsimp [z];omega
  nlinarith only [prior,extra,hp]

lemma Layout.logarithmic_runtime_bound {n : ℕ} (hn:0<n) (j : Fin (axisCount n))
    (c : Config) (B : ℕ) (h:Layout n j c B) : runtimeBudget n j c≤
    100000300*(1024*(Nat.log 3 (2*n)+2)^2+3*Nat.clog 2 (n+1)+12)^5 := by
  have r:=UniformSelectedCRT.radix_quadratic hn j
  change radix n j≤128*(UniformInitialPreparation.ell n+2)^2 at r
  have ell:=UniformWorkingLength.axisCount_log_bound hn
  have square:(UniformInitialPreparation.ell n+2)^2≤(Nat.log 3 (2*n)+2)^2:=
    Nat.pow_le_pow_left (Nat.add_le_add_right ell 2) 2
  have master:=UniformSeedHeightPreparation.master_log_bound hn
  have base:8*radix n j+Nat.log2 (UniformMasterRootMachine.order n+1)+2≤
    1024*(Nat.log 3 (2*n)+2)^2+3*Nat.clog 2 (n+1)+12:=by omega
  exact (h.runtime_bound j c B).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 5))

/-- A genuinely selected odd-prime radix can accommodate the smallest nonempty
    measured cross. This uses no evaluation of an astronomical startup array. -/
theorem exists_selected_capacity : ∃n,0<n ∧ ∃j:Fin (axisCount n),196≤radix n j := by
  let n:=UniformWorkingLength.primeProduct 194
  have hn:0<n:=UniformWorkingLength.primeProduct_pos 194
  have axes:194≤UniformWorkingLength.axisCount n:=by
    by_contra h
    have hi:UniformWorkingLength.axisCount n+1≤194:=by omega
    have bound:=UniformWorkingLength.primeProduct_strictMono.monotone hi
    have big:2*n<UniformWorkingLength.primeProduct (UniformWorkingLength.axisCount n+1):=by
      simpa only [UniformWorkingLength.primeProduct,UniformWorkingLength.oddProduct,
        UniformWorkingLength.nextPrime] using (UniformWorkingLength.maximal_product hn).2
    change UniformWorkingLength.primeProduct (UniformWorkingLength.axisCount n+1)≤n at bound
    omega
  let i:Fin (UniformWorkingLength.axisCount n):=⟨193,by omega⟩
  let j:Fin (axisCount n):=i.castSucc
  refine ⟨n,hn,j,?_⟩
  change 196≤UniformSelectedCRT.radices n i.castSucc
  simpa only [UniformSelectedCRT.radices,Fin.snoc_castSucc] using UniformWorkingLength.oddPrime_lower 193

/-- Nonempty unit chunks have K=2 and G=194; their total coordinate capacity
    is exactly196. Zero-width chunks are not used by the nonvacuity witness. -/
def unitSeed : UniformSeedHeightPreparation.Config :=
  ⟨1,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,false⟩
lemma unit_exponent : unitSeed.exponent=2 := by decide
lemma unit_gates : unitSeed.gates=194 := by decide
lemma unit_capacity : unitSeed.gates+unitSeed.e+unitSeed.a=196 := by decide
lemma selected_unit_geometry : ∃n,0<n ∧ ∃j:Fin (axisCount n),
    unitSeed.gates+unitSeed.e+unitSeed.a≤radix n j ∧
    unitSeed.i0+unitSeed.a≤radix n j ∧ unitSeed.j0+unitSeed.e≤unitSeed.i0 := by
  obtain ⟨n,hn,j,capacity⟩:=exists_selected_capacity
  refine ⟨n,hn,j,?_,?_,?_⟩
  · simpa only [unit_capacity] using capacity
  · change 2≤radix n j;omega
  · decide


lemma seed_layout_mono {n B₀ B : ℕ} {j : Fin (axisCount n)}
    {seed:UniformSeedHeightPreparation.Config} (original:UniformSeedHeightPreparation.Layout n j seed B₀)
    (big:B₀≤B) : UniformSeedHeightPreparation.Layout n j seed B := by
  constructor
  · exact original.positiveA
  · exact original.positiveE
  · exact original.hRows
  · exact original.gSplit
  · exact original.interior
  · exact original.columns
  · exact original.hFresh
  · exact original.gFresh
  · exact original.masterFresh
  · exact original.outputBound.trans big
  · exact original.sourceEnd
  · exact original.arenaPositive
  · exact original.bankAfter
  · exact original.spectrumEnvelope.trans big
  · exact original.convFresh
  · exact original.topologyEnvelope.trans big
  · exact original.tapeFresh
  · exact original.depthBound.trans big
  · exact original.fftFresh
  · exact original.depthFresh
  · exact original.directoryFresh
  · exact original.directoryBound.trans big
  · exact original.negativeFresh
  · exact original.constantsFresh
  · exact original.constantsBound.trans big
  · exact original.oldBanks
  · exact original.heightLayout
  · exact original.heightEnvelope.trans big
  · exact original.codeBound.trans big

/-- Fresh physical pools exist constructively over any valid seed layout and
    feasible nonempty chunk. The enlarged ambient budget is chosen explicitly;
    this is not an assertion that it equals the selected global word budget. -/
lemma extend_seed_layout {n B₀ : ℕ} {j : Fin (axisCount n)}
    (seed:UniformSeedHeightPreparation.Config)
    (original:UniformSeedHeightPreparation.Layout n j seed B₀)
    (capacity:seed.gates+seed.e+seed.a≤radix n j) :
    ∃c:Config,∃B,c.seed=seed ∧ Layout n j c B := by
  let borrowed:=UniformCrossHeightPreparationMachine.rowBase seed.height (8*seed.exponent+7)+
    UniformCrossHeightPreparationMachine.colorBase seed.height (8*seed.exponent+7)+
    UniformCrossHeightPreparationMachine.recordBase seed.height (8*seed.exponent+7)
  let c:Config:=⟨seed,borrowed,borrowed+seed.gates,borrowed+7*seed.gates,
    borrowed+9*seed.gates,borrowed+15*seed.gates,borrowed+15*seed.gates+radix n j,
    borrowed+15*seed.gates+2*radix n j,borrowed+15*seed.gates+3*radix n j,0,0⟩
  let B:=B₀+borrowed+15*seed.gates+3*radix n j+1286
  have big:B₀≤B:=by dsimp [B];omega
  have hseed:UniformSeedHeightPreparation.Layout n j seed B:=seed_layout_mono original big
  refine ⟨c,B,rfl,?_⟩
  constructor
  · exact hseed
  · exact capacity
  · change UniformCrossHeightPreparationMachine.rowBase seed.height (8*seed.exponent+7)≤borrowed
    dsimp [borrowed];omega
  · change UniformCrossHeightPreparationMachine.colorBase seed.height (8*seed.exponent+7)≤borrowed
    dsimp [borrowed];omega
  · change UniformCrossHeightPreparationMachine.recordBase seed.height (8*seed.exponent+7)≤borrowed
    dsimp [borrowed];omega
  · change borrowed+seed.gates≤borrowed+seed.gates;omega
  · change borrowed+seed.gates+6*seed.gates≤borrowed+7*seed.gates;omega
  · change borrowed+7*seed.gates+2*seed.gates≤borrowed+9*seed.gates;omega
  · change borrowed+9*seed.gates+6*seed.gates≤borrowed+15*seed.gates;omega
  · change borrowed+15*seed.gates+radix n j≤borrowed+15*seed.gates+radix n j;omega
  · change borrowed+15*seed.gates+radix n j+radix n j≤borrowed+15*seed.gates+2*radix n j;omega
  · change borrowed+15*seed.gates+2*radix n j+radix n j≤borrowed+15*seed.gates+3*radix n j;omega
  · change borrowed+15*seed.gates+3*radix n j+4≤B;dsimp [B];omega
  · change 0<8*seed.exponent+7;omega
  · change 0<11;decide
  · dsimp [B];omega

end
end ExactFourierCircuits.UniformSeedChunkPreparation
