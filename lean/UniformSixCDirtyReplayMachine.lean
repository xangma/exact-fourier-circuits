import UniformSixCInverseMatchingPreparation

set_option autoImplicit false

/-! A continuous forward/inverse six-C matching invocation. This is the
per-layer restoration component of a dirty replay. The outer descending
depth/color controller and the two output-broadcast phases are separate
obligations; this module does not assert a complete cross-DAG replay driver. -/
namespace ExactFourierCircuits.UniformSixCDirtyReplayMachine
open UniformMachine UniformAssembly UniformReplayPrint
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformMatchingCoefficientValueBridge

def forwardSetup : List Op := [.literal 3000 0,
 .add 1640 3001 3000,.add 1641 3002 3000,.add 1642 3003 3000,
 .add 1643 3004 3000,.add 1644 3005 3000,.add 1645 3006 3000,
 .add 1646 3007 3000,.add 1647 3008 3000,.add 1648 3009 3000,
 .add 1649 3010 3000,.add 1650 3011 3000]
def inverseSetup : List Op := [
 .add 2400 3005 3000,.add 2401 3012 3000,.add 2402 3013 3000,
 .add 2403 3014 3000,.add 2404 3015 3000,.add 2405 3016 3000,
 .add 2406 3017 3000,.add 2407 3018 3000,.add 2408 3019 3000,
 .add 2409 3003 3000,.add 2410 3020 3000,.add 2411 3001 3000,
 .add 2412 3006 3000,.add 2413 3007 3000,.add 2414 3008 3000,
 .add 2415 3009 3000,.add 2416 3010 3000,.add 2417 3011 3000]
def beforeInverse : Program := forwardSetup.map Op.code ++
 UniformPackedMatchingShearMachine.program.map (relocate 12 434) ++ inverseSetup.map Op.code
def program : Program := beforeInverse ++ UniformSixCInverseMatchingPreparation.program.map (relocate 452 1135) ++ [.halt]

theorem forwardSetup_length : forwardSetup.length=12 := rfl
theorem inverseSetup_length : inverseSetup.length=18 := rfl
theorem beforeInverse_length : beforeInverse.length=452 := by
 simp [beforeInverse,UniformPackedMatchingShearMachine.program_length,forwardSetup_length,inverseSetup_length]
theorem program_length : program.length=1136 := by
 simp [program,beforeInverse_length,UniformSixCInverseMatchingPreparation.program_length]
theorem forward_code : CodeAt UniformPackedMatchingShearMachine.program program 12 434 := by
 let tail := inverseSetup.map Op.code ++ UniformSixCInverseMatchingPreparation.program.map (relocate 452 1135) ++ [.halt]
 have h : program=forwardSetup.map Op.code ++ UniformPackedMatchingShearMachine.program.map (relocate 12 434) ++ tail := by
  simp [program,beforeInverse,tail,List.append_assoc]
 rw [h]
 exact UniformChunkRowTableMachine.segment_code _ tail _ 12 434 (by simp [forwardSetup_length])
theorem inverse_code : CodeAt UniformSixCInverseMatchingPreparation.program program 452 1135 :=
 UniformChunkRowTableMachine.segment_code beforeInverse [.halt] _ 452 1135 beforeInverse_length
theorem forwardSetup_code : BlockAt forwardSetup program 0 := by
 intro j hj
 have h := UniformAllAxisSeedPreparation.lookup_segment [] (forwardSetup.map Op.code)
  (UniformPackedMatchingShearMachine.program.map (relocate 12 434) ++ inverseSetup.map Op.code ++
   UniformSixCInverseMatchingPreparation.program.map (relocate 452 1135) ++ [.halt]) j (by simpa using hj)
 simpa only [program,beforeInverse,List.append_assoc,List.length_nil,Nat.zero_add,List.nil_append,
  List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some] using h
theorem inverseSetup_code : BlockAt inverseSetup program 434 := by
 intro j hj
 have h := UniformAllAxisSeedPreparation.lookup_segment
  (forwardSetup.map Op.code ++ UniformPackedMatchingShearMachine.program.map (relocate 12 434)) (inverseSetup.map Op.code)
  (UniformSixCInverseMatchingPreparation.program.map (relocate 452 1135) ++ [.halt]) j (by simpa using hj)
 simpa only [program,beforeInverse,List.append_assoc,List.length_append,List.length_map,
  forwardSetup_length,UniformPackedMatchingShearMachine.program_length,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some] using h
theorem halt_at : program[1135]?=some .halt := by
 have len : (beforeInverse ++ UniformSixCInverseMatchingPreparation.program.map (relocate 452 1135)).length=1135 := by
  simp [beforeInverse_length,UniformSixCInverseMatchingPreparation.program_length]
 unfold program
 rw [List.getElem?_append,ite_eq_right (by rw [len];omega),len]
 rfl

noncomputable section

structure Config where
 inverse : UniformSixCInverseMatchingPreparation.Config
 forwardPacked : ℕ
 forwardInverse : ℕ
def Config.forward (c : Config) : UniformPackedMatchingShearMachine.Config :=
 ⟨c.inverse.packing.total,c.forwardPacked,c.inverse.packing.source,c.forwardInverse,
 c.inverse.forward,c.inverse.positive,c.inverse.negative,c.inverse.constants,
 c.inverse.conjugates,c.inverse.mu,c.inverse.conjugateMu⟩

/-- Only ordinary allocation bases enter the high caller registers. The
generated count remains in Nat894 and is read by both actual matching loops. -/
structure Header (c : Config) (s : State) : Prop where
 length : s.natReg 3001=c.inverse.packing.total
 packed : s.natReg 3002=c.forwardPacked
 source : s.natReg 3003=c.inverse.packing.source
 inverse : s.natReg 3004=c.forwardInverse
 rows : s.natReg 3005=c.inverse.forward
 positive : s.natReg 3006=c.inverse.positive
 negative : s.natReg 3007=c.inverse.negative
 constants : s.natReg 3008=c.inverse.constants
 conjugates : s.natReg 3009=c.inverse.conjugates
 mu : s.natReg 3010=c.inverse.mu
 conjugateMu : s.natReg 3011=c.inverse.conjugateMu
 inverseRows : s.natReg 3012=c.inverse.inverseRows
 permutation : s.natReg 3013=c.inverse.permutation
 widths : s.natReg 3014=c.inverse.widths
 markers : s.natReg 3015=c.inverse.markers
 axis : s.natReg 3016=c.inverse.axis
 suffix : s.natReg 3017=c.inverse.packing.suffix
 stack : s.natReg 3018=c.inverse.packing.stack
 inverseBank : s.natReg 3019=c.inverse.packing.inverse
 inversePacked : s.natReg 3020=c.inverse.packing.destination

theorem Header.transport {c : Config} {s u : State} (h : Header c s)
 (same : ∀ j,3001≤j → j≤3020 → u.natReg j=s.natReg j) : Header c u := by
 constructor <;> first
 | exact (same _ (by omega) (by omega)).trans h.length
 | exact (same _ (by omega) (by omega)).trans h.packed
 | exact (same _ (by omega) (by omega)).trans h.source
 | exact (same _ (by omega) (by omega)).trans h.inverse
 | exact (same _ (by omega) (by omega)).trans h.rows
 | exact (same _ (by omega) (by omega)).trans h.positive
 | exact (same _ (by omega) (by omega)).trans h.negative
 | exact (same _ (by omega) (by omega)).trans h.constants
 | exact (same _ (by omega) (by omega)).trans h.conjugates
 | exact (same _ (by omega) (by omega)).trans h.mu
 | exact (same _ (by omega) (by omega)).trans h.conjugateMu
 | exact (same _ (by omega) (by omega)).trans h.inverseRows
 | exact (same _ (by omega) (by omega)).trans h.permutation
 | exact (same _ (by omega) (by omega)).trans h.widths
 | exact (same _ (by omega) (by omega)).trans h.markers
 | exact (same _ (by omega) (by omega)).trans h.axis
 | exact (same _ (by omega) (by omega)).trans h.suffix
 | exact (same _ (by omega) (by omega)).trans h.stack
 | exact (same _ (by omega) (by omega)).trans h.inverseBank
 | exact (same _ (by omega) (by omega)).trans h.inversePacked

def labels {R : ℕ} (W : List (ShearCode ℕ R)) (i : ℕ) : UniformMatchingConjugateLoadMachine.Coefficient R :=
 if hi:i<W.length then UniformMatchingConjugateLoadMachine.fromReference W[i].coefficient else .constant 0
lemma labels_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ) (W : List (ShearCode ℕ R))
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient) (i : Fin W.length) :
 UniformMatchingConjugateLoadMachine.value K bank (labels W i.val)=W[i.val].coefficient.eval bank := by
 simp only [labels,dite_eq_left i.isLt]
 exact forward_value K bank _ (good _ (List.getElem_mem i.isLt))
lemma labels_reference {R : ℕ} (C T P : ℕ) (W : List (ShearCode ℕ R)) (i : ℕ) (hi:i<W.length) :
 ((UniformSixCInverseMatchingPreparation.forwardRows C T P W)[i]'(by simpa only [UniformSixCInverseMatchingPreparation.forwardRows_length] using hi)).coefficient=
 UniformMatchingConjugateLoadMachine.address C T P (labels W i) := by
 simp only [UniformSixCInverseMatchingPreparation.forwardRows,List.getElem_map,UniformInPlaceMachine.rowOf,
  labels,dite_eq_left hi]
 exact UniformMatchingConjugateLoadMachine.reference_address C T P _


lemma forwardSetup_args (c : Config) (s : State) (h : Header c s) :
 UniformPackedMatchingShearMachine.Header c.forward (applyBlock forwardSetup s) := by
 constructor <;> simp [forwardSetup,applyBlock,Op.apply,writeNat,next,Config.forward,
  h.length,h.packed,h.source,h.inverse,h.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu]
lemma inverseSetup_args (c : Config) (s : State) (h : Header c s) (z:s.natReg 3000=0) :
 UniformSixCInverseMatchingPreparation.Header c.inverse (applyBlock inverseSetup s) := by
 constructor <;> simp [inverseSetup,applyBlock,Op.apply,writeNat,next,z,
  h.length,h.source,h.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu,
  h.inverseRows,h.permutation,h.widths,h.markers,h.axis,h.suffix,h.stack,h.inverseBank,h.inversePacked]
lemma forwardSetup_high (s : State) (q : ℕ) (h:3001≤q) :
 (applyBlock forwardSetup s).natReg q=s.natReg q := by
 simp (disch:=omega) [forwardSetup,applyBlock,Op.apply,writeNat,next]
lemma inverseSetup_high (s : State) (q : ℕ) (h:3000≤q) :
 (applyBlock inverseSetup s).natReg q=s.natReg q := by
 simp (disch:=omega) [inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma setup_count (s : State) :
 (applyBlock forwardSetup s).natReg 894=s.natReg 894 ∧
 (applyBlock inverseSetup s).natReg 894=s.natReg 894 := by
 constructor <;> simp [forwardSetup,inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma setup_heap (s : State) :
 (applyBlock forwardSetup s).natHeap=s.natHeap ∧
 (applyBlock forwardSetup s).scalarHeap=s.scalarHeap ∧
 (applyBlock inverseSetup s).natHeap=s.natHeap ∧
 (applyBlock inverseSetup s).scalarHeap=s.scalarHeap := ⟨rfl,rfl,rfl,rfl⟩
lemma forwardSetup_safe (B : ℕ) (s : State) (hs:WordBound B s) :
 readable forwardSetup s ∧ peak forwardSetup s≤B := by
 constructor
 · simp [forwardSetup,readable,Op.readable]
 · simp [forwardSetup,peak,Op.peak,Op.apply,writeNat,next] 
   have b1:=hs.2.1 3001;have b2:=hs.2.1 3002;have b3:=hs.2.1 3003
   have b4:=hs.2.1 3004;have b5:=hs.2.1 3005;have b6:=hs.2.1 3006
   have b7:=hs.2.1 3007;have b8:=hs.2.1 3008;have b9:=hs.2.1 3009
   have b10:=hs.2.1 3010;have b11:=hs.2.1 3011
   omega
lemma inverseSetup_safe (B : ℕ) (s : State) (hs:WordBound B s) (z:s.natReg 3000=0) :
 readable inverseSetup s ∧ peak inverseSetup s≤B := by
 constructor
 · simp [inverseSetup,readable,Op.readable]
 · simp [inverseSetup,peak,Op.peak,Op.apply,writeNat,next,z]
   have b1:=hs.2.1 3001;have b3:=hs.2.1 3003;have b5:=hs.2.1 3005
   have b6:=hs.2.1 3006;have b7:=hs.2.1 3007;have b8:=hs.2.1 3008
   have b9:=hs.2.1 3009;have b10:=hs.2.1 3010;have b11:=hs.2.1 3011
   have b12:=hs.2.1 3012;have b13:=hs.2.1 3013;have b14:=hs.2.1 3014
   have b15:=hs.2.1 3015;have b16:=hs.2.1 3016;have b17:=hs.2.1 3017
   have b18:=hs.2.1 3018;have b19:=hs.2.1 3019;have b20:=hs.2.1 3020
   omega

structure Layout (c : Config) (M R B : ℕ) : Prop where
 forward : UniformPackedMatchingShearMachine.Layout c.forward M R B
 inverse : UniformSixCInverseMatchingPreparation.Layout c.inverse M R B
 code : 1136≤B

def packedValues {L : ℕ} (phi : Fin L≃Fin L) (v : Fin L→Scalar) (i : ℕ) : Scalar :=
 if hi:i<L then v (phi ⟨i,hi⟩) else Scalar.zero


def forwardValues {R : ℕ} (K : ℕ) (c : Config) (W : List (ShearCode ℕ R))
 (bank : Fin R→ℂ) (phi : Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (v : Fin c.inverse.packing.total→Scalar) (j : Fin c.inverse.packing.total) : Scalar :=
 UniformPackedMatchingShearMachine.matchingAction K bank (labels W) 0 W.length (packedValues phi v) (phi.symm j).val

def runtimeBudget {R : ℕ} (c : Config) (W : List (ShearCode ℕ R)) :=
 UniformPackedMatchingShearMachine.matchingCost (labels W) 0 W.length+9*c.inverse.packing.total+52+UniformSixCInverseMatchingPreparation.runtimeBudget c.inverse W


structure ForwardPost {R : ℕ} (K : ℕ) (c : Config) (W : List (ShearCode ℕ R))
 (bank : Fin R→ℂ) (phi : Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (v : Fin c.inverse.packing.total→Scalar) (s u : State) : Prop where
 pc : u.pc=434
 header : Header c u
 zero : u.natReg 3000=0
 count : u.natReg 894=W.length
 table : UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) u
 coefficients : UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank u
 constants : UniformHadamardPairMachine.Constants u
 values : UniformSectorPackingMachine.SourceReady c.inverse.packing (forwardValues K c W bank phi v) u
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 nats : ∀ q,3001≤q→u.natReg q=s.natReg q

/-- Actual charged forward phase; its output bank supplies the inverse input. -/
theorem forward_stage {R K B n : ℕ} (x : Fin n→ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (fl : UniformPackedMatchingShearMachine.Layout c.forward W.length R B) (code:1136≤B)
 (bank : Fin R→ℂ) (phi : Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (v : Fin c.inverse.packing.total→Scalar) (s : State)
 (args : Header c s) (count:s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) s)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s)
 (inverse : UniformGlobalNatPreparation.PermutationBank c.inverse.packing.total c.forwardInverse s.natHeap phi)
 (data : UniformPackedMatchingShearMachine.Packed c.forward (packedValues phi v) s)
 (pc:s.pc=0) (bound:WordBound B s) :
 ∃ u,BoundedRuns program n x B s
  (12+UniformPackedMatchingShearMachine.matchingCost (labels W) 0 W.length+9*c.inverse.packing.total+21) u ∧
 ForwardPost K c W bank phi v s u := by
 have fsafe:=forwardSetup_safe B s bound
 have start:=block_runs forwardSetup program 0 n B x s forwardSetup_code pc bound
   (by rw [forwardSetup_length];have:=code;omega) fsafe.1 fsafe.2
 let a:=applyBlock forwardSetup s
 have ap:a.pc=12:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,forwardSetup_length]
 let a0:=setPC a 0
 have ab:=changePC_bound B a 0 start.final_bound (by omega)
 have atable:UniformCrossShearTableMachine.Table c.forward.rows
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) a0:=table
 have adata:UniformPackedMatchingShearMachine.Packed c.forward (packedValues phi v) a0:=data
 have acount:a0.natReg 894=(UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W).length:=by
   rw [UniformSixCInverseMatchingPreparation.forwardRows_length];exact (setup_count s).1.trans count
 have ah:UniformPackedMatchingShearMachine.Header c.forward a0:=by
  have h:=forwardSetup_args c s args
  exact ⟨h.length,h.packed,h.destination,h.inverse,h.rows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu⟩
 have asrc:UniformMatchingConjugateLoadMachine.Sources K c.forward.positive c.forward.negative c.forward.constants c.forward.conjugates bank a0:=
  ⟨src.positive,src.negative,src.conjugate,src.constants⟩
 obtain ⟨b,br,bresult⟩:=UniformPackedMatchingShearMachine.execution x c.forward
  (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W)
  (by simpa only [UniformSixCInverseMatchingPreparation.forwardRows_length] using fl) bank (labels W)
  (fun i hi=>labels_reference _ _ _ W i (by simpa only [UniformSixCInverseMatchingPreparation.forwardRows_length] using hi))
  phi (packedValues phi v) a0 ah acount asrc atable inverse adata constants rfl ab
 have moved:=UniformBoundedAssembly.boundedExecution_placed forward_code
  (by rw [UniformPackedMatchingShearMachine.program_length];have:=code;omega) (by have:=code;omega) br
 have placed_eq:placed 12 a0=a:=by change {a with pc:=12}=a;rw [←ap]
 rw [placed_eq] at moved
 let b0:=setPC b 434
 have bh:Header c b0:=args.transport (fun j lo hi=>
  (bresult.frame.natReg j (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans (forwardSetup_high s j lo))
 have bz:b0.natReg 3000=0:=by
  rw [show b0.natReg 3000=b.natReg 3000 from rfl,bresult.frame.natReg 3000 (by unfold UniformPackedMatchingShearMachine.NatStable;omega)]
  change (applyBlock forwardSetup s).natReg 3000=0
  simp [forwardSetup,applyBlock,Op.apply,writeNat,next]

 have bc:b0.natReg 894=W.length:=(bresult.count_retained).trans ((setup_count s).1.trans count)
 have bt:UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) b0:=by
  intro i hi
  have heap:b0.natHeap=s.natHeap:=bresult.frame.natHeap
  rw [heap]
  exact table i hi
 have bs:UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank b0:=
  ⟨bresult.coefficients.positive,bresult.coefficients.negative,bresult.coefficients.conjugate,bresult.coefficients.constants⟩
 have bv:UniformSectorPackingMachine.SourceReady c.inverse.packing (forwardValues K c W bank phi v) b0:=by
  intro j
  have h:=bresult.destination j
  rw [UniformSixCInverseMatchingPreparation.forwardRows_length] at h
  exact h
 refine ⟨b0,?_,rfl,bh,bz,bc,bt,bs,bresult.constants,bv,?_,?_,?_⟩
 · convert start.trans moved using 1
   · simp only [forwardSetup_length,UniformSixCInverseMatchingPreparation.forwardRows_length,Config.forward]
     omega
   · rfl
 · exact bresult.frame.outputs
 · exact bresult.frame.rootOrders
 · intro q lo
   exact (bresult.frame.natReg q (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans (forwardSetup_high s q lo)


lemma inverse_start {B n : ℕ} (x : Fin n→ℂ) (c : Config) (s : State)
 (args:Header c s) (zero:s.natReg 3000=0) (pc:s.pc=434) (bound:WordBound B s) (code:1136≤B) :
 ∃d,BoundedRuns program n x B s 18 d ∧ d.pc=452 ∧
 UniformSixCInverseMatchingPreparation.Header c.inverse (setPC d 0) ∧
 d.natHeap=s.natHeap ∧ d.scalarHeap=s.scalarHeap ∧
 d.natReg 894=s.natReg 894 ∧ Header c d ∧
 (∀q,3000≤q→d.natReg q=s.natReg q) := by
 have safe:=inverseSetup_safe B s bound zero
 have run:=block_runs inverseSetup program 434 n B x s inverseSetup_code pc bound
  (by rw [inverseSetup_length];omega) safe.1 safe.2
 let d:=applyBlock inverseSetup s
 have dp:d.pc=452:=by rw [UniformTensorMonomialMachine.applyBlock_pc,inverseSetup_length,pc]
 have dh:UniformSixCInverseMatchingPreparation.Header c.inverse (setPC d 0):=
  (inverseSetup_args c s args zero).transport (fun _ _ _=>rfl)
 exact ⟨d,run,dp,dh,rfl,rfl,(setup_count s).2,args.transport (fun j lo _=>inverseSetup_high s j (by omega)),inverseSetup_high s⟩

/-- Actual inverse phase. Its rows, axis, packing inverse and six-C scales
are generated by683 rather than provided by its caller. -/
theorem inverse_stage {R K B n : ℕ} (x : Fin n→ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (il : UniformSixCInverseMatchingPreparation.Layout c.inverse W.length R B) (code:1136≤B)
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (bank : Fin R→ℂ) (v : Fin c.inverse.packing.total→Scalar) (s : State)
 (args : Header c s) (zero:s.natReg 3000=0) (count:s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) s)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s)
 (data : UniformSectorPackingMachine.SourceReady c.inverse.packing v s) (pc:s.pc=434) (bound:WordBound B s) :
 ∃ ticks u middle localOut,ticks≤18+UniformSixCInverseMatchingPreparation.runtimeBudget c.inverse W+1 ∧
 BoundedExecution program n x B s ticks u ∧
 UniformSixCInverseMatchingPreparation.Result (K:=K) c.inverse W
   (UniformSixCInverseMatchingPreparation.reverse_matching W hm)
   (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W hr) il.radix bank v middle localOut ∧
 u.scalarHeap=localOut.scalarHeap ∧ u.pc=1135 ∧ Header c u ∧ u.natReg 894=W.length := by
 obtain ⟨d,setup,dp,dh,dhNat,dhScalar,dc0,dheader,dhHigh⟩:=inverse_start x c s args zero pc bound code
 let d0:=setPC d 0
 have db:=changePC_bound B d 0 setup.final_bound (by omega)
 have dc:d0.natReg 894=W.length:=dc0.trans count
 have dt:UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) d0:=by
  intro i hi
  change d.natHeap _=some _ ∧ d.natHeap _=some _ ∧ d.natHeap _=some _
  rw [dhNat];exact table i hi
 have dd:UniformSectorPackingMachine.SourceReady c.inverse.packing v d0:=by
  intro j
  change d.scalarHeap _=some _
  rw [dhScalar];exact data j
 have dsrc:UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank d0:=by
  constructor
  · intro j;change d.scalarHeap _=_;rw [dhScalar];exact src.positive j
  · intro j;change d.scalarHeap _=_;rw [dhScalar];exact src.negative j
  · intro j;change d.scalarHeap _=_;rw [dhScalar];exact src.conjugate j
  · intro j hj;change d.scalarHeap _=_;rw [dhScalar];exact src.constants j hj
 have dconstants:UniformHadamardPairMachine.Constants d0:=by
  unfold UniformHadamardPairMachine.Constants
  rw [show d0.scalarHeap=s.scalarHeap from dhScalar];exact constants
 obtain ⟨ti,out,ci,ri,result⟩:=UniformSixCInverseMatchingPreparation.execution x c.inverse W il hm hr bank
  v d0 dh dc dt good dsrc dconstants dd rfl db
 have last:=UniformBoundedAssembly.boundedExecution_placed inverse_code
  (by rw [UniformSixCInverseMatchingPreparation.program_length];have:=code;omega) (by have:=code;omega) ri
 have placed_d:placed 452 d0=d:=by change {d with pc:=452}=d;rw [←dp]
 rw [placed_d] at last
 let u:=setPC out 1135
 have stop:BoundedExecution program n x B u 1 u:=.halt last.final_bound
   (by simp [step,u,setPC,halt_at])

 have hu:Header c u:=dheader.transport (fun j lo hi=>
  (result.nats j (by unfold UniformSixCInverseMatchingPreparation.KeepNat;omega) (by omega)))
 refine ⟨18+ti+1,u,d0,out,by omega,?_,result,rfl,rfl,hu,result.count⟩
 simpa only [Nat.add_assoc] using setup.executes (last.executes stop)


/-- Continuous1136: the second input contract is derived from the actual
forward output, and the original forward rows/count are retained physically. -/
theorem execution {R K B n : ℕ} (x : Fin n→ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (l : Layout c W.length R B)
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (bank : Fin R→ℂ) (phi : Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (v : Fin c.inverse.packing.total→Scalar) (s : State)
 (args : Header c s) (count:s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) s)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s)
 (inverse : UniformGlobalNatPreparation.PermutationBank c.inverse.packing.total c.forwardInverse s.natHeap phi)
 (data : UniformPackedMatchingShearMachine.Packed c.forward (packedValues phi v) s)
 (pc:s.pc=0) (bound:WordBound B s) :
 ∃ ticks u middle localOut,ticks≤runtimeBudget c W ∧ BoundedExecution program n x B s ticks u ∧
 UniformSixCInverseMatchingPreparation.Result (K:=K) c.inverse W (UniformSixCInverseMatchingPreparation.reverse_matching W hm) (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W hr)
   l.inverse.radix bank (forwardValues K c W bank phi v) middle localOut ∧
 u.scalarHeap=localOut.scalarHeap ∧ u.pc=1135 ∧ Header c u ∧ u.natReg 894=W.length := by
 obtain ⟨a,runA,post⟩:=forward_stage x c W l.forward l.code bank phi v s args count table src constants inverse data pc bound
 obtain ⟨ti,u,middle,localOut,ci,runI,result,heap,up,uh,uc⟩:=inverse_stage x c W l.inverse l.code hm hr bank
  (forwardValues K c W bank phi v) a post.header post.zero post.count post.table good post.coefficients post.constants
  post.values post.pc runA.final_bound
 refine ⟨12+UniformPackedMatchingShearMachine.matchingCost (labels W) 0 W.length+9*c.inverse.packing.total+21+ti,u,middle,localOut,?_,
  runA.executes runI,result,heap,up,uh,uc⟩
 unfold runtimeBudget;omega

lemma runtime_linear {R B : ℕ} {c : Config} {W : List (ShearCode ℕ R)} (l : Layout c W.length R B) :
 runtimeBudget c W≤660*c.inverse.packing.total+153 := by
 have f:=UniformPackedMatchingShearMachine.matchingCost_bound (labels W) 0 W.length
 have inv:=UniformSixCInverseMatchingPreparation.runtime_linear l.inverse
 have cap:=l.forward.capacity
 change 2*W.length≤c.inverse.packing.total at cap
 unfold runtimeBudget
 omega

/-- This is a coordinate contract, not an action certificate. The actual
sector-packing result supplies it for its computed forward permutation. -/
def PairCoordinates {R L : ℕ} (W : List (ShearCode ℕ R)) (phi : Fin L≃Fin L)
 (capacity:2*W.length≤L) : Prop := ∀ (i:Fin W.length) (t:Fin 2),
 (phi ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩).val=
 if t.val=0 then (UniformSixCInverseMatchingPreparation.forwardEdges W i).left else (UniformSixCInverseMatchingPreparation.forwardEdges W i).right

lemma forwardValues_pair {R K : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (bank:Fin R→ℂ) (phi:Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (capacity:2*W.length≤c.inverse.packing.total) (pairs:PairCoordinates W phi capacity)
 (good:∀row∈W,ForwardLeaf K row.coefficient) (v:Fin c.inverse.packing.total→Scalar) (i:Fin W.length) :
 let left:Fin c.inverse.packing.total:=⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).left,(hr i).1⟩
 let right:Fin c.inverse.packing.total:=⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).right,(hr i).2⟩
 forwardValues K c W bank phi v left=
  ⟨(v left).value+W[i.val].coefficient.eval bank*(v right).value,(v left).dependent||(v right).dependent⟩ ∧
 forwardValues K c W bank phi v right=
  ⟨(v right).value,(v left).dependent||(v right).dependent⟩ := by
 dsimp only
 let left:Fin c.inverse.packing.total:=⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).left,(hr i).1⟩
 let right:Fin c.inverse.packing.total:=⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).right,(hr i).2⟩
 let l:Fin c.inverse.packing.total:=⟨2*i.val,by have:=i.isLt;omega⟩
 let r:Fin c.inverse.packing.total:=⟨2*i.val+1,by have:=i.isLt;omega⟩
 have lp:phi l=left:=Fin.ext (pairs i 0)
 have rp:phi r=right:=Fin.ext (pairs i 1)
 have li:phi.symm left=l:=by rw [←lp];exact phi.symm_apply_apply l
 have ri:phi.symm right=r:=by rw [←rp];exact phi.symm_apply_apply r
 have numeric:=UniformPackedMatchingShearMachine.matchingAction_pair K bank (labels W) 0 W.length i.val (packedValues phi v) (by omega) (by have:=i.isLt;omega)
 have lv:packedValues phi v (2*i.val)=v left:=by rw [packedValues,dite_eq_left l.isLt];exact congrArg v lp
 have rv:packedValues phi v (2*i.val+1)=v right:=by rw [packedValues,dite_eq_left r.isLt];exact congrArg v rp
 rw [lv,rv,labels_value K bank W good i] at numeric
 change UniformPackedMatchingShearMachine.matchingAction K bank (labels W) 0 W.length (packedValues phi v) (phi.symm left).val=_ ∧
   UniformPackedMatchingShearMachine.matchingAction K bank (labels W) 0 W.length (packedValues phi v) (phi.symm right).val=_
 rw [li,ri]
 exact numeric


lemma coordinates_tail {M L : ℕ} (E : Fin M→UniformColoring.Edge) (capacity:2*M≤L)
 (phi:Fin L≃Fin L)
 (pairs:∀(i:Fin M)(t:Fin 2),(phi ⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩).val=
   if t.val=0 then (E i).left else (E i).right)
 (q:Fin L) (unused:∀i:Fin M,q.val≠(E i).left ∧ q.val≠(E i).right) :
 2*M≤(phi.symm q).val := by
 by_contra notTail
 have inside:(phi.symm q).val<2*M:=by omega
 have rem:(phi.symm q).val%2<2:=Nat.mod_lt _ (by omega)
 have split:=Nat.mod_add_div (phi.symm q).val 2
 let i:Fin M:=⟨(phi.symm q).val/2,by omega⟩
 let t:Fin 2:=⟨(phi.symm q).val%2,rem⟩
 have eq:(⟨2*i.val+t.val,by have:=i.isLt;have:=t.isLt;omega⟩:Fin L)=phi.symm q:=Fin.ext (by dsimp [i,t];omega)
 have coordinate:=pairs i t
 rw [eq,phi.apply_symm_apply] at coordinate
 split at coordinate
 · exact (unused i).1 coordinate
 · exact (unused i).2 coordinate

lemma forwardValues_unused {R K : ℕ} (c:Config) (W:List (ShearCode ℕ R))
 (bank:Fin R→ℂ) (phi:Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (capacity:2*W.length≤c.inverse.packing.total) (pairs:PairCoordinates W phi capacity)
 (v:Fin c.inverse.packing.total→Scalar) (q:Fin c.inverse.packing.total)
 (unused:∀i:Fin W.length,q.val≠(UniformSixCInverseMatchingPreparation.forwardEdges W i).left ∧ q.val≠(UniformSixCInverseMatchingPreparation.forwardEdges W i).right) :
 forwardValues K c W bank phi v q=v q := by
 have tail:=coordinates_tail (UniformSixCInverseMatchingPreparation.forwardEdges W) capacity phi pairs q unused
 unfold forwardValues
 rw [UniformPackedMatchingShearMachine.matchingAction_outside K bank (labels W) 0 W.length _ _ (Or.inr (by omega)),
  packedValues,dite_eq_left (phi.symm q).isLt,phi.apply_symm_apply]

lemma reverseReference_rev {R : ℕ} (W:List (ShearCode ℕ R)) (i:Fin W.length) :
 UniformSixCInverseMatchingPreparation.reverseReference W i.rev=W[i.val].coefficient := by
 have eq:W.length-i.rev.val-1=i.val:=by simp only [Fin.val_rev];have:=i.isLt;omega
 simp only [UniformSixCInverseMatchingPreparation.reverseReference,eq]

/-- The inverse's actual six-C result cancels the actual forward result at
all paired coordinates and all untouched coordinates. Tags need not restore. -/
theorem numeric_restored {R K : ℕ} (c:Config) (W:List (ShearCode ℕ R))
 (hm:UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hp:2≤c.inverse.packing.total) (bank:Fin R→ℂ)
 (phi:Fin c.inverse.packing.total≃Fin c.inverse.packing.total)
 (capacity:2*W.length≤c.inverse.packing.total) (pairs:PairCoordinates W phi capacity)
 (good:∀row∈W,ForwardLeaf K row.coefficient) (v:Fin c.inverse.packing.total→Scalar)
 (s u:State)
 (result:UniformSixCInverseMatchingPreparation.Result (K:=K) c.inverse W (UniformSixCInverseMatchingPreparation.reverse_matching W hm) (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W hr)
  hp bank (forwardValues K c W bank phi v) s u) (q:Fin c.inverse.packing.total) :
 (u.scalarHeap (c.inverse.packing.source+q.val)).map Scalar.value=some (v q).value := by
 by_cases isLeft:∃i:Fin W.length,(UniformSixCInverseMatchingPreparation.forwardEdges W i).left=q.val
 · obtain ⟨i,iq⟩:=isLeft
   have forward:=forwardValues_pair c W hr bank phi capacity pairs good v i
   have backward:=result.pair_values good i.rev
   simp only [UniformSixCInverseMatchingPreparation.reverseEdges_eq,Fin.rev_rev,reverseReference_rev] at backward
   have li:(⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).left,(hr i).1⟩:Fin c.inverse.packing.total)=q:=Fin.ext iq
   have b:=congrArg (Option.map Scalar.value) backward.1
   rw [forward.1,forward.2] at b
   simp only [Option.map_some] at b
   simp only [add_sub_cancel_right] at b
   change Option.map Scalar.value (u.scalarHeap (c.inverse.packing.source+
    (⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).left,(hr i).1⟩:Fin c.inverse.packing.total).val))=
    some (v ⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).left,(hr i).1⟩).value at b
   simp only [li] at b
   rw [iq] at b
   exact b
 · by_cases isRight:∃i:Fin W.length,(UniformSixCInverseMatchingPreparation.forwardEdges W i).right=q.val
   · obtain ⟨i,iq⟩:=isRight
     have forward:=forwardValues_pair c W hr bank phi capacity pairs good v i
     have backward:=result.pair_values good i.rev
     simp only [UniformSixCInverseMatchingPreparation.reverseEdges_eq,Fin.rev_rev,reverseReference_rev] at backward
     have ri:(⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).right,(hr i).2⟩:Fin c.inverse.packing.total)=q:=Fin.ext iq
     have b:=congrArg (Option.map Scalar.value) backward.2
     rw [forward.2] at b
     simp only [Option.map_some] at b
     change Option.map Scalar.value (u.scalarHeap (c.inverse.packing.source+
      (⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).right,(hr i).2⟩:Fin c.inverse.packing.total).val))=
      some (v ⟨(UniformSixCInverseMatchingPreparation.forwardEdges W i).right,(hr i).2⟩).value at b
     simp only [ri] at b
     rw [iq] at b
     exact b
   · have unused:∀i:Fin W.length,q.val≠(UniformSixCInverseMatchingPreparation.forwardEdges W i).left ∧ q.val≠(UniformSixCInverseMatchingPreparation.forwardEdges W i).right:=by
       intro i;constructor
       · intro eq;exact isLeft ⟨i,eq.symm⟩
       · intro eq;exact isRight ⟨i,eq.symm⟩
     let psi:=UniformSixCInverseMatchingPreparation.unpacking c.inverse W (UniformSixCInverseMatchingPreparation.reverse_matching W hm) (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W hr) hp
     have reverseUnused:∀i:Fin W.length,q.val≠(UniformSixCInverseMatchingPreparation.reverseEdges W i).left ∧ q.val≠(UniformSixCInverseMatchingPreparation.reverseEdges W i).right:=by
       intro i;rw [UniformSixCInverseMatchingPreparation.reverseEdges_eq];exact unused i.rev
     have tail:=coordinates_tail (UniformSixCInverseMatchingPreparation.reverseEdges W) capacity psi
       (UniformSixCInverseMatchingPreparation.unpacking_pair c.inverse W _ _ hp) q reverseUnused
     have stored:=result.tail (psi.symm q) tail
     rw [psi.apply_symm_apply] at stored
     rw [stored,forwardValues_unused c W bank phi capacity pairs v q unused]
     rfl

def forwardAxes {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (positive : 2 ≤ c.inverse.packing.total) :=
 [UniformMatchingAxisTableMachine.physicalAxis c.inverse.packing.total c.inverse.widths c.inverse.permutation
   (UniformSixCInverseMatchingPreparation.forwardEdges W) matching range positive]

lemma forwardAxes_volume {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (positive : 2 ≤ c.inverse.packing.total) :
 UniformSectorPackingMachine.physicalVolume (forwardAxes c W matching range positive)=c.inverse.packing.total := by
 simp [forwardAxes,UniformSectorPackingMachine.physicalVolume,UniformSectorPackingMachine.physicalAxes,
   UniformSectorPacking.radices,UniformMatchingAxisTableMachine.physicalAxis,
   UniformMatchingAxisTableMachine.geometry,
   UniformMatchingAxisTableMachine.widths_sum c.inverse.packing.total W.length
     (UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) matching range)]


def forwardUnpacking {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hp : 2≤c.inverse.packing.total) : Fin c.inverse.packing.total≃Fin c.inverse.packing.total :=
 UniformSectorPackingMachine.physicalUnpacking (forwardAxes c W hm hr hp) c.inverse.packing
  (forwardAxes_volume c W hm hr hp)

theorem forwardUnpacking_pair {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hp : 2 ≤ c.inverse.packing.total) (i : Fin W.length) (t : Fin 2) :
 (forwardUnpacking c W hm hr hp ⟨2*i.val+t.val,by
   have cap:=UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr
   have:=i.isLt;have:=t.isLt;omega⟩).val=
 if t.val=0 then (UniformSixCInverseMatchingPreparation.forwardEdges W i).left else (UniformSixCInverseMatchingPreparation.forwardEdges W i).right := by
 let a:=UniformMatchingAxisTableMachine.geometry c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr hp
 let pos:=UniformMatchingPackingPreparation.matchingPosition c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr hp i t
 let z:UniformSectorPacking.SectorPosition [a]:=⟨(pos.1,()),(pos.2,())⟩
 have packed:(UniformSectorPacking.packedEquiv [a] z).val=2*i.val+t.val := by
   rw [UniformMatchingPackingPreparation.single_packed_value]
   change UniformTraversal.blockBefore (UniformMatchingAxisTableMachine.widths c.inverse.packing.total W.length)
     (UniformMatchingPackingPreparation.pairBlock c.inverse.packing.total
       (UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr) i)+t.val=_
   rw [UniformMatchingPackingPreparation.pair_before]
 have original:(UniformSectorPacking.originalEquiv [a] z).val=
   if t.val=0 then (UniformSixCInverseMatchingPreparation.forwardEdges W i).left else (UniformSixCInverseMatchingPreparation.forwardEdges W i).right := by
   rw [UniformMatchingPackingPreparation.single_original_value]
   exact UniformMatchingPackingPreparation.matching_position_original _ _ _ _ _ i t
 have h:=UniformMatchingPackingPreparation.physicalUnpacking_coordinate (forwardAxes c W hm hr hp) c.inverse.packing
   (forwardAxes_volume c W hm hr hp) z
 have same:finCongr (forwardAxes_volume c W hm hr hp)
   (UniformSectorPacking.packedEquiv [a] z)=⟨2*i.val+t.val,by
     have cap:=UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr
     have:=i.isLt;have:=t.isLt;omega⟩ := Fin.ext packed
 change (forwardUnpacking c W hm hr hp) (finCongr (forwardAxes_volume c W hm hr hp)
   (UniformSectorPacking.packedEquiv [a] z))=finCongr (forwardAxes_volume c W hm hr hp)
   (UniformSectorPacking.originalEquiv [a] z) at h
 rw [same] at h
 exact (congrArg Fin.val h).trans original

lemma forwardUnpacking_coordinates {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm:UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hp:2≤c.inverse.packing.total) :
 PairCoordinates W (forwardUnpacking c W hm hr hp)
  (UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr) :=
 forwardUnpacking_pair c W hm hr hp

/-- Numeric restoration for the actual sector geometry. In particular this
requires neither a supplied transformed-bank action nor a supplied inverse
permutation/action. All inverse addresses are printed inside literal683. -/
theorem execution_numeric {R K B n : ℕ} (x : Fin n→ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (l : Layout c W.length R B)
 (hm : UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W))
 (bank : Fin R→ℂ) (v : Fin c.inverse.packing.total→Scalar) (s : State)
 (args : Header c s) (count:s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.inverse.forward
   (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W) s)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.inverse.positive c.inverse.negative c.inverse.constants c.inverse.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s)
 (inverse : UniformGlobalNatPreparation.PermutationBank c.inverse.packing.total c.forwardInverse s.natHeap
   (forwardUnpacking c W hm hr l.inverse.radix))
 (data : UniformPackedMatchingShearMachine.Packed c.forward (packedValues (forwardUnpacking c W hm hr l.inverse.radix) v) s)
 (pc:s.pc=0) (bound:WordBound B s) :
 ∃ ticks u,ticks≤runtimeBudget c W ∧ BoundedExecution program n x B s ticks u ∧
 (∀q:Fin c.inverse.packing.total,(u.scalarHeap (c.inverse.packing.source+q.val)).map Scalar.value=some (v q).value) ∧
 u.pc=1135 ∧ Header c u ∧ u.natReg 894=W.length := by
 let phi:=forwardUnpacking c W hm hr l.inverse.radix
 obtain ⟨ticks,u,middle,localOut,cost,run,result,heap,up,uh,uc⟩:=execution x c W l hm hr bank phi v s
   args count table good src constants inverse data pc bound
 refine ⟨ticks,u,cost,run,?_,up,uh,uc⟩
 intro q
 rw [heap]
 exact numeric_restored c W hm hr l.inverse.radix bank phi
  (UniformMatchingAxisTableMachine.matching_capacity c.inverse.packing.total (UniformSixCInverseMatchingPreparation.forwardEdges W) hm hr)
  (forwardUnpacking_coordinates c W hm hr l.inverse.radix) good v middle localOut result q


/-- Actual colored logical rows, with the deterministic printed borrowed-port
mapping. No coefficients or occurrences are discarded by this adapter. -/
def physicalWord {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W) : List (ShearCode ℕ R) :=
 List.ofFn (fun i:Fin (UniformChunkMatchingPreparation.indices p W).length =>
  let edge:=UniformChunkMatchingPreparation.physicalEdges l W dom i
  let index:=UniformColorLayerTableMachine.selectionIndex W.length p.color
    (UniformChunkMatchingPreparation.colors W) i
  ⟨edge.left,edge.right,edge.different,W[index.val].coefficient⟩)

lemma physicalWord_length {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W) :
 (physicalWord l W dom).length=(UniformChunkMatchingPreparation.indices p W).length := by
 simp only [physicalWord,List.length_ofFn]

lemma physicalWord_edges {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) :
 UniformSixCInverseMatchingPreparation.forwardEdges (physicalWord l W dom) ⟨i.val,by rw [physicalWord_length];exact i.isLt⟩=
 UniformChunkMatchingPreparation.physicalEdges l W dom i := by
 simp only [UniformSixCInverseMatchingPreparation.forwardEdges,physicalWord,List.getElem_ofFn]

lemma physicalWord_matching {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 UniformMatchingAxisTableMachine.Matching (UniformSixCInverseMatchingPreparation.forwardEdges (physicalWord l W dom)) := by
 intro i j neq
 let a:Fin (UniformChunkMatchingPreparation.indices p W).length:=⟨i.val,by rw [←physicalWord_length l W dom];exact i.isLt⟩
 let b:Fin (UniformChunkMatchingPreparation.indices p W).length:=⟨j.val,by rw [←physicalWord_length l W dom];exact j.isLt⟩
 have ai:(⟨a.val,by rw [physicalWord_length];exact a.isLt⟩:Fin (physicalWord l W dom).length)=i:=rfl
 have bj:(⟨b.val,by rw [physicalWord_length];exact b.isLt⟩:Fin (physicalWord l W dom).length)=j:=rfl
 rw [←ai,←bj,physicalWord_edges,physicalWord_edges]
 exact UniformChunkMatchingPreparation.physical_matching l dom degree a b (fun eq=>neq (Fin.ext (by exact congrArg (fun x:Fin (UniformChunkMatchingPreparation.indices p W).length=>x.val) eq)))

lemma physicalWord_range {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W) :
 UniformMatchingAxisTableMachine.InRange p.radix (UniformSixCInverseMatchingPreparation.forwardEdges (physicalWord l W dom)) := by
 intro i
 let a:Fin (UniformChunkMatchingPreparation.indices p W).length:=⟨i.val,by rw [←physicalWord_length l W dom];exact i.isLt⟩
 have ai:(⟨a.val,by rw [physicalWord_length];exact a.isLt⟩:Fin (physicalWord l W dom).length)=i:=rfl
 rw [←ai,physicalWord_edges]
 exact UniformChunkMatchingPreparation.physical_range l dom a

lemma physicalWord_leaf {R B K : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W) (good:∀row∈W,ForwardLeaf K row.coefficient) :
 ∀row∈physicalWord l W dom,ForwardLeaf K row.coefficient := by
 intro row member
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
 change ForwardLeaf K (W[(UniformColorLayerTableMachine.selectionIndex W.length p.color
   (UniformChunkMatchingPreparation.colors W) i).val].coefficient)
 exact good _ (List.getElem_mem _)

lemma physicalWord_rows {R B : ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W) (C T P:ℕ) :
 UniformSixCInverseMatchingPreparation.forwardRows C T P (physicalWord l W dom)=
 UniformChunkMatchingPreparation.mappedRows p l.capacity W (UniformCrossShearTableMachine.locations R C T P) := by
 apply List.ext_getElem
 · simp [UniformSixCInverseMatchingPreparation.forwardRows_length,physicalWord_length,UniformPackedMatchingShearMachine.mappedRows_length]
 · intro i hi hj
   have idx:i<(UniformChunkMatchingPreparation.indices p W).length:=by
     simpa only [UniformSixCInverseMatchingPreparation.forwardRows_length,physicalWord_length] using hi
   let j:Fin (UniformChunkMatchingPreparation.indices p W).length:=⟨i,idx⟩
   have align:=UniformChunkMatchingPreparation.selected_align p W
    (UniformCrossShearTableMachine.locations R C T P) j
   have ref:=UniformPackedMatchingShearMachine.mappedRows_reference p l.capacity W C T P i hj
   simp only [UniformSixCInverseMatchingPreparation.forwardRows,List.getElem_map,UniformInPlaceMachine.rowOf,physicalWord,List.getElem_ofFn,
    UniformChunkMatchingPreparation.physicalEdges]
   change UniformInPlaceMachine.Row.mk _ _ _=UniformInPlaceMachine.Row.mk
    ((UniformChunkMatchingPreparation.mappedRows p l.capacity W (UniformCrossShearTableMachine.locations R C T P))[i]).dst
    ((UniformChunkMatchingPreparation.mappedRows p l.capacity W (UniformCrossShearTableMachine.locations R C T P))[i]).src
    ((UniformChunkMatchingPreparation.mappedRows p l.capacity W (UniformCrossShearTableMachine.locations R C T P))[i]).coefficient
   congr 1
   · simpa only [UniformChunkMatchingPreparation.mappedRows,List.getElem_map,UniformChunkRowTableMachine.mappedRow,
      UniformChunkMatchingPreparation.rowParameters,UniformChunkRowTableMachine.borrowed,
      UniformChunkMatchingPreparation.coordinate,j] using
      congrArg (UniformChunkMatchingPreparation.coordinate p l.capacity) align.1.symm
   · simpa only [UniformChunkMatchingPreparation.mappedRows,List.getElem_map,UniformChunkRowTableMachine.mappedRow,
      UniformChunkMatchingPreparation.rowParameters,UniformChunkRowTableMachine.borrowed,
      UniformChunkMatchingPreparation.coordinate,j] using
      congrArg (UniformChunkMatchingPreparation.coordinate p l.capacity) align.2.symm
   · rw [UniformMatchingConjugateLoadMachine.reference_address]
     rw [UniformPackedMatchingShearMachine.selectedLabels,dite_eq_left idx] at ref
     exact ref.symm


def cCalls {R:ℕ} (W:List (ShearCode ℕ R)) :=
 UniformPackedMatchingShearMachine.cCalls W.length+UniformSixCInverseMatchingPreparation.cCalls W
lemma cCalls_eq {R:ℕ} (W:List (ShearCode ℕ R)) : cCalls W=12*W.length := by
 rw [cCalls,UniformPackedMatchingShearMachine.cCalls_eq,UniformSixCInverseMatchingPreparation.cCalls_eq]
 omega

/-- The actual Mapping/packing output discharges the physical row/count
contracts for the deterministic selected logical code adapter. -/
theorem produced_rows {R B:ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformMatchingPackingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (C T P:ℕ) (v:Fin l.packing.total→Scalar) (origin s:State)
 (result:UniformMatchingPackingPreparation.Result l W (UniformCrossShearTableMachine.locations R C T P) dom degree v origin s) :
 UniformInverseShearTableMachine.Rows p.mapped
  (UniformSixCInverseMatchingPreparation.forwardRows C T P (physicalWord l.matching W dom)) s ∧
 s.natReg 894=(physicalWord l.matching W dom).length := by
 constructor
 · rw [physicalWord_rows];exact result.mapped
 · rw [physicalWord_length];exact result.count

/-- Every actual colored corrected-cross layer is in the genuine forward-leaf
value domain, after exactly the printed borrowed-coordinate mapping. -/
theorem cross_physicalWord_leaf {B:ℕ} {p:UniformChunkMatchingPreparation.Parameters}
 (l:UniformChunkMatchingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height) :
 ∀row∈physicalWord l (UniformChunkMatchingPreparation.crossWord p ha he)
  (UniformChunkMatchingPreparation.cross_domain p ha he),ForwardLeaf p.height.K row.coefficient :=
 physicalWord_leaf l _ _ (crossWord_leaf p ha he)

end
end ExactFourierCircuits.UniformSixCDirtyReplayMachine
