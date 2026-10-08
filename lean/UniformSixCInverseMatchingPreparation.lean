import UniformMatchingCoefficientValueBridge
import UniformInverseShearTableMachine

set_option autoImplicit false

/-! Charged inverse-row production and six-C matching execution. Forward syntax
is restricted by the actual coefficient-value bridge; inverse normalization is
never routed through the frozen forward-only decoder. -/
namespace ExactFourierCircuits.UniformSixCInverseMatchingPreparation
open UniformMachine UniformAssembly UniformReplayPrint UniformColoring
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformMatchingCoefficientValueBridge
noncomputable section

/-- The existing forward row printer's exact address policy. -/
def forwardRows {R : ℕ} (C T P : ℕ) (W : List (ShearCode ℕ R)) :=
 W.map (UniformInPlaceMachine.rowOf (UniformCrossShearTableMachine.locations R C T P))

lemma forwardRows_length {R : ℕ} (C T P : ℕ) (W : List (ShearCode ℕ R)) :
 (forwardRows C T P W).length = W.length := by simp [forwardRows]

/-- Agreement with the actual inverse36 branch/address operations. -/
theorem inverse_pointer {R : ℕ} (K C T P : ℕ) (c : UniformReplayPrint.Coefficient R)
 (good : ForwardLeaf K c) (below : C+R ≤ P) :
 UniformInverseShearTableMachine.inverseAddress C T P
   ((UniformCrossShearTableMachine.locations R C T P).address c) =
 UniformMatchingConjugateLoadMachine.address C T P (inverseReference c) := by
 rcases good with rfl | rfl | rfl | ⟨i,rfl⟩
 · norm_num [UniformCrossShearTableMachine.locations,UniformInPlaceMachine.Locations.address,
     UniformInverseShearTableMachine.inverseAddress,inverseReference,
     UniformMatchingConjugateLoadMachine.address]
 · norm_num [UniformCrossShearTableMachine.locations,UniformInPlaceMachine.Locations.address,
     UniformInverseShearTableMachine.inverseAddress,inverseReference,
     UniformMatchingConjugateLoadMachine.address]
 · rw [UniformCrossShearTableMachine.reciprocal_location _ C T P _ (UniformRadixTwoDAG.width_pos K),
     inverse_reciprocal_address]
   by_cases one : UniformRadixTwoDAG.width K = 1
   · rw [ite_eq_left (by omega),ite_eq_left one,UniformInverseShearTableMachine.inverseAddress_unit]
   · rw [ite_eq_right (by have := UniformRadixTwoDAG.width_pos K;omega),ite_eq_right one,
       UniformInverseShearTableMachine.inverseAddress_normalization]
 · change UniformInverseShearTableMachine.inverseAddress C T P (C+i.val) = T+i.val
   exact UniformInverseShearTableMachine.inverseAddress_prepared C T P R i.val i.isLt below

lemma forward_domain {R : ℕ} (K C T P : ℕ) (c : UniformReplayPrint.Coefficient R)
 (good : ForwardLeaf K c) :
 UniformInverseShearTableMachine.Domain C P R
   ((UniformCrossShearTableMachine.locations R C T P).address c) := by
 rcases good with rfl | rfl | rfl | ⟨i,rfl⟩
 · norm_num [UniformCrossShearTableMachine.locations,UniformInPlaceMachine.Locations.address,
     UniformInverseShearTableMachine.Domain]
 · norm_num [UniformCrossShearTableMachine.locations,UniformInPlaceMachine.Locations.address,
     UniformInverseShearTableMachine.Domain]
 · rw [UniformCrossShearTableMachine.reciprocal_location _ C T P _ (UniformRadixTwoDAG.width_pos K)]
   split <;> simp [UniformInverseShearTableMachine.Domain]
 · exact Or.inl ⟨i.val,i.isLt,rfl⟩

lemma forwardRows_domain {R : ℕ} (K C T P : ℕ) (W : List (ShearCode ℕ R))
 (good : ∀ row ∈ W, ForwardLeaf K row.coefficient) :
 ∀ row ∈ forwardRows C T P W, UniformInverseShearTableMachine.Domain C P R row.coefficient := by
 intro row member
 obtain ⟨code,hcode,rfl⟩ := List.mem_map.mp member
 exact forward_domain K C T P code.coefficient (good code hcode)

def reverseReference {R : ℕ} (W : List (ShearCode ℕ R)) (i : Fin W.length) :=
 (W[W.length-i.val-1]'(by have := i.isLt;omega)).coefficient

def inverseLabels {R : ℕ} (W : List (ShearCode ℕ R)) (i : ℕ) :
 UniformMatchingConjugateLoadMachine.Coefficient R :=
 if hi : i < W.length then inverseReference (reverseReference W ⟨i,hi⟩) else .constant 0

lemma reverseReference_leaf {R : ℕ} (K : ℕ) (W : List (ShearCode ℕ R))
 (good : ∀ row ∈ W, ForwardLeaf K row.coefficient) (i : Fin W.length) :
 ForwardLeaf K (reverseReference W i) := good _ (List.getElem_mem _)

lemma inverseLabels_value {R : ℕ} (K : ℕ) (bank : Fin R → ℂ)
 (W : List (ShearCode ℕ R)) (good : ∀ row ∈ W, ForwardLeaf K row.coefficient) (i : Fin W.length) :
 UniformMatchingConjugateLoadMachine.value K bank (inverseLabels W i.val) =
   -(reverseReference W i).eval bank := by
 simp only [inverseLabels,dite_eq_left i.isLt]
 rw [inverse_value K bank _ (reverseReference_leaf K W good i),UniformReplayPrint.Coefficient.eval_negate]

/-- Every permitted forward prepared reference reverses into the negative
bank; rational leaves reverse into real constants. The generic row loader's
positive branch therefore has no valid inverse-domain instance here. -/
lemma inverse_address_lower {R : ℕ} (K C T P : ℕ) (c : UniformReplayPrint.Coefficient R)
 (good : ForwardLeaf K c) (below : T≤P) :
 T≤UniformMatchingConjugateLoadMachine.address C T P (inverseReference c) := by
 rcases good with rfl | rfl | rfl | ⟨i,rfl⟩
 · norm_num [inverseReference,UniformMatchingConjugateLoadMachine.address];omega
 · norm_num [inverseReference,UniformMatchingConjugateLoadMachine.address];omega
 · simp only [inverseReference]
   split
   · simp only [UniformMatchingConjugateLoadMachine.address];omega
   · split <;> simp only [UniformMatchingConjugateLoadMachine.address] <;> omega
 · simp [inverseReference,UniformMatchingConjugateLoadMachine.address]

/-- Per-row pointers are derived from the physical inverse producer's output. -/
theorem inverseRows_reference {R : ℕ} (K C T P : ℕ) (W : List (ShearCode ℕ R))
 (good : ∀ row ∈ W, ForwardLeaf K row.coefficient) (below : C+R ≤ P) (i : Fin W.length) :
 ((UniformInverseShearTableMachine.inverseRows C T P (forwardRows C T P W))[i.val]'(by
   rw [UniformInverseShearTableMachine.inverseRows_length,forwardRows_length];exact i.isLt)).coefficient =
 UniformMatchingConjugateLoadMachine.address C T P (inverseLabels W i.val) := by
 rw [UniformInverseShearTableMachine.inverseRows_get C T P _ i.val (by rw [forwardRows_length];exact i.isLt)]
 simp only [UniformInverseShearTableMachine.inverseRow,forwardRows,List.length_map,List.getElem_map,
   UniformInPlaceMachine.rowOf,inverseLabels,dite_eq_left i.isLt]
 exact inverse_pointer K C T P _ (reverseReference_leaf K W good i) below

/-- Logical endpoints of the actual reversed forward list. -/
def reverseEdges {R : ℕ} (W : List (ShearCode ℕ R)) (i : Fin W.length) : Edge :=
 let row := W[W.length-i.val-1]'(by have := i.isLt;omega)
 ⟨row.dst,row.src,row.different⟩
def forwardEdges {R : ℕ} (W : List (ShearCode ℕ R)) (i : Fin W.length) : Edge :=
 ⟨W[i.val].dst,W[i.val].src,W[i.val].different⟩

lemma reverseEdges_eq {R : ℕ} (W : List (ShearCode ℕ R)) (i : Fin W.length) :
 reverseEdges W i = forwardEdges W i.rev := by
 have eq : W.length-i.val-1 = i.rev.val := by simp only [Fin.val_rev];omega
 simp [reverseEdges,forwardEdges,eq]

lemma reverse_matching {R : ℕ} (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (forwardEdges W)) :
 UniformMatchingAxisTableMachine.Matching (reverseEdges W) := by
 intro i j ne
 rw [reverseEdges_eq,reverseEdges_eq]
 exact matching i.rev j.rev (fun eq => ne (Fin.rev_injective eq))

lemma reverse_range {R : ℕ} (r : ℕ) (W : List (ShearCode ℕ R))
 (range : UniformMatchingAxisTableMachine.InRange r (forwardEdges W)) :
 UniformMatchingAxisTableMachine.InRange r (reverseEdges W) := by
 intro i
 rw [reverseEdges_eq]
 exact range i.rev

lemma inverseRows_edges {R C T P O : ℕ} {W : List (ShearCode ℕ R)} {s : State}
 (table : UniformInverseShearTableMachine.Rows O
   (UniformInverseShearTableMachine.inverseRows C T P (forwardRows C T P W)) s) :
 UniformMatchingAxisTableMachine.Edges (reverseEdges W) O s := by
 intro i
 have row := table i.val (by rw [UniformInverseShearTableMachine.inverseRows_length,forwardRows_length];exact i.isLt)
 rw [UniformInverseShearTableMachine.inverseRows_get C T P _ i.val (by rw [forwardRows_length];exact i.isLt)] at row
 simp only [forwardRows,List.length_map,List.getElem_map,UniformInPlaceMachine.rowOf,
   UniformInverseShearTableMachine.inverseRow] at row
 exact ⟨row.1,row.2.1⟩

/-- Ordinary fresh allocations, inherited from a genuine forward row/count
postcondition. No inverse table or matching permutation enters this structure. -/
structure Config where
 forward : ℕ
 inverseRows : ℕ
 permutation : ℕ
 widths : ℕ
 markers : ℕ
 axis : ℕ
 positive : ℕ
 negative : ℕ
 constants : ℕ
 conjugates : ℕ
 mu : ℕ
 conjugateMu : ℕ
 packing : UniformSectorPackingMachine.Layout

def Config.packed (c : Config) : UniformPackedMatchingShearMachine.Config :=
 ⟨c.packing.total,c.packing.destination,c.packing.source,c.packing.inverse,c.inverseRows,
   c.positive,c.negative,c.constants,c.conjugates,c.mu,c.conjugateMu⟩

def inverseSetup : List Op := [.literal 2418 0,.add 980 894 2418,.add 981 2400 2418,
 .add 982 2401 2418,.add 983 2412 2418,.add 984 2413 2418,.add 985 2414 2418]
def axisSetup : List Op := [.add 840 2411 2418,.add 841 894 2418,.add 842 2401 2418,
 .add 843 2402 2418,.add 844 2403 2418,.add 845 2404 2418,.add 846 2405 2418]
def packingSetup : List Op := [.literal 600 1,.add 601 2405 2418,.add 602 2406 2418,
 .add 603 2407 2418,.add 637 2408 2418,.add 604 2409 2418,.add 605 2410 2418]
def matchingSetup : List Op := [.add 1640 2411 2418,.add 1641 2410 2418,.add 1642 2409 2418,
 .add 1643 2408 2418,.add 1644 2401 2418,.add 1645 2412 2418,.add 1646 2413 2418,
 .add 1647 2414 2418,.add 1648 2415 2418,.add 1649 2416 2418,.add 1650 2417 2418]

def beforeAxis : Program := inverseSetup.map Op.code ++
 UniformInverseShearTableMachine.program.map (relocate 7 43) ++ axisSetup.map Op.code
def beforePacking : Program := beforeAxis ++
 UniformMatchingAxisTableMachine.program.map (relocate 50 105) ++ packingSetup.map Op.code
def beforeMatching : Program := beforePacking ++
 UniformSectorPackingMachine.program.map (relocate 112 249) ++ matchingSetup.map Op.code
def program : Program := beforeMatching ++
 UniformPackedMatchingShearMachine.program.map (relocate 260 682) ++ [.halt]

lemma inverseSetup_length : inverseSetup.length = 7 := rfl
lemma axisSetup_length : axisSetup.length = 7 := rfl
lemma packingSetup_length : packingSetup.length = 7 := rfl
lemma matchingSetup_length : matchingSetup.length = 11 := rfl
lemma beforeAxis_length : beforeAxis.length = 50 := by
 simp [beforeAxis,inverseSetup_length,UniformInverseShearTableMachine.program_length,axisSetup_length]
lemma beforePacking_length : beforePacking.length = 112 := by
 simp [beforePacking,beforeAxis_length,UniformMatchingAxisTableMachine.program_length,packingSetup_length]
lemma beforeMatching_length : beforeMatching.length = 260 := by
 simp [beforeMatching,beforePacking_length,UniformSectorPackingMachine.program_length,matchingSetup_length]
lemma program_length : program.length = 683 := by
 simp [program,beforeMatching_length,UniformPackedMatchingShearMachine.program_length]


lemma inverse_code : CodeAt UniformInverseShearTableMachine.program program 7 43 := by
 let after := axisSetup.map Op.code++UniformMatchingAxisTableMachine.program.map (relocate 50 105)++
   packingSetup.map Op.code++UniformSectorPackingMachine.program.map (relocate 112 249)++
   matchingSetup.map Op.code++UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 have eq : program=inverseSetup.map Op.code++UniformInverseShearTableMachine.program.map (relocate 7 43)++after := by
   simp [program,beforeMatching,beforePacking,beforeAxis,after,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code _ after _ 7 43 (by simp [inverseSetup_length])
lemma axis_code : CodeAt UniformMatchingAxisTableMachine.program program 50 105 := by
 let after := packingSetup.map Op.code++UniformSectorPackingMachine.program.map (relocate 112 249)++
   matchingSetup.map Op.code++UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 have eq : program=beforeAxis++UniformMatchingAxisTableMachine.program.map (relocate 50 105)++after := by
   simp [program,beforeMatching,beforePacking,after,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code _ after _ 50 105 beforeAxis_length
lemma packing_code : CodeAt UniformSectorPackingMachine.program program 112 249 := by
 let after := matchingSetup.map Op.code++UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 have eq : program=beforePacking++UniformSectorPackingMachine.program.map (relocate 112 249)++after := by
   simp [program,beforeMatching,after,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code _ after _ 112 249 beforePacking_length
lemma matching_code : CodeAt UniformPackedMatchingShearMachine.program program 260 682 :=
 UniformChunkRowTableMachine.segment_code beforeMatching [.halt] _ 260 682 beforeMatching_length

lemma block_at (before after : Program) (ops : List Op) (base : ℕ) (len : before.length=base)
 (eq : program=before++ops.map Op.code++after) : BlockAt ops program base := by
 intro i hi
 have h := UniformAllAxisSeedPreparation.lookup_segment before (ops.map Op.code) after i
   (by simpa only [List.length_map] using hi)
 rw [eq]
 simpa only [len,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h

lemma inverseSetup_code : BlockAt inverseSetup program 0 := by
 let after := UniformInverseShearTableMachine.program.map (relocate 7 43)++axisSetup.map Op.code++
   UniformMatchingAxisTableMachine.program.map (relocate 50 105)++packingSetup.map Op.code++
   UniformSectorPackingMachine.program.map (relocate 112 249)++matchingSetup.map Op.code++
   UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 apply block_at [] after inverseSetup 0 rfl
 simp [program,beforeMatching,beforePacking,beforeAxis,after,List.append_assoc]
lemma axisSetup_code : BlockAt axisSetup program 43 := by
 let after := UniformMatchingAxisTableMachine.program.map (relocate 50 105)++packingSetup.map Op.code++
   UniformSectorPackingMachine.program.map (relocate 112 249)++matchingSetup.map Op.code++
   UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 apply block_at (inverseSetup.map Op.code++UniformInverseShearTableMachine.program.map (relocate 7 43))
   after axisSetup 43 (by simp [inverseSetup_length,UniformInverseShearTableMachine.program_length])
 simp [program,beforeMatching,beforePacking,beforeAxis,after,List.append_assoc]
lemma packingSetup_code : BlockAt packingSetup program 105 := by
 let after := UniformSectorPackingMachine.program.map (relocate 112 249)++matchingSetup.map Op.code++
   UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]
 apply block_at (beforeAxis++UniformMatchingAxisTableMachine.program.map (relocate 50 105))
   after packingSetup 105 (by simp [beforeAxis_length,UniformMatchingAxisTableMachine.program_length])
 simp [program,beforeMatching,beforePacking,after,List.append_assoc]
lemma matchingSetup_code : BlockAt matchingSetup program 249 := by
 apply block_at (beforePacking++UniformSectorPackingMachine.program.map (relocate 112 249))
   (UniformPackedMatchingShearMachine.program.map (relocate 260 682)++[.halt]) matchingSetup 249
   (by simp [beforePacking_length,UniformSectorPackingMachine.program_length])
 simp [program,beforeMatching,List.append_assoc]
lemma halt_at : program[682]?=some .halt := by
 have len : (beforeMatching++UniformPackedMatchingShearMachine.program.map (relocate 260 682)).length=682 := by
   simp [beforeMatching_length,UniformPackedMatchingShearMachine.program_length]
 unfold program
 rw [List.getElem?_append,ite_eq_right (by rw [len];omega),len]
 rfl

structure Header (c : Config) (s : State) : Prop where
 forward : s.natReg 2400=c.forward
 inverseRows : s.natReg 2401=c.inverseRows
 permutation : s.natReg 2402=c.permutation
 widths : s.natReg 2403=c.widths
 markers : s.natReg 2404=c.markers
 axis : s.natReg 2405=c.axis
 suffix : s.natReg 2406=c.packing.suffix
 stack : s.natReg 2407=c.packing.stack
 inverse : s.natReg 2408=c.packing.inverse
 source : s.natReg 2409=c.packing.source
 destination : s.natReg 2410=c.packing.destination
 radix : s.natReg 2411=c.packing.total
 positive : s.natReg 2412=c.positive
 negative : s.natReg 2413=c.negative
 constants : s.natReg 2414=c.constants
 conjugates : s.natReg 2415=c.conjugates
 mu : s.natReg 2416=c.mu
 conjugateMu : s.natReg 2417=c.conjugateMu

lemma Header.transport {c : Config} {s u : State} (h : Header c s)
 (same : ∀ q, 2400 ≤ q → q < 2418 → u.natReg q=s.natReg q) : Header c u := by
 constructor
 all_goals first
 | exact (same _ (by omega) (by omega)).trans h.forward
 | exact (same _ (by omega) (by omega)).trans h.inverseRows
 | exact (same _ (by omega) (by omega)).trans h.permutation
 | exact (same _ (by omega) (by omega)).trans h.widths
 | exact (same _ (by omega) (by omega)).trans h.markers
 | exact (same _ (by omega) (by omega)).trans h.axis
 | exact (same _ (by omega) (by omega)).trans h.suffix
 | exact (same _ (by omega) (by omega)).trans h.stack
 | exact (same _ (by omega) (by omega)).trans h.inverse
 | exact (same _ (by omega) (by omega)).trans h.source
 | exact (same _ (by omega) (by omega)).trans h.destination
 | exact (same _ (by omega) (by omega)).trans h.radix
 | exact (same _ (by omega) (by omega)).trans h.positive
 | exact (same _ (by omega) (by omega)).trans h.negative
 | exact (same _ (by omega) (by omega)).trans h.constants
 | exact (same _ (by omega) (by omega)).trans h.conjugates
 | exact (same _ (by omega) (by omega)).trans h.mu
 | exact (same _ (by omega) (by omega)).trans h.conjugateMu

structure Layout (c : Config) (M R B : ℕ) : Prop where
 budget : c.packing.B=B
 oneAxis : c.packing.ell=1
 axisRow : c.packing.rows=c.axis
 radix : 2 ≤ c.packing.total
 forwardBelow : c.forward+3*M ≤ c.inverseRows
 inverseBelow : c.inverseRows+3*M ≤ c.permutation
 permutationBelow : c.permutation+c.packing.total ≤ c.widths
 widthsBelow : c.widths+c.packing.total ≤ c.markers
 markersBelow : c.markers+c.packing.total ≤ c.axis
 packed : UniformPackedMatchingShearMachine.Layout c.packed M R B
 code : 683 ≤ B

lemma inverseSetup_spec {c : Config} {M : ℕ} {s : State} (h : Header c s) (count : s.natReg 894=M) :
 UniformInverseShearTableMachine.Header M c.forward c.inverseRows c.positive c.negative c.constants
   (applyBlock inverseSetup s) ∧ (applyBlock inverseSetup s).natReg 2418=0 := by
 constructor
 · constructor <;> simp [inverseSetup,applyBlock,Op.apply,writeNat,next,h.forward,h.inverseRows,
     h.positive,h.negative,h.constants,count]
 · simp [inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma axisSetup_spec {c : Config} {M : ℕ} {s : State} (h : Header c s)
 (count : s.natReg 894=M) (zero : s.natReg 2418=0) :
 UniformMatchingAxisTableMachine.Header c.packing.total M c.inverseRows c.permutation c.widths c.markers c.axis
   (applyBlock axisSetup s) := by
 constructor <;> simp [axisSetup,applyBlock,Op.apply,writeNat,next,h.radix,h.inverseRows,
   h.permutation,h.widths,h.markers,h.axis,count,zero]
lemma packingSetup_spec {c : Config} {M R B : ℕ} {s : State} (l : Layout c M R B)
 (h : Header c s) (zero : s.natReg 2418=0) :
 UniformSectorPackingMachine.Header c.packing (applyBlock packingSetup s) := by
 constructor <;> simp [packingSetup,applyBlock,Op.apply,writeNat,next,h.axis,h.suffix,h.stack,h.inverse,
   h.source,h.destination,zero,l.oneAxis,l.axisRow]
lemma matchingSetup_spec {c : Config} {s : State} (h : Header c s) (zero : s.natReg 2418=0) :
 UniformPackedMatchingShearMachine.Header c.packed (applyBlock matchingSetup s) := by
 constructor <;> simp [matchingSetup,applyBlock,Op.apply,writeNat,next,Config.packed,h.radix,
   h.inverseRows,h.positive,h.negative,h.constants,h.conjugates,h.mu,h.conjugateMu,
   h.destination,h.source,h.inverse,zero]

lemma setups_safe {s : State} {B : ℕ} (bound : WordBound B s) (code : 1 ≤ B)
 (zero : s.natReg 2418=0) :
 (readable inverseSetup s ∧ peak inverseSetup s ≤ B) ∧
 (readable axisSetup s ∧ peak axisSetup s ≤ B) ∧
 (readable packingSetup s ∧ peak packingSetup s ≤ B) ∧
 (readable matchingSetup s ∧ peak matchingSetup s ≤ B) := by
 simp [inverseSetup,axisSetup,packingSetup,matchingSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero]
 repeat' constructor
 all_goals first | exact bound.2.1 _ | exact code

lemma inverseSetup_safe {s : State} {B : ℕ} (bound : WordBound B s) (_code : 1 ≤ B) :
 readable inverseSetup s ∧ peak inverseSetup s ≤ B := by
 simp [inverseSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 repeat' constructor
 all_goals exact bound.2.1 _


def KeepNat (q : ℕ) : Prop := (100 ≤ q ∧ q ≤ 106) ∨ q=894 ∨ 2400 ≤ q
lemma inverseSetup_keeps (s : State) (q : ℕ) (keep : KeepNat q) (neq : q ≠ 2418) :
 (applyBlock inverseSetup s).natReg q=s.natReg q := by
 unfold KeepNat at keep
 simp (disch:=omega) [inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma laterSetups_keeps (s : State) (q : ℕ) (keep : KeepNat q) (ops : List Op)
 (member : ops=axisSetup ∨ ops=packingSetup ∨ ops=matchingSetup) :
 (applyBlock ops s).natReg q=s.natReg q := by
 unfold KeepNat at keep
 rcases member with rfl | rfl | rfl
 all_goals simp (disch:=omega) [axisSetup,packingSetup,matchingSetup,applyBlock,Op.apply,writeNat,next]
lemma inverseSetup_header {c : Config} {s : State} (h : Header c s) :
 Header c (applyBlock inverseSetup s) :=
 h.transport (fun q lo hi => inverseSetup_keeps s q (Or.inr (Or.inr lo)) (by omega))
lemma laterSetups_header {c : Config} {s : State} (h : Header c s) (ops : List Op)
 (member : ops=axisSetup ∨ ops=packingSetup ∨ ops=matchingSetup) : Header c (applyBlock ops s) :=
 h.transport (fun q lo _ => laterSetups_keeps s q (Or.inr (Or.inr lo)) ops member)
lemma setups_heaps (s : State) (ops : List Op)
 (member : ops=inverseSetup ∨ ops=axisSetup ∨ ops=packingSetup ∨ ops=matchingSetup) :
 (applyBlock ops s).natHeap=s.natHeap ∧ (applyBlock ops s).scalarHeap=s.scalarHeap ∧
 (applyBlock ops s).scalarReg=s.scalarReg ∧ (applyBlock ops s).outputs=s.outputs ∧
 (applyBlock ops s).rootOrders=s.rootOrders := by
 rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

structure InverseResult {R : ℕ} (c : Config) (W : List (ShearCode ℕ R)) (s u : State) : Prop where
 pc : u.pc=43
 header : Header c u
 zero : u.natReg 2418=0
 count : u.natReg 894=W.length
 table : UniformInverseShearTableMachine.Rows c.inverseRows
   (UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
     (forwardRows c.positive c.negative c.constants W)) u
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 nats : ∀ q, KeepNat q → q ≠ 2418 → u.natReg q=s.natReg q
 outside : UniformInverseShearTableMachine.Outside c.inverseRows W.length s u

/-- First continuous phase: only the original physical forward table and its
actual count enter. Inverse pointers and values are generated by literal36. -/
theorem inverse_stage {R K B n : ℕ} (x : Fin n → ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (layout : Layout c W.length R B) (s : State) (args : Header c s)
 (count : s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.forward (forwardRows c.positive c.negative c.constants W) s)
 (good : ∀ row ∈ W, ForwardLeaf K row.coefficient) (pc : s.pc=0) (bound : WordBound B s) :
 ∃ ticks u, ticks ≤ 25*W.length+13 ∧ BoundedRuns program n x B s ticks u ∧ InverseResult c W s u := by
 have code:=layout.code
 have safe:=inverseSetup_safe bound (by omega)
 have first:=block_runs inverseSetup program 0 n B x s inverseSetup_code pc bound
   (by rw [inverseSetup_length];omega) safe.1 safe.2
 let a:=applyBlock inverseSetup s
 have ap : a.pc=7 := by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 let e:=setPC a 0
 have headers := inverseSetup_spec args count
 have src : UniformInverseShearTableMachine.Rows c.forward
   (forwardRows c.positive c.negative c.constants W) e := table
 have hC:=layout.packed.coefficient.positiveBelow
 have hT:=layout.packed.coefficient.negativeBelow
 have hP:=layout.packed.coefficient.constantsBelow
 have hV:=layout.packed.coefficient.conjugatesBelow
 have ha:=layout.packed.coefficient.destinations
 have hb:=layout.packed.coefficient.bound
 dsimp only [Config.packed] at hC hT hP hV ha hb
 obtain ⟨ticks,out,cost,run,op,_,printed,_,outside,frame⟩ :=
   UniformInverseShearTableMachine.execution W.length c.forward c.inverseRows c.positive c.negative c.constants R B n x
     (forwardRows c.positive c.negative c.constants W) e
     ⟨headers.1.count,headers.1.source,headers.1.output,headers.1.positive,headers.1.negative,headers.1.constants⟩
     rfl (forwardRows_length ..) src (forwardRows_domain K c.positive c.negative c.constants W good)
     hC hT (by omega) layout.forwardBelow layout.packed.rowsBound (by omega)
     (changePC_bound B a 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed inverse_code
   (by rw [UniformInverseShearTableMachine.program_length];omega) (by omega) run
 have ep : placed 7 e=a := by change {a with pc:=7}=a;rw [←ap]
 rw [ep] at moved
 let u:=setPC out 43
 have header : Header c u := (inverseSetup_header args).transport
   (fun q lo _ => frame.2.2.2.2 q (Or.inr (by omega)))
 refine ⟨7+ticks,u,?_,?_,rfl,header,?_,?_,printed,frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,?_,outside⟩
 · unfold UniformInverseShearTableMachine.runtimeBudget at cost
   omega
 · simpa only [inverseSetup_length,u,setPC] using first.trans moved
 · exact (frame.2.2.2.2 2418 (Or.inr (by omega))).trans headers.2
 · exact (frame.2.2.2.2 894 (Or.inl (by omega))).trans
     ((inverseSetup_keeps s 894 (Or.inr (Or.inl rfl)) (by omega)).trans count)
 · intro q keep neq
   exact (frame.2.2.2.2 q (by unfold KeepNat at keep;omega)).trans (inverseSetup_keeps s q keep neq)


def axes {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) :=
 [UniformMatchingAxisTableMachine.physicalAxis c.packing.total c.widths c.permutation
   (reverseEdges W) matching range positive]

lemma axes_volume {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) :
 UniformSectorPackingMachine.physicalVolume (axes c W matching range positive)=c.packing.total := by
 simp [axes,UniformSectorPackingMachine.physicalVolume,UniformSectorPackingMachine.physicalAxes,
   UniformSectorPacking.radices,UniformMatchingAxisTableMachine.physicalAxis,
   UniformMatchingAxisTableMachine.geometry,
   UniformMatchingAxisTableMachine.widths_sum c.packing.total W.length
     (UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) matching range)]

structure AxisResult {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) (s u : State) : Prop where
 pc : u.pc=105
 header : Header c u
 zero : u.natReg 2418=0
 count : u.natReg 894=W.length
 table : UniformInverseShearTableMachine.Rows c.inverseRows
   (UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
     (forwardRows c.positive c.negative c.constants W)) u
 rows : UniformSectorPackingMachine.Rows (axes c W matching range positive) 0 c.axis u
 widths : UniformSectorPackingMachine.Widths (axes c W matching range positive) u
 permutations : UniformSectorPackingMachine.Permutations (axes c W matching range positive) u
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 nats : ∀ q, KeepNat q → u.natReg q=s.natReg q
 outside : ∀ q, (q<c.permutation ∨ c.axis+4 ≤ q) → u.natHeap q=s.natHeap q

/-- The actual reversed rows determine their own matching axis, including
permutation, widths, markers and four-word axis header. Dirty output banks
are overwritten internally. -/
theorem axis_stage {R B n : ℕ} (x : Fin n → ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (layout : Layout c W.length R B)
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 {origin : State} (s : State) (before : InverseResult c W origin s) (bound : WordBound B s) :
 ∃ u, BoundedRuns program n x B s
   (7+UniformMatchingAxisTableMachine.runtime c.packing.total W.length) u ∧
 AxisResult c W matching range layout.radix s u := by
 have code:=layout.code
 have safe:readable axisSetup s ∧ peak axisSetup s ≤ B := (setups_safe bound (by omega) before.zero).2.1
 have first:=block_runs axisSetup program 43 n B x s axisSetup_code before.pc bound
   (by rw [axisSetup_length];omega) safe.1 safe.2
 let a:=applyBlock axisSetup s
 have ap:a.pc=50:=by rw [UniformTensorMonomialMachine.applyBlock_pc,before.pc];rfl
 let e:=setPC a 0
 have heads:=axisSetup_spec before.header before.count before.zero
 have src:UniformMatchingAxisTableMachine.Edges (reverseEdges W) c.inverseRows e :=
   inverseRows_edges before.table
 have hA:c.axis+4 ≤ B := by
   have h:=c.packing.rowsBelow
   have h1:=c.packing.suffixBelow
   have h2:=c.packing.stackBelow
   have h3:=c.packing.inverseBound
   rw [layout.axisRow,layout.oneAxis] at h
   rw [layout.budget] at h3
   omega
 obtain ⟨out,run,op,_,perm,widths,_,row,_,outside,frame⟩ :=
   UniformMatchingAxisTableMachine.execution c.packing.total W.length c.inverseRows c.permutation c.widths c.markers c.axis B n x
     (reverseEdges W) e
     ⟨heads.radix,heads.count,heads.source,heads.permutation,heads.widths,heads.markers,heads.row⟩
     rfl src matching range layout.inverseBelow layout.permutationBelow layout.widthsBelow layout.markersBelow hA
     (by omega) (changePC_bound B a 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed axis_code
   (by rw [UniformMatchingAxisTableMachine.program_length];omega) (by omega) run
 have ep:placed 50 e=a:=by change {a with pc:=50}=a;rw [←ap]
 rw [ep] at moved
 let u:=setPC out 105
 have headsU:Header c u := (laterSetups_header before.header axisSetup (Or.inl rfl)).transport
   (fun q lo _ => frame.2.2.2.2 q (Or.inr (by omega)))
 have banks:=UniformMatchingAxisTableMachine.physical_axis (reverseEdges W) out matching range layout.radix row perm widths
 have nat:∀q,KeepNat q → u.natReg q=s.natReg q := by
   intro q keep
   exact (frame.2.2.2.2 q (by unfold KeepNat at keep;omega)).trans (laterSetups_keeps s q keep axisSetup (Or.inl rfl))
 have original:UniformInverseShearTableMachine.Rows c.inverseRows
   (UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
     (forwardRows c.positive c.negative c.constants W)) u := by
   intro i hi
   have small:i<W.length:=by simpa only [UniformInverseShearTableMachine.inverseRows_length,forwardRows_length] using hi
   have same:∀q,q<c.inverseRows+3*W.length → q ≥ c.inverseRows → u.natHeap q=s.natHeap q := by
     intro q low _
     exact outside q (Or.inl (by have:=layout.inverseBelow;omega))
       (Or.inl (by have:=layout.inverseBelow;have:=layout.permutationBelow;omega))
       (Or.inl (by have:=layout.inverseBelow;have:=layout.permutationBelow;have:=layout.widthsBelow;omega))
       (Or.inl (by have:=layout.inverseBelow;have:=layout.permutationBelow;have:=layout.widthsBelow;have:=layout.markersBelow;omega))
   rw [same _ (by omega) (by omega),same _ (by omega) (by omega),same _ (by omega) (by omega)]
   exact before.table i hi
 refine ⟨u,?_,rfl,headsU,(nat 2418 (Or.inr (Or.inr (by omega)))).trans before.zero,
   (nat 894 (Or.inr (Or.inl rfl))).trans before.count,original,banks.1,banks.2.1,banks.2.2,
   frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,nat,?_⟩
 · simpa only [axisSetup_length,u,setPC] using first.trans moved
 · intro q hq
   exact outside q (by rcases hq with h|h;exact Or.inl h;right;have:=layout.permutationBelow;have:=layout.widthsBelow;have:=layout.markersBelow;omega)
     (by rcases hq with h|h;left;have:=layout.permutationBelow;omega;right;have:=layout.widthsBelow;have:=layout.markersBelow;omega)
     (by rcases hq with h|h;left;have:=layout.permutationBelow;have:=layout.widthsBelow;omega;right;have:=layout.markersBelow;omega)
     (by rcases hq with h|h;left;have:=layout.permutationBelow;have:=layout.widthsBelow;have:=layout.markersBelow;omega;right;exact h)


def unpacking {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) :=
 UniformSectorPackingMachine.physicalUnpacking (axes c W matching range positive) c.packing
   (axes_volume c W matching range positive)

structure PackingResult {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) (v : Fin c.packing.total → Scalar) (s u : State) : Prop where
 pc : u.pc=249
 header : Header c u
 zero : u.natReg 2418=0
 count : u.natReg 894=W.length
 table : UniformInverseShearTableMachine.Rows c.inverseRows
   (UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
     (forwardRows c.positive c.negative c.constants W)) u
 inverse : UniformSectorPackingMachine.InverseReady c.packing (unpacking c W matching range positive) u
 data : ∀ i,u.scalarHeap (c.packing.destination+i.val)=some (v (unpacking c W matching range positive i))
 scalarOutside : ∀ q,(q<c.packing.destination ∨ c.packing.destination+c.packing.total ≤ q) → u.scalarHeap q=s.scalarHeap q
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 nats : ∀ q,KeepNat q → u.natReg q=s.natReg q
 scalarReg : ∀ q,q ≠ 70 → u.scalarReg q=s.scalarReg q
 outside : UniformSectorPackingMachine.OutsideAllocation c.packing s u

/-- Consume the freshly printed matching axis. Packing computes its inverse
addresses and gathers every original tagged scalar through charged operations. -/
theorem packing_stage {R B n : ℕ} (x : Fin n → ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (layout : Layout c W.length R B)
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (v : Fin c.packing.total → Scalar) {origin : State} (s : State)
 (before : AxisResult c W matching range layout.radix origin s)
 (data : UniformSectorPackingMachine.SourceReady c.packing v s) (bound : WordBound B s) :
 ∃ ticks u,ticks ≤ 213*c.packing.total+27 ∧ BoundedRuns program n x B s ticks u ∧
 PackingResult c W matching range layout.radix v s u := by
 have code:=layout.code
 have safe:readable packingSetup s ∧ peak packingSetup s ≤ B :=
   (setups_safe bound (by omega) before.zero).2.2.1
 have first:=block_runs packingSetup program 105 n B x s packingSetup_code before.pc bound
   (by rw [packingSetup_length];omega) safe.1 safe.2
 let a:=applyBlock packingSetup s
 have ap:a.pc=112:=by rw [UniformTensorMonomialMachine.applyBlock_pc,before.pc];rfl
 let e:=setPC a 0
 have header:=packingSetup_spec layout before.header before.zero
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) matching range
 have fresh:c.axis+4 ≤ c.packing.suffix:=by
   have h:=c.packing.rowsBelow
   simpa only [layout.oneAxis,layout.axisRow,Nat.mul_one] using h
 have widthsBelow:∀ ax ∈ axes c W matching range layout.radix,
   ax.widthsBase+ax.geometry.widths.length ≤ c.packing.suffix := by
   intro ax member
   have eq:ax=UniformMatchingAxisTableMachine.physicalAxis c.packing.total c.widths c.permutation
     (reverseEdges W) matching range layout.radix := by simpa only [axes,List.mem_singleton] using member
   subst ax
   change c.widths+(UniformMatchingAxisTableMachine.widths c.packing.total W.length).length ≤ c.packing.suffix
   rw [UniformMatchingAxisTableMachine.widths_length _ _ cap]
   have h:=layout.widthsBelow;have h1:=layout.markersBelow
   omega
 have permsBelow:∀ ax ∈ axes c W matching range layout.radix,
   ax.permutationBase+ax.geometry.widths.sum ≤ c.packing.suffix := by
   intro ax member
   have eq:ax=UniformMatchingAxisTableMachine.physicalAxis c.packing.total c.widths c.permutation
     (reverseEdges W) matching range layout.radix := by simpa only [axes,List.mem_singleton] using member
   subst ax
   change c.permutation+(UniformMatchingAxisTableMachine.widths c.packing.total W.length).sum ≤ c.packing.suffix
   rw [UniformMatchingAxisTableMachine.widths_sum _ _ cap]
   have h:=layout.permutationBelow;have h1:=layout.widthsBelow;have h2:=layout.markersBelow
   omega
 have eb:WordBound c.packing.B e := by
   rw [layout.budget]
   exact changePC_bound B a 0 first.final_bound (by omega)
 obtain ⟨out,ticks,cost,run,op,inverse,values,scalars,outside,frame⟩ :=
   UniformSectorPackingMachine.execution (axes c W matching range layout.radix) c.packing n x v e
     (by simp only [axes,List.length_singleton,layout.oneAxis])
     (axes_volume c W matching range layout.radix)
     ⟨header.count,header.rows,header.suffix,header.stack,header.inverse,header.source,header.destination⟩
     (by rw [layout.axisRow];exact before.rows) before.widths before.permutations
     widthsBelow permsBelow data rfl eb
 rw [layout.budget] at run
 have moved:=UniformBoundedAssembly.boundedExecution_placed packing_code
   (by rw [UniformSectorPackingMachine.program_length];omega) (by omega) run
 have ep:placed 112 e=a:=by change {a with pc:=112}=a;rw [←ap]
 rw [ep] at moved
 let u:=setPC out 249
 have nats:∀ q,KeepNat q → u.natReg q=s.natReg q := by
   intro q keep
   exact (frame.2.2.1 q (by unfold KeepNat at keep;omega)).trans
     (laterSetups_keeps s q keep packingSetup (Or.inr (Or.inl rfl)))
 have heads:Header c u := (laterSetups_header before.header packingSetup (Or.inr (Or.inl rfl))).transport
   (fun q lo _ => frame.2.2.1 q (Or.inr (Or.inl (by omega))))
 have table:UniformInverseShearTableMachine.Rows c.inverseRows
   (UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
     (forwardRows c.positive c.negative c.constants W)) u := by
   intro i hi
   have small:i<W.length:=by simpa only [UniformInverseShearTableMachine.inverseRows_length,forwardRows_length] using hi
   have limit:c.inverseRows+3*W.length ≤ c.packing.suffix:=by
     have h:=layout.inverseBelow;have h1:=layout.permutationBelow;have h2:=layout.widthsBelow;have h3:=layout.markersBelow
     omega
   have same:∀ q,q<c.inverseRows+3*W.length → u.natHeap q=s.natHeap q := by
     intro q low
     exact outside q (Or.inl (by omega)) (Or.inl (by have:=c.packing.suffixBelow;omega))
       (Or.inl (by have:=c.packing.suffixBelow;have:=c.packing.stackBelow;omega))
   rw [same _ (by omega),same _ (by omega),same _ (by omega)]
   exact before.table i hi
 refine ⟨7+ticks,u,by omega,?_,rfl,heads,(nats 2418 (Or.inr (Or.inr (by omega)))).trans before.zero,
   (nats 894 (Or.inr (Or.inl rfl))).trans before.count,table,inverse,values,scalars,
   frame.1,frame.2.1,nats,frame.2.2.2,outside⟩
 simpa only [packingSetup_length,u,setPC] using first.trans moved

abbrev printedInverse {R : ℕ} (c : Config) (W : List (ShearCode ℕ R)) :=
 UniformInverseShearTableMachine.inverseRows c.positive c.negative c.constants
   (forwardRows c.positive c.negative c.constants W)

lemma printedInverse_length {R : ℕ} (c : Config) (W : List (ShearCode ℕ R)) :
 (printedInverse c W).length=W.length := by
 rw [printedInverse,UniformInverseShearTableMachine.inverseRows_length,forwardRows_length]

/-- The packed input is the actual gather through the freshly computed
inverse permutation. Values outside the allocated bank are immaterial. -/
def packedInput {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) (v : Fin c.packing.total → Scalar) (i : ℕ) : Scalar :=
 if hi:i<c.packing.total then v (unpacking c W matching range positive ⟨i,hi⟩) else Scalar.zero

def matchingEntry (s : State) := setPC (applyBlock matchingSetup s) 0

structure MatchingResult {R K : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (positive : 2 ≤ c.packing.total) (bank : Fin R → ℂ) (v : Fin c.packing.total → Scalar)
 (s u : State) : Prop where
 pc : u.pc=682
 action : UniformPackedMatchingShearMachine.Result c.packed (printedInverse c W) K bank
   (inverseLabels W) (unpacking c W matching range positive)
   (packedInput c W matching range positive v) (matchingEntry s) (setPC u 421)
 header : Header c u
 count : u.natReg 894=W.length
 nats : ∀ q,KeepNat q → u.natReg q=s.natReg q
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 scalarReg : ∀ q,UniformPackedMatchingShearMachine.ScalarStable q → u.scalarReg q=s.scalarReg q
 scalarHeap : ∀ q,UniformPackedMatchingShearMachine.HeapStable c.packed q → u.scalarHeap q=s.scalarHeap q

/-- The last stage reads the inverse pointers printed by literal36, executes
six real C calls per pair, then scatters using the generated packing inverse. -/
theorem matching_stage {R K B n : ℕ} (x : Fin n → ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (layout : Layout c W.length R B)
 (matching : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (range : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (bank : Fin R → ℂ) (v : Fin c.packing.total → Scalar) {origin : State} (s : State)
 (before : PackingResult c W matching range layout.radix v origin s)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s) (bound : WordBound B s) :
 ∃ ticks u,ticks=UniformPackedMatchingShearMachine.matchingCost (inverseLabels W) 0 W.length+
   9*c.packing.total+33 ∧ BoundedExecution program n x B s ticks u ∧
 MatchingResult (K:=K) c W matching range layout.radix bank v s u := by
 have code:=layout.code
 have safe:readable matchingSetup s ∧ peak matchingSetup s ≤ B :=
   (setups_safe bound (by omega) before.zero).2.2.2
 have first:=block_runs matchingSetup program 249 n B x s matchingSetup_code before.pc bound
   (by rw [matchingSetup_length];omega) safe.1 safe.2
 let a:=applyBlock matchingSetup s
 have ap:a.pc=260:=by rw [UniformTensorMonomialMachine.applyBlock_pc,before.pc];rfl
 let e:=matchingEntry s
 have args:=matchingSetup_spec before.header before.zero
 have hC:=layout.packed.coefficient.positiveBelow
 have hT:=layout.packed.coefficient.negativeBelow
 dsimp only [Config.packed] at hC hT
 have refs:∀ i (hi:i<(printedInverse c W).length),
   ((printedInverse c W)[i]'hi).coefficient=
   UniformMatchingConjugateLoadMachine.address c.positive c.negative c.constants (inverseLabels W i) := by
   intro i hi
   have small:i<W.length:=by simpa only [printedInverse_length] using hi
   exact inverseRows_reference K c.positive c.negative c.constants W good (by omega) ⟨i,small⟩
 have inverse:UniformGlobalNatPreparation.PermutationBank c.packing.total c.packing.inverse
   e.natHeap (unpacking c W matching range layout.radix) := before.inverse
 have data:UniformPackedMatchingShearMachine.Packed c.packed
   (packedInput c W matching range layout.radix v) e := by
   intro i hi
   dsimp only [Config.packed] at hi ⊢
   rw [packedInput,dite_eq_left hi]
   exact before.data ⟨i,hi⟩
 have l:UniformPackedMatchingShearMachine.Layout c.packed (printedInverse c W).length R B := by
   rw [printedInverse_length];exact layout.packed
 have count:e.natReg 894=(printedInverse c W).length := by
   rw [printedInverse_length]
   exact (laterSetups_keeps s 894 (Or.inr (Or.inl rfl)) matchingSetup (Or.inr (Or.inr rfl))).trans before.count
 obtain ⟨out,run,result⟩:=UniformPackedMatchingShearMachine.execution x c.packed (printedInverse c W) l
   bank (inverseLabels W) refs (unpacking c W matching range layout.radix)
   (packedInput c W matching range layout.radix v) e ⟨args.length,args.packed,args.destination,args.inverse,args.rows,args.positive,args.negative,
     args.constants,args.conjugates,args.mu,args.conjugateMu⟩ count
   ⟨src.positive,src.negative,src.conjugate,src.constants⟩ before.table inverse data constants rfl
   (changePC_bound B a 0 first.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed matching_code
   (by rw [UniformPackedMatchingShearMachine.program_length];omega) (by omega) run
 have ep:placed 260 e=a:=by change {a with pc:=260}=a;rw [←ap]
 rw [ep] at moved
 let u:=setPC out 682
 have stop:BoundedExecution program n x B u 1 u:=.halt moved.final_bound
   (by simp [step,u,setPC,halt_at])
 have nats:∀ q,KeepNat q → u.natReg q=s.natReg q := by
   intro q keep
   exact (result.frame.natReg q (by unfold KeepNat at keep;unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans
     (laterSetups_keeps s q keep matchingSetup (Or.inr (Or.inr rfl)))
 have heads:Header c u := (laterSetups_header before.header matchingSetup (Or.inr (Or.inr rfl))).transport
   (fun q lo _ => result.frame.natReg q (by unfold UniformPackedMatchingShearMachine.NatStable;omega))
 have action:UniformPackedMatchingShearMachine.Result c.packed (printedInverse c W) K bank
   (inverseLabels W) (unpacking c W matching range layout.radix)
   (packedInput c W matching range layout.radix v) e (setPC u 421) :=
   ⟨rfl,result.packed,result.destination,
     ⟨result.coefficients.positive,result.coefficients.negative,result.coefficients.conjugate,result.coefficients.constants⟩,
     result.constants,result.frame.setPC 421⟩
 refine ⟨11+(UniformPackedMatchingShearMachine.matchingCost (inverseLabels W) 0
   (printedInverse c W).length+9*c.packing.total+21)+1,u,?_,?_,rfl,action,heads,
   (nats 894 (Or.inr (Or.inl rfl))).trans before.count,nats,result.frame.natHeap,
   result.frame.outputs,result.frame.rootOrders,result.frame.scalarReg,result.frame.scalarHeap⟩
 · rw [printedInverse_length];omega
 · simpa only [matchingSetup_length,Config.packed,u,setPC,Nat.add_assoc] using first.executes (moved.executes stop)

lemma PackingResult.sources {R K B : ℕ} {c : Config} {W : List (ShearCode ℕ R)}
 {hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W)}
 {hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W)}
 {hp : 2 ≤ c.packing.total} {v : Fin c.packing.total → Scalar} {s u : State}
 (h : PackingResult c W hm hr hp v s u) (l : Layout c W.length R B) (bank : Fin R → ℂ)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s) :
 UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank u := by
 have a:=l.packed.coefficient.positiveBelow;have b:=l.packed.coefficient.negativeBelow
 have d:=l.packed.coefficient.constantsBelow;have e:=l.packed.coefficient.conjugatesBelow
 have f:=l.packed.coefficient.destinations;have g:=l.packed.packedFresh
 dsimp only [Config.packed] at a b d e f g
 constructor
 · intro i;rw [h.scalarOutside _ (Or.inl (by have:=i.isLt;omega))];exact src.positive i
 · intro i;rw [h.scalarOutside _ (Or.inl (by have:=i.isLt;omega))];exact src.negative i
 · intro i;rw [h.scalarOutside _ (Or.inl (by have:=i.isLt;omega))];exact src.conjugate i
 · intro i hi;rw [h.scalarOutside _ (Or.inl (by omega))];exact src.constants i hi

lemma PackingResult.constants {R B : ℕ} {c : Config} {W : List (ShearCode ℕ R)}
 {hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W)}
 {hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W)}
 {hp : 2 ≤ c.packing.total} {v : Fin c.packing.total → Scalar} {s u : State}
 (h : PackingResult c W hm hr hp v s u) (l : Layout c W.length R B)
 (src : UniformHadamardPairMachine.Constants s) : UniformHadamardPairMachine.Constants u := by
 have low:=l.packed.below
 dsimp only [Config.packed] at low
 rcases src with ⟨h1,h2,h3,h4,h5⟩
 refine ⟨?_,?_,?_,?_,?_⟩
 all_goals first
 | rw [h.scalarOutside 1 (Or.inl (by omega))];exact h1
 | rw [h.scalarOutside 2 (Or.inl (by omega))];exact h2
 | rw [h.scalarOutside 3 (Or.inl (by omega))];exact h3
 | rw [h.scalarOutside 4 (Or.inl (by omega))];exact h4
 | rw [h.scalarOutside 5 (Or.inl (by omega))];exact h5

/-- Exact inverse matching action on the original contiguous tagged bank.
Every row, permutation and helper header has been produced by the program. -/
structure Result {R K : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (hp : 2 ≤ c.packing.total) (bank : Fin R → ℂ) (v : Fin c.packing.total → Scalar)
 (s u : State) : Prop where
 pc : u.pc=682
 header : Header c u
 count : u.natReg 894=W.length
 destination : ∀ j:Fin c.packing.total,u.scalarHeap (c.packing.source+j.val)=some
   (UniformPackedMatchingShearMachine.matchingAction K bank (inverseLabels W) 0 W.length
     (packedInput c W hm hr hp v) ((unpacking c W hm hr hp).symm j).val)
 packed : UniformPackedMatchingShearMachine.Packed c.packed
   (UniformPackedMatchingShearMachine.matchingAction K bank (inverseLabels W) 0 W.length
     (packedInput c W hm hr hp v)) u
 coefficients : UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank u
 constants : UniformHadamardPairMachine.Constants u
 nats : ∀ q,KeepNat q → q≠2418 → u.natReg q=s.natReg q
 outputs : u.outputs=s.outputs
 rootOrders : u.rootOrders=s.rootOrders
 scalarReg : ∀ q,UniformPackedMatchingShearMachine.ScalarStable q → u.scalarReg q=s.scalarReg q
 scalarHeap : ∀ q,UniformPackedMatchingShearMachine.HeapStable c.packed q → u.scalarHeap q=s.scalarHeap q
 natOutside : ∀ q,(q<c.inverseRows ∨ c.axis+4≤q) →
   (q<c.packing.suffix ∨ c.packing.suffix+c.packing.ell+1≤q) →
   (q<c.packing.stack ∨ c.packing.stack+9*c.packing.ell≤q) →
   (q<c.packing.inverse ∨ c.packing.inverse+c.packing.total≤q) → u.natHeap q=s.natHeap q

def runtimeBudget {R : ℕ} (c : Config) (W : List (ShearCode ℕ R)) :=
 UniformPackedMatchingShearMachine.matchingCost (inverseLabels W) 0 W.length+
   33*W.length+239*c.packing.total+101

/-- Continuous literal683 from genuine forward rows/count and original data.
It computes inverse pointers, reverses the matching, packs, performs six-C
updates using those pointers, and scatters. The coefficient banks and layout
are physical entry contracts, not an inverse-action certificate. -/
theorem execution {R K B n : ℕ} (x : Fin n → ℂ) (c : Config) (W : List (ShearCode ℕ R))
 (l : Layout c W.length R B)
 (hm : UniformMatchingAxisTableMachine.Matching (forwardEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (forwardEdges W))
 (bank : Fin R → ℂ) (v : Fin c.packing.total → Scalar) (s : State)
 (args : Header c s) (count : s.natReg 894=W.length)
 (table : UniformInverseShearTableMachine.Rows c.forward (forwardRows c.positive c.negative c.constants W) s)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient)
 (src : UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank s)
 (constants : UniformHadamardPairMachine.Constants s)
 (data : UniformSectorPackingMachine.SourceReady c.packing v s) (pc : s.pc=0) (bound : WordBound B s) :
 ∃ ticks u,ticks≤runtimeBudget c W ∧ BoundedExecution program n x B s ticks u ∧
 Result (K:=K) c W (reverse_matching W hm) (reverse_range c.packing.total W hr) l.radix bank v s u := by
 let revMatching:=reverse_matching W hm
 let revRange:=reverse_range c.packing.total W hr
 obtain ⟨t1,u1,cost1,run1,result1⟩:=inverse_stage x c W l s args count table good pc bound
 let t2:=7+UniformMatchingAxisTableMachine.runtime c.packing.total W.length
 obtain ⟨u2,run2,result2⟩:=axis_stage x c W l revMatching revRange u1 result1 run1.final_bound
 have data2:UniformSectorPackingMachine.SourceReady c.packing v u2 := by
   intro i;rw [result2.scalarHeap,result1.scalarHeap];exact data i
 obtain ⟨t3,u3,cost3,run3,result3⟩:=packing_stage x c W l revMatching revRange v u2 result2 data2 run2.final_bound
 have src2:UniformMatchingConjugateLoadMachine.Sources K c.positive c.negative c.constants c.conjugates bank u2 := by
   constructor
   · intro i;rw [result2.scalarHeap,result1.scalarHeap];exact src.positive i
   · intro i;rw [result2.scalarHeap,result1.scalarHeap];exact src.negative i
   · intro i;rw [result2.scalarHeap,result1.scalarHeap];exact src.conjugate i
   · intro i hi;rw [result2.scalarHeap,result1.scalarHeap];exact src.constants i hi
 have const2:UniformHadamardPairMachine.Constants u2 := by
   unfold UniformHadamardPairMachine.Constants
   rw [result2.scalarHeap,result1.scalarHeap];exact constants
 obtain ⟨t4,u4,cost4,run4,result4⟩:=matching_stage x c W l revMatching revRange bank v u3 result3 good
   (result3.sources l bank src2) (result3.constants l const2) run3.final_bound
 refine ⟨t1+t2+t3+t4,u4,?_,?_,result4.pc,result4.header,result4.count,?_,?_,?_,result4.action.constants,
   ?_,?_,?_,?_,?_,?_⟩
 · unfold runtimeBudget
   dsimp only [t2] at *
   unfold UniformMatchingAxisTableMachine.runtime at *
   omega
 · simpa only [t2,Nat.add_assoc] using run1.executes (run2.executes (run3.executes run4))
 · intro j
   have h:=result4.action.destination j
   rw [printedInverse_length] at h
   exact h
 · simpa only [printedInverse_length,revMatching,revRange,UniformPackedMatchingShearMachine.Packed,setPC] using result4.action.packed
 · exact ⟨result4.action.coefficients.positive,result4.action.coefficients.negative,
     result4.action.coefficients.conjugate,result4.action.coefficients.constants⟩
 · intro q keep ne
   exact (result4.nats q keep).trans ((result3.nats q keep).trans
     ((result2.nats q keep).trans (result1.nats q keep ne)))
 · exact result4.outputs.trans (result3.outputs.trans (result2.outputs.trans result1.outputs))
 · exact result4.rootOrders.trans (result3.rootOrders.trans (result2.rootOrders.trans result1.rootOrders))
 · intro q stable
   exact (result4.scalarReg q stable).trans ((result3.scalarReg q stable.2.1).trans
     (congrFun result2.scalarReg q |>.trans (congrFun result1.scalarReg q)))
 · intro q stable
   exact (result4.scalarHeap q stable).trans ((result3.scalarOutside q stable.2.2.1).trans
     (congrFun result2.scalarHeap q |>.trans (congrFun result1.scalarHeap q)))
 · intro q first suffix stack inverse
   rw [result4.natHeap,result3.outside q suffix stack inverse]
   have h1:=l.inverseBelow;have h2:=l.permutationBelow;have h3:=l.widthsBelow;have h4:=l.markersBelow
   rw [result2.outside q (by omega),result1.outside q (by omega)]

lemma runtime_linear {R B : ℕ} {c : Config} {W : List (ShearCode ℕ R)}
 (l : Layout c W.length R B) : runtimeBudget c W≤450*c.packing.total+101 := by
 have h:=UniformPackedMatchingShearMachine.matchingCost_bound (inverseLabels W) 0 W.length
 have cap:=l.packed.capacity
 dsimp only [Config.packed] at cap
 unfold runtimeBudget
 omega

/-- The literal matching helper executes two three-C words per reversed row.
Packing and table production themselves contain no C calls. -/
def cCalls {R : ℕ} (W : List (ShearCode ℕ R)) := UniformPackedMatchingShearMachine.cCalls W.length
lemma cCalls_eq {R : ℕ} (W : List (ShearCode ℕ R)) : cCalls W=6*W.length :=
 UniformPackedMatchingShearMachine.cCalls_eq W.length

/-- The address returned by the real packing inverse at each paired position.
This follows from its sector equivalence and the actual matching permutation. -/
theorem unpacking_pair {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (hp : 2 ≤ c.packing.total) (i : Fin W.length) (t : Fin 2) :
 (unpacking c W hm hr hp ⟨2*i.val+t.val,by
   have cap:=UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) hm hr
   have:=i.isLt;have:=t.isLt;omega⟩).val=
 if t.val=0 then (reverseEdges W i).left else (reverseEdges W i).right := by
 let a:=UniformMatchingAxisTableMachine.geometry c.packing.total (reverseEdges W) hm hr hp
 let pos:=UniformMatchingPackingPreparation.matchingPosition c.packing.total (reverseEdges W) hm hr hp i t
 let z:UniformSectorPacking.SectorPosition [a]:=⟨(pos.1,()),(pos.2,())⟩
 have packed:(UniformSectorPacking.packedEquiv [a] z).val=2*i.val+t.val := by
   rw [UniformMatchingPackingPreparation.single_packed_value]
   change UniformTraversal.blockBefore (UniformMatchingAxisTableMachine.widths c.packing.total W.length)
     (UniformMatchingPackingPreparation.pairBlock c.packing.total
       (UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) hm hr) i)+t.val=_
   rw [UniformMatchingPackingPreparation.pair_before]
 have original:(UniformSectorPacking.originalEquiv [a] z).val=
   if t.val=0 then (reverseEdges W i).left else (reverseEdges W i).right := by
   rw [UniformMatchingPackingPreparation.single_original_value]
   exact UniformMatchingPackingPreparation.matching_position_original _ _ _ _ _ i t
 have h:=UniformMatchingPackingPreparation.physicalUnpacking_coordinate (axes c W hm hr hp) c.packing
   (axes_volume c W hm hr hp) z
 have same:finCongr (axes_volume c W hm hr hp)
   (UniformSectorPacking.packedEquiv [a] z)=⟨2*i.val+t.val,by
     have cap:=UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) hm hr
     have:=i.isLt;have:=t.isLt;omega⟩ := Fin.ext packed
 change (unpacking c W hm hr hp) (finCongr (axes_volume c W hm hr hp)
   (UniformSectorPacking.packedEquiv [a] z))=finCongr (axes_volume c W hm hr hp)
   (UniformSectorPacking.originalEquiv [a] z) at h
 rw [same] at h
 exact (congrArg Fin.val h).trans original

lemma packedInput_pair {R : ℕ} (c : Config) (W : List (ShearCode ℕ R))
 (hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W))
 (hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W))
 (hp : 2 ≤ c.packing.total) (v : Fin c.packing.total → Scalar) (i : Fin W.length) (t : Fin 2) :
 packedInput c W hm hr hp v (2*i.val+t.val)=v ⟨
   if t.val=0 then (reverseEdges W i).left else (reverseEdges W i).right,by
     split;exact (hr i).1;exact (hr i).2⟩ := by
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) hm hr
 have small:2*i.val+t.val<c.packing.total:=by have:=i.isLt;have:=t.isLt;omega
 rw [packedInput,dite_eq_left small]
 congr 1
 exact Fin.ext (unpacking_pair c W hm hr hp i t)

/-- Exact negative logical coefficient values, including N=1 and zero/complex
prepared coefficients; both tags are conservatively ORed by the six-C circuit. -/
theorem Result.pair_values {R K : ℕ} {c : Config} {W : List (ShearCode ℕ R)}
 {hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W)}
 {hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W)}
 {hp : 2 ≤ c.packing.total} {bank : Fin R → ℂ} {v : Fin c.packing.total → Scalar} {s u : State}
 (result : Result (K:=K) c W hm hr hp bank v s u)
 (good : ∀ row ∈ W,ForwardLeaf K row.coefficient) (i : Fin W.length) :
 let left:=v ⟨(reverseEdges W i).left,(hr i).1⟩
 let right:=v ⟨(reverseEdges W i).right,(hr i).2⟩
 u.scalarHeap (c.packing.source+(reverseEdges W i).left)=some
   ⟨left.value-(reverseReference W i).eval bank*right.value,left.dependent||right.dependent⟩ ∧
 u.scalarHeap (c.packing.source+(reverseEdges W i).right)=some
   ⟨right.value,left.dependent||right.dependent⟩ := by
 dsimp only
 let phi:=unpacking c W hm hr hp
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.packing.total (reverseEdges W) hm hr
 let l:Fin c.packing.total:=⟨2*i.val,by have:=i.isLt;omega⟩
 let r:Fin c.packing.total:=⟨2*i.val+1,by have:=i.isLt;omega⟩
 have a:=result.destination (phi l)
 have b:=result.destination (phi r)
 simp only [phi,Equiv.symm_apply_apply] at a b
 have ll:(phi l).val=(reverseEdges W i).left:=unpacking_pair c W hm hr hp i 0
 have rr:(phi r).val=(reverseEdges W i).right:=unpacking_pair c W hm hr hp i 1
 rw [ll] at a;rw [rr] at b
 have numeric:=UniformPackedMatchingShearMachine.matchingAction_pair K bank (inverseLabels W) 0
   W.length i.val (packedInput c W hm hr hp v) (by omega) (by have:=i.isLt;omega)
 have vl:=packedInput_pair c W hm hr hp v i 0
 have vr:=packedInput_pair c W hm hr hp v i 1
 simp only [Fin.val_zero,Nat.add_zero,ite_true,Fin.val_one,show (1:ℕ)≠0 by omega,ite_false] at vl vr
 rw [vl,vr,inverseLabels_value K bank W good i] at numeric
 refine ⟨a.trans (congrArg some ?_),b.trans (congrArg some numeric.2)⟩
 simpa only [sub_eq_add_neg,neg_mul] using numeric.1

theorem Result.tail {R K : ℕ} {c : Config} {W : List (ShearCode ℕ R)}
 {hm : UniformMatchingAxisTableMachine.Matching (reverseEdges W)}
 {hr : UniformMatchingAxisTableMachine.InRange c.packing.total (reverseEdges W)}
 {hp : 2 ≤ c.packing.total} {bank : Fin R → ℂ} {v : Fin c.packing.total → Scalar} {s u : State}
 (result : Result (K:=K) c W hm hr hp bank v s u) (j : Fin c.packing.total) (tail : 2*W.length≤j.val) :
 u.scalarHeap (c.packing.source+(unpacking c W hm hr hp j).val)=some (v (unpacking c W hm hr hp j)) := by
 have h:=result.destination (unpacking c W hm hr hp j)
 rw [Equiv.symm_apply_apply,UniformPackedMatchingShearMachine.matchingAction_outside K bank (inverseLabels W)
   0 W.length j.val _ (Or.inr (by omega)),packedInput,dite_eq_left j.isLt] at h
 exact h

end
end ExactFourierCircuits.UniformSixCInverseMatchingPreparation
