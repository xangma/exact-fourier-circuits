import UniformSixCDirtyReplayMachine
import UniformCrossBroadcastTableMachine

set_option autoImplicit false

/-! Controller foundation: continuous bodies derive matching geometry and
packed data, then execute the real six-C loop. UniformSixCPhaseLoop proves the
ascending/descending cursors; UniformSixCWholeReplay joins the six phases. -/
namespace ExactFourierCircuits.UniformSixCDepthColorController
open UniformMachine UniformAssembly UniformReplayPrint
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

abbrev setup := UniformSixCDirtyReplayMachine.forwardSetup

def forwardProgram : Program :=
 UniformMatchingPackingPreparation.program.map (relocate 0 361) ++ setup.map Op.code ++
 UniformPackedMatchingShearMachine.program.map (relocate 373 795) ++ [.halt]
lemma forwardProgram_length : forwardProgram.length=796 := by
 simp [forwardProgram,UniformMatchingPackingPreparation.program_length,
  UniformSixCDirtyReplayMachine.forwardSetup_length,UniformPackedMatchingShearMachine.program_length]
attribute [local irreducible] UniformMatchingPackingPreparation.program UniformPackedMatchingShearMachine.program
lemma packing_code : CodeAt UniformMatchingPackingPreparation.program forwardProgram 0 361 := by
 have eq:forwardProgram=[]++UniformMatchingPackingPreparation.program.map (relocate 0 361)++
  (setup.map Op.code++UniformPackedMatchingShearMachine.program.map (relocate 373 795)++[.halt]):=by
  simp only [forwardProgram,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code [] _ _ 0 361 rfl
lemma setup_code : BlockAt setup forwardProgram 361 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformMatchingPackingPreparation.program.map (relocate 0 361)) (setup.map Op.code)
  (UniformPackedMatchingShearMachine.program.map (relocate 373 795)++[.halt]) i (by simpa using hi)
 simpa only [forwardProgram,List.length_map,UniformMatchingPackingPreparation.program_length,
  List.append_assoc,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma matching_code : CodeAt UniformPackedMatchingShearMachine.program forwardProgram 373 795 := by
 exact UniformChunkRowTableMachine.segment_code
  (UniformMatchingPackingPreparation.program.map (relocate 0 361)++setup.map Op.code) [.halt] _ 373 795
  (by simp [UniformMatchingPackingPreparation.program_length,UniformSixCDirtyReplayMachine.forwardSetup_length])
lemma halt_at : forwardProgram[795]?=some .halt := by
 let pre:=UniformMatchingPackingPreparation.program.map (relocate 0 361)++setup.map Op.code++
  UniformPackedMatchingShearMachine.program.map (relocate 373 795)
 have len:pre.length=795:=by
  simp [pre,UniformMatchingPackingPreparation.program_length,
   UniformSixCDirtyReplayMachine.forwardSetup_length,UniformPackedMatchingShearMachine.program_length]
 change (pre++[.halt])[795]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl


def inverseInstall : List Op := [.literal 3000 0] ++ UniformSixCDirtyReplayMachine.inverseSetup
lemma inverseInstall_length : inverseInstall.length=19 := rfl
def inverseProgram : Program :=
 UniformChunkMatchingPreparation.program.map (relocate 0 215) ++ inverseInstall.map Op.code ++
 UniformSixCInverseMatchingPreparation.program.map (relocate 234 917) ++ [.halt]
lemma inverseProgram_length : inverseProgram.length=918 := by
 simp [inverseProgram,UniformChunkMatchingPreparation.program_length,
  inverseInstall_length,UniformSixCInverseMatchingPreparation.program_length]
attribute [local irreducible] UniformChunkMatchingPreparation.program UniformSixCInverseMatchingPreparation.program
lemma chunk_code : CodeAt UniformChunkMatchingPreparation.program inverseProgram 0 215 := by
 have eq:inverseProgram=[]++UniformChunkMatchingPreparation.program.map (relocate 0 215)++
  (inverseInstall.map Op.code++UniformSixCInverseMatchingPreparation.program.map (relocate 234 917)++[.halt]):=by
  simp only [inverseProgram,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code [] _ _ 0 215 rfl
lemma inverseInstall_code : BlockAt inverseInstall inverseProgram 215 := by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (UniformChunkMatchingPreparation.program.map (relocate 0 215)) (inverseInstall.map Op.code)
  (UniformSixCInverseMatchingPreparation.program.map (relocate 234 917)++[.halt]) i (by simpa using hi)
 simpa only [inverseProgram,List.length_map,UniformChunkMatchingPreparation.program_length,
  List.append_assoc,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma inverse_code : CodeAt UniformSixCInverseMatchingPreparation.program inverseProgram 234 917 :=
 UniformChunkRowTableMachine.segment_code
  (UniformChunkMatchingPreparation.program.map (relocate 0 215)++inverseInstall.map Op.code) [.halt] _ 234 917
  (by simp [UniformChunkMatchingPreparation.program_length,inverseInstall_length])
lemma inverse_halt_at : inverseProgram[917]?=some .halt := by
 let pre:=UniformChunkMatchingPreparation.program.map (relocate 0 215)++inverseInstall.map Op.code++
  UniformSixCInverseMatchingPreparation.program.map (relocate 234 917)
 have len:pre.length=917:=by
  simp [pre,UniformChunkMatchingPreparation.program_length,inverseInstall_length,
   UniformSixCInverseMatchingPreparation.program_length]
 change (pre++[.halt])[917]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

def readonly (q:ℕ) : Bool := (1050≤q && q<1080) || (1180≤q && q<1193) || (1400≤q && q<1405)
def writesReadonly (ins:Instruction) : Bool := match ins with
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => readonly d
 | _ => false
lemma writesReadonly_relocate (b pc:ℕ) (ins:Instruction) :
 writesReadonly (relocate b pc ins)=writesReadonly ins:=by cases ins <;> rfl
lemma sector_readonly : UniformSectorPackingMachine.program.all (fun ins=>!writesReadonly ins)=true := by decide
lemma axis_readonly : UniformMatchingAxisTableMachine.program.all (fun ins=>!writesReadonly ins)=true := by decide
lemma inverse_rows_readonly : UniformInverseShearTableMachine.program.all (fun ins=>!writesReadonly ins)=true := by decide
lemma scatter_readonly : UniformScalarScatterMachine.program.all (fun ins=>!writesReadonly ins)=true := by decide
lemma loader_readonly : UniformMatchingConjugateLoadMachine.rowProgram.all (fun ins=>!writesReadonly ins)=true := by decide
lemma hadamard_readonly : UniformHadamardPairMachine.program.all (fun ins=>!writesReadonly ins)=true := by decide
lemma phase_readonly (a:UniformZeroFreePairShearMachine.Phase) : a.code.all (fun ins=>!writesReadonly ins)=true := by
 cases a with
 | hadamard=>exact hadamard_readonly
 | diagonal c d=>
  cases c <;> cases d <;> simp [UniformZeroFreePairShearMachine.Phase.code,
   UniformZeroFreePairShearMachine.Coefficient.code,UniformPairDiagonalMachine.program,
   relocate,writesReadonly]
lemma emit_readonly (ps:List UniformZeroFreePairShearMachine.Phase) (base:ℕ) :
 (UniformZeroFreePairShearMachine.emit base ps).all (fun ins=>!writesReadonly ins)=true:=by
 induction ps generalizing base with
 | nil=>rfl
 | cons a ps ih=>
  simp only [UniformZeroFreePairShearMachine.emit,List.all_append,List.all_map,
   Function.comp_def,writesReadonly_relocate,phase_readonly,ih,Bool.true_and]
lemma pair_readonly : UniformZeroFreePairShearMachine.program.all (fun ins=>!writesReadonly ins)=true:=by
 simp only [UniformZeroFreePairShearMachine.program,List.all_append,emit_readonly,Bool.and_true]
 decide
lemma matching_readonly : UniformPackedMatchingShearMachine.program.all (fun ins=>!writesReadonly ins)=true:=by
 simp only [UniformPackedMatchingShearMachine.program,UniformPackedMatchingShearMachine.beforeScatter,
  UniformPackedMatchingShearMachine.beforePair,UniformPackedMatchingShearMachine.beforeRow,
  List.all_append,List.all_map,Function.comp_def,writesReadonly_relocate,
  pair_readonly,loader_readonly,scatter_readonly,Bool.and_true]
 decide
lemma inverse_readonly : UniformSixCInverseMatchingPreparation.program.all (fun ins=>!writesReadonly ins)=true := by
 simp only [UniformSixCInverseMatchingPreparation.program,UniformSixCInverseMatchingPreparation.beforeMatching,
  UniformSixCInverseMatchingPreparation.beforePacking,UniformSixCInverseMatchingPreparation.beforeAxis,
  List.all_append,List.all_map,Function.comp_def,writesReadonly_relocate,
  inverse_rows_readonly,axis_readonly,sector_readonly,matching_readonly,Bool.and_true]
 decide

lemma inverse_keeps_readonly (q:ℕ) (read:readonly q=true) :
 ∀ins∈UniformSixCInverseMatchingPreparation.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins mem
 have eq:=List.all_eq_true.mp inverse_readonly ins mem
 cases ins <;> simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals intro same;subst_vars;simp [writesReadonly,read] at eq
lemma setup_readonly (s:State) (q:ℕ) (read:readonly q=true) :
 (applyBlock setup s).natReg q=s.natReg q:=by
 simp only [readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at read
 simp (disch:=omega) [setup,UniformSixCDirtyReplayMachine.forwardSetup,applyBlock,Op.apply,writeNat,next]


/-- The layer ordinal is advanced by real RAM instructions. Descending mode
computes total-1-index before division/remainder; there is no reverse list. -/
def traversalBoot : List Op := [.literal 3021 0,.literal 3022 1,.literal 3023 11,
 .literal 3024 8,.literal 3025 7,.literal 3026 0,
 .mul 3027 1050 3024,.add 3027 3027 3025,.mul 3027 3027 3023]
def cursorHead (backwards:Bool) : Program :=
 if backwards then [ .natBinary .sub 3028 3027 3022,.natBinary .sub 3028 3028 3021,
  .natBinary .div 1191 3028 3023,.natBinary .mod 1192 3028 3023]
 else [.natBinary .div 1191 3021 3023,.natBinary .mod 1192 3021 3023]
def traversalBody (backwards:Bool) : Program := if backwards then inverseProgram else forwardProgram
def traversalBodyBase (backwards:Bool) := 10+(cursorHead backwards).length
def traversalTickPC (backwards:Bool) := traversalBodyBase backwards+(traversalBody backwards).length
def traversalHaltPC (backwards:Bool) := traversalTickPC backwards+2
def traversalProgram (backwards:Bool) : Program := traversalBoot.map Op.code ++
 [.branchLT 3021 3027 10 (traversalHaltPC backwards)] ++ cursorHead backwards ++
 (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards)) ++
 [.natBinary .add 3021 3021 3022,.jump 9,.halt]
lemma traversalBoot_length : traversalBoot.length=9:=rfl
lemma cursorHead_length (backwards:Bool) : (cursorHead backwards).length=if backwards then 4 else 2:=by
 cases backwards <;> rfl
lemma traversalBody_length (backwards:Bool) : (traversalBody backwards).length=if backwards then 918 else 796:=by
 cases backwards <;> simp only [traversalBody,Bool.false_eq_true,ite_false,ite_true,
  inverseProgram_length,forwardProgram_length]
lemma traversalProgram_length (backwards:Bool) : (traversalProgram backwards).length=if backwards then 935 else 811:=by
 cases backwards <;> simp [traversalProgram,traversalBoot_length,cursorHead_length,traversalBody_length]
lemma traversal_boot_code (backwards:Bool) : BlockAt traversalBoot (traversalProgram backwards) 0:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (traversalBoot.map Op.code)
  ([.branchLT 3021 3027 10 (traversalHaltPC backwards)]++cursorHead backwards++
   (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))++
   [.natBinary .add 3021 3021 3022,.jump 9,.halt]) i (by simpa using hi)
 simpa only [traversalProgram,List.append_assoc,List.nil_append,List.length_nil,Nat.zero_add,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma traversal_body_code (backwards:Bool) : CodeAt (traversalBody backwards)
 (traversalProgram backwards) (traversalBodyBase backwards) (traversalTickPC backwards):=by
 have eq:traversalProgram backwards=
  (traversalBoot.map Op.code++[.branchLT 3021 3027 10 (traversalHaltPC backwards)]++cursorHead backwards)++
  (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))++
  [.natBinary .add 3021 3021 3022,.jump 9,.halt]:=by simp [traversalProgram,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code _ _ _ _ _
  (by simp [traversalBoot_length,traversalBodyBase];omega)
lemma traversal_branch_at (backwards:Bool) :
 (traversalProgram backwards)[9]?=some (.branchLT 3021 3027 10 (traversalHaltPC backwards)):=by
 unfold traversalProgram
 simp only [List.append_assoc]
 rw [List.getElem?_append_right (by simp [traversalBoot_length])]
 simp [traversalBoot_length]
lemma traversal_tick_at (backwards:Bool) :
 (traversalProgram backwards)[traversalTickPC backwards]?=some (.natBinary .add 3021 3021 3022):=by
 let pre:=traversalBoot.map Op.code++[.branchLT 3021 3027 10 (traversalHaltPC backwards)]++cursorHead backwards++
  (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))
 have len:pre.length=traversalTickPC backwards:=by
  simp [pre,traversalTickPC,traversalBodyBase,traversalBoot_length];omega
 change (pre++[.natBinary .add 3021 3021 3022,.jump 9,.halt])[traversalTickPC backwards]?=_
 rw [List.getElem?_append_right (by omega),len,Nat.sub_self];rfl
lemma traversal_jump_at (backwards:Bool) : (traversalProgram backwards)[traversalTickPC backwards+1]?=some (.jump 9):=by
 let pre:=traversalBoot.map Op.code++[.branchLT 3021 3027 10 (traversalHaltPC backwards)]++cursorHead backwards++
  (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))
 have len:pre.length=traversalTickPC backwards:=by
  simp [pre,traversalTickPC,traversalBodyBase,traversalBoot_length];omega
 change (pre++[.natBinary .add 3021 3021 3022,.jump 9,.halt])[traversalTickPC backwards+1]?=_
 rw [List.getElem?_append_right (by omega),len];simp
lemma traversal_halt_at (backwards:Bool) : (traversalProgram backwards)[traversalHaltPC backwards]?=some .halt:=by
 let pre:=traversalBoot.map Op.code++[.branchLT 3021 3027 10 (traversalHaltPC backwards)]++cursorHead backwards++
  (traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))
 have len:pre.length=traversalTickPC backwards:=by
  simp [pre,traversalTickPC,traversalBodyBase,traversalBoot_length];omega
 change (pre++[.natBinary .add 3021 3021 3022,.jump 9,.halt])[traversalTickPC backwards+2]?=_
 rw [List.getElem?_append_right (by omega),len];simp

noncomputable section

def fields (c:UniformPackedMatchingShearMachine.Config) : List ℕ :=
 [c.length,c.packed,c.destination,c.inverse,c.rows,c.positive,c.negative,c.constants,
 c.conjugates,c.mu,c.conjugateMu]
/-- Ordinary allocation header, not generated geometry or transformed data. -/
def Args (c:UniformPackedMatchingShearMachine.Config) (s:State) : Prop :=
 ∀i:Fin 11,s.natReg (3001+i.val)=(fields c)[i.val]'(by simpa only [fields,List.length_cons,List.length_nil] using i.isLt)
lemma Args.transport {c:UniformPackedMatchingShearMachine.Config} {s u:State}
 (h:Args c s) (same:∀q,3001≤q→q≤3011→u.natReg q=s.natReg q) : Args c u := by
 intro i;rw [same _ (by omega) (by have:=i.isLt;omega)];exact h i
lemma setup_args (c:UniformPackedMatchingShearMachine.Config) (s:State) (h:Args c s) :
 UniformPackedMatchingShearMachine.Header c (applyBlock setup s) := by
 have h0:=h ⟨0,by decide⟩;have h1:=h ⟨1,by decide⟩;have h2:=h ⟨2,by decide⟩
 have h3:=h ⟨3,by decide⟩;have h4:=h ⟨4,by decide⟩;have h5:=h ⟨5,by decide⟩
 have h6:=h ⟨6,by decide⟩;have h7:=h ⟨7,by decide⟩;have h8:=h ⟨8,by decide⟩
 have h9:=h ⟨9,by decide⟩;have h10:=h ⟨10,by decide⟩
 simp only [fields,List.getElem_cons_zero,List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
 constructor <;> simp [setup,UniformSixCDirtyReplayMachine.forwardSetup,applyBlock,Op.apply,writeNat,next,
  h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

def config {p:UniformChunkMatchingPreparation.Parameters} {B:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (C T P V mu bar:ℕ) :=
 UniformPackedMatchingShearMachine.packingConfig l.packing p.mapped C T P V mu bar

def labels {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters) (W:List (ShearCode ℕ R)) :=
 UniformPackedMatchingShearMachine.selectedLabels p W

def phi {p:UniformChunkMatchingPreparation.Parameters} {B R:ℕ}
 (l:UniformMatchingPackingPreparation.Layout p B) (W:List (ShearCode ℕ R))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :=
 UniformSectorPackingMachine.physicalUnpacking [UniformChunkMatchingPreparation.axis l.matching W dom degree]
  l.packing (UniformMatchingPackingPreparation.axis_volume l W dom degree)

def packedValues {L:ℕ} (e:Fin L≃Fin L) (v:Fin L→Scalar) (i:ℕ) : Scalar :=
 if hi:i<L then v (e ⟨i,hi⟩) else Scalar.zero

/-- The real packing result derives every table/count/inverse/data input to
422. The only scalar premises are original source presence and actual prepared
coefficient/conjugate/constant banks. No completed matching action is supplied. -/
theorem forward_execution {p:UniformChunkMatchingPreparation.Parameters} {B R n:ℕ}
 (x:Fin n→ℂ) (W:List (ShearCode ℕ R))
 (l:UniformMatchingPackingPreparation.Layout p B) (C T P V mu bar:ℕ)
 (fl:UniformPackedMatchingShearMachine.Layout (config l C T P V mu bar)
  (UniformChunkMatchingPreparation.indices p W).length R B)
 (bank:Fin R→ℂ) (v:Fin l.packing.total→Scalar) (s:State)
 (head:UniformMatchingPackingPreparation.Header l s) (args:Args (config l C T P V mu bar) s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0 (UniformCrossShearTableMachine.locations R C T P))) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (source:UniformSectorPackingMachine.SourceReady l.packing v s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K C T P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (pc:s.pc=0) (bound:WordBound B s) (code:796≤B) : ∃u t,
 BoundedExecution forwardProgram n x B s t u ∧ t≤4*p.height.K+596*p.radix+155 ∧ u.pc=795 ∧
 (∀j:Fin l.packing.total,u.scalarHeap (l.packing.source+j.val)=some
  (UniformPackedMatchingShearMachine.matchingAction p.height.K bank (labels p W) 0
   (UniformChunkMatchingPreparation.indices p W).length (packedValues (phi l W dom degree) v)
   ((phi l W dom degree).symm j).val)) ∧
 UniformMatchingConjugateLoadMachine.Sources p.height.K C T P V bank u ∧
 UniformHadamardPairMachine.Constants u ∧
 (∀q,3001≤q→u.natReg q=s.natReg q) ∧
 (∀q,readonly q=true→u.natReg q=s.natReg q) ∧
 (∀q,(q<p.borrowed ∨ l.packing.inverse+l.packing.total≤q)→u.natHeap q=s.natHeap q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable (config l C T P V mu bar) q→u.scalarHeap q=s.scalarHeap q) := by
 let loc:=UniformCrossShearTableMachine.locations R C T P
 let c:=config l C T P V mu bar
 let rows:=UniformChunkMatchingPreparation.mappedRows p l.matching.capacity W loc
 have rowLength:rows.length=(UniformChunkMatchingPreparation.indices p W).length:=
  UniformPackedMatchingShearMachine.mappedRows_length p l.matching.capacity W loc
 obtain ⟨ticks,a,cost,first,post⟩:=UniformMatchingPackingPreparation.execution_result
  (n:=n) (x:=x) W loc l v s head size record table colors dom degree source pc bound
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed packing_code
  (by rw [UniformMatchingPackingPreparation.program_length];omega) (by omega) first
 have start:placed 0 s=s:=by simp [placed]
 rw [start] at placedFirst
 let b:=setPC a 361
 have bs:WordBound B b:=placedFirst.final_bound
 have ah:Args c b:=args.transport (fun q lo hi=>post.frame.2.2.1 q
  (by unfold UniformMatchingPackingPreparation.Protected UniformChunkMatchingPreparation.Protected;omega))
 have safe:=UniformSixCDirtyReplayMachine.forwardSetup_safe B b bs
 have install:=block_runs setup forwardProgram 361 n B x b setup_code rfl bs
  (by rw [UniformSixCDirtyReplayMachine.forwardSetup_length];omega) safe.1 safe.2
 let d:=applyBlock setup b
 have dp:d.pc=373:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 let entry:=setPC d 0
 have eb:WordBound B entry:=changePC_bound B d 0 install.final_bound (by omega)
 have header:UniformPackedMatchingShearMachine.Header c entry:=by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩:=setup_args c b ah
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
 have natSame:entry.natHeap=a.natHeap:=rfl
 have scalarSame:entry.scalarHeap=a.scalarHeap:=rfl
 have cs:UniformMatchingConjugateLoadMachine.Sources p.height.K C T P V bank entry:=by
  refine ⟨?_,?_,?_,?_⟩
  · intro i;rw [scalarSame,post.scalarOutside _ (Or.inl (by have h:=fl.coefficient.positiveBelow;have h2:=fl.packedFresh;have h3:=fl.coefficient.positiveBelow;have h4:=fl.coefficient.negativeBelow;have h5:=fl.coefficient.constantsBelow;have h6:=fl.coefficient.conjugatesBelow;have h7:=fl.coefficient.destinations;have:=i.isLt;dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at *;omega))];exact src.positive i
  · intro i;rw [scalarSame,post.scalarOutside _ (Or.inl (by have h:=fl.coefficient.negativeBelow;have h2:=fl.packedFresh;have h3:=fl.coefficient.positiveBelow;have h4:=fl.coefficient.negativeBelow;have h5:=fl.coefficient.constantsBelow;have h6:=fl.coefficient.conjugatesBelow;have h7:=fl.coefficient.destinations;have:=i.isLt;dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at *;omega))];exact src.negative i
  · intro i;rw [scalarSame,post.scalarOutside _ (Or.inl (by have h:=fl.coefficient.conjugatesBelow;have h2:=fl.packedFresh;have h3:=fl.coefficient.positiveBelow;have h4:=fl.coefficient.negativeBelow;have h5:=fl.coefficient.constantsBelow;have h6:=fl.coefficient.conjugatesBelow;have h7:=fl.coefficient.destinations;have:=i.isLt;dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at *;omega))];exact src.conjugate i
  · intro i hi;rw [scalarSame,post.scalarOutside _ (Or.inl (by have h:=fl.coefficient.constantsBelow;have h2:=fl.packedFresh;have h3:=fl.coefficient.conjugatesBelow;have h4:=fl.coefficient.destinations;dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at *;omega))];exact src.constants i hi
 have hc:UniformHadamardPairMachine.Constants entry:=by
  have below:6≤l.packing.destination:=by
   have h:=fl.coefficient.constantsBelow;have h2:=fl.packedFresh;have h3:=fl.coefficient.conjugatesBelow;have h4:=fl.coefficient.destinations
   dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at *;omega
  rcases constants with ⟨h1,h2,h3,h4,h5⟩
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rw [scalarSame,post.scalarOutside _ (Or.inl (by omega))] <;> assumption
 have ready:UniformPackedMatchingShearMachine.Packed c (packedValues (phi l W dom degree) v) entry:=by
  intro i hi
  change entry.scalarHeap (l.packing.destination+i)=some (packedValues (phi l W dom degree) v i)
  have hi':i<l.packing.total:=hi
  rw [scalarSame,packedValues,dite_eq_left hi']
  exact post.packed ⟨i,hi⟩
 have inv:UniformGlobalNatPreparation.PermutationBank c.length c.inverse entry.natHeap (phi l W dom degree):=by
  rw [natSame];exact post.inverse
 have ref:∀i (hi:i<rows.length),(rows[i]'hi).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P (labels p W i):=by
  intro i hi;exact UniformPackedMatchingShearMachine.mappedRows_reference p l.matching.capacity W C T P i hi
 have lay:UniformPackedMatchingShearMachine.Layout c rows.length R B:=by rw [rowLength];exact fl
 obtain ⟨out,run,res⟩:=UniformPackedMatchingShearMachine.execution x c rows lay bank (labels p W) ref
  (phi l W dom degree) (packedValues (phi l W dom degree) v) entry header
  (by change (applyBlock setup b).natReg 894=rows.length;rw [(UniformSixCDirtyReplayMachine.setup_count b).1];exact post.count.trans rowLength.symm)
  cs (by intro i hi;exact post.mapped i hi) inv ready hc rfl eb
 have moved:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformPackedMatchingShearMachine.program_length];omega) (by omega) run
 have en:placed 373 entry=d:=by change {d with pc:=373}=d;rw [←dp]
 rw [en] at moved
 let u:=setPC out 795
 have stop:BoundedExecution forwardProgram n x B u 1 u:=.halt moved.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:=placedFirst.executes (install.executes (moved.executes stop))
 have us:UniformMatchingConjugateLoadMachine.Sources p.height.K C T P V bank u:=
  ⟨res.coefficients.positive,res.coefficients.negative,res.coefficients.conjugate,res.coefficients.constants⟩
 refine ⟨u,ticks+12+(UniformPackedMatchingShearMachine.matchingCost (labels p W) 0 rows.length+9*l.packing.total+21)+1,?_,?_,rfl,?_,us,res.constants,?_,?_,?_,?_,?_,?_⟩
 · convert all using 1
   simp only [UniformSixCDirtyReplayMachine.forwardSetup_length]
   dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig]
   omega
 · have h:=UniformPackedMatchingShearMachine.runtime_linear (labels p W) lay.capacity
   dsimp [c,config,UniformPackedMatchingShearMachine.packingConfig] at h
   rw [l.volume] at h ⊢;omega
 · intro j
   have h:=res.destination j
   change out.scalarHeap (l.packing.source+j.val)=_ at h
   rw [rowLength] at h
   exact h
 · intro q lo
   exact (res.frame.natReg q (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans
    ((UniformSixCDirtyReplayMachine.forwardSetup_high b q lo).trans
     (post.frame.2.2.1 q (by unfold UniformMatchingPackingPreparation.Protected UniformChunkMatchingPreparation.Protected;omega)))
 · intro q read
   have range:=read
   simp only [readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
   exact (res.frame.natReg q (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans
    ((setup_readonly b q read).trans
     (post.frame.2.2.1 q (by unfold UniformMatchingPackingPreparation.Protected UniformChunkMatchingPreparation.Protected;omega)))
 · intro q hq
   exact (congrFun res.frame.natHeap q).trans (post.outside q hq)
 · exact res.frame.outputs.trans post.frame.1
 · exact res.frame.rootOrders.trans post.frame.2.1
 · intro q stable
   exact (res.frame.scalarHeap q stable).trans (post.scalarOutside q stable.2.2.1)

/-- Actual logical coefficient interpretation is restricted to the proved
forward-leaf domain; arbitrary rational fallback is not certified. -/
lemma selected_coefficient_value {R:ℕ} (K:ℕ) (bank:Fin R→ℂ)
 (p:UniformChunkMatchingPreparation.Parameters) (W:List (ShearCode ℕ R))
 (good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf K row.coefficient)
 (i:Fin (UniformChunkMatchingPreparation.indices p W).length) :
 UniformMatchingConjugateLoadMachine.value K bank (labels p W i.val)=
  (UniformMatchingCoefficientValueBridge.selectedReference p W i).eval bank :=
 UniformMatchingCoefficientValueBridge.selected_labels_value K bank p W good i

/-- The genuine corrected-cross constructor supplies that syntax domain. -/
lemma cross_coefficient_value (p:UniformChunkMatchingPreparation.Parameters)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (bank:Fin (UniformToeplitzCrossDAG.bankSize p.height.K)→ℂ)
 (i:Fin (UniformChunkMatchingPreparation.indices p (UniformChunkMatchingPreparation.crossWord p ha he)).length) :
 UniformMatchingConjugateLoadMachine.value p.height.K bank
  (labels p (UniformChunkMatchingPreparation.crossWord p ha he) i.val)=
 (UniformMatchingCoefficientValueBridge.selectedReference p
  (UniformChunkMatchingPreparation.crossWord p ha he) i).eval bank :=
 UniformMatchingCoefficientValueBridge.cross_selected_value p ha he bank i

lemma inverseInstall_args (c:UniformSixCDirtyReplayMachine.Config) (s:State)
 (h:UniformSixCDirtyReplayMachine.Header c s) :
 UniformSixCInverseMatchingPreparation.Header c.inverse (applyBlock inverseInstall s) := by
 have zero:((Op.literal 3000 0).apply s).natReg 3000=0:=by simp [Op.apply,writeNat,next]
 have header:UniformSixCDirtyReplayMachine.Header c ((Op.literal 3000 0).apply s):=
  h.transport (by intro q lo hi;simp [Op.apply,writeNat,next,show q≠3000 by omega])
 exact UniformSixCDirtyReplayMachine.inverseSetup_args c _ header zero
lemma inverseInstall_high (s:State) (q:ℕ) (lo:3001≤q) :
 (applyBlock inverseInstall s).natReg q=s.natReg q := by
 change (applyBlock UniformSixCDirtyReplayMachine.inverseSetup ((Op.literal 3000 0).apply s)).natReg q=s.natReg q
 exact (UniformSixCDirtyReplayMachine.inverseSetup_high _ q (by omega)).trans
  (by simp [Op.apply,writeNat,next,show q≠3000 by omega])
lemma inverseInstall_safe (B:ℕ) (s:State) (bound:WordBound B s) (code:1≤B) :
 readable inverseInstall s ∧ peak inverseInstall s≤B := by
 let z:=(Op.literal 3000 0).apply (setPC s 0)
 have zb:WordBound B z:=Op.apply_bound (.literal 3000 0) B (setPC s 0)
  (changePC_bound B s 0 bound (by omega)) code (by simp [Op.peak])
 have zero:z.natReg 3000=0:=by simp [z,setPC,Op.apply,writeNat,next]
 have safe:=UniformSixCDirtyReplayMachine.inverseSetup_safe B z zb zero
 constructor
 · change True ∧ readable UniformSixCDirtyReplayMachine.inverseSetup ((Op.literal 3000 0).apply s)
   exact ⟨trivial,by simp [UniformSixCDirtyReplayMachine.inverseSetup,readable,Op.readable]⟩
 · simpa [inverseInstall,UniformSixCDirtyReplayMachine.inverseSetup,peak,Op.peak,Op.apply,writeNat,next,z,setPC] using safe.2
lemma inverseInstall_frame (s:State) :
 (applyBlock inverseInstall s).natHeap=s.natHeap ∧
 (applyBlock inverseInstall s).scalarHeap=s.scalarHeap ∧
 (applyBlock inverseInstall s).outputs=s.outputs ∧
 (applyBlock inverseInstall s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩
lemma inverseInstall_count (s:State) : (applyBlock inverseInstall s).natReg 894=s.natReg 894:=by
 simp [inverseInstall,UniformSixCDirtyReplayMachine.inverseSetup,applyBlock,Op.apply,writeNat,next]
attribute [local irreducible] inverseInstall

/-- The descending body regenerates one actual forward color from Height,
then literal683 itself reverses/negates its rows and generates its packing.
The input coefficient banks and ordinary allocation bases are the only scalar
preparation contracts; no inverse rows/count/permutation/action are supplied. -/
theorem inverse_execution {p:UniformChunkMatchingPreparation.Parameters} {B R n:ℕ}
 (x:Fin n→ℂ) (W:List (ShearCode ℕ R))
 (l:UniformChunkMatchingPreparation.Layout p B) (c:UniformSixCDirtyReplayMachine.Config)
 (rowEq:c.inverse.forward=p.mapped) (volume:c.inverse.packing.total=p.radix)
 (dom:UniformChunkMatchingPreparation.CodesDomain p W)
 (il:UniformSixCInverseMatchingPreparation.Layout c.inverse
  (UniformSixCDirtyReplayMachine.physicalWord l W dom).length R B)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (good:∀row∈W,UniformMatchingCoefficientValueBridge.ForwardLeaf p.height.K row.coefficient)
 (bank:Fin R→ℂ) (v:Fin c.inverse.packing.total→Scalar) (s:State)
 (head:UniformChunkMatchingPreparation.Header p s) (args:UniformSixCDirtyReplayMachine.Header c s)
 (size:W.length≤2*UniformCrossHeightPreparationMachine.gates p.height)
 (record:UniformCrossHeightPreparationMachine.Record p.height p.depth W.length s)
 (table:UniformCrossShearTableMachine.Table (UniformCrossHeightPreparationMachine.rowBase p.height p.depth)
  (W.map (UniformCrossShearTableMachine.shiftedRow 0
   (UniformCrossShearTableMachine.locations R c.inverse.positive c.inverse.negative c.inverse.constants))) s)
 (colors:∀i:Fin W.length,s.natHeap (UniformCrossHeightPreparationMachine.colorBase p.height p.depth+i.val)=
  some (UniformChunkMatchingPreparation.colors W i.val))
 (source:UniformSectorPackingMachine.SourceReady c.inverse.packing v s)
 (src:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (pc:s.pc=0) (bound:WordBound B s) (code:918≤B) :
 ∃ticks u middle,ticks≤4*p.height.K+630*p.radix+213 ∧
 BoundedExecution inverseProgram n x B s ticks u ∧ u.pc=917 ∧
 UniformSixCInverseMatchingPreparation.Result (K:=p.height.K) c.inverse
  (UniformSixCDirtyReplayMachine.physicalWord l W dom)
  (UniformSixCInverseMatchingPreparation.reverse_matching _
   (UniformSixCDirtyReplayMachine.physicalWord_matching l W dom degree))
  (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total _
   (by rw [volume];exact UniformSixCDirtyReplayMachine.physicalWord_range l W dom))
  il.radix bank v middle (setPC u 682) ∧
 (∀q,3001≤q→u.natReg q=s.natReg q) ∧
 (∀q,readonly q=true→u.natReg q=s.natReg q) ∧
 (∀q,(q<p.borrowed ∨ p.axis+4≤q)→
  (q<c.inverse.inverseRows ∨ c.inverse.axis+4≤q)→
  (q<c.inverse.packing.suffix ∨ c.inverse.packing.suffix+c.inverse.packing.ell+1≤q)→
  (q<c.inverse.packing.stack ∨ c.inverse.packing.stack+9*c.inverse.packing.ell≤q)→
  (q<c.inverse.packing.inverse ∨ c.inverse.packing.inverse+c.inverse.packing.total≤q)→u.natHeap q=s.natHeap q) ∧
 (∀q,UniformPackedMatchingShearMachine.HeapStable c.inverse.packed q→u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 let W':=UniformSixCDirtyReplayMachine.physicalWord l W dom
 let hm:=UniformSixCDirtyReplayMachine.physicalWord_matching l W dom degree
 have hr:UniformMatchingAxisTableMachine.InRange c.inverse.packing.total
  (UniformSixCInverseMatchingPreparation.forwardEdges W'):=by
  rw [volume];exact UniformSixCDirtyReplayMachine.physicalWord_range l W dom
 let loc:=UniformCrossShearTableMachine.locations R c.inverse.positive c.inverse.negative c.inverse.constants
 obtain ⟨t1,a,cost,run1,ah,count,ar,aw,ap,rows,outside,frame⟩:=
  UniformChunkMatchingPreparation.execution (n:=n) (x:=x) W loc s l head size record table colors dom degree pc bound
 have first:=UniformBoundedAssembly.boundedExecution_placed chunk_code
  (by rw [UniformChunkMatchingPreparation.program_length];omega) (by omega) run1
 rw [show placed 0 s=s by simp [placed]] at first
 let b:=setPC a 215
 have bh:UniformSixCDirtyReplayMachine.Header c b:=args.transport (by
  intro q lo hi;exact frame.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega))
 have safe:=inverseInstall_safe B b first.final_bound (by omega)
 have install:=block_runs inverseInstall inverseProgram 215 n B x b inverseInstall_code rfl
  first.final_bound (by rw [inverseInstall_length];omega) safe.1 safe.2
 let d:=applyBlock inverseInstall b
 have dp:d.pc=234:=by rw [UniformTensorMonomialMachine.applyBlock_pc,inverseInstall_length];rfl
 let e:=setPC d 0
 have eb:WordBound B e:=changePC_bound B d 0 install.final_bound (by omega)
 have eh:UniformSixCInverseMatchingPreparation.Header c.inverse e:=by
  exact (inverseInstall_args c b bh).transport (fun _ _ _=>rfl)
 have ec:e.natReg 894=W'.length:=by
  change (applyBlock inverseInstall b).natReg 894=W'.length
  rw [inverseInstall_count,UniformSixCDirtyReplayMachine.physicalWord_length];exact count
 have er:UniformInverseShearTableMachine.Rows c.inverse.forward
  (UniformSixCInverseMatchingPreparation.forwardRows c.inverse.positive c.inverse.negative c.inverse.constants W') e:=by
  rw [rowEq,UniformSixCDirtyReplayMachine.physicalWord_rows]
  intro i hi
  change d.natHeap _=some _ ∧ d.natHeap _=some _ ∧ d.natHeap _=some _
  rw [(inverseInstall_frame b).1];exact rows i hi
 have es:UniformMatchingConjugateLoadMachine.Sources p.height.K c.inverse.positive c.inverse.negative
  c.inverse.constants c.inverse.conjugates bank e:=by
  constructor
  · intro i;change d.scalarHeap _=_;rw [(inverseInstall_frame b).2.1];change a.scalarHeap _=_;rw [frame.1];exact src.positive i
  · intro i;change d.scalarHeap _=_;rw [(inverseInstall_frame b).2.1];change a.scalarHeap _=_;rw [frame.1];exact src.negative i
  · intro i;change d.scalarHeap _=_;rw [(inverseInstall_frame b).2.1];change a.scalarHeap _=_;rw [frame.1];exact src.conjugate i
  · intro i hi;change d.scalarHeap _=_;rw [(inverseInstall_frame b).2.1];change a.scalarHeap _=_;rw [frame.1];exact src.constants i hi
 have ehc:UniformHadamardPairMachine.Constants e:=by
  unfold UniformHadamardPairMachine.Constants
  rw [show e.scalarHeap=d.scalarHeap from rfl,(inverseInstall_frame b).2.1];change UniformHadamardPairMachine.Constants a;unfold UniformHadamardPairMachine.Constants;rw [frame.1];exact constants
 have ed:UniformSectorPackingMachine.SourceReady c.inverse.packing v e:=by
  intro i;change d.scalarHeap _=_;rw [(inverseInstall_frame b).2.1];change a.scalarHeap _=_;rw [frame.1];exact source i
 obtain ⟨t2,z,cost2,run2,res⟩:=UniformSixCInverseMatchingPreparation.execution x c.inverse W' il hm hr
  bank v e eh ec er (UniformSixCDirtyReplayMachine.physicalWord_leaf l W dom good) es ehc ed rfl eb
 have second:=UniformBoundedAssembly.boundedExecution_placed inverse_code
  (by rw [UniformSixCInverseMatchingPreparation.program_length];omega) (by omega) run2
 rw [show placed 234 e=d by change {d with pc:=234}=d;rw [←dp]] at second
 let u:=setPC z 917
 have halt:BoundedExecution inverseProgram n x B u 1 u:=.halt second.final_bound
  (by simp [step,u,setPC,inverse_halt_at])
 have result:UniformSixCInverseMatchingPreparation.Result (K:=p.height.K) c.inverse W'
  (UniformSixCInverseMatchingPreparation.reverse_matching W' hm)
  (UniformSixCInverseMatchingPreparation.reverse_range c.inverse.packing.total W' hr)
  il.radix bank v e (setPC u 682):=by
  rcases res with ⟨hpc,hheader,hcount,hdest,hpacked,hcoef,hconst,hnat,hout,hroot,hsreg,hheap,houtside⟩
  exact ⟨rfl,hheader.transport (fun _ _ _=>rfl),hcount,hdest,hpacked,
   ⟨hcoef.positive,hcoef.negative,hcoef.conjugate,hcoef.constants⟩,hconst,hnat,hout,hroot,hsreg,hheap,houtside⟩
 refine ⟨t1+19+t2+1,u,e,?_,?_,rfl,result,?_,?_,?_,?_,?_,?_⟩
 · have linear:=UniformSixCInverseMatchingPreparation.runtime_linear il
   change UniformSixCInverseMatchingPreparation.runtimeBudget c.inverse W'≤450*c.inverse.packing.total+101 at linear
   rw [volume] at linear;omega
 · simpa only [inverseInstall_length,Nat.add_assoc] using first.executes (install.executes (second.executes halt))
 · intro q lo
   exact (res.nats q (by unfold UniformSixCInverseMatchingPreparation.KeepNat;omega) (by omega)).trans
    ((inverseInstall_high b q lo).trans (frame.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega)))
 · intro q read
   have range:=read
   simp only [readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
   have keep:=UniformNewtonTableMachine.Executes.keeps_nat run2.executes (inverse_keeps_readonly q read)
   have setupEq:(applyBlock inverseInstall b).natReg q=b.natReg q:=by
    unfold inverseInstall
    simp (disch:=omega) [UniformSixCDirtyReplayMachine.inverseSetup,applyBlock,Op.apply,writeNat,next]
   exact keep.trans (setupEq.trans (frame.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega)))
 · intro q firstRange nextRange suffix stack inv
   exact (res.natOutside q nextRange suffix stack inv).trans
    ((congrFun (inverseInstall_frame b).1 q).trans (outside q firstRange))
 · intro q stable
   exact (res.scalarHeap q stable).trans ((congrFun (inverseInstall_frame b).2.1 q).trans (congrFun frame.1 q))
 · exact res.outputs.trans ((inverseInstall_frame b).2.2.1.trans frame.2.2.1)
 · exact res.rootOrders.trans ((inverseInstall_frame b).2.2.2.trans frame.2.2.2.1)

end
end ExactFourierCircuits.UniformSixCDepthColorController
