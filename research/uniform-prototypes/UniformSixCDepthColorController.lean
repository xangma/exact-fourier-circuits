import UniformSixCDirtyReplayMachine

set_option autoImplicit false

/-! Work-in-progress controller foundation. The first continuous body derives
all matching geometry and packed data, then executes the real six-C loop.
The outer ascending/descending cursor and the full six phases are not yet proved. -/
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
 (∀q,3001≤q→q≤3011→u.natReg q=s.natReg q) ∧
 (∀q,(q<p.borrowed ∨ l.packing.inverse+l.packing.total≤q)→u.natHeap q=s.natHeap q) := by
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
 refine ⟨u,ticks+12+(UniformPackedMatchingShearMachine.matchingCost (labels p W) 0 rows.length+9*l.packing.total+21)+1,?_,?_,rfl,?_,us,res.constants,?_,?_⟩
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
 · intro q lo hi
   exact (res.frame.natReg q (by unfold UniformPackedMatchingShearMachine.NatStable;omega)).trans
    ((UniformSixCDirtyReplayMachine.forwardSetup_high b q lo).trans
     (post.frame.2.2.1 q (by unfold UniformMatchingPackingPreparation.Protected UniformChunkMatchingPreparation.Protected;omega)))
 · intro q hq
   exact (congrFun res.frame.natHeap q).trans (post.outside q hq)

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

end
end ExactFourierCircuits.UniformSixCDepthColorController
