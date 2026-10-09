import UniformForwardMatchingFactorChunk
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
lemma row_count_bound (c:Config) (l:Layout c B) (ha he):
 (rows c l ha he).length≤2*UniformCrossHeightPreparationMachine.gates c.chunk.height:=by
 rw[rows_length]
 have selected:=UniformChunkMatchingPreparation.selected_count c.chunk (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
 have bound:=UniformCrossHeightPreparationMachine.bucket_length
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  c.chunk.height.enabled c.chunk.depth
 exact selected.trans (by simpa only[UniformChunkMatchingPreparation.crossWord,UniformCrossHeightPreparationMachine.cross_size c.chunk.height ha he] using bound)
lemma original_range (c:Config) (l:Layout c B) (ha he):
 ∀r∈originalRows c l ha he,r.dst<c.ambient ∧r.src<c.ambient:=by
 intro r hr
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hr
 let j:Fin (rows c l ha he).length:=⟨i,by simpa only[rows,originalRows,List.length_map] using hi⟩
 have h:=(rows_geometry c l ha he).1 j
 simp only[rows,List.getElem_map,UniformTranslatedMatchingRows.translated] at h
 change c.offset+((originalRows c l ha he)[i]'hi).dst<c.ambient ∧
  c.offset+((originalRows c l ha he)[i]'hi).src<c.ambient at h
 rw[eq] at h;constructor <;>omega
structure AfterTranslation (c:Config) (l:Layout c B) (ha he) (s u:State):Prop where
 table:UniformCrossShearTableMachine.Table c.translated (rows c l ha he) u
 scalar:u.scalarHeap=s.scalarHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 high:∀q,4410≤q → q≤4429 → u.natReg q=s.natReg q
 zero:u.natReg 4430=0
 count:u.natReg 894=(rows c l ha he).length
 positive:u.natReg 1060=c.chunk.height.C
 constants:u.natReg 1062=c.chunk.height.P
 saved:∀q,100≤q → q≤106 → u.natReg q=s.natReg q
 natPrefix:∀q,q<c.chunk.borrowed → u.natHeap q=s.natHeap q
lemma translate_execution {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n → ℂ)
 (s a:State) (args:Header c s) (ap:a.pc=238) (h:AfterChunk c l ha he s a) (wb:WordBound B a):∃u,
 BoundedRuns program n x B a (19*(rows c l ha he).length+9) u ∧u.pc=265 ∧
 AfterTranslation c l ha he s u:=by
 have safe:=translationSetup_safe h.zero wb
 have start:=block_runs translationSetup program 238 n B x a translationSetup_code ap wb
  (by rw[translationSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock translationSetup a
 have bp:b.pc=242:=by rw[applyBlock_pc,ap,translationSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have hh:∀q,4410≤q → q≤4429 → ready.natReg q=s.natReg q:=by
  intro q lo hi
  exact (translationSetup_nat a q (Or.inl (by omega))).trans (h.high q lo hi)
 have c0:ready.natReg 4990=(originalRows c l ha he).length:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.count,
   rows,originalRows,List.length_map]
 have ca:ready.natReg 4991=c.chunk.mapped:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.header.mapped]
 have cd:ready.natReg 4992=c.translated:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4422 (by omega) (by omega),args.translated]
 have co:ready.natReg 4993=c.offset:=by
  simp[ready,b,setPC,translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4423 (by omega) (by omega),args.offset]
 have src:UniformCrossShearTableMachine.Table c.chunk.mapped (originalRows c l ha he) ready:=h.table
 have len:(originalRows c l ha he).length=(rows c l ha he).length:=by
  simp only[rows,originalRows,List.length_map]
 have mBound:=row_count_bound c l ha he
 have mappedBelow:c.chunk.mapped+3*(originalRows c l ha he).length≤c.translated:=by
  have l0:=l.chunk.mappedFresh;have l1:=l.chunk.permutationFresh;have l2:=l.chunk.widthsFresh
  have l3:=l.chunk.markersFresh;have l4:=l.translatedFresh
  rw[len];omega
 have db:c.translated+3*(originalRows c l ha he).length≤B:=by
  rw[len];have:=l.translatedBound;omega
 have extent:c.offset+c.ambient≤B:=by
  have:=l.poolBound;have:=l.extent;omega
 obtain ⟨z,run,table,_,frame,out,zp⟩:=UniformTranslatedMatchingRows.execution n B
  c.chunk.mapped c.translated c.offset c.ambient (originalRows c l ha he) x ready rfl c0 ca cd co
  src (original_range c l ha he) mappedBelow (by have:=l.code;omega)
  (by omega) db extent rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed translation_code
  (by rw[UniformTranslatedMatchingRows.program_length];have:=l.code;omega)
  (by have:=l.code;omega) run
 rw[show placed 242 ready=b by change {b with pc:=242}=b;rw[←bp]] at moved
 let u:=setPC z 265
 have high:∀q,4410≤q → q≤4429 → u.natReg q=s.natReg q:=by
  intro q lo hi;exact (frame.2.2.2.2 q (Or.inl (by omega))).trans (hh q lo hi)
 have zero:u.natReg 4430=0:=by
  exact (frame.2.2.2.2 4430 (Or.inl (by omega))).trans
   ((translationSetup_nat a 4430 (Or.inl (by omega))).trans h.zero)
 have count:u.natReg 894=(rows c l ha he).length:=by
  exact (frame.2.2.2.2 894 (Or.inl (by omega))).trans
   ((translationSetup_nat a 894 (Or.inl (by omega))).trans h.count)
 have pos:u.natReg 1060=c.chunk.height.C:=by
  exact (frame.2.2.2.2 1060 (Or.inl (by omega))).trans
   ((translationSetup_nat a 1060 (Or.inl (by omega))).trans h.header.height.coefficients)
 have constants:u.natReg 1062=c.chunk.height.P:=by
  exact (frame.2.2.2.2 1062 (Or.inl (by omega))).trans
   ((translationSetup_nat a 1062 (Or.inl (by omega))).trans h.header.height.constants)
 refine ⟨u,?_,rfl,⟨table,?_,?_,?_,high,zero,count,pos,constants,?_,?_⟩⟩
 · convert start.trans moved using 1
   · simp only[translationSetup_length,len]
     omega
   · rfl
 · exact frame.1.trans ((translationSetup_heap a).2.1.trans h.scalar)
 · exact frame.2.2.1.trans ((translationSetup_heap a).2.2.1.trans h.outputs)
 · exact frame.2.2.2.1.trans ((translationSetup_heap a).2.2.2.trans h.roots)
 · intro q lo hi
   exact (frame.2.2.2.2 q (Or.inl (by omega))).trans
    ((translationSetup_nat a q (Or.inl (by omega))).trans (h.saved q lo hi))
 · intro q hq
   have below:c.chunk.borrowed≤c.translated:=by
    have l0:=l.chunk.borrowFresh;have l1:=l.chunk.selectedFresh;have l2:=l.chunk.ordinalFresh
    have l3:=l.chunk.mappedFresh;have l4:=l.chunk.permutationFresh;have l5:=l.chunk.widthsFresh
    have l6:=l.chunk.markersFresh;have l7:=l.translatedFresh;omega
   exact (out q (Or.inl (by omega))).trans (h.outside q (Or.inl hq))
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
