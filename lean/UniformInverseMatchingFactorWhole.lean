import UniformInverseMatchingFactorResult
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
def Slot (A:ℕ) (p:UniformChunkMatchingPreparation.Parameters) (s:State):Prop:=
 s.natHeap A=some 0 ∧s.natHeap (A+1)=some (if p.height.enabled then 1 else 0) ∧
 s.natHeap (A+2)=some 1 ∧s.natHeap (A+3)=some p.depth ∧s.natHeap (A+4)=some p.color
def prefixProgram:Program:=UniformForwardMatchingFactorPreparation.beforeTranslate++
 UniformTranslatedMatchingRows.program.map (relocate 242 265)
def wholeProgram:Program:=prefixProgram++program.map (relocate 265 458)++[.halt]
lemma prefixProgram_length:prefixProgram.length=265:=by
 simp[prefixProgram,UniformForwardMatchingFactorPreparation.beforeTranslate_length,UniformTranslatedMatchingRows.program_length]
lemma wholeProgram_length:wholeProgram.length=459:=by simp[wholeProgram,prefixProgram_length,program_length]
lemma continuation_code:CodeAt program wholeProgram 265 458:=
 UniformChunkRowTableMachine.segment_code prefixProgram [.halt] _ 265 458 prefixProgram_length
lemma whole_halt:wholeProgram[458]?=some .halt:=by
 rw[wholeProgram,List.getElem?_append_right (by simp[prefixProgram_length,program_length])]
 simp only[List.length_append,List.length_map,prefixProgram_length,program_length];rfl
lemma whole_chunkSetup_code:BlockAt UniformForwardMatchingFactorPreparation.chunkSetup wholeProgram 0:=by
 intro i hi;change i<23 at hi;interval_cases i <;>rfl
lemma whole_translationSetup_code:BlockAt UniformForwardMatchingFactorPreparation.translationSetup wholeProgram 238:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma whole_chunk_code:CodeAt UniformChunkMatchingPreparation.program wholeProgram 23 238:=by
 let after:=UniformForwardMatchingFactorPreparation.translationSetup.map Op.code++
  UniformTranslatedMatchingRows.program.map (relocate 242 265)++program.map (relocate 265 458)++[.halt]
 have eq:wholeProgram=UniformForwardMatchingFactorPreparation.chunkSetup.map Op.code++
  UniformChunkMatchingPreparation.program.map (relocate 23 238)++after:=by
  simp[wholeProgram,prefixProgram,UniformForwardMatchingFactorPreparation.beforeTranslate,after,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code _ after _ 23 238
  (by rw[List.length_map,UniformForwardMatchingFactorPreparation.chunkSetup_length])
lemma whole_translation_code:CodeAt UniformTranslatedMatchingRows.program wholeProgram 242 265:=by
 let after:=program.map (relocate 265 458)++[.halt]
 have eq:wholeProgram=UniformForwardMatchingFactorPreparation.beforeTranslate++
  UniformTranslatedMatchingRows.program.map (relocate 242 265)++after:=by
  simp only[wholeProgram,prefixProgram,after,List.append_assoc]
 rw[eq]
 exact UniformChunkRowTableMachine.segment_code UniformForwardMatchingFactorPreparation.beforeTranslate
  after _ 242 265 UniformForwardMatchingFactorPreparation.beforeTranslate_length
lemma setup_header {c:F.Config} {s:State} (h:UniformForwardMatchingFactorPreparation.Header c s) (slot:Slot c.slot c.chunk s):
 UniformChunkMatchingPreparation.Header c.chunk (applyBlock UniformForwardMatchingFactorPreparation.chunkSetup s):=by
 rcases slot with ⟨bc,en,inv,dep,col⟩
 constructor
 · constructor <;>simp[UniformForwardMatchingFactorPreparation.chunkSetup,applyBlock,Op.apply,writeNat,next,h.slot,
    h.height.exponent,h.height.targets,h.height.inputs,h.height.tape,h.height.order,
    h.height.sourceDirectory,h.height.rows,h.height.colors,h.height.palette,h.height.directory,
    h.height.coefficients,h.height.constants,en,Nat.add_assoc]
 all_goals simp[UniformForwardMatchingFactorPreparation.chunkSetup,applyBlock,Op.apply,writeNat,next,h.radix,h.source,h.target,h.borrowed,
  h.selected,h.ordinals,h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,dep,col,Nat.add_assoc]
lemma setup_safe {c:F.Config} {s:State} {B:ℕ} (h:UniformForwardMatchingFactorPreparation.Header c s) (slot:Slot c.slot c.chunk s)
 (hs:WordBound B s) (_code:415≤B):readable UniformForwardMatchingFactorPreparation.chunkSetup s ∧peak UniformForwardMatchingFactorPreparation.chunkSetup s≤B:=by
 rcases slot with ⟨bc,en,inv,dep,col⟩
 have bcB:=hs.2.2.1 _ _ bc
 have enB:=hs.2.2.1 _ _ en
 have invB:=hs.2.2.1 _ _ inv
 have depB:=hs.2.2.1 _ _ dep
 have colB:=hs.2.2.1 _ _ col
 have regs:=hs.2.1
 have rb:=regs 4410;have sb:=regs 4411;have tb:=regs 4412;have bb:=regs 4413
 have selb:=regs 4414;have ob:=regs 4415;have mb:=regs 4416;have pb:=regs 4417
 have wb:=regs 4418;have vb:=regs 4419;have ab:=regs 4420
 simp only[h.radix,h.source,h.target,h.borrowed,h.selected,h.ordinals,h.mapped,
  h.permutation,h.widths,h.markers,h.axis] at rb sb tb bb selb ob mb pb wb vb ab
 constructor
 · simp[UniformForwardMatchingFactorPreparation.chunkSetup,readable,Op.readable,Op.apply,writeNat,next,h.slot,bc,en,inv,dep,col,Nat.add_assoc]
 · simp[UniformForwardMatchingFactorPreparation.chunkSetup,peak,Op.peak,Op.apply,writeNat,next,h.radix,h.source,h.target,h.borrowed,
    h.selected,h.ordinals,h.mapped,h.permutation,h.widths,h.markers,h.axis,h.slot,bc,en,inv,dep,col,Nat.add_assoc]
   omega
lemma setup_inverse (s:State):
 (applyBlock UniformForwardMatchingFactorPreparation.chunkSetup s).natReg 4460=s.natReg 4460:=
 UniformForwardMatchingFactorPreparation.setup_nat s 4460 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
lemma chunk_execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (x:Fin n→ℂ) (s:State)
 (h:UniformForwardMatchingFactorPreparation.Header c s) (slot:Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedRuns wholeProgram n x B s t u ∧t≤4*c.chunk.height.K+180*c.chunk.radix+115 ∧u.pc=238 ∧
 UniformForwardMatchingFactorPreparation.AfterChunk c l ha he s u ∧u.natReg 4460=s.natReg 4460:=by
 have safe:=setup_safe h slot wb l.code
 have first:=block_runs UniformForwardMatchingFactorPreparation.chunkSetup wholeProgram 0 n B x s whole_chunkSetup_code pc wb
  (by rw[UniformForwardMatchingFactorPreparation.chunkSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock UniformForwardMatchingFactorPreparation.chunkSetup s
 have bp:b.pc=23:=by rw[applyBlock_pc,pc,UniformForwardMatchingFactorPreparation.chunkSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 first.final_bound (by omega)
 have head:UniformChunkMatchingPreparation.Header c.chunk ready:=(setup_header h slot).withPC 0
 have source:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) ready:=processed
 obtain ⟨t,u,cost,run,uh,count,_,_,_,table,proc,out,frame⟩:=
  UniformChunkMatchingPreparation.cross_execution c.chunk c.negative B n x ready ha he
   l.chunk head source rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed whole_chunk_code
  (by rw[UniformChunkMatchingPreparation.program_length];have:=l.code;omega) (by have:=l.code;omega) run
 rw[show placed 23 ready=b by change {b with pc:=23}=b;rw[←bp]] at placedRun
 let z:=setPC u 238
 have pre:UniformForwardMatchingFactorPreparation.PreludeFrame s ready:=(UniformForwardMatchingFactorPreparation.PreludeFrame.setup s).withPC 0
 have result:=UniformForwardMatchingFactorPreparation.after_chunk (l:=l) pre uh count table proc out frame
 refine ⟨z,23+t,?_,by omega,rfl,result.withPC 238,?_⟩
 · simpa only[UniformForwardMatchingFactorPreparation.chunkSetup_length,z,setPC] using first.trans placedRun
 · have a:=setup_inverse s
   have step:u.natReg 4460=ready.natReg 4460:=UniformForwardMatchingFactorPreparation.chunk_high frame 4460 (by omega)
   simp only[ready,b,setPC] at step
   exact step.trans a
lemma translate_execution {n:ℕ} (c:F.Config) (l:F.Layout c B) (ha he) (x:Fin n → ℂ)
 (s a:State) (args:UniformForwardMatchingFactorPreparation.Header c s) (ap:a.pc=238) (h:UniformForwardMatchingFactorPreparation.AfterChunk c l ha he s a) (wb:WordBound B a):∃u,
 BoundedRuns wholeProgram n x B a (19*(UniformForwardMatchingFactorPreparation.rows c l ha he).length+9) u ∧u.pc=265 ∧
 UniformForwardMatchingFactorPreparation.AfterTranslation c l ha he s u ∧u.natReg 4460=a.natReg 4460:=by
 have safe:=UniformForwardMatchingFactorPreparation.translationSetup_safe h.zero wb
 have start:=block_runs UniformForwardMatchingFactorPreparation.translationSetup wholeProgram 238 n B x a whole_translationSetup_code ap wb
  (by rw[UniformForwardMatchingFactorPreparation.translationSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock UniformForwardMatchingFactorPreparation.translationSetup a
 have bp:b.pc=242:=by rw[applyBlock_pc,ap,UniformForwardMatchingFactorPreparation.translationSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 start.final_bound (by omega)
 have hh:∀q,4410≤q → q≤4429 → ready.natReg q=s.natReg q:=by
  intro q lo hi
  exact (UniformForwardMatchingFactorPreparation.translationSetup_nat a q (Or.inl (by omega))).trans (h.high q lo hi)
 have c0:ready.natReg 4990=(UniformForwardMatchingFactorPreparation.originalRows c l ha he).length:=by
  simp[ready,b,setPC,UniformForwardMatchingFactorPreparation.translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.count,
   UniformForwardMatchingFactorPreparation.rows,UniformForwardMatchingFactorPreparation.originalRows,List.length_map]
 have ca:ready.natReg 4991=c.chunk.mapped:=by
  simp[ready,b,setPC,UniformForwardMatchingFactorPreparation.translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,h.header.mapped]
 have cd:ready.natReg 4992=c.translated:=by
  simp[ready,b,setPC,UniformForwardMatchingFactorPreparation.translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4422 (by omega) (by omega),args.translated]
 have co:ready.natReg 4993=c.offset:=by
  simp[ready,b,setPC,UniformForwardMatchingFactorPreparation.translationSetup,applyBlock,Op.apply,writeNat,next,h.zero,
   h.high 4423 (by omega) (by omega),args.offset]
 have src:UniformCrossShearTableMachine.Table c.chunk.mapped (UniformForwardMatchingFactorPreparation.originalRows c l ha he) ready:=h.table
 have len:(UniformForwardMatchingFactorPreparation.originalRows c l ha he).length=(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by
  simp only[UniformForwardMatchingFactorPreparation.rows,UniformForwardMatchingFactorPreparation.originalRows,List.length_map]
 have mBound:=UniformForwardMatchingFactorPreparation.row_count_bound c l ha he
 have mappedBelow:c.chunk.mapped+3*(UniformForwardMatchingFactorPreparation.originalRows c l ha he).length≤c.translated:=by
  have l0:=l.chunk.mappedFresh;have l1:=l.chunk.permutationFresh;have l2:=l.chunk.widthsFresh
  have l3:=l.chunk.markersFresh;have l4:=l.translatedFresh
  rw[len];omega
 have db:c.translated+3*(UniformForwardMatchingFactorPreparation.originalRows c l ha he).length≤B:=by
  rw[len];have:=l.translatedBound;omega
 have extent:c.offset+c.ambient≤B:=by
  have:=l.poolBound;have:=l.extent;omega
 obtain ⟨z,run,table,_,frame,out,zp⟩:=UniformTranslatedMatchingRows.execution n B
  c.chunk.mapped c.translated c.offset c.ambient (UniformForwardMatchingFactorPreparation.originalRows c l ha he) x ready rfl c0 ca cd co
  src (UniformForwardMatchingFactorPreparation.original_range c l ha he) mappedBelow (by have:=l.code;omega)
  (by omega) db extent rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed whole_translation_code
  (by rw[UniformTranslatedMatchingRows.program_length];have:=l.code;omega)
  (by have:=l.code;omega) run
 rw[show placed 242 ready=b by change {b with pc:=242}=b;rw[←bp]] at moved
 let u:=setPC z 265
 have high:∀q,4410≤q → q≤4429 → u.natReg q=s.natReg q:=by
  intro q lo hi;exact (frame.2.2.2.2 q (Or.inl (by omega))).trans (hh q lo hi)
 have zero:u.natReg 4430=0:=by
  exact (frame.2.2.2.2 4430 (Or.inl (by omega))).trans
   ((UniformForwardMatchingFactorPreparation.translationSetup_nat a 4430 (Or.inl (by omega))).trans h.zero)
 have count:u.natReg 894=(UniformForwardMatchingFactorPreparation.rows c l ha he).length:=by
  exact (frame.2.2.2.2 894 (Or.inl (by omega))).trans
   ((UniformForwardMatchingFactorPreparation.translationSetup_nat a 894 (Or.inl (by omega))).trans h.count)
 have pos:u.natReg 1060=c.chunk.height.C:=by
  exact (frame.2.2.2.2 1060 (Or.inl (by omega))).trans
   ((UniformForwardMatchingFactorPreparation.translationSetup_nat a 1060 (Or.inl (by omega))).trans h.header.height.coefficients)
 have constants:u.natReg 1062=c.chunk.height.P:=by
  exact (frame.2.2.2.2 1062 (Or.inl (by omega))).trans
   ((UniformForwardMatchingFactorPreparation.translationSetup_nat a 1062 (Or.inl (by omega))).trans h.header.height.constants)
 refine ⟨u,?_,rfl,⟨table,?_,?_,?_,high,zero,count,pos,constants,?_,?_⟩,?_⟩
 · convert start.trans moved using 1
   · simp only[UniformForwardMatchingFactorPreparation.translationSetup_length,len]
     omega
   · rfl
 · exact frame.1.trans ((UniformForwardMatchingFactorPreparation.translationSetup_heap a).2.1.trans h.scalar)
 · exact frame.2.2.1.trans ((UniformForwardMatchingFactorPreparation.translationSetup_heap a).2.2.1.trans h.outputs)
 · exact frame.2.2.2.1.trans ((UniformForwardMatchingFactorPreparation.translationSetup_heap a).2.2.2.trans h.roots)
 · intro q lo hi
   exact (frame.2.2.2.2 q (Or.inl (by omega))).trans
    ((UniformForwardMatchingFactorPreparation.translationSetup_nat a q (Or.inl (by omega))).trans (h.saved q lo hi))
 · intro q hq
   have below:c.chunk.borrowed≤c.translated:=by
    have l0:=l.chunk.borrowFresh;have l1:=l.chunk.selectedFresh;have l2:=l.chunk.ordinalFresh
    have l3:=l.chunk.mappedFresh;have l4:=l.chunk.permutationFresh;have l5:=l.chunk.widthsFresh
    have l6:=l.chunk.markersFresh;have l7:=l.translatedFresh;omega
   exact (out q (Or.inl (by omega))).trans (h.outside q (Or.inl hq))
 · exact (frame.2.2.2.2 4460 (Or.inl (by omega))).trans
    (UniformForwardMatchingFactorPreparation.translationSetup_nat a 4460 (Or.inl (by omega)))

end
end ExactFourierCircuits.UniformInverseMatchingFactorPreparation
