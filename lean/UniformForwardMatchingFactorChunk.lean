import UniformForwardMatchingFactorGeometry
import UniformForwardMatchingFactorFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
variable {B:ℕ}
def originalRows (c:Config) (l:Layout c B) (ha he):=
 UniformChunkMatchingPreparation.mappedRows c.chunk l.chunk.capacity
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)
  (UniformChunkMatchingPreparation.crossLocations c.chunk c.negative)
structure AfterChunk (c:Config) (l:Layout c B) (ha he) (s u:State):Prop where
 header:UniformChunkMatchingPreparation.Header c.chunk u
 count:u.natReg 894=(rows c l ha he).length
 table:UniformCrossShearTableMachine.Table c.chunk.mapped (originalRows c l ha he) u
 processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) u
 scalar:u.scalarHeap=s.scalarHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 high:∀q,4410≤q→q≤4429→u.natReg q=s.natReg q
 zero:u.natReg 4430=0
 saved:∀q,100≤q→q≤106→u.natReg q=s.natReg q
 outside:UniformChunkMatchingPreparation.Outside c.chunk s u
lemma AfterChunk.withPC {c:Config} {l:Layout c B} {ha he} {s u:State}
 (h:AfterChunk c l ha he s u) (p:ℕ):AfterChunk c l ha he s (setPC u p):=
 ⟨h.header.withPC p,h.count,h.table,h.processed,h.scalar,h.outputs,h.roots,h.high,h.zero,h.saved,h.outside⟩
lemma after_chunk {c:Config} {l:Layout c B} {ha he} {s a u:State} (pre:PreludeFrame s a)
 (h:UniformChunkMatchingPreparation.Header c.chunk u)
 (count:u.natReg 894=(UniformChunkMatchingPreparation.indices c.chunk
  (UniformChunkMatchingPreparation.crossWord c.chunk ha he)).length)
 (table:UniformCrossShearTableMachine.Table c.chunk.mapped (originalRows c l ha he) u)
 (proc:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) u)
 (out:UniformChunkMatchingPreparation.Outside c.chunk a u)
 (frame:UniformChunkMatchingPreparation.Frame a u):AfterChunk c l ha he s u:=by
 refine ⟨h,?_,table,proc,frame.1.trans pre.scalar,frame.2.2.1.trans pre.outputs,
  frame.2.2.2.1.trans pre.roots,?_,?_,?_,?_⟩
 · simpa only[rows,List.length_map,UniformPackedMatchingShearMachine.mappedRows_length] using count
 · intro q lo hi;exact (chunk_high frame q (by omega)).trans (pre.high q lo hi)
 · exact (chunk_high frame 4430 (by omega)).trans pre.zero
 · intro q lo hi;exact (UniformChunkMatchingPreparation.saved_metadata_frame frame q lo hi).trans (pre.saved q lo hi)
 · intro q hq;exact (out q hq).trans (congrArg (fun heap=>heap q) pre.natHeap)
lemma chunk_execution {n:ℕ} (c:Config) (l:Layout c B) (ha he) (x:Fin n→ℂ) (s:State)
 (h:Header c s) (slot:Slot c.slot c.chunk s)
 (processed:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) s)
 (pc:s.pc=0) (wb:WordBound B s):∃u t,
 BoundedRuns program n x B s t u ∧t≤4*c.chunk.height.K+180*c.chunk.radix+115 ∧u.pc=238 ∧
 AfterChunk c l ha he s u:=by
 have safe:=setup_safe h slot wb l.code
 have first:=block_runs chunkSetup program 0 n B x s chunkSetup_code pc wb
  (by rw[chunkSetup_length];have:=l.code;omega) safe.1 safe.2
 let b:=applyBlock chunkSetup s
 have bp:b.pc=23:=by rw[applyBlock_pc,pc,chunkSetup_length]
 let ready:=setPC b 0
 have rb:WordBound B ready:=changePC_bound B b 0 first.final_bound (by omega)
 have head:UniformChunkMatchingPreparation.Header c.chunk ready:=(setup_header h slot).withPC 0
 have source:UniformCrossHeightPreparationMachine.Processed c.chunk.height c.negative
  (UniformToeplitzCrossDAG.crossDAG c.chunk.height.K c.chunk.height.a c.chunk.height.e ha he).program
  (UniformCrossHeightPreparationMachine.height c.chunk.height) ready:=processed
 obtain ⟨t,u,cost,run,uh,count,_,_,_,table,proc,out,frame⟩:=
  UniformChunkMatchingPreparation.cross_execution c.chunk c.negative B n x ready ha he
   l.chunk head source rfl rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed chunk_code
  (by rw[UniformChunkMatchingPreparation.program_length];have:=l.code;omega) (by have:=l.code;omega) run
 rw[show placed 23 ready=b by change {b with pc:=23}=b;rw[←bp]] at placedRun
 let z:=setPC u 238
 have pre:PreludeFrame s ready:=(PreludeFrame.setup s).withPC 0
 have result:=after_chunk (l:=l) pre uh count table proc out frame
 refine ⟨z,23+t,?_,by omega,rfl,result.withPC 238⟩
 simpa only[chunkSetup_length,z,setPC] using first.trans placedRun
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
