import UniformProducedSectorBatchPreparation
import UniformAllSectorTransposeMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedSectorTransposePreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
/-- The actual158 producer, two charged directory-header moves, then the
actual41 complete role/sector transpose. No generated directory/table/count
is a physical entry premise. -/
def setup:List Op:=[.literal 4572 0,.add 4532 4441 4572]
def programFor (W:ℕ):Program:=(UniformProducedSectorBatchPreparation.programFor W).map (relocate 0 158)++
 setup.map Op.code++(UniformAllSectorTransposeMachine.programFor W false).map (relocate 160 201)++[.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=202:=by
 simp only[programFor,List.length_append,List.length_map,
  UniformProducedSectorBatchPreparation.program_length,
  UniformAllSectorTransposeMachine.program_length,List.length_singleton]
 rfl
lemma producer_code (W:ℕ):CodeAt (UniformProducedSectorBatchPreparation.programFor W) (programFor W) 0 158:=by
 exact UniformRankCrossPreparationMachine.segment_code []
  (setup.map Op.code++(UniformAllSectorTransposeMachine.programFor W false).map (relocate 160 201)++[.halt]) _ 0 158 rfl
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 158:=by
 intro i hi;change i < 2 at hi;interval_cases i <;>rfl
lemma transpose_code (W:ℕ):CodeAt (UniformAllSectorTransposeMachine.programFor W false) (programFor W) 160 201:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((UniformProducedSectorBatchPreparation.programFor W).map (relocate 0 158)++setup.map Op.code) [.halt] _ 160 201 rfl
lemma halt_at (W:ℕ):(programFor W)[201]?=some .halt:=rfl

def writesArguments:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>[4441,4530,4531].contains d
 | _=>false
lemma relocate_arguments (b ret:ℕ) (i:Instruction):writesArguments (relocate b ret i)=writesArguments i:=by cases i <;>rfl
lemma producer_arguments (W:ℕ):(UniformProducedSectorBatchPreparation.programFor W).all (fun i=> !writesArguments i)=true:=by
 simp only[UniformProducedSectorBatchPreparation.programFor,List.all_append,List.all_map,Function.comp_def,relocate_arguments,
  UniformMultiAxisSectorMetadataPreparation.program,UniformSectorBatchDirectoryMachine.programFor,
  UniformSectorBatchDirectoryMachine.boot,UniformSectorBatchDirectoryMachine.body,List.all_cons,List.all_nil]
 simp only[Op.code,writesArguments]
 decide
lemma producer_keeps_argument (W q:ℕ) (hq:q∈([4441,4530,4531]:List ℕ)):
 ∀i∈UniformProducedSectorBatchPreparation.programFor W,UniformNewtonTableMachine.KeepsNat q i:=by
 intro i mem
 have free:=List.all_eq_true.mp (producer_arguments W) i mem
 cases i <;>simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals intro equal;subst_vars
 all_goals simp[writesArguments,hq] at free
lemma execution_arguments {W B n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution (UniformProducedSectorBatchPreparation.programFor W) n x B s t u):
 ∀q∈([4441,4530,4531]:List ℕ),u.natReg q=s.natReg q:=by
 intro q hq
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (producer_keeps_argument W q hq)

/-- Continuous physical axes/widths→generated sectors→all W child-layout
copies. Source data remain an honest present contiguous role-bank input. -/
theorem execution {W n a:ℕ} (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout)
 (g:UniformAllSectorTransposeMachine.Geometry W false
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)))
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (sameB:g.B=L.B) (sameVolume:g.volume=L.total)
 (hlen:as.length=L.ell) (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows:UniformSectorPackingMachine.Rows as 0 a s) (widths:UniformSectorPackingMachine.Widths as s)
 (below:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep:a+4*L.ell ≤ L.rows) (entry:g.directory+5*L.total ≤ L.B)
 (directory:L.directory+3*L.total ≤ g.directory) (code:202 ≤ L.B) (pc:s.pc=0)
 (count:s.natReg 102+1=L.ell) (ha:s.natReg 3201=a) (hd:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hq:s.natReg 3215=L.directory)
 (he:s.natReg 4441=g.directory) (hb:s.natReg 4442=g.buffer)
 (native:s.natReg 4531=g.native) (volume:s.natReg 4530=g.volume)
 (source:UniformAllSectorTransposeMachine.Source g v s) (wb:WordBound L.B s):
 ∃u,BoundedExecution (programFor W) n x L.B s
  (UniformSectorMetadataMachine.treeCost
    (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length+
   7*W*L.total+50) u ∧u.pc=201 ∧
 UniformAllSectorTransposeMachine.Filled g v
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length u ∧
 UniformAllSectorTransposeMachine.Table g u ∧
 u.natReg 464=(UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length ∧
 (∀q,100 ≤ q→q ≤ 106→u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < L.rows→u.natHeap q=s.natHeap q) ∧
 UniformScalarCopyMachine.Outside g.buffer (W*g.volume) s.scalarHeap u:=by
 let xs:=UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)
 have buffer:g.buffer+W*L.total ≤ L.B:=by simpa only[sameB,sameVolume] using g.bufferFit
 have roles:W ≤ L.B:=by simpa only[sameB] using g.roles
 obtain ⟨t,run,tp,written,_oldTable,num,ret,low⟩:=UniformProducedSectorBatchPreparation.execution as L n a x s
  hlen hvolume rows widths below sep entry buffer directory roles (by omega) pc count ha hd hs ht hq he hb wb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (producer_code W)
  (by rw[UniformProducedSectorBatchPreparation.program_length];omega) (by omega) run
 rw[show placed 0 s=s by cases s;simp[placed]] at moved
 have args:=execution_arguments run
 have td:t.natReg 4441=g.directory:=(args 4441 (by simp)).trans he
 have bound:g.directory ≤ L.B:=by have:=g.entry;rw[sameB] at this;omega
 let ready:=setPC t 158
 have safe:readable setup ready ∧peak setup ready ≤ L.B:=by
  simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,ready,setPC,td]
  omega
 have second:=block_runs setup (programFor W) 158 n L.B x ready (setup_code W) rfl moved.final_bound
  (by change 158+2 ≤ L.B;omega) safe.1 safe.2
 let b:=applyBlock setup ready
 have bp:b.pc=160:=by rw[applyBlock_pc];rfl
 let input:=setPC b 0
 have header:UniformAllSectorTransposeMachine.Header g input:=by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [input,b,ready,setPC,setup,applyBlock,Op.apply,writeNat,next] using (args 4530 (by simp)).trans volume
  · simpa [input,b,ready,setPC,setup,applyBlock,Op.apply,writeNat,next] using (args 4531 (by simp)).trans native
  · simp[input,b,ready,setPC,setup,applyBlock,Op.apply,writeNat,next,td]
  · simpa [input,b,ready,setPC,setup,applyBlock,Op.apply,writeNat,next] using num
 have table:UniformAllSectorTransposeMachine.Table g input:=by
  intro i hi
  exact written i hi hi
 have src:UniformAllSectorTransposeMachine.Source g v input:=by
  intro i hi r hr j hj
  exact (congrFun ret.1 _).trans (source i hi r hr j hj)
 have inputBound:WordBound g.B input:=by
  rw[sameB]
  exact changePC_bound L.B b 0 second.final_bound (by omega)
 obtain ⟨u,transpose,up,filled,frame,out⟩:=UniformAllSectorTransposeMachine.execution g v x input header table src rfl inputBound
 have transpose':BoundedExecution (UniformAllSectorTransposeMachine.programFor W false) n x L.B input
  (7*W*(xs.map UniformSectorPacking.BlockState.width).sum+(12*W+20)*xs.length+5) u:=by
  simpa only[sameB,xs] using transpose
 have finalRun:=UniformBoundedAssembly.boundedExecution_placed (transpose_code W)
  (by rw[UniformAllSectorTransposeMachine.program_length];omega) (by omega) transpose'
 rw[UniformMultiAxisSectorMetadataPreparation.placed_zero b 160 bp] at finalRun
 let z:=setPC u 201
 have stop:BoundedExecution (programFor W) n x L.B z 1 z:=.halt finalRun.final_bound
  (by simp[step,z,setPC,halt_at])
 refine ⟨z,?_,rfl,filled,?_,?_,?_,frame.2.1.trans ret.2.2.1,frame.2.2.1.trans ret.2.2.2.1,?_,?_⟩
 · convert moved.executes (second.executes (finalRun.executes stop)) using 1
   have widthSum:(xs.map UniformSectorPacking.BlockState.width).sum=L.total:=by
    simpa only[xs,hvolume] using UniformSectorBatchDirectoryMachine.sector_width_sum (UniformSectorPackingMachine.physicalAxes as)
   rw[widthSum]
   dsimp[xs]
   simp only[setup,List.length_cons,List.length_nil]
   ring
 · intro i hi
   simpa only[z,setPC,UniformSectorBatchDirectoryMachine.BatchCell,frame.1] using table i hi
 · exact (frame.2.2.2.2 464 (by omega) (by omega) (by omega) (by omega)).trans header.count
 · intro q hlo hhi
   have tail:=frame.2.2.2.2 q (by omega) (by omega) (by omega) (by omega)
   have middle:input.natReg q=t.natReg q:=by
    simp (disch:=omega)[input,b,ready,setPC,setup,applyBlock,Op.apply,writeNat,next]
   exact tail.trans (middle.trans (ret.2.2.2.2 q hlo hhi))
 · intro q hq
   exact (congrFun frame.1 q).trans (low q hq)
 · intro q hq
   exact (out q hq).trans (congrFun ret.1 q)
end
end ExactFourierCircuits.UniformProducedSectorTransposePreparation
