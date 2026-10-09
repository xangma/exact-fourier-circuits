import UniformProducedSectorBatchPreparation
import UniformAllSectorPaddingMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedSectorPaddingPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
/-- The actual158 producer and actual44 padding cursor, with two charged
instructions installing its directory header. No generated table, count,
padding bank, or recursive action is an input. -/
def setup:List Op:=[.literal 4482 0,.add 4473 4441 4482]
def programFor (W:ℕ):Program:=
 (UniformProducedSectorBatchPreparation.programFor W).map (relocate 0 158)++
 setup.map Op.code++(UniformAllSectorPaddingMachine.programFor W).map (relocate 160 204)++[.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=205:=by
 simp only[programFor,List.length_append,List.length_map,
  UniformProducedSectorBatchPreparation.program_length,
  UniformAllSectorPaddingMachine.program_length,List.length_singleton];rfl
lemma metadata_code (W:ℕ):CodeAt (UniformProducedSectorBatchPreparation.programFor W)
 (programFor W) 0 158:=by
 exact UniformRankCrossPreparationMachine.segment_code []
  (setup.map Op.code++(UniformAllSectorPaddingMachine.programFor W).map (relocate 160 204)++[.halt])
  _ 0 158 rfl
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 158:=by
 intro i hi;change i < 2 at hi
 interval_cases i <;>rfl
lemma padding_code (W:ℕ):CodeAt (UniformAllSectorPaddingMachine.programFor W)
 (programFor W) 160 204:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((UniformProducedSectorBatchPreparation.programFor W).map (relocate 0 158)++setup.map Op.code)
  [.halt] _ 160 204 (by simp only[List.length_append,List.length_map,
   UniformProducedSectorBatchPreparation.program_length];rfl)
lemma halt_at (W:ℕ):(programFor W)[204]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformProducedSectorBatchPreparation.program_length,
  UniformAllSectorPaddingMachine.program_length];change 158+2+44 ≤ 204;omega)]
 simp only[List.length_append,List.length_map,UniformProducedSectorBatchPreparation.program_length,
  UniformAllSectorPaddingMachine.program_length];rfl

def writesArgument:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>[4441,4472].contains d
 | _=>false
lemma relocate_argument (b ret:ℕ) (i:Instruction):
 writesArgument (relocate b ret i)=writesArgument i:=by cases i <;>rfl
lemma metadata_arguments (W:ℕ):
 (UniformProducedSectorBatchPreparation.programFor W).all (fun i=> !writesArgument i)=true:=by
 rfl
lemma metadata_keeps_argument (W q:ℕ) (hq:q∈([4441,4472]:List ℕ)):
 ∀i∈UniformProducedSectorBatchPreparation.programFor W,UniformNewtonTableMachine.KeepsNat q i:=by
 intro i mem
 have free:=List.all_eq_true.mp (metadata_arguments W) i mem
 cases i <;>simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals intro eq;subst_vars
 all_goals simp[writesArgument,hq] at free
lemma execution_arguments {W B n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution (UniformProducedSectorBatchPreparation.programFor W) n x B s t u):
 ∀q∈([4441,4472]:List ℕ),u.natReg q=s.natReg q:=by
 intro q hq
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (metadata_keeps_argument W q hq)

/-- Produce the genuine sector partition and all W-role padding buffers from
physical axis rows and arbitrary present tagged input. Child Fourier calls are
not part of this program. -/
theorem execution {W S E A:ℕ} (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout) (n a:ℕ) (x:Fin n→ℂ)
 (v:Fin L.total→Scalar) (s:State)
 (hlen:as.length=L.ell) (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows:UniformSectorPackingMachine.Rows as 0 a s) (widths:UniformSectorPackingMachine.Widths as s)
 (below:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep:a+4*L.ell ≤ L.rows) (entry:E+5*L.total ≤ L.B) (buffer:A+W*L.total ≤ L.B)
 (old:L.directory+3*L.total ≤ E) (roles:W ≤ L.B) (positive:0 < W)
 (data:UniformSectorPaddingMachine.Source v S s) (fresh:S+L.total ≤ A)
 (code:205 ≤ L.B) (pc:s.pc=0) (count:s.natReg 102+1=L.ell)
 (ha:s.natReg 3201=a) (hd:s.natReg 3202=L.rows) (hs:s.natReg 3213=L.suffix)
 (ht:s.natReg 3214=L.stack) (hq:s.natReg 3215=L.directory)
 (he:s.natReg 4441=E) (hb:s.natReg 4442=A) (hsource:s.natReg 4472=S)
 (wb:WordBound L.B s):
 ∃u,BoundedExecution (programFor W) n x L.B s
  (UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+54*(UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length+
   (5*W+2)*L.total+50) u ∧u.pc=204 ∧
 UniformAllSectorPaddingMachine.Filled W A
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as))
  (by simpa only[UniformAllSectorPaddingMachine.Fits,hvolume] using
   UniformSectorBatchDirectoryMachine.sector_fits (UniformSectorPackingMachine.physicalAxes as))
  v (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length u ∧
 (∀q,100 ≤ q→q ≤ 106→u.natReg q=s.natReg q) ∧
 (∀q,q < L.rows→u.natHeap q=s.natHeap q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 UniformSectorPaddingMachine.Outside A (W*L.total) s u:=by
 obtain ⟨t,metaRun,tp,table,_oldTable,num,ret,low⟩:=
  UniformProducedSectorBatchPreparation.execution as L n a x s hlen hvolume rows widths below sep
   entry buffer old roles (by omega) pc count ha hd hs ht hq he hb wb
 have movedM:=UniformBoundedAssembly.boundedExecution_placed (metadata_code W)
  (by rw[UniformProducedSectorBatchPreparation.program_length];omega) (by omega) metaRun
 rw[show placed 0 s=s by cases s;simp[placed]] at movedM
 let after:=setPC t 158
 have args:=execution_arguments metaRun
 have he':after.natReg 4441=E:=(args 4441 (by simp)).trans he
 have hs':after.natReg 4472=S:=(args 4472 (by simp)).trans hsource
 have safe:readable setup after ∧peak setup after ≤ L.B:=by
  simp[readable,peak,setup,Op.readable,Op.peak,Op.apply,writeNat,next,he']
  omega
 have setRun:=block_runs setup (programFor W) 158 n L.B x after (setup_code W) rfl
  movedM.final_bound (by change 158+2 ≤ L.B;omega) safe.1 safe.2
 let ready:=setPC (applyBlock setup after) 0
 have rb:=changePC_bound L.B (applyBlock setup after) 0 setRun.final_bound (by omega)
 have readyHeader:UniformAllSectorPaddingMachine.Header S E
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length ready:=by
  constructor
  · simpa[ready,setPC,setup,applyBlock,Op.apply,writeNat,next] using hs'
  · simpa[ready,setPC,setup,applyBlock,Op.apply,writeNat,next] using he'
  · simpa[ready,setPC,setup,applyBlock,Op.apply,writeNat,next,after] using num
 have readySource:UniformSectorPaddingMachine.Source v S ready:=by
  intro j;exact (congrFun ret.1 (S+j.val)).trans (data j)
 have countBound:(UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)).length ≤ L.total:=by
  have cap:=UniformSectorMetadataMachine.sector_count_le_volume
   (UniformMultiAxisSectorMetadataPreparation.metadataAxes as)
  simpa only[UniformSectorBatchDirectoryMachine.sector_count,
   UniformSectorMetadataMachine.counts,UniformMultiAxisSectorMetadataPreparation.metadataAxes_geometry,
   UniformMultiAxisSectorMetadataPreparation.metadataAxes_volume,hvolume] using cap
 have readyTable:UniformAllSectorPaddingMachine.Table W E A
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)) ready:=by
  intro j hj
  simpa only[UniformSectorBatchDirectoryMachine.BatchCell,ready,setPC,setup,applyBlock,
   Op.apply,writeNat,next,after] using table j hj hj
 obtain ⟨u,padRun,up,padded,frame,out⟩:=UniformAllSectorPaddingMachine.execution
  (UniformSectorPackingMachine.physicalAxes as) v x ready hvolume readyHeader readyTable readySource
   positive roles fresh buffer (by omega) (by omega) rfl rb
 have movedP:=UniformBoundedAssembly.boundedExecution_placed (padding_code W)
  (by rw[UniformAllSectorPaddingMachine.program_length];omega) (by omega) padRun
 have setPCeq:placed 160 ready=applyBlock setup after:=by
  have cp:(applyBlock setup after).pc=160:=by rw[applyBlock_pc];rfl
  simpa only[ready,placed,setPC,Nat.add_zero] using
   (show placed 160 (setPC (applyBlock setup after) 0)=applyBlock setup after from
    UniformMultiAxisSectorMetadataPreparation.placed_zero _ _ cp)
 rw[setPCeq] at movedP
 let done:=setPC u 204
 have stop:BoundedExecution (programFor W) n x L.B done 1 done:=
  .halt movedP.final_bound (by simp[step,done,setPC,halt_at])
 refine ⟨done,?_,rfl,padded,?_,?_,frame.2.1.trans ret.2.2.1,
  frame.2.2.1.trans ret.2.2.2.1,?_⟩
 · convert movedM.executes (setRun.executes (movedP.executes stop)) using 1
   simp only[show setup.length=2 from rfl]
   omega
 · intro q h0 h1
   have saved:=frame.2.2.2.2 q (by omega) (by omega) (by omega) (by omega) (by omega)
   have same:ready.natReg q=t.natReg q:=by
    simp (disch:=omega) [ready,setPC,setup,applyBlock,Op.apply,writeNat,next,after]
   exact saved.trans (same.trans (ret.2.2.2.2 q h0 h1))
 · intro q less;exact (congrFun frame.1 q).trans (low q less)
 · intro q hq;exact (out q hq).trans (congrFun ret.1 q)
end
end ExactFourierCircuits.UniformProducedSectorPaddingPreparation
