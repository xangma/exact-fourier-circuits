import UniformDirectLeafCacheLeafProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLeafExecution
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformDirectLeafCacheReader UniformDirectLeafCacheLoopData UniformDirectLeafCacheLoopGeometry
open UniformDirectLeafCacheLoopBoot UniformDirectLeafCacheLoopChoice UniformDirectLeafCacheProducedSource
open UniformTransposeDescriptorMachine (Record leafRecords)
noncomputable section

structure Result (c:Config) (readOnly r A C:ℕ) (qs:List Record) (positive:2≤r) (s u:State):Prop where
 pc:u.pc=387
 args:Args (slot c r qs qs.length) u
 controls:Controls r qs.length qs.length u
 inputs:Inputs c r A C qs u
 events:∀(j:ℕ)(hj:j<qs.length),Nonempty
  (UniformDirectLeafCacheExecution.Result (slot c r qs j) r qs[j]
   (UniformDirectLeafCacheSource.mu r (A+3*r) qs[j]) positive u)
 scalarOutside:∀j,(j<c.pool∨(slot c r qs qs.length).pool≤j) → u.scalarHeap j=s.scalarHeap j
 natPrefix:∀j,j < min readOnly c.rows → u.natHeap j=s.natHeap j
 natHigh:∀j,(slot c r qs qs.length).permutation≤j → u.natHeap j=s.natHeap j
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

/-- Full fixed388: actual header setup, actual82 descriptor production,
actual303 cache loop, final halt. No descriptor/factor/partition/table output
is a caller premise. Both genuine coefficient lanes come from Retained. -/
theorem execution {n B:ℕ} (c:Config) (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))
 (v o P D E flip:ℕ) (x:Fin n→ℂ) (s:State)
 (original:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (operands:UniformInitialPreparation.Operands n x s)
 (args:Args c s) (node:s.natReg 5600=P) (forward:s.natReg 5602=D) (transpose:s.natReg 5603=E)
 (flag:s.natReg 6611=flip) (width:s.natHeap P=some v) (offset:s.natHeap (P+1)=some o)
 (od:c.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:c.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (extent:o+v≤UniformAllAxisSeedPreparation.radix n axis)
 (positive:2≤UniformAllAxisSeedPreparation.radix n axis)
 (layout:UniformDirectLeafCacheLoopGeometry.Layout {c with record:=bank flip D E}
  (UniformAllAxisSeedPreparation.radix n axis) (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B
  (records v o (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) flip))
 (sourceNode:P+2≤D) (sourceOriginal:c.originalDirectory+2≤D) (sourceConjugate:c.conjugateDirectory+1≤D)
 (apart:D+4*size v≤E) (before:E+4*size v≤c.rows)
 (quadratic:v*(v-1)≤B) (scalarStride:9*UniformAllAxisSeedPreparation.radix n axis≤B)
 (natStride:3*UniformAllAxisSeedPreparation.radix n axis+11≤B)
 (code:388≤B) (pc:s.pc=0) (wb:WordBound B s):∃u ticks,
 BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B s ticks u ∧
 ticks≤(62*UniformAllAxisSeedPreparation.radix n axis+246)*size v+64 ∧
 UniformDirectLeafCacheLeafExecution.Result {c with record:=bank flip D E} D (UniformAllAxisSeedPreparation.radix n axis)
  (UniformAllAxisSeedPreparation.axisBase n axis.val) (UniformAllAxisConjugatePreparation.axisBase n axis.val)
  (records v o (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) flip)
  positive s u:=by
 let r:=UniformAllAxisSeedPreparation.radix n axis
 let A:=UniformAllAxisSeedPreparation.axisBase n axis.val
 let C:=UniformAllAxisConjugatePreparation.axisBase n axis.val
 let qs:=records v o (A+3*r) flip
 let base:Config:={c with record:=bank flip D E}
 have len:qs.length=size v:=records_length v o (A+3*r) flip
 have leafLen:(leafRecords v o (A+3*r)).length=qs.length:=by
  rw[UniformTransposeDescriptorMachine.leafRecords_length,len];rfl
 have originalDirectory:s.natHeap c.originalDirectory=some A:=by rw[od];exact original.address axis axis.isLt
 have radix:s.natHeap (c.originalDirectory+1)=some r:=by rw[od];exact original.width axis axis.isLt
 have conjugateDirectory:s.natHeap c.conjugateDirectory=some C:=by rw[cd];exact conjugate.address axis axis.isLt
 have natEnd:=layout.natEnd
 change c.permutation+(3*r+11)*qs.length+3*r+4≤B at natEnd
 have rowSpacing:c.rows+3≤c.permutation:=layout.rows
 have rowsBound:c.rows≤B:=by omega
 have db:D+4*qs.length≤B:=by rw[len];omega
 have eb:E+4*qs.length≤B:=by rw[len];omega
 let z:=applyBlock UniformDirectLeafCacheLeafProgram.setup s
 have setupRun:BoundedRuns UniformDirectLeafCacheLeafProgram.program n x B s 2 z:=by
  apply block_runs UniformDirectLeafCacheLeafProgram.setup UniformDirectLeafCacheLeafProgram.program 0 n B x s
   UniformDirectLeafCacheLeafProgram.setup_code pc wb (by change 2≤B;omega)
  · simp [UniformDirectLeafCacheLeafProgram.setup,readable,Op.readable]
  · simp [UniformDirectLeafCacheLeafProgram.setup,peak,Op.peak,Op.apply,writeNat,next,args.originalDirectory]
    have:=wb.2.1 6601;rw[args.originalDirectory] at this;omega
 have zp:z.pc=2:=by rw[applyBlock_pc,pc];rfl
 have za:Args c z:=by
  constructor <;>simp [z,UniformDirectLeafCacheLeafProgram.setup,applyBlock,Op.apply,writeNat,next,
   args.record,args.originalDirectory,args.conjugateDirectory,args.pool,args.rows,args.permutation,
   args.widths,args.markers,args.axis,args.entry,args.time]
 have zh:UniformStoredDirectLeafOrientations.Header P c.originalDirectory D E (setPC z 0):=by
  constructor <;>simp [z,UniformDirectLeafCacheLeafProgram.setup,applyBlock,Op.apply,writeNat,next,setPC,
   node,forward,transpose,args.originalDirectory]
 have zs:UniformStoredDirectLeafOrientations.Stored v o A r P c.originalDirectory (setPC z 0):=
  ⟨width,offset,originalDirectory,radix⟩
 obtain ⟨b,printed,bp,fwd,trans,_ptr,frame,outside⟩:=UniformStoredDirectLeafOrientations.execution
  n v o A r P c.originalDirectory D E B x (setPC z 0) zh zs rfl
  (changePC_bound B z 0 setupRun.final_bound (by omega)) (by omega)
  (by omega) (by have:=sourceOriginal;omega) (by omega)
  (by have:=layout.original;have:=layout.scalarEnd;omega) (by rw[leafLen];exact db) (by rw[leafLen];exact eb) (by rw[leafLen,len];exact apart)
 have placedPrint:=UniformBoundedAssembly.boundedExecution_placed UniformDirectLeafCacheLeafProgram.orientations_code
  (by rw[UniformStoredDirectLeafOrientations.program_length];omega) (by omega) printed
 have printStart:placed 2 (setPC z 0)=z:=by change setPC z 2=z;rw[←zp];cases z;rfl
 rw[printStart] at placedPrint
 let ready:=setPC b 0
 have ba:Args c ready:=by
  have keep (j:ℕ)(lo:6600≤j)(hi:j≤6610):b.natReg j=z.natReg j:=frame.natReg j (Or.inr (by omega)) (Or.inr (by omega))
  exact ⟨(keep _ (by omega) (by omega)).trans za.record,(keep _ (by omega) (by omega)).trans za.originalDirectory,
   (keep _ (by omega) (by omega)).trans za.conjugateDirectory,(keep _ (by omega) (by omega)).trans za.pool,
   (keep _ (by omega) (by omega)).trans za.rows,(keep _ (by omega) (by omega)).trans za.permutation,
   (keep _ (by omega) (by omega)).trans za.widths,(keep _ (by omega) (by omega)).trans za.markers,
   (keep _ (by omega) (by omega)).trans za.axis,(keep _ (by omega) (by omega)).trans za.entry,
   (keep _ (by omega) (by omega)).trans za.time⟩
 have keepNat (j:ℕ)(lo:5520≤j)(hi:5615≤j)(ne:j≠6612):ready.natReg j=s.natReg j:=by
  have f:=frame.natReg j (Or.inr lo) (Or.inr hi)
  simpa (disch:=omega) [ready,z,UniformDirectLeafCacheLeafProgram.setup,
   applyBlock,Op.apply,writeNat,next,setPC] using f

 have heapLow (j:ℕ)(hj:j<D):ready.natHeap j=s.natHeap j:=
  outside j (Or.inl hj) (Or.inl (lt_of_lt_of_le hj (by omega : D≤E)))
 have values:Inputs base r A C qs ready:=by
  constructor
  · exact records_at fwd trans
  · exact (heapLow _ (by change c.originalDirectory<D;omega)).trans originalDirectory
  · exact (heapLow _ (by change c.originalDirectory+1<D;omega)).trans radix
  · exact (heapLow _ (by change c.conjugateDirectory<D;omega)).trans conjugateDirectory
  · intro i hi
    have good:UniformDirectLeafCacheSource.InRange r (A+3*r) qs[i]:=
     (records_valid v o (A+3*r) flip r extent qs[i] (List.getElem_mem hi)).1
    have val:=UniformDirectLeafCacheSource.retained_sources axis s original conjugate qs[i] good
    exact ⟨(congrFun frame.scalarHeap _).trans val.1,(congrFun frame.scalarHeap _).trans val.2⟩
  · rcases UniformDirectLeafCacheRetained.constants_of_operands operands with ⟨a,b,c',d,e⟩
    exact ⟨(congrFun frame.scalarHeap _).trans a,(congrFun frame.scalarHeap _).trans b,
     (congrFun frame.scalarHeap _).trans c',(congrFun frame.scalarHeap _).trans d,(congrFun frame.scalarHeap _).trans e⟩
 have readyWidth:ready.natHeap (ready.natReg 5600)=some v:=by
  have reg:ready.natReg 5600=P:=by
   have fr:=frame.natReg 5600 (Or.inr (by omega)) (Or.inl (by omega))
   exact fr.trans (by simp [z,UniformDirectLeafCacheLeafProgram.setup,applyBlock,Op.apply,writeNat,next,setPC,node])
  rw[reg];exact (heapLow P (by omega)).trans width
 have f:ready.natReg 6611=flip:=(keepNat _ (by omega) (by omega) (by omega)).trans flag
 have d:ready.natReg 5602=D:=by
  have fr:=frame.natReg 5602 (Or.inr (by omega)) (Or.inl (by omega))
  exact fr.trans (by simp [z,UniformDirectLeafCacheLeafProgram.setup,applyBlock,Op.apply,writeNat,next,setPC,forward])
 have e:ready.natReg 5603=E:=by
  have fr:=frame.natReg 5603 (Or.inr (by omega)) (Or.inl (by omega))
  exact fr.trans (by simp [z,UniformDirectLeafCacheLeafProgram.setup,applyBlock,Op.apply,writeNat,next,setPC,transpose])
 obtain ⟨u,ticks,loop,cost,done⟩:=UniformDirectLeafCacheLoopComplete.execution v flip D E qs x ready ba f d e readyWidth
  layout values (records_valid v o (A+3*r) flip r extent) positive len quadratic scalarStride natStride rfl
  (changePC_bound B b 0 printed.final_bound (by omega))
 have placedLoop:=UniformBoundedAssembly.boundedExecution_placed UniformDirectLeafCacheLeafProgram.loop_code
  (by rw[UniformDirectLeafCacheLoopProgram.program_length];omega) (by omega) loop
 have loopStart:placed 84 ready=setPC b 84:=rfl
 rw[loopStart] at placedLoop
 let final:=setPC u 387
 have halt:BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B final 1 final:=
  .halt placedLoop.final_bound (by simp[UniformMachine.step,final,setPC,UniformDirectLeafCacheLeafProgram.halt_at])
 refine ⟨final,_,setupRun.executes (placedPrint.executes (placedLoop.executes halt)),?_,?_,⟩
 · change ticks≤(62*r+212)*qs.length+24 at cost
   have bound:2+(34*(leafRecords v o (A+3*r)).length+37+(ticks+1))≤(62*r+246)*qs.length+64:=by
    rw[leafLen]
    calc
     _ ≤2+(34*qs.length+37+(((62*r+212)*qs.length+24)+1)):=by omega
     _ =(62*r+246)*qs.length+64:=by ring
   simpa only[len] using bound
 · refine ⟨rfl,UniformDirectLeafCacheSetup.Args.setPC done.args 387,done.controls.setPC 387,
    ⟨done.inputs.records,done.inputs.original,done.inputs.radix,done.inputs.conjugate,
     done.inputs.values,done.inputs.constants⟩,?_,?_,?_,?_,done.outputs.trans frame.outputs,
    done.roots.trans frame.roots⟩
   · intro j hj
     obtain ⟨res⟩:=done.events j hj (by omega)
     have good:=records_valid v o (A+3*r) flip r extent qs[j] (List.getElem_mem hj)
     exact ⟨UniformDirectLeafCacheLoopRetention.result res (slot_layout layout j hj)
      good.1.1 good.1.2.1 (fun _ _ _=>rfl) (fun _ _ _=>rfl)⟩
   · intro j outside
     have d:=done.scalarOutside j (by simpa only[slot_zero] using outside)
     exact d.trans (congrFun frame.scalarHeap j)
   · intro j below
     have lowD:j<D:=lt_of_lt_of_le below (Nat.min_le_left _ _)
     have lowRows:j<c.rows:=lt_of_lt_of_le below (Nat.min_le_right _ _)
     have d:=done.natPrefix j (by
      rw[slot_zero];have:=layout.rows;change j<c.permutation;omega) (Or.inl lowRows)
     exact d.trans (heapLow j lowD)
   · intro j above
     have d:=done.natHigh j above
     have low:c.rows≤(slot base r qs qs.length).permutation:=by
      change c.rows≤c.permutation+(3*r+11)*qs.length
      omega
     have hj:c.rows≤j:=low.trans above
     have b:=outside j (Or.inr (by rw[leafLen,len];omega)) (Or.inr (by rw[leafLen,len];omega))
     exact d.trans b

end
end ExactFourierCircuits.UniformDirectLeafCacheLeafExecution
