import UniformMultiAxisSectorMetadataPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorMetadataCountBridge
open UniformMachine UniformAssembly UniformMultiAxisSectorMetadataPreparation
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section
/-- Strengthen the genuine124 execution by retaining its actual92 cursor count.
All phase headers and projection writes are charged exactly as in the original producer. -/
theorem execution_count (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout) (n a:ℕ) (x:Fin n → ℂ) (s:State)
 (hlen:as.length=L.ell) (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows:UniformSectorPackingMachine.Rows as 0 a s) (widths:UniformSectorPackingMachine.Widths as s)
 (below:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep:a+4*L.ell ≤ L.rows) (code:124 ≤ L.B) (pc:s.pc=0)
 (count:s.natReg 102+1=L.ell) (ha:s.natReg 3201=a) (hd:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hq:s.natReg 3215=L.directory)
 (wb:WordBound L.B s):∃u,
 BoundedExecution program n x L.B s
  (UniformSectorMetadataMachine.treeCost (UniformSectorMetadataMachine.counts (metadataAxes as))+43*L.ell+31) u ∧
 u.pc=123 ∧UniformSectorMetadataMachine.Header L u ∧
 UniformSectorMetadataMachine.Directory L 0
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)) u ∧
 UniformSectorMetadataMachine.WrittenSuffix (metadataAxes as) L 0 u ∧
 u.natReg 464=(UniformSectorMetadataMachine.counts (metadataAxes as)).prod ∧
 Retention s u ∧(∀j,j < L.rows → u.natHeap j=s.natHeap j) ∧
 OutsideWork L (UniformSectorMetadataMachine.counts (metadataAxes as)).prod s u :=by
 have r0:=L.rowsBelow;have r1:=L.suffixBelow;have r2:=L.stackBelow;have r3:=L.directoryBound
 have fit:L.rows+3*L.ell ≤ L.B:=by omega
 have countSafe:readable countSetup s ∧peak countSetup s ≤ L.B:=by
  simp [countSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
  omega
 have first:=block_runs countSetup program 0 n L.B x s countSetup_code pc wb
  (by rw [countSetup_length];omega) countSafe.1 countSafe.2
 let ready:=setPC (applyBlock countSetup s) 0
 have rb:=changePC_bound L.B (applyBlock countSetup s) 0 first.final_bound (by omega)
 have args:=countSetup_state L.ell a L.rows s count ha hd
 have source:Source L.ell a ready.natHeap:=by
  simpa only [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next,Nat.mul_zero,Nat.add_zero,hlen]
   using rows_source as 0 a s rows
 obtain ⟨v,copyRun,vpc,copied,out,frame⟩:=projection_execution n x L.ell a L.rows L.B ready
  source sep fit (by omega) rfl args.1 args.2.1 args.2.2 rb
 have placedCopy:=UniformBoundedAssembly.boundedExecution_placed projection_code
  (by rw [projection_length];omega) (by omega) copyRun
 have firstpc:(applyBlock countSetup s).pc=2:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,countSetup_length,pc]
 rw [show placed 2 ready=applyBlock countSetup s from placed_zero _ _ firstpc] at placedCopy
 let afterCopy:=setPC v 25
 have vc:afterCopy.natReg 3200=L.ell:=(frame.2.2.2.2 3200 (by omega) (by omega)).trans args.1
 have vd:afterCopy.natReg 3202=L.rows:=(frame.2.2.2.2 3202 (by omega) (by omega)).trans args.2.2
 have vs:afterCopy.natReg 3213=L.suffix:=by
  rw [show afterCopy.natReg 3213=ready.natReg 3213 from frame.2.2.2.2 3213 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using hs
 have vt:afterCopy.natReg 3214=L.stack:=by
  rw [show afterCopy.natReg 3214=ready.natReg 3214 from frame.2.2.2.2 3214 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using ht
 have vq:afterCopy.natReg 3215=L.directory:=by
  rw [show afterCopy.natReg 3215=ready.natReg 3215 from frame.2.2.2.2 3215 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using hq
 have installed:=block_runs metadataSetup program 25 n L.B x afterCopy metadataSetup_code rfl
  placedCopy.final_bound (by rw [metadataSetup_length];omega)
  (metadataSetup_safe L afterCopy vc vd vs vt vq).1
  (metadataSetup_safe L afterCopy vc vd vs vt vq).2
 let metadataReady:=setPC (applyBlock metadataSetup afterCopy) 0
 have mb:=changePC_bound L.B (applyBlock metadataSetup afterCopy) 0 installed.final_bound (by omega)
 have mr:UniformSectorMetadataMachine.Rows (metadataAxes as) 0 L.rows metadataReady:=by
  apply rows_project as 0 a L.rows s metadataReady rows
  intro i hi f hf
  change v.natHeap (L.rows+3*(0+i)+f)=s.natHeap (a+4*(0+i)+f)
  simpa only [Nat.zero_add,ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using copied i (by omega) f hf
 have low:∀j,j < L.rows → metadataReady.natHeap j=s.natHeap j:=by
  intro j hj
  exact out j (Or.inl hj)
 have mw:=widths_transfer as s metadataReady widths L.rows below low
 have mbelow:∀ax∈metadataAxes as,ax.widthsBase+ax.geometry.widths.length ≤ L.suffix:=by
  intro ax axin
  obtain ⟨b,hb,eq⟩:=List.mem_map.mp axin
  subst ax
  have bound:=below b hb
  exact bound.trans (by omega)
 obtain ⟨t,metaRun,_tpc,header,_constants,cursor,directory,suffix,metaOutside,metaFrame⟩:=
  UniformSectorMetadataMachine.execution (metadataAxes as) L n x metadataReady
   (by rw [metadataAxes_length,hlen]) (by rw [metadataAxes_volume,hvolume])
   (UniformSectorMetadataMachine.header_setPC L _ 0 (metadataSetup_header L afterCopy vc vd vs vt vq)) mr mw mbelow rfl mb
 have placedMeta:=UniformBoundedAssembly.boundedExecution_placed metadata_code
  (by rw [UniformSectorMetadataMachine.program_length];omega) (by omega) metaRun
 have installedpc:(applyBlock metadataSetup afterCopy).pc=31:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,metadataSetup_length];rfl
 rw [show placed 31 metadataReady=applyBlock metadataSetup afterCopy from placed_zero _ _ installedpc]
  at placedMeta
 let u:=setPC t 123
 have halt:BoundedExecution program n x L.B u 1 u:=.halt placedMeta.final_bound
  (by simp [step,u,setPC,program_halt])
 have rcopy:Retention (applyBlock countSetup s) afterCopy:=frame.retention
 have rmeta:Retention (applyBlock metadataSetup afterCopy) u:=metadata_retention metaFrame
 have ret:Retention s u:=(countSetup_retention s).trans
  (rcopy.trans ((metadataSetup_retention afterCopy).trans rmeta))
 refine ⟨u,?_,rfl,UniformSectorMetadataMachine.header_setPC L t 123 header,?_,suffix,cursor.count,ret,?_,?_⟩
 · convert first.executes (placedCopy.executes (installed.executes (placedMeta.executes halt))) using 1
   simp only [countSetup_length,metadataSetup_length]
   omega
 · apply UniformSectorMetadataMachine.directory_transfer L 0 _ t u ?_ (fun _ _ _=>rfl)
   simpa only [metadataAxes_geometry] using directory
 · intro j hj
   exact (UniformSectorMetadataMachine.protected_prefix _ L metadataReady t metaOutside j (by omega)).trans (low j hj)
 · intro j jrows jsuffix jstack jdir
   exact (metaOutside j jsuffix (by simpa only [Nat.mul_comm] using jstack)
    (by simpa only [Nat.mul_comm] using jdir)).trans (out j jrows)

def writesArguments : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => [3215,4441,4442].contains d
 | _ => false
lemma relocate_arguments (b ret:ℕ) (i:Instruction):
 writesArguments (relocate b ret i)=writesArguments i:=by cases i <;> rfl
lemma program_arguments : UniformMultiAxisSectorMetadataPreparation.program.all (fun i=> !writesArguments i)=true:=by
 simp only[UniformMultiAxisSectorMetadataPreparation.program,List.all_append,List.all_map,
  Function.comp_def,relocate_arguments]
 decide
lemma program_keeps_argument (q:ℕ) (hq:q∈([3215,4441,4442]:List ℕ)):
 ∀ i∈UniformMultiAxisSectorMetadataPreparation.program,UniformNewtonTableMachine.KeepsNat q i:=by
 intro i mem
 have free:=List.all_eq_true.mp program_arguments i mem
 cases i <;> simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals intro eq;subst_vars
 all_goals simp[writesArguments,hq] at free
lemma execution_arguments {B n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformMultiAxisSectorMetadataPreparation.program n x B s t u):
 ∀ q∈([3215,4441,4442]:List ℕ),u.natReg q=s.natReg q:=by
 intro q hq
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps_argument q hq)

end
end ExactFourierCircuits.UniformSectorMetadataCountBridge
