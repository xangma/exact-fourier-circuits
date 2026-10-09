import UniformProducedInversePacking
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalInverseReturn
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
noncomputable section

/-- The retained high header uses actual runtime addresses. Every low helper
header is reinstalled by these15 ordinary operations after common C returns. -/
def setup:List Op:=[.literal 5911 0,
 .add 4530 5900 5911,.add 4531 5901 5911,.add 4532 5902 5911,
 .add 600 5903 5911,.add 601 5904 5911,.add 602 5905 5911,.add 603 5906 5911,
 .add 637 5907 5911,.add 604 5901 5911,.add 605 5908 5911,
 .add 5960 5900 5911,.add 5961 5901 5911,.add 5962 5910 5911,.add 5963 5907 5911]
def programFor (W:ℕ):Program:=setup.map Op.code++
 (UniformAllSectorTransposeMachine.programFor W true).map (relocate 15 56)++
 (UniformProducedInversePacking.programFor W).map (relocate 56 219)++[.halt]
lemma program_length (W:ℕ):(programFor W).length=220:=by
 simp only[programFor,List.length_append,List.length_map,
  UniformAllSectorTransposeMachine.program_length,UniformProducedInversePacking.program_length,
  setup,List.length_cons,List.length_nil]
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 0:=by
 intro i hi;change i < 15 at hi;interval_cases i <;>rfl
lemma transpose_code (W:ℕ):CodeAt (UniformAllSectorTransposeMachine.programFor W true) (programFor W) 15 56:=by
 exact UniformRankCrossPreparationMachine.segment_code (setup.map Op.code)
  ((UniformProducedInversePacking.programFor W).map (relocate 56 219)++[.halt]) _ 15 56 rfl
lemma inverse_code (W:ℕ):CodeAt (UniformProducedInversePacking.programFor W) (programFor W) 56 219:=by
 exact UniformRankCrossPreparationMachine.segment_code
  (setup.map Op.code++(UniformAllSectorTransposeMachine.programFor W true).map (relocate 15 56))
  [.halt] _ 56 219 (by simp only[List.length_append,List.length_map,
   UniformAllSectorTransposeMachine.program_length,setup,List.length_cons,List.length_nil])
lemma halt_at (W:ℕ):(programFor W)[219]?=some .halt:=by
 unfold programFor
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformAllSectorTransposeMachine.program_length,UniformProducedInversePacking.program_length,
  setup,List.length_cons,List.length_nil];omega)]
 simp only[List.length_append,List.length_map,UniformAllSectorTransposeMachine.program_length,
  UniformProducedInversePacking.program_length,setup,List.length_cons,List.length_nil];rfl

structure Args {W:ℕ} (p:UniformProducedInversePacking.Preparation W) (E:ℕ) (s:State):Prop where
 volume:s.natReg 5900=p.layout.total
 source:s.natReg 5901=p.layout.source
 directory:s.natReg 5902=E
 axes:s.natReg 5903=p.layout.ell
 rows:s.natReg 5904=p.layout.rows
 suffix:s.natReg 5905=p.layout.suffix
 stack:s.natReg 5906=p.layout.stack
 inverse:s.natReg 5907=p.layout.inverse
 temporary:s.natReg 5908=p.layout.destination
 destination:s.natReg 5910=p.destination
lemma setup_safe {W E:ℕ} (p:UniformProducedInversePacking.Preparation W) (s:State)
 (_args:Args p E s) (wb:WordBound p.layout.B s):
 readable setup s ∧peak setup s ≤ p.layout.B:=by
 have h0:=wb.2.1 5900;have h1:=wb.2.1 5901;have h2:=wb.2.1 5902
 have h3:=wb.2.1 5903;have h4:=wb.2.1 5904;have h5:=wb.2.1 5905
 have h6:=wb.2.1 5906;have h7:=wb.2.1 5907;have h8:=wb.2.1 5908;have h10:=wb.2.1 5910
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
 omega
lemma setup_headers {W E:ℕ} (p:UniformProducedInversePacking.Preparation W) (s:State)
 (args:Args p E s):
 UniformSectorPackingMachine.Header p.layout (applyBlock setup s) ∧
 UniformGlobalRoleScatterMachine.Header p.scatter (applyBlock setup s) ∧
 (applyBlock setup s).natReg 4530=p.layout.total ∧
 (applyBlock setup s).natReg 4531=p.layout.source ∧
 (applyBlock setup s).natReg 4532=E:=by
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,args.volume,args.source,args.directory,
    args.axes,args.rows,args.suffix,args.stack,args.inverse,args.temporary,args.destination]
 constructor
 · constructor <;>simp[UniformProducedInversePacking.Preparation.scatter,setup,applyBlock,Op.apply,writeNat,next,
    args.volume,args.source,args.directory,args.axes,args.rows,args.suffix,args.stack,args.inverse,args.temporary,args.destination]
 simp[setup,applyBlock,Op.apply,writeNat,next,args.volume,args.source,args.directory]

lemma sector_cover (axes:List UniformSectorPacking.Axis) (j:Fin (UniformSectorPacking.radices axes).prod):
 ∃i,∃hi:i < (UniformSectorPacking.sectorStates axes).length,
 ∃t,t < ((UniformSectorPacking.sectorStates axes)[i]'hi).width ∧
 ((UniformSectorPacking.sectorStates axes)[i]'hi).start+t=j.val:=by
 obtain ⟨b,k,equal⟩:=UniformSectorPacking.sectors_cover axes j
 let i:=UniformSectorPacking.sectorIndexEquiv axes b
 have hi:i.val < (UniformSectorPacking.sectorStates axes).length:=by
  simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using i.isLt
 have st:(UniformSectorPacking.sectorStates axes)[i.val]'hi=UniformSectorPacking.expectedBlockState axes b:=by
  simp only[UniformSectorPacking.sectorStates,List.getElem_ofFn]
  have eq: (⟨i.val,by simpa only[UniformSectorPacking.sectorStates,List.length_ofFn] using hi⟩:
   Fin (UniformSectorPacking.sectorWidths axes).length)=i:=Fin.ext rfl
  rw[eq]
  exact congrArg (UniformSectorPacking.expectedBlockState axes) ((UniformSectorPacking.sectorIndexEquiv axes).symm_apply_apply b)
 refine ⟨i.val,hi,k.val,?_,?_⟩
 · simpa only[st,UniformSectorPacking.expectedBlockState] using k.isLt
 · rw[st]
   exact (UniformSectorPacking.sectorCoordinate_value axes b k).symm.trans (congrArg Fin.val equal)

lemma transpose_source {W:ℕ} (p:UniformProducedInversePacking.Preparation W)
 (as:List PhysicalAxis) (volume:UniformSectorPackingMachine.physicalVolume as=p.layout.total)
 (g:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (sameVolume:g.volume=p.layout.total) (sameSource:g.native=p.layout.source)
 (v:ℕ→ℕ→Scalar) (s:State)
 (done:UniformAllSectorTransposeMachine.Filled g v (UniformProducedSectorChildABI.states as).length s):
 UniformGlobalRoleScatterMachine.Source p.scatter (fun r j=>v r j.val) s:=by
 intro r hr j
 have geom:(UniformSectorPacking.radices (UniformSectorPackingMachine.physicalAxes as)).prod=p.layout.total:=by
  simpa only[UniformSectorPackingMachine.physicalVolume] using volume
 obtain ⟨i,hi,t,ht,equal⟩:=sector_cover (UniformSectorPackingMachine.physicalAxes as) (finCongr geom.symm j)
 have result:=done i hi hi r hr t ht
 have ij:((UniformProducedSectorChildABI.states as)[i]'hi).start+t=j.val:=by
  change ((UniformProducedSectorChildABI.states as)[i]'hi).start+t=j.val at equal
  exact equal
 simpa only[UniformSectorTransposeMachine.Filled,UniformSectorTransposeMachine.targetAddress,
  UniformAllSectorTransposeMachine.Geometry.local,UniformAllSectorTransposeMachine.slice,
  UniformProducedInversePacking.Preparation.scatter,sameVolume,sameSource,
  ite_true,Nat.add_assoc,ij,finCongr_apply,Fin.val_cast] using result

lemma setup_count (s:State):(applyBlock setup s).natReg 464=s.natReg 464:=by
 simp[setup,applyBlock,Op.apply,writeNat,next]
lemma setup_heaps (s:State):(applyBlock setup s).natHeap=s.natHeap ∧
 (applyBlock setup s).scalarHeap=s.scalarHeap ∧(applyBlock setup s).outputs=s.outputs ∧
 (applyBlock setup s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma transpose_header {W:ℕ} (p:UniformProducedInversePacking.Preparation W)
 (as:List PhysicalAxis) (g:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (sameVolume:g.volume=p.layout.total) (sameSource:g.native=p.layout.source)
 (s:State) (args:Args p g.directory s) (count:s.natReg 464=(UniformProducedSectorChildABI.states as).length):
 UniformAllSectorTransposeMachine.Header g (applyBlock setup s):=by
 have h:=setup_headers p s args
 refine ⟨h.2.2.1.trans sameVolume.symm,h.2.2.2.1.trans sameSource.symm,h.2.2.2.2,?_⟩
 exact (setup_count s).trans count

lemma packing_header_after {W:ℕ} (p:UniformProducedInversePacking.Preparation W) (s u:State)
 (h:UniformSectorPackingMachine.Header p.layout s) (f:UniformAllSectorTransposeMachine.Frame s u):
 UniformSectorPackingMachine.Header p.layout (setPC u 0):=by
 constructor
 · exact (f.2.2.2.2 600 (by omega) (by omega) (by omega) (by omega)).trans h.count
 · exact (f.2.2.2.2 601 (by omega) (by omega) (by omega) (by omega)).trans h.rows
 · exact (f.2.2.2.2 602 (by omega) (by omega) (by omega) (by omega)).trans h.suffix
 · exact (f.2.2.2.2 603 (by omega) (by omega) (by omega) (by omega)).trans h.stack
 · exact (f.2.2.2.2 637 (by omega) (by omega) (by omega) (by omega)).trans h.inverse
 · exact (f.2.2.2.2 604 (by omega) (by omega) (by omega) (by omega)).trans h.source
 · exact (f.2.2.2.2 605 (by omega) (by omega) (by omega) (by omega)).trans h.destination
lemma scatter_header_after {W:ℕ} (p:UniformProducedInversePacking.Preparation W) (s u:State)
 (h:UniformGlobalRoleScatterMachine.Header p.scatter s) (f:UniformAllSectorTransposeMachine.Frame s u):
 UniformGlobalRoleScatterMachine.Header p.scatter (setPC u 0):=by
 constructor
 · exact (f.2.2.2.2 5960 (by omega) (by omega) (by omega) (by omega)).trans h.volume
 · exact (f.2.2.2.2 5961 (by omega) (by omega) (by omega) (by omega)).trans h.source
 · exact (f.2.2.2.2 5962 (by omega) (by omega) (by omega) (by omega)).trans h.destination
 · exact (f.2.2.2.2 5963 (by omega) (by omega) (by omega) (by omega)).trans h.permutation
lemma rows_same_heap (as:List PhysicalAxis) (depth base:ℕ) (s u:State)
 (h:Rows as depth base s) (heap:u.natHeap=s.natHeap):Rows as depth base u:=by
 induction as generalizing depth with
 | nil=>trivial
 | cons a as ih=>
  rcases h with ⟨h0,h1,h2,h3,tail⟩
  exact ⟨(congrFun heap _).trans h0,(congrFun heap _).trans h1,
   (congrFun heap _).trans h2,(congrFun heap _).trans h3,ih (depth+1) tail⟩

/-- Actual15 headers→actual all-sector41 scatter→genuine137 inverse-address
production→actual25 all-W inverse packing. Child execution is a separate
upstream obligation; here the source is the physical generated sector bank. -/
theorem continuation {W n:ℕ} (p:UniformProducedInversePacking.Preparation W)
 (as:List PhysicalAxis) (length:as.length=p.layout.ell)
 (volume:UniformSectorPackingMachine.physicalVolume as=p.layout.total)
 (g:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (sameB:g.B=p.layout.B) (sameVolume:g.volume=p.layout.total) (sameSource:g.native=p.layout.source)
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (gh:UniformAllSectorTransposeMachine.Header g s)
 (ph:UniformSectorPackingMachine.Header p.layout s) (sh:UniformGlobalRoleScatterMachine.Header p.scatter s)
 (table:UniformAllSectorTransposeMachine.Table g s) (source:UniformAllSectorTransposeMachine.Source g v s)
 (rows:Rows as 0 p.layout.rows s) (widths:Widths as s) (permutations:Permutations as s)
 (widthsBelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ p.layout.suffix)
 (permutationsBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ p.layout.suffix)
 (positive:0 < W) (code:220 ≤ p.layout.B) (pc:s.pc=15) (wb:WordBound p.layout.B s):
 ∃u ticks,BoundedExecution (programFor W) n x p.layout.B s ticks u ∧
 ticks ≤ 213*p.layout.total+W*(16*p.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states as).length+33 ∧u.pc=219 ∧
 (∀r,r < W→∀j:Fin p.layout.total,u.scalarHeap (p.destination+r*p.layout.total+j.val)=
  some (v r ((UniformSectorPackingMachine.physicalUnpacking as p.layout volume).symm j).val)) ∧
 (∀q,(q < g.native ∨g.native+W*g.volume ≤ q)→
  (q < p.layout.destination ∨p.layout.destination+p.layout.total ≤ q)→
  (q < p.destination ∨p.destination+W*p.layout.total ≤ q)→u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let entry:=setPC s 0
 have eb:=changePC_bound p.layout.B s 0 wb (by omega)
 have gh':UniformAllSectorTransposeMachine.Header g entry:=⟨gh.volume,gh.native,gh.directory,gh.count⟩
 obtain ⟨t,first,tp,filled,frame,out⟩:=UniformAllSectorTransposeMachine.execution g v x entry gh' table source rfl
  (by rw[sameB];exact eb)
 have first':BoundedExecution (UniformAllSectorTransposeMachine.programFor W true) n x p.layout.B entry
  (7*W*((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum+
   (12*W+20)*(UniformProducedSectorChildABI.states as).length+5) t:=by simpa only[sameB] using first
 have moved:=UniformBoundedAssembly.boundedExecution_placed (transpose_code W)
  (by rw[UniformAllSectorTransposeMachine.program_length];omega) (by omega) first'
 have atTranspose:placed 15 entry=s:=UniformMultiAxisSectorMetadataPreparation.placed_zero _ _ pc
 rw[atTranspose] at moved
 let nextEntry:=setPC t 0
 have nb:=changePC_bound p.layout.B t 0 first'.final_bound (by omega)
 have ph0:UniformSectorPackingMachine.Header p.layout entry:=
  ⟨ph.count,ph.rows,ph.suffix,ph.stack,ph.inverse,ph.source,ph.destination⟩
 have sh0:UniformGlobalRoleScatterMachine.Header p.scatter entry:=
  ⟨sh.volume,sh.source,sh.destination,sh.permutation⟩
 have ph:=packing_header_after p entry t ph0 frame
 have sh:=scatter_header_after p entry t sh0 frame
 have nh:nextEntry.natHeap=s.natHeap:=frame.1
 have rows':Rows as 0 p.layout.rows nextEntry:=rows_same_heap as 0 p.layout.rows s nextEntry rows nh
 have widths':Widths as nextEntry:=by intro a ha j;exact (congrFun nh _).trans (widths a ha j)
 have permutations':Permutations as nextEntry:=by intro a ha j;exact (congrFun nh _).trans (permutations a ha j)
 have actualSource:=transpose_source p as volume g sameVolume sameSource v nextEntry filled
 obtain ⟨z,steps,last,cheap,zp,values,inverse,low,outputs,roots⟩:=UniformProducedInversePacking.execution p as
  length volume (fun r j=>v r j.val) x nextEntry ph rows' widths' permutations' widthsBelow permutationsBelow sh
  actualSource positive rfl nb
 have placedLast:=UniformBoundedAssembly.boundedExecution_placed (inverse_code W)
  (by rw[UniformProducedInversePacking.program_length];omega) (by omega) last
 rw[show placed 56 nextEntry=setPC t 56 by cases t;rfl] at placedLast
 let u:=setPC z 219
 have stop:BoundedExecution (programFor W) n x p.layout.B u 1 u:=.halt placedLast.final_bound
  (by simp[step,u,setPC,halt_at])
 refine ⟨u,(7*W*((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum+
  (12*W+20)*(UniformProducedSectorChildABI.states as).length+5)+(steps+1),?_,?_,rfl,values,?_,
  outputs.trans frame.2.1,roots.trans frame.2.2.1⟩
 · exact moved.executes (placedLast.executes stop)
 · have sum:((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum=p.layout.total:=by
    rw[UniformProducedSectorChildABI.states,UniformSectorBatchDirectoryMachine.sector_width_sum]
    simpa only[UniformSectorPackingMachine.physicalVolume] using volume
   rw[sum];nlinarith
 · intro q native temp final
   exact (low q temp final).trans (out q native)
/-- Actual15 headers→actual all-sector41 scatter→genuine137 inverse-address
production→actual25 all-W inverse packing. Child execution is a separate
upstream obligation; here the source is the physical generated sector bank. -/
theorem execution {W n:ℕ} (p:UniformProducedInversePacking.Preparation W)
 (as:List PhysicalAxis) (length:as.length=p.layout.ell)
 (volume:UniformSectorPackingMachine.physicalVolume as=p.layout.total)
 (g:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (sameB:g.B=p.layout.B) (sameVolume:g.volume=p.layout.total) (sameSource:g.native=p.layout.source)
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (args:Args p g.directory s) (count:s.natReg 464=(UniformProducedSectorChildABI.states as).length)
 (table:UniformAllSectorTransposeMachine.Table g s) (source:UniformAllSectorTransposeMachine.Source g v s)
 (rows:Rows as 0 p.layout.rows s) (widths:Widths as s) (permutations:Permutations as s)
 (widthsBelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ p.layout.suffix)
 (permutationsBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ p.layout.suffix)
 (positive:0 < W) (code:220 ≤ p.layout.B) (pc:s.pc=0) (wb:WordBound p.layout.B s):
 ∃u ticks,BoundedExecution (programFor W) n x p.layout.B s ticks u ∧
 ticks ≤ 213*p.layout.total+W*(16*p.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states as).length+48 ∧u.pc=219 ∧
 (∀r,r < W→∀j:Fin p.layout.total,u.scalarHeap (p.destination+r*p.layout.total+j.val)=
  some (v r ((UniformSectorPackingMachine.physicalUnpacking as p.layout volume).symm j).val)) ∧
 (∀q,(q < g.native ∨g.native+W*g.volume ≤ q)→
  (q < p.layout.destination ∨p.layout.destination+p.layout.total ≤ q)→
  (q < p.destination ∨p.destination+W*p.layout.total ≤ q)→u.scalarHeap q=s.scalarHeap q) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 have safe:=setup_safe p s args wb
 have boot:=block_runs setup (programFor W) 0 n p.layout.B x s (setup_code W) pc wb
  (by change 0+15 ≤ p.layout.B;omega) safe.1 safe.2
 let a:=applyBlock setup s
 have ap:a.pc=15:=by rw[applyBlock_pc,pc];rfl
 have gh:=transpose_header p as g sameVolume sameSource s args count
 have hs:=setup_headers p s args
 have heaps:=setup_heaps s
 have rowsA:Rows as 0 p.layout.rows a:=rows_same_heap as 0 p.layout.rows s a rows heaps.1
 have widthsA:Widths as a:=by intro ax ha j;exact (congrFun heaps.1 _).trans (widths ax ha j)
 have permutationsA:Permutations as a:=by intro ax ha j;exact (congrFun heaps.1 _).trans (permutations ax ha j)
 obtain ⟨u,ticks,tail,cheap,up,values,out,outputs,roots⟩:=continuation p as length volume g sameB sameVolume sameSource
  v x a gh hs.1 hs.2.1 table source rowsA widthsA permutationsA widthsBelow permutationsBelow positive code ap boot.final_bound
 refine ⟨u,15+ticks,?_,by omega,up,values,?_,outputs.trans heaps.2.2.1,roots.trans heaps.2.2.2⟩
 · simpa only[setup,List.length_cons,List.length_nil] using boot.executes tail
 · intro q native temp final
   exact (out q native temp final).trans (congrFun heaps.2.1 q)
end
end ExactFourierCircuits.UniformGlobalInverseReturn
