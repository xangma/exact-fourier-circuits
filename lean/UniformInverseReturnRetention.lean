import UniformGlobalInverseReturn
import UniformInversePackingRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInverseReturnRetention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
open UniformGlobalInverseReturn
noncomputable section
lemma setup_high (s:State) (j:ℕ) (lo:6000 ≤ j):
 (applyBlock setup s).natReg j=s.natReg j:=by
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
/-- The actual all-sector scatter leaves Nat heaps intact; the following
computed inverse retains every cell outside its genuine workspaces. -/
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
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 UniformSectorPackingMachine.OutsideAllocation p.layout s u ∧
 (∀j,6000 ≤ j → u.natReg j=s.natReg j):=by
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
 obtain ⟨z,steps,last,cheap,zp,values,inverse,low,outputs,roots,nat,high⟩:=UniformInversePackingRetention.execution p as
  length volume (fun r j=>v r j.val) x nextEntry ph rows' widths' permutations' widthsBelow permutationsBelow sh
  actualSource positive rfl nb
 have placedLast:=UniformBoundedAssembly.boundedExecution_placed (inverse_code W)
  (by rw[UniformProducedInversePacking.program_length];omega) (by omega) last
 rw[show placed 56 nextEntry=setPC t 56 by cases t;rfl] at placedLast
 let u:=setPC z 219
 have stop:BoundedExecution (programFor W) n x p.layout.B u 1 u:=.halt placedLast.final_bound
  (by simp[step,u,setPC,UniformGlobalInverseReturn.halt_at])
 refine ⟨u,(7*W*((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum+
  (12*W+20)*(UniformProducedSectorChildABI.states as).length+5)+(steps+1),?_,?_,rfl,values,?_,
  outputs.trans frame.2.1,roots.trans frame.2.2.1,?_,?_⟩
 · exact moved.executes (placedLast.executes stop)
 · have sum:((UniformProducedSectorChildABI.states as).map UniformSectorPacking.BlockState.width).sum=p.layout.total:=by
    rw[UniformProducedSectorChildABI.states,UniformSectorBatchDirectoryMachine.sector_width_sum]
    simpa only[UniformSectorPackingMachine.physicalVolume] using volume
   rw[sum];nlinarith
 · intro q native temp final
   exact (low q temp final).trans (out q native)
 · intro q suffix stack inverse
   exact (nat q suffix stack inverse).trans (congrFun frame.1 q)
 · intro j lo
   exact (high j lo).trans (frame.2.2.2.2 j (by omega) (by omega) (by omega) (by omega))
/-- All exact cache cells and high caller registers survive actual220. -/
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
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 UniformSectorPackingMachine.OutsideAllocation p.layout s u ∧
 (∀j,6000 ≤ j → u.natReg j=s.natReg j):=by
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
 obtain ⟨u,ticks,tail,cheap,up,values,out,outputs,roots,nat,high⟩:=continuation p as length volume g sameB sameVolume sameSource
  v x a gh hs.1 hs.2.1 table source rowsA widthsA permutationsA widthsBelow permutationsBelow positive code ap boot.final_bound
 refine ⟨u,15+ticks,?_,by omega,up,values,?_,outputs.trans heaps.2.2.1,roots.trans heaps.2.2.2,?_,?_⟩
 · simpa only[setup,List.length_cons,List.length_nil] using boot.executes tail
 · intro q native temp final
   exact (out q native temp final).trans (congrFun heaps.2.1 q)
 · intro q suffix stack inverse
   exact (nat q suffix stack inverse).trans (congrFun heaps.1 q)
 · intro j lo
   exact (high j lo).trans (setup_high s j lo)
end
end ExactFourierCircuits.UniformInverseReturnRetention
