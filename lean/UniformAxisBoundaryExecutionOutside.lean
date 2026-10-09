import UniformBoundaryGeometryOutside
import UniformFourierAxisPrepareBoundary
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundaryExecutionOutside
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
open UniformJointAllocation (Constants envelope slab)
open UniformJointCacheAllocation (ell)
open UniformAxisCacheSelectedPreparation (natAt scalarAt)
open UniformFourierAxisPrepareBoundary
noncomputable section

theorem execution_outside(c:Constants){n d g:ℕ}(hn:0<n)(j:Fin (ell n))(x:Fin n→ℂ)(s:State)
 (head:UniformAxisCacheClockLookup.Header c n j.val s)
 (later:0<j.val→UniformAxisCacheStartupMachine.Frontiers c n j.val s)
 (input:UniformAxisCacheInputs.Inputs n x s)
 (natFrontier:s.natReg 5924=H.freshNat c n j)
 (scalarFrontier:s.natReg 5925=H.freshScalar c n j)
 (epoch:s.natReg 5920=g)
 (duration:s.natHeap (UniformJointCacheAllocation.axis c n j).durations=some d)
 (fit:2*d+5≤envelope c n)(pc:s.pc=0)(bound:WordBound (envelope c n) s)
 (boundary:BoundaryAt d g)(pool:s.natReg 6020=slab c n)
 (physical:s.natReg 6028=5*slab c n)(directory:s.natReg 5923=slab c n+2*j.val):
 ∃u ticks q,BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u ∧
 ticks≤4*Nat.clog 2 (4*UniformAllAxisSeedPreparation.radix n j)+70*UniformAllAxisSeedPreparation.radix n j+233 ∧
 Result c n d g hn j q x s u ∧
 (∀z,(z<(W.axis c n j).selected∨(W.axis c n j).phase≤z)→u.natHeap z=s.natHeap z):=by
 have geo:=UniformFourierAxisGeometry.geometry c hn j
 have code:=geo.code
 have before:=UniformFourierAxisGeometry.axis_directory_before c n j
 have selectedAbove:slab c n≤(W.axis c n j).selected:=by omega
 obtain ⟨a,t,run,time,ap,workspace,allocation,radix,seed,selected,inputA,hf⟩:=
  UniformFourierAxisPrepareHead.execution c hn j x s head later input natFrontier scalarFrontier
   epoch duration fit code pc bound
 obtain ⟨q,mode,lane,family⟩:=boundary_values selected boundary
 let b:=C.decisionState 1 a
 have decision:=UniformFourierAxisPrepareControl.decision_execution n (envelope c n) 1 x a ap mode run.final_bound code
 change BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) a 4 b at decision
 have bp:b.pc=232:=UniformFourierAxisPrepareControl.decision_pc 1 a
 have df:C.Frame [7081] a b:=UniformFourierAxisPrepareControl.decision_frame 1 a
 have workB:=UniformFourierAxisPrepareControl.decision_workspace (mode:=1) workspace
 have keepB(q:ℕ)(hq:H.Protected q):b.natReg q=s.natReg q:=
  (df.natReg q (decision_away q hq)).trans (hf.natReg q hq)
 have allocB:=UniformFourierAxisPrepareHead.allocation_transfer allocation (u:=b) (by
  intro q lo hi;exact df.natReg q (by simp only[List.mem_cons,List.not_mem_nil,or_false];omega))
 have radixB:b.natReg 6800=UniformAllAxisSeedPreparation.radix n j:=
  (df.natReg 6800 (by decide)).trans radix
 have seedB:b.natReg 7000=UniformAllAxisSeedPreparation.directoryBase n+2*j.val:=
  (df.natReg 7000 (by decide)).trans seed
 have poolB:b.natReg 6020=slab c n:=(keepB _ (by unfold H.Protected;omega)).trans pool
 have clockB:b.natReg 5920=g:=(keepB _ (by unfold H.Protected;omega)).trans epoch
 have laneB:b.natReg 7001=q.val:=(df.natReg 7001 (by decide)).trans lane
 let b0:=setPC b 0
 have wb0:WordBound (envelope c n) b0:=⟨by change 0≤envelope c n;omega,decision.final_bound.2⟩
 have retained:UniformAllAxisSeedPreparation.Retained n (ell n) b0:=by
  constructor
  · intro i hi z l;exact (congrFun df.scalarHeap _).trans (inputA.original.coefficients i hi z l)
  · intro i hi;exact (congrFun df.natHeap _).trans (inputA.original.address i hi)
  · intro i hi;exact (congrFun df.natHeap _).trans (inputA.original.width i hi)
 have work0:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) b0:=
  ⟨workB.selected,workB.boundary,workB.phase,workB.rows,workB.permutation,workB.widths,
   workB.markers,workB.pool,workB.endNat,workB.endScalar,workB.nextNat,workB.nextScalar⟩
 obtain ⟨z,printed,outside⟩:=UniformFourierAxisGeometry.boundary_execution_outside c hn j g q x b0
  work0 retained poolB seedB clockB laneB rfl wb0
 have third:=UniformBoundedAssembly.boundedExecution_placed UniformFourierAxisPrepareMachine.boundary_code
  (by rw[UniformBoundaryDiagonalCaller.program_length];omega) (by omega) printed.execution
 have start:placed 232 b0=b:=by
  simp only[b0,placed,setPC,Nat.add_zero]
  rw[←bp]
 rw[start] at third
 let v:=setPC z 370
 change BoundedRuns UniformFourierAxisPrepareMachine.program n x (envelope c n) b
  (70*UniformAllAxisSeedPreparation.radix n j+93) v at third
 have keepV(q:ℕ)(hq:H.Protected q):v.natReg q=s.natReg q:=
  (UniformBoundaryDiagonalCaller.nat_frame printed.execution q (boundary_away q hq)).trans (keepB q hq)
 have workV:UniformFourierAxisWorkspaceHeader.Header (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) v:=
  UniformFourierAxisPrepareHead.workspace_transfer workB (by
   intro q h
   apply UniformBoundaryDiagonalCaller.nat_frame printed.execution q
   simp only[UniformBoundaryDiagonalCaller.written,UniformBoundaryDiagonalMachine.written,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
   omega)
 have allocV:=UniformFourierAxisPrepareHead.allocation_transfer allocB (u:=v) (by
  intro q lo hi
  apply UniformBoundaryDiagonalCaller.nat_frame printed.execution q
  simp only[UniformBoundaryDiagonalCaller.written,UniformBoundaryDiagonalMachine.written,
   List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
  omega)
 have radixV:v.natReg 6800=UniformAllAxisSeedPreparation.radix n j:=
  (UniformBoundaryDiagonalCaller.nat_frame printed.execution 6800 (by decide)).trans radixB
 have args:UniformFourierAxisPrepareFooter.Args (UniformAllAxisSeedPreparation.radix n j)
  (H.freshNat c n j) (H.freshScalar c n j) 1 j.val (5*slab c n) (slab c n+2*j.val)
  (cache c n j).endNat (cache c n j).endScalar v:=
  ⟨workV,printed.mode,radixV,(keepV _ (by unfold H.Protected;omega)).trans head.axis,
   (keepV _ (by unfold H.Protected;omega)).trans physical,
   (keepV _ (by unfold H.Protected;omega)).trans directory,allocV.endNat,allocV.endScalar⟩
 obtain ⟨done,result,ff⟩:=UniformFourierAxisPrepareControl.footer_execution n (envelope c n)
  (UniformAllAxisSeedPreparation.radix n j) (H.freshNat c n j) (H.freshScalar c n j) 1 j.val
  (5*slab c n) (slab c n+2*j.val) (cache c n j).endNat (cache c n j).endScalar x v args rfl
  third.final_bound code (by have:=geo.axisRowFit;omega)
 let u:=applyBlock UniformFourierAxisPrepareFooter.block v
 have separation:=geo.selectedBoundary
 have frames:Frame c n j s u:=by
  constructor
  · intro y below
    exact (congrFun ff.natHeap y).trans ((printed.natPrefix y (by omega) (Or.inl below)).trans
     ((congrFun df.natHeap y).trans (congrFun hf.natHeap y)))
  · intro y outside
    exact (congrFun ff.scalarHeap y).trans ((printed.scalarOutside y outside).trans
     ((congrFun df.scalarHeap y).trans (congrFun hf.scalarHeap y)))
  · intro y a b
    exact (congrFun ff.scalarReg y).trans ((printed.frame.registers y a b).trans
     ((congrFun df.scalarReg y).trans (congrFun hf.scalarReg y)))
  · exact ff.outputs.trans (printed.frame.outputs.trans (df.outputs.trans hf.outputs))
  · exact ff.roots.trans (printed.frame.roots.trans (df.roots.trans hf.roots))
  · intro q hq;exact (ff.natReg q (footer_away q hq)).trans (keepV q hq)
 have finalInput:=input_transport c hn x s u input
  (fun y hy=>frames.natPrefix y (by omega)) (fun y hy=>frames.scalarOutside y (Or.inl hy))
  (fun q lo hi=>frames.natReg q (by unfold H.Protected;omega)) frames.outputs frames.roots
 have nheap:u.natHeap=z.natHeap:=ff.natHeap
 have sheap:u.scalarHeap=z.scalarHeap:=ff.scalarHeap
 have payload:Payload c n g hn j q u:=by
  constructor
  · simpa only[UniformGlobalCalendarDispatch.Selected,nheap] using printed.selectedRow
  · simpa only[UniformGlobalCalendarDispatch.Stored,nheap] using printed.stored
  · simpa only[UniformLocalMatchingSlotDirectory.Entry,nheap] using printed.entry
  · simpa only[UniformGlobalDiagonalRowsMachine.Pools,sheap] using printed.pools
  · simpa only[UniformSectorPackingMachine.Rows,nheap] using printed.row
  · simpa only[UniformSectorPackingMachine.Widths,nheap] using printed.widths
  · simpa only[UniformSectorPackingMachine.Permutations,nheap] using printed.permutation
 have allocU:=UniformFourierAxisPrepareHead.allocation_transfer allocV (u:=u) (by
  intro q lo hi;apply ff.natReg q
  simp only[C.footerWrites,UniformFourierAxisPrepareControl.footerWrites,List.mem_cons,List.not_mem_nil,or_false]
  omega)
 have up:u.pc=388:=by rw[UniformFourierAxisPrepareControl.block_pc,UniformFourierAxisPrepareFooter.block_length];rfl
 refine ⟨u,_,q,(run.trans (decision.trans third)).executes done,by omega,⟨up,family,result,
  UniformFourierAxisPrepareControl.footer_workspace args,allocU,?_,?_,?_,?_,payload,finalInput,frames⟩,?_⟩
 · exact (ff.natReg 7000 (by decide)).trans
    ((UniformBoundaryDiagonalCaller.nat_frame printed.execution 7000 (by decide)).trans seedB)
 · exact (ff.natReg 7080 (by decide)).trans
    ((UniformBoundaryDiagonalCaller.nat_frame printed.execution 7080 (by decide)).trans
     ((df.natReg 7080 (by decide)).trans mode))
 · exact (ff.natReg 7001 (by decide)).trans
    ((UniformBoundaryDiagonalCaller.nat_frame printed.execution 7001 (by decide)).trans laneB)
 · exact (ff.natReg 6705 (by decide)).trans printed.mode
 · intro y hy
   exact (congrFun ff.natHeap y).trans ((outside y hy).trans
    ((congrFun df.natHeap y).trans (congrFun hf.natHeap y)))

end
end ExactFourierCircuits.UniformAxisBoundaryExecutionOutside
