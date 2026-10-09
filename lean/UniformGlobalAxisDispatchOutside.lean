import UniformGlobalAxisDispatchExecution
import UniformGlobalCalendarDispatchOutside
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalAxisDispatchOutside
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformGlobalCalendarDispatch UniformGlobalAxisDispatchExecution
noncomputable section
attribute [local irreducible] Nat.add UniformGlobalClockConductor.programFor

/-- The fixed281 fold is followed immediately by the fixed69 partitioner.
Its rows and factor pool are the actual dispatcher output; the ordered union
injection supplies only the proved geometry of those printed endpoints. -/
theorem execution_outside {n A N r O T phaseBank P W marker axis D B:ℕ}
 (prepare child:Program) (roles:ℕ) (x:Fin n→ℂ) (s:State) (es:List Event)
 (position:(Σ _:Fin (callTotal r es),Fin 2) ↪ Fin r)
 (order:allRows r es=List.ofFn (fun i:Fin (callTotal r es)=>
  ((position ⟨i,0⟩).val,(position ⟨i,1⟩).val)))
 (input:Inputs A N r O T phaseBank s) (args:PlacementArgs P W marker axis D s)
 (pc:s.pc=UniformGlobalClockConductor.dispatchBase prepare) (wb:WordBound B s)
 (code:(UniformGlobalClockConductor.programFor prepare child roles).length ≤ B)
 (count:es.length=N) (selection:Selections A 0 es s)
 (cached:∀e∈es,CachedEvent r O phaseBank B e s)
 (selectionFit:A+2*N ≤ phaseBank) (phaseFit:phaseBank+56 ≤ T)
 (poolFit:O+9*r ≤ B) (positive:2 ≤ r)
 (hT:T+3*callTotal r es ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ marker)
 (hU:marker+r ≤ axis) (hA:axis+4 ≤ B) (hD:D+2 ≤ P):
 ∃u ticks,BoundedRuns (UniformGlobalClockConductor.programFor prepare child roles) n x B s ticks u ∧
 ticks ≤ 66*r+226+es.length*(9*r+48) ∧u.pc=UniformGlobalClockConductor.advanceBase prepare ∧
 u.natHeap D=some r ∧u.natHeap (D+1)=some O ∧
 UniformSectorPackingMachine.Rows [UniformMatchingAxisTableMachine.physicalAxis r W P
  (UniformMatchingKernelAmbient.edges position) (UniformMatchingKernelAmbient.matching position)
  (UniformMatchingKernelAmbient.range position) positive] 0 axis u ∧
 UniformSectorPackingMachine.Widths [UniformMatchingAxisTableMachine.physicalAxis r W P
  (UniformMatchingKernelAmbient.edges position) (UniformMatchingKernelAmbient.matching position)
  (UniformMatchingKernelAmbient.range position) positive] u ∧
 UniformSectorPackingMachine.Permutations [UniformMatchingAxisTableMachine.physicalAxis r W P
  (UniformMatchingKernelAmbient.edges position) (UniformMatchingKernelAmbient.matching position)
  (UniformMatchingKernelAmbient.range position) positive] u ∧
 (∀lane:Fin 9,∀i:Fin r,u.scalarHeap (O+lane.val*r+i.val)=some (UniformPairMachine.prepared
  (if lane.val=0 then foldValues es (fun _=>1) i.val else 1))) ∧
 (∀z,(z<phaseBank∨phaseBank+56≤z)→(z<T∨T+3*callTotal r es≤z)→(z<D ∨D+2 ≤ z)→(z<P ∨P+r ≤ z)→(z<W ∨W+r ≤ z)→
  (z < marker ∨marker+r ≤ z)→(z<axis ∨axis+4 ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z<O ∨O+9*r ≤ z→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,UniformAxisDispatchCallerFrame.Kept j→u.natReg j=s.natReg j):=by
 let p:=UniformGlobalClockConductor.programFor prepare child roles
 have sites:(UniformGlobalClockConductor.dispatchBase prepare)+281 ≤ B ∧
  (UniformGlobalClockConductor.adapterBase prepare)+69 ≤ B ∧
  UniformGlobalClockConductor.advanceBase prepare ≤ B:=by
  rw[UniformGlobalClockConductor.program_length] at code
  simp only[UniformGlobalClockConductor.dispatchBase,UniformGlobalClockConductor.adapterBase,UniformGlobalClockConductor.advanceBase]
  omega
 let ready:=setPC s 0
 have readyBound:WordBound B ready:=changePC_bound B s 0 wb (by omega)
 have readyInput:Inputs A N r O T phaseBank ready:=
  ⟨input.selected,input.count,input.radix,input.pool,input.rows,input.phaseBankReg⟩
 have readySelection:Selections A 0 es ready:=Selections.transfer 0 selection (by omega) selectionFit (fun _ _=>rfl)
 have readyCached:∀e∈es,CachedEvent r O phaseBank B e ready:=fun e h=>
  (cached e h).transfer (fun _ _=>rfl) (fun _ _=>rfl)
 obtain ⟨b,v,time,_boot,run,cheap,vp,head,_decoder,pool,heap,natOutside,_nat,scalar,roots,outputs⟩:=
  UniformGlobalCalendarDispatchOutside.execution_outside x ready es readyInput rfl readyBound (by omega) count readySelection readyCached
   selectionFit phaseFit poolFit (by omega)
 have dispatchSize:UniformGlobalClockConductor.dispatchBase prepare+UniformGlobalCalendarDispatch.program.length ≤ B:=by
  rw[UniformGlobalCalendarDispatch.program_length];exact sites.1
 have dispatchReturn:UniformGlobalClockConductor.adapterBase prepare ≤ B:=by
  rw[UniformGlobalClockConductor.adapterBase];exact sites.1
 have dispatch:=UniformBoundedAssembly.boundedExecution_placed
  (UniformGlobalClockConductor.dispatch_code prepare child roles) dispatchSize dispatchReturn run
 have start:placed (UniformGlobalClockConductor.dispatchBase prepare) ready=s:=by
  rw[placed_reset,←pc];cases s;rfl
 rw[start] at dispatch
 let v0:=setPC v 0
 have kept (j:ℕ) (h:UniformAxisDispatchCallerFrame.Kept j):v0.natReg j=s.natReg j:=
  UniformAxisDispatchCallerFrame.dispatch run j h
 have placement (j:ℕ) (lo:5926 ≤ j) (hi:j < 5931):v0.natReg j=s.natReg j:=placement_frame run j lo hi
 have va:UniformGlobalAxisUnionAdapter.Args r (callTotal r es) O T P W marker axis D v0:=
  ⟨head.radix,head.pool,head.rows,head.usedReg,
   (placement _ (by omega) (by omega)).trans args.permutation,
   (placement _ (by omega) (by omega)).trans args.widths,
   (placement _ (by omega) (by omega)).trans args.marker,
   (placement _ (by omega) (by omega)).trans args.axis,
   (placement _ (by omega) (by omega)).trans args.directory⟩
 have source:=actual_edges es position order v0 b.natHeap heap
 have vb:WordBound B v0:=changePC_bound B v 0 run.final_bound (by omega)
 obtain ⟨u,arun,acap,_up,dr,dp,rows,widths,perms,sh,_sr,uo,ur,nh⟩:=
  UniformGlobalAxisUnionAdapter.execution x position v0 va source positive hT hP hW hU hA hD (by omega) rfl vb
 have adapterSize:UniformGlobalClockConductor.adapterBase prepare+UniformGlobalAxisUnionAdapter.program.length ≤ B:=by
  rw[UniformGlobalAxisUnionAdapter.program_length];exact sites.2.1
 have adapter:=UniformBoundedAssembly.boundedExecution_placed
  (UniformGlobalClockConductor.adapter_code prepare child roles) adapterSize sites.2.2 arun
 rw[placed_reset] at adapter
 refine ⟨setPC u (UniformGlobalClockConductor.advanceBase prepare),time+(UniformMatchingAxisTableMachine.runtime r (callTotal r es)+14),
  dispatch.trans adapter,by omega,rfl,dr,dp,rows,widths,perms,?_,?_,?_,uo.trans outputs,ur.trans roots,?_⟩
 · intro lane i;rw[show (setPC u (UniformGlobalClockConductor.advanceBase prepare)).scalarHeap=u.scalarHeap from rfl,sh];exact pool lane i
 · intro z phaseOutside rowOutside d p w m a;exact (nh z d p w m a).trans (natOutside z phaseOutside rowOutside)
 · intro z outside;exact (congrFun sh z).trans (scalar z outside)
 · intro j h;exact (UniformAxisDispatchCallerFrame.adapter arun j h).trans (kept j h)
end
end ExactFourierCircuits.UniformGlobalAxisDispatchOutside
