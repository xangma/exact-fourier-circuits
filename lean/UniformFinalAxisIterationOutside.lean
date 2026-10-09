import UniformFinalAxisDispatchOutside
import UniformGlobalClockAdvanceExecution

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisIterationOutside
open UniformMachine UniformAssembly UniformGlobalCalendarDispatch
open UniformTensorMonomialMachine (setPC applyBlock)
noncomputable section
attribute [local irreducible] Nat.add UniformGlobalClockConductor.programFor

/-- Actual281→69→five header updates→charged backedge. The cache selection
is factual input from the executed preparation site, not a produced-output
or numerical-action premise. -/
theorem execution_outside {n A N r O T phaseBank P W marker axis D B:ℕ}
 (prepare child:Program) (roles:ℕ) (x:Fin n→ℂ) (s:State) (es:List Event)
 (position:(Σ _:Fin (callTotal r es),Fin 2) ↪ Fin r)
 (order:allRows r es=List.ofFn (fun i:Fin (callTotal r es)=>
  ((position ⟨i,0⟩).val,(position ⟨i,1⟩).val)))
 (input:Inputs A N r O T phaseBank s)
 (args:UniformGlobalAxisDispatchExecution.PlacementArgs P W marker axis D s)
 (pc:s.pc=UniformGlobalClockConductor.dispatchBase prepare) (wb:WordBound B s)
 (code:(UniformGlobalClockConductor.programFor prepare child roles).length ≤ B)
 (count:es.length=N) (selection:Selections A 0 es s)
 (cached:∀e∈es,CachedEvent r O phaseBank B e s)
 (selectionFit:A+2*N ≤ phaseBank) (phaseFit:phaseBank+56 ≤ T)
 (poolFit:O+9*r ≤ B) (positive:2 ≤ r)
 (hT:T+3*callTotal r es ≤ P) (hP:P+r ≤ W) (hW:W+r ≤ marker)
 (hU:marker+r ≤ axis) (hA:axis+4 ≤ B) (hD:D+2 ≤ P)
 (one:s.natReg 5939=1) (index:s.natReg 5922+1 ≤ B) (directory:s.natReg 5923+2 ≤ B):
 ∃u ticks,BoundedRuns (UniformGlobalClockConductor.programFor prepare child roles) n x B s ticks u ∧
 ticks ≤ 66*r+232+es.length*(9*r+48) ∧u.pc=10 ∧
 u.natReg 5922=s.natReg 5922+1 ∧u.natReg 5923=s.natReg 5923+2 ∧
 u.natReg 5924=s.natReg 5934 ∧u.natReg 5925=s.natReg 5935 ∧
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
 (∀z,(z<phaseBank∨phaseBank+56≤z)→(z<T∨T+3*callTotal r es≤z)→(z < D ∨D+2 ≤ z)→(z < P ∨P+r ≤ z)→(z < W ∨W+r ≤ z)→
  (z < marker ∨marker+r ≤ z)→(z < axis ∨axis+4 ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z < O ∨O+9*r ≤ z→u.scalarHeap z=s.scalarHeap z) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,UniformFinalAxisStartupFrame.Kept j→j≠5922→j≠5923→j≠5924→j≠5925→u.natReg j=s.natReg j):=by
 obtain ⟨t,time,run,cheap,tp,dr,dp,rows,widths,perms,pool,nat,scalar,outputs,roots,frame⟩:=
  UniformFinalAxisDispatchOutside.execution_outside prepare child roles x s es position order input args pc wb code count
   selection cached selectionFit phaseFit poolFit positive hT hP hW hU hA hD
 have clock(j:ℕ)(lo:5920 ≤ j)(hi:j < 5926):t.natReg j=s.natReg j:=
  frame j (Or.inl (Or.inl ⟨lo,hi⟩))
 have next(j:ℕ)(lo:5934 ≤ j)(hi:j < 5940):t.natReg j=s.natReg j:=
  frame j (Or.inl (Or.inr (Or.inl ⟨lo,hi⟩)))
 obtain ⟨advance,headers⟩:=UniformGlobalClockAdvanceExecution.axis_execution prepare child roles x t tp
  ((next 5939 (by omega) (by omega)).trans one) run.final_bound code
  (by rw[clock 5922 (by omega) (by omega)];exact index)
  (by rw[clock 5923 (by omega) (by omega)];exact directory)
 let u:=setPC (applyBlock UniformGlobalClockConductor.advance t) 10
 have heaps:=UniformGlobalClockControl.heap_frame t UniformGlobalClockConductor.advance (Or.inr (Or.inr (Or.inl rfl)))
 refine ⟨u,time+6,run.trans advance,by omega,rfl,?_,?_,?_,?_,dr,dp,rows,widths,perms,pool,?_,?_,?_,?_,?_⟩
 · exact headers.1.trans (congrArg (fun q=>q+1) (clock 5922 (by omega) (by omega)))
 · exact headers.2.1.trans (congrArg (fun q=>q+2) (clock 5923 (by omega) (by omega)))
 · exact headers.2.2.1.trans (next 5934 (by omega) (by omega))
 · exact headers.2.2.2.trans (next 5935 (by omega) (by omega))
 · intro z a b c d e f g;exact (congrFun heaps.1 z).trans (nat z a b c d e f g)
 · intro z outside;exact (congrFun heaps.2.1 z).trans (scalar z outside)
 · exact heaps.2.2.2.1.trans outputs
 · exact heaps.2.2.2.2.trans roots
 · intro j kept a b c d
   exact (UniformGlobalClockAdvanceExecution.axis_kept t j ⟨a,b,c,d,by unfold UniformFinalAxisStartupFrame.Kept UniformAxisDispatchCallerFrame.Kept at kept;omega⟩).trans (frame j kept)
end
end ExactFourierCircuits.UniformFinalAxisIterationOutside
