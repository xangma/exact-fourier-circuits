import UniformFourierAxisCommonResult
import UniformFinalAxisIterationOutside
import UniformCalendarIterationFrame
import UniformActualGlobalClockProgram

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalAxisSuffix
noncomputable section
open UniformMachine UniformGlobalCalendarDispatch UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformJointAllocation (envelope slab)
open UniformFourierAxisWorkspace UniformFourierAxisCommonResult
open UniformTensorMonomialMachine (setPC)
open UniformCalendarPrintedPrefix

def selectedAction {n g:ℕ}{j:Fin (axisCount n)}{treeEvents:ℕ→List Event}
 {x:Fin n→ℂ}{s v:State}(actual:Result constants n g j treeEvents x s v):=
 Classical.choice actual.action

def physicalAxis {n g:ℕ}(hn:0<n){j:Fin (axisCount n)}{treeEvents:ℕ→List Event}
 {x:Fin n→ℂ}{s v:State}(actual:Result constants n g j treeEvents x s v):=
 UniformMatchingAxisTableMachine.physicalAxis (radix n j) (axis constants n j).widths
  (axis constants n j).permutation (UniformMatchingKernelAmbient.edges (selectedAction actual).position)
  (UniformMatchingKernelAmbient.matching (selectedAction actual).position)
  (UniformMatchingKernelAmbient.range (selectedAction actual).position)
  (UniformFourierAxisGeometry.geometry constants hn j).radix

structure Output {n g:ℕ}(hn:0<n)(j:Fin (axisCount n))(treeEvents:ℕ→List Event)
 (x:Fin n→ℂ)(s v:State)(actual:Result constants n g j treeEvents x s v)(u:State):Prop where
 pc:u.pc=10
 index:u.natReg 5922=j.val+1
 directory:u.natReg 5923=slab constants n+2*j.val+2
 nextNat:u.natReg 5924=(axis constants n j).endNat
 nextScalar:u.natReg 5925=(axis constants n j).endScalar
 row:UniformSectorPackingMachine.Rows [physicalAxis hn actual] 0 (5*slab constants n+4*j.val) u
 widths:UniformSectorPackingMachine.Widths [physicalAxis hn actual] u
 permutations:UniformSectorPackingMachine.Permutations [physicalAxis hn actual] u
 directoryCells:u.natHeap (slab constants n+2*j.val)=some (radix n j) ∧
  u.natHeap (slab constants n+2*j.val+1)=some (axis constants n j).pool
 pool:∀lane:Fin 9,∀k:Fin (radix n j),
  u.scalarHeap ((axis constants n j).pool+lane.val*radix n j+k.val)=
   some (UniformPairMachine.prepared (if lane.val=0 then
    foldValues (events constants n g j treeEvents) (fun _=>1) k.val else 1))
 natOutside:∀z,(z<(axis constants n j).selected∨(axis constants n j).endNat≤z)→
  (z<slab constants n+2*j.val∨slab constants n+2*j.val+2≤z)→
  (z<5*slab constants n+4*j.val∨5*slab constants n+4*j.val+4≤z)→u.natHeap z=s.natHeap z
 scalarOutside:∀z,(z<slab constants n∨slab constants n+9*radix n j≤z)→
  (z<(axis constants n j).pool∨(axis constants n j).endScalar≤z)→u.scalarHeap z=s.scalarHeap z
 frame:StepFrame j s u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 seed:∀q,200≤q→q<210→u.natReg q=v.natReg q
 allocatorFrontiers:u.natReg 6819=v.natReg 6819∧u.natReg 6821=v.natReg 6821
 cacheNat:u.natReg 6801=(UniformJointCacheAllocation.axis constants n j).endNat
 cacheScalar:u.natReg 6802=(UniformJointCacheAllocation.axis constants n j).endScalar
 registers:∀q,UniformFourierAxisPrepareHead.Protected q→q≠5922→q≠5923→q≠5924→q≠5925→
  u.natReg q=s.natReg q

/-- The concrete real281/69/advance segment consumes the actual common389
postcondition. All addresses and ordinary capacities are derived here. -/
theorem execution {n g:ℕ}(hn:0<n)(j:Fin (axisCount n))(treeEvents:ℕ→List Event)
 (x:Fin n→ℂ)(s v:State)(actual:Result constants n g j treeEvents x s v)
 (capacity:(events constants n g j treeEvents).length≤UniformJointCacheExtent.capacity (radix n j))
 (physical:s.natReg 6028=5*slab constants n)(directory:s.natReg 5923=slab constants n+2*j.val)
 (index:s.natReg 5922=j.val)(one:s.natReg 5939=1)(bound:WordBound (envelope constants n) v):
 ∃u ticks,BoundedRuns UniformActualGlobalClockProgram.program n x (envelope constants n)
  (setPC v 400) ticks u ∧
 ticks≤66*radix n j+232+(events constants n g j treeEvents).length*(9*radix n j+48) ∧
 Output hn j treeEvents x s v actual u:=by
 let a:=selectedAction actual
 let es:=events constants n g j treeEvents
 let w:=axis constants n j
 have geo:=UniformFourierAxisGeometry.geometry constants hn j
 have shape:=axis_geometry constants n j
 have count:=UniformMatchingAxisTableMachine.matching_capacity _ _
  (UniformMatchingKernelAmbient.matching a.position) (UniformMatchingKernelAmbient.range a.position)
 have calls:callTotal (radix n j) es≤radix n j:=by
  dsimp only[es]
  omega
 have cap:=Nat.mul_le_mul_left 2 capacity
 have endFit:=(axis_fit constants hn j).1
 have code:=UniformActualGlobalClockProgram.code_bound n
 have kept(q:ℕ)(hq:UniformFourierAxisPrepareHead.Protected q):v.natReg q=s.natReg q:=actual.natReg q hq
 have args:UniformGlobalAxisDispatchExecution.PlacementArgs w.permutation w.widths w.markers
  (5*slab constants n+4*j.val) (slab constants n+2*j.val) (setPC v 400):=by
  refine ⟨actual.footer.permutation,actual.footer.widths,actual.footer.markers,?_,?_⟩
  · exact actual.footer.physical.trans (congrArg (fun q=>q+4*j.val) physical)
  · exact actual.footer.directory.trans directory
 have wb:WordBound (envelope constants n) (setPC v 400):=
  changePC_bound _ v 400 bound (by have h:=UniformActualGlobalClockProgram.program_length;omega)
 have suffixCode:(UniformGlobalClockConductor.programFor UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W).length≤envelope constants n:=by
  exact code
 have nextIndex:v.natReg 5922+1≤envelope constants n:=by
  rw[kept 5922 (by unfold UniformFourierAxisPrepareHead.Protected;omega),index]
  have hi:=j.isLt
  have small:=UniformJointAllocation.actual_arithmetic constants n hn
  unfold envelope
  omega
 have nextDirectory:v.natReg 5923+2≤envelope constants n:=by
  rw[kept 5923 (by unfold UniformFourierAxisPrepareHead.Protected;omega),directory]
  exact geo.directoryPermutation.trans (by have h:=geo.natEndFit;omega)
 have input:Inputs w.selected es.length (radix n j) w.pool w.rawRows w.phase (setPC v 400):=by
  have h:=actual.dispatch
  exact ⟨h.selected,h.count,h.radix,h.pool,h.rows,h.phaseBankReg⟩
 have selection:Selections w.selected 0 es (setPC v 400):=
  Selections.transfer (N:=es.length) (T:=w.selected+2*es.length) 0 actual.selections (by omega) (le_refl _) (fun _ _=>rfl)
 have cached:∀e∈es,CachedEvent (radix n j) w.pool w.phase (envelope constants n) e (setPC v 400):=by
  intro e he
  exact (actual.cached e he).transfer (fun _ _=>rfl) (fun _ _=>rfl)
 have selectFit:w.selected+2*es.length≤w.phase:=by
  dsimp only[w,es]
  omega
 have rowsFit:w.rawRows+3*callTotal (radix n j) es≤w.permutation:=by
  dsimp only[w]
  omega
 obtain ⟨u,ticks,run,cheap,pc,idx,dir,nt,st,dr,dp,rows,widths,perms,pool,nat,scalar,outputs,roots,regs⟩:=
  UniformFinalAxisIterationOutside.execution_outside UniformFourierAxisPrepareMachine.program
   UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x (setPC v 400) es a.position a.rows
   input args (by simp only[UniformGlobalClockConductor.dispatchBase,
    UniformFourierAxisPrepareMachine.program_length];rfl) wb suffixCode rfl selection cached
   selectFit geo.phaseRows geo.mergedPoolFit geo.radix rowsFit geo.permutationWidths
   geo.widthsMarkers geo.markersRow geo.axisRowFit geo.directoryPermutation
   ((kept 5939 (by unfold UniformFourierAxisPrepareHead.Protected;omega)).trans one) nextIndex nextDirectory
 have first:StepFrame j s (setPC v 400):=
  UniformCalendarIterationFrame.preparation hn j s (setPC v 400) actual.natOutside actual.scalarOutside
 have second:StepFrame j (setPC v 400) u:=
  UniformCalendarIterationFrame.dispatch hn j es a.position (setPC v 400) u nat scalar
 have strongNat:∀z,(z<w.selected∨w.endNat≤z)→
   (z<slab constants n+2*j.val∨slab constants n+2*j.val+2≤z)→
   (z<5*slab constants n+4*j.val∨5*slab constants n+4*j.val+4≤z)→u.natHeap z=s.natHeap z:=by
  intro z fresh directoryOutside rowOutside
  have sh: w.selected+2*UniformJointCacheExtent.capacity (radix n j)=w.boundary ∧
   w.boundary+3*radix n j+11=w.phase ∧w.phase+64=w.rawRows ∧
   w.rawRows+3*radix n j=w.permutation ∧w.permutation+radix n j=w.widths ∧
   w.widths+radix n j=w.markers ∧w.markers+radix n j+5=w.endNat:=shape
  exact (nat z (by omega) (by omega) directoryOutside (by omega) (by omega) (by omega) rowOutside).trans
   (actual.natOutside z (by dsimp only[w] at fresh sh;omega))
 have strongScalar:∀z,(z<slab constants n∨slab constants n+9*radix n j≤z)→
   (z<w.pool∨w.endScalar≤z)→u.scalarHeap z=s.scalarHeap z:=by
  intro z firstOutside lastOutside
  have send:w.endScalar=w.pool+9*radix n j:=rfl
  exact (scalar z (by omega)).trans (actual.scalarOutside z firstOutside)
 refine ⟨u,ticks,run,cheap,pc,?_,?_,?_,?_,rows,widths,perms,⟨dr,dp⟩,pool,strongNat,strongScalar,
  UniformCalendarIterationFrame.trans j first second,outputs.trans actual.outputs,roots.trans actual.roots,?_,?_,?_,?_,?_⟩
 · exact idx.trans (congrArg (fun q=>q+1) ((kept 5922 (by unfold UniformFourierAxisPrepareHead.Protected;omega)).trans index))
 · exact dir.trans (congrArg (fun q=>q+2) ((kept 5923 (by unfold UniformFourierAxisPrepareHead.Protected;omega)).trans directory))
 · exact nt.trans actual.footer.nextNat
 · exact st.trans actual.footer.nextScalar
 · intro q lo hi
   exact regs q (Or.inr (Or.inr ⟨lo,hi⟩)) (by omega) (by omega) (by omega) (by omega)
 · exact ⟨regs 6819 (Or.inl (Or.inr (Or.inr (Or.inr (by omega))))) (by omega) (by omega) (by omega) (by omega),
    regs 6821 (Or.inl (Or.inr (Or.inr (Or.inr (by omega))))) (by omega) (by omega) (by omega) (by omega)⟩
 · exact (regs 6801 (Or.inl (Or.inr (Or.inr (Or.inr (by omega))))) (by omega) (by omega) (by omega) (by omega)).trans actual.footer.cacheNat
 · exact (regs 6802 (Or.inl (Or.inr (Or.inr (Or.inr (by omega))))) (by omega) (by omega) (by omega) (by omega)).trans actual.footer.cacheScalar
 · intro q hq a' b' c' d'
   exact (regs q (by unfold UniformFinalAxisStartupFrame.Kept UniformAxisDispatchCallerFrame.Kept UniformFourierAxisPrepareHead.Protected at *;omega)
    a' b' c' d').trans (kept q hq)

end
end ExactFourierCircuits.UniformFinalAxisSuffix
