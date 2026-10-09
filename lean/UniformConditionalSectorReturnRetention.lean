import UniformConditionalSectorReturn
import UniformInverseReturnRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalSectorReturnRetention
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
open UniformConditionalSectorLoop (RootBody Geometry Table Pending Completed budget)
open UniformConditionalSectorReturn (programFor loop_code return_code args_transfer rows_prefix widths_prefix permutations_prefix)
noncomputable section
/-- Real cache heap prefixes survive the finite same-child loop and every
physical return movement. The actual child RootBody obligation stays explicit. -/
theorem execution {W F reserve A E n:ℕ} (child:Program)
 (p:UniformProducedInversePacking.Preparation W) (as:List PhysicalAxis)
 (length:as.length=p.layout.ell) (volume:UniformSectorPackingMachine.physicalVolume as=p.layout.total)
 (g:Geometry W p.layout.B F reserve A E (UniformProducedSectorChildABI.states as))
 (gVolume:g.volume=p.layout.total)
 (transpose:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states as))
 (sameB:transpose.B=p.layout.B) (sameVolume:transpose.volume=p.layout.total)
 (sameSource:transpose.native=p.layout.source) (sameBuffer:transpose.buffer=A) (sameDirectory:transpose.directory=E)
 (cost:ℕ → ℕ) (v:ℕ → ℕ → Scalar) (x:Fin n → ℂ) (s:State)
 (root:RootBody child W n p.layout.B F reserve cost x)
 (table:Table W E A (UniformProducedSectorChildABI.states as) s)
 (source:Pending W A (UniformProducedSectorChildABI.states as) v 0 s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (count:s.natReg 464=(UniformProducedSectorChildABI.states as).length)
 (dir:s.natReg 4441=E) (fresh:s.natReg 5801=F)
 (args:UniformGlobalInverseReturn.Args p transpose.directory s)
 (rows:Rows as 0 p.layout.rows s) (widths:Widths as s) (permutations:Permutations as s)
 (widthsBelow:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ p.layout.suffix)
 (permutationsBelow:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ p.layout.suffix)
 (cacheBelow:p.layout.suffix ≤ F) (positive:0 < W)
 (code:child.length+241 ≤ p.layout.B) (pc:s.pc=0) (wb:WordBound p.layout.B s):
 ∃mid u ticks,Completed W A (UniformProducedSectorChildABI.states as) v
  (UniformProducedSectorChildABI.states as).length mid ∧
 BoundedExecution (programFor child W) n x p.layout.B s ticks u ∧
 ticks ≤ budget cost (UniformProducedSectorChildABI.states as)+
  213*p.layout.total+W*(16*p.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states as).length+56 ∧u.pc=child.length+240 ∧
 (∀r,r < W → ∀j:Fin p.layout.total,u.scalarHeap (p.destination+r*p.layout.total+j.val)=some
  (UniformSectorPayloadBridge.payload (UniformSectorPayloadBridge.actual_cover as g.volume (volume.trans gVolume.symm))
   W A mid r ((UniformSectorPackingMachine.physicalUnpacking as p.layout volume).symm j).val)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < F → q < p.layout.suffix → q < p.layout.stack → q < p.layout.inverse →
  u.natHeap q=s.natHeap q) ∧
 (∀q,q < F → q < A → q < transpose.native → q < p.layout.destination → q < p.destination →
  u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨t,first,firstRun,firstCheap,tp,done,tableT,ct,nat,scalar,countT,saved,outputs,roots⟩:=
  UniformConditionalSectorLoop.execution child g cost v x s root (by omega) table source constants
   count dir fresh pc wb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (loop_code child W)
  (by rw[UniformSameProgramSectorLoop.assembly_length];omega) (by omega) firstRun
 rw[show placed 0 s=s by cases s;simp[placed]] at moved
 let mid:=setPC t 0
 have mb:WordBound p.layout.B mid:=changePC_bound p.layout.B t 0 firstRun.final_bound (by omega)
 have doneM:Completed W A (UniformProducedSectorChildABI.states as) v
  (UniformProducedSectorChildABI.states as).length mid:=done
 have natM:∀q,q < F → mid.natHeap q=s.natHeap q:=nat
 have argsM:UniformGlobalInverseReturn.Args p transpose.directory mid:=args_transfer p s mid args saved
 have rowsM:Rows as 0 p.layout.rows mid:=rows_prefix as 0 p.layout.rows F s mid rows
  (by have:=p.layout.rowsBelow;rw[length];omega) natM
 have widthsM:Widths as mid:=widths_prefix as F s mid widths
  (fun a ha=>(widthsBelow a ha).trans cacheBelow) natM
 have permutationsM:Permutations as mid:=permutations_prefix as F s mid permutations
  (fun a ha=>(permutationsBelow a ha).trans cacheBelow) natM
 have tableM:UniformAllSectorTransposeMachine.Table transpose mid:=by
  intro i hi
  rw[sameDirectory,sameBuffer]
  exact tableT i hi
 have sourceM:=UniformSectorPayloadBridge.inverse_source g (volume.trans gVolume.symm) transpose
  sameBuffer v mid doneM
 obtain ⟨z,last,lastRun,lastCheap,zp,values,out,outZ,rootsZ,natZ,_highZ⟩:=UniformInverseReturnRetention.execution p as length
  volume transpose sameB sameVolume sameSource
  (UniformSectorPayloadBridge.payload (UniformSectorPayloadBridge.actual_cover as g.volume (volume.trans gVolume.symm)) W A mid)
  x mid argsM countT tableM sourceM rowsM widthsM permutationsM widthsBelow permutationsBelow
  positive (by omega) rfl mb
 have movedLast:=UniformBoundedAssembly.boundedExecution_placed (return_code child W)
  (by rw[UniformGlobalInverseReturn.program_length];omega) (by omega) lastRun
 rw[show placed (child.length+20) mid=setPC t (child.length+20) by cases t;rfl] at movedLast
 let u:=setPC z (child.length+240)
 have stop:BoundedExecution (programFor child W) n x p.layout.B u 1 u:=.halt movedLast.final_bound
  (by simp[step,u,setPC,UniformConditionalSectorReturn.halt_at])
 refine ⟨mid,u,first+(last+1),doneM,moved.executes (movedLast.executes stop),by omega,rfl,values,
  outZ.trans outputs,rootsZ.trans roots,?_,?_⟩
 · intro q before suffix stack inverse
   exact (natZ q (Or.inl suffix) (Or.inl stack) (Or.inl inverse)).trans (nat q before)
 · intro q before bank native temporary destination
   exact (out q (Or.inl native) (Or.inl temporary) (Or.inl destination)).trans
    (scalar q before (Or.inl bank))
end
end ExactFourierCircuits.UniformConditionalSectorReturnRetention
