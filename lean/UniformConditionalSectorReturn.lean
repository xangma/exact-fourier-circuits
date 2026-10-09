import UniformSectorPayloadBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalSectorReturn
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
open UniformConditionalSectorLoop (RootBody Geometry Table Pending Completed budget)
noncomputable section

/-- One fixed child site inside the finite sector loop, followed continuously
by the actual220 inverse return. RootBody is still an OPEN internal obligation. -/
def programFor (child:Program) (W:ℕ):Program:=UniformGlobalMovementAssembly.assembly
 (UniformSameProgramSectorLoop.assembly child) (UniformGlobalInverseReturn.programFor W) []
lemma program_length (child:Program) (W:ℕ):(programFor child W).length=child.length+241:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly_length,
  UniformSameProgramSectorLoop.assembly_length,UniformGlobalInverseReturn.program_length,List.length_nil]
lemma loop_code (child:Program) (W:ℕ):CodeAt (UniformSameProgramSectorLoop.assembly child)
 (programFor child W) 0 (child.length+20):=by
 simpa only[programFor,UniformSameProgramSectorLoop.assembly_length] using
  UniformGlobalMovementAssembly.first_code (UniformSameProgramSectorLoop.assembly child)
   (UniformGlobalInverseReturn.programFor W) []
lemma return_code (child:Program) (W:ℕ):CodeAt (UniformGlobalInverseReturn.programFor W)
 (programFor child W) (child.length+20) (child.length+240):=by
 simpa only[programFor,UniformSameProgramSectorLoop.assembly_length,
  UniformGlobalInverseReturn.program_length,show child.length+20+220=child.length+240 by omega] using
  UniformGlobalMovementAssembly.second_code (UniformSameProgramSectorLoop.assembly child)
   (UniformGlobalInverseReturn.programFor W) []
lemma halt_at (child:Program) (W:ℕ):(programFor child W)[child.length+240]?=some .halt:=by
 simpa only[programFor,UniformSameProgramSectorLoop.assembly_length,
  UniformGlobalInverseReturn.program_length,List.length_nil,Nat.add_zero,
  show child.length+20+220=child.length+240 by omega] using
  UniformGlobalMovementAssembly.halt_at (UniformSameProgramSectorLoop.assembly child)
   (UniformGlobalInverseReturn.programFor W) []
lemma args_transfer {W E:ℕ} (p:UniformProducedInversePacking.Preparation W) (s u:State)
 (h:UniformGlobalInverseReturn.Args p E s)
 (kept:∀q,5900 ≤ q → q ≤ 5910 → u.natReg q=s.natReg q):UniformGlobalInverseReturn.Args p E u:=by
 constructor
 · exact (kept 5900 (by omega) (by omega)).trans h.volume
 · exact (kept 5901 (by omega) (by omega)).trans h.source
 · exact (kept 5902 (by omega) (by omega)).trans h.directory
 · exact (kept 5903 (by omega) (by omega)).trans h.axes
 · exact (kept 5904 (by omega) (by omega)).trans h.rows
 · exact (kept 5905 (by omega) (by omega)).trans h.suffix
 · exact (kept 5906 (by omega) (by omega)).trans h.stack
 · exact (kept 5907 (by omega) (by omega)).trans h.inverse
 · exact (kept 5908 (by omega) (by omega)).trans h.temporary
 · exact (kept 5910 (by omega) (by omega)).trans h.destination
lemma rows_prefix (as:List PhysicalAxis) (depth base F:ℕ) (s u:State)
 (h:Rows as depth base s) (bound:base+4*(depth+as.length) ≤ F)
 (kept:∀q,q < F → u.natHeap q=s.natHeap q):Rows as depth base u:=by
 induction as generalizing depth with
 | nil=>trivial
 | cons a as ih=>
  rcases h with ⟨h0,h1,h2,h3,tail⟩
  have hbound:base+4*(depth+1+as.length) ≤ F:=by simp only[List.length_cons] at bound;omega
  exact ⟨(kept _ (by simp only[List.length_cons] at bound;omega)).trans h0,
   (kept _ (by simp only[List.length_cons] at bound;omega)).trans h1,
   (kept _ (by simp only[List.length_cons] at bound;omega)).trans h2,
   (kept _ (by simp only[List.length_cons] at bound;omega)).trans h3,
   ih (depth+1) tail hbound⟩
lemma widths_prefix (as:List PhysicalAxis) (F:ℕ) (s u:State) (h:Widths as s)
 (bound:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ F)
 (kept:∀q,q < F → u.natHeap q=s.natHeap q):Widths as u:=by
 intro a ha j
 exact (kept _ (by have:=bound a ha;omega)).trans (h a ha j)
lemma permutations_prefix (as:List PhysicalAxis) (F:ℕ) (s u:State) (h:Permutations as s)
 (bound:∀a∈as,a.permutationBase+a.geometry.widths.sum ≤ F)
 (kept:∀q,q < F → u.natHeap q=s.natHeap q):Permutations as u:=by
 intro a ha j
 exact (kept _ (by have:=bound a ha;omega)).trans (h a ha j)

/-- The intermediate heap is an actual completed sector loop, not a supplied
kernel action. All physical movements after it are unconditional machine code.
Only RootBody remains to be discharged by the corrected recursive program. -/
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
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
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
 obtain ⟨z,last,lastRun,lastCheap,zp,values,out,outZ,rootsZ⟩:=UniformGlobalInverseReturn.execution p as length
  volume transpose sameB sameVolume sameSource
  (UniformSectorPayloadBridge.payload (UniformSectorPayloadBridge.actual_cover as g.volume (volume.trans gVolume.symm)) W A mid)
  x mid argsM countT tableM sourceM rowsM widthsM permutationsM widthsBelow permutationsBelow
  positive (by omega) rfl mb
 have movedLast:=UniformBoundedAssembly.boundedExecution_placed (return_code child W)
  (by rw[UniformGlobalInverseReturn.program_length];omega) (by omega) lastRun
 rw[show placed (child.length+20) mid=setPC t (child.length+20) by cases t;rfl] at movedLast
 let u:=setPC z (child.length+240)
 have stop:BoundedExecution (programFor child W) n x p.layout.B u 1 u:=.halt movedLast.final_bound
  (by simp[step,u,setPC,halt_at])
 refine ⟨mid,u,first+(last+1),doneM,moved.executes (movedLast.executes stop),by omega,rfl,values,
  outZ.trans outputs,rootsZ.trans roots⟩
end
end ExactFourierCircuits.UniformConditionalSectorReturn
