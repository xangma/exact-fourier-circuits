import UniformDirectLeafForestLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestExit
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformDirectLeafForestIteration UniformDirectLeafForestFrame
open UniformLocalCacheTreeMachine
noncomputable section

def finished(s:State):State:=applyBlock UniformDirectLeafForestProgram.finish (setPC s 453)
lemma heap(s:State):(finished s).natHeap=s.natHeap ∧(finished s).scalarHeap=s.scalarHeap ∧
 (finished s).outputs=s.outputs ∧(finished s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma pc(s:State):(finished s).pc=460:=rfl

structure Endpoints(p:Parameters)(visits:List Visit)(s:State):Prop where
 pool:s.natReg 6160=(position p visits visits.length).pool
 permutation:s.natReg 6162=(position p visits visits.length).permutation
 widths:s.natReg 6163=(position p visits visits.length).widths
 markers:s.natReg 6164=(position p visits visits.length).markers
 axis:s.natReg 6165=(position p visits visits.length).axis
 entry:s.natReg 6166=(position p visits visits.length).entry
 innerPool:s.natReg 6128=(position p visits visits.length).pool
 ordinal:s.natReg 6680=p.rectangles+demand visits
lemma endpoints {p:Parameters}{visits:List Visit}{s:State}(h:Cursor p visits visits.length s):
 Endpoints p visits (finished s):=by
 constructor <;>simp [finished,UniformDirectLeafForestProgram.finish,applyBlock,Op.apply,writeNat,next,setPC,
  h.pool,h.permutation,h.widths,h.markers,h.axis,h.entry,h.zero,h.ordinal,before_length]

/-- Exit branch, seven measured-endpoint copies and halt are all charged. -/
theorem execution {p:Parameters}{visits:List Visit}{n B:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Cursor p visits visits.length s)(code:461≤B)(hp:s.pc=31)(wb:WordBound B s):
 BoundedExecution UniformDirectLeafForestProgram.program n x B s 9 (finished s):=by
 have bound:=changePC_bound B s 453 wb (by omega)
 have branch:BoundedRuns UniformDirectLeafForestProgram.program n x B s 1 (setPC s 453):=
  .next wb (by simp[UniformMachine.step,hp,UniformDirectLeafForestProgram.branch_at,h.index,h.count,setPC])
   (.refl bound)
 have run:BoundedRuns UniformDirectLeafForestProgram.program n x B (setPC s 453) 7 (finished s):=by
  apply block_runs UniformDirectLeafForestProgram.finish UniformDirectLeafForestProgram.program 453 n B x
   (setPC s 453) UniformDirectLeafForestProgram.finish_code rfl bound (by change 460≤B;omega)
  · simp[UniformDirectLeafForestProgram.finish,readable,Op.readable]
  · simp[UniformDirectLeafForestProgram.finish,peak,Op.peak,Op.apply,writeNat,next,setPC,h.zero]
    have h0:=wb.2.1 6603
    have h1:=wb.2.1 6605
    have h2:=wb.2.1 6606
    have h3:=wb.2.1 6607
    have h4:=wb.2.1 6608
    have h5:=wb.2.1 6609
    omega
 have halt:BoundedExecution UniformDirectLeafForestProgram.program n x B (finished s) 1 (finished s):=
  .halt run.final_bound (by simp[UniformMachine.step,pc,UniformDirectLeafForestProgram.halt_at])
 simpa using branch.executes (run.executes halt)
end
end ExactFourierCircuits.UniformDirectLeafForestExit
