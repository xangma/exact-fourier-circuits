import UniformDirectLeafCacheBranches
import UniformDirectLeafDirectoryRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheFinish
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheProgram
noncomputable section

/-- Real Matching55 partition construction and ABI7 publication continue
from the same state. This internal helper's endpoint facts are derived by the
public descriptor execution, never supplied as a finished generated table. -/
theorem execution {c:Config} {r M kind n B:ℕ} (x:Fin n→ℂ)
 (E:Fin M→UniformColoring.Edge) (s:State)
 (args:UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry kind M s)
 (edges:UniformMatchingAxisTableMachine.Edges E c.rows s)
 (hm:UniformMatchingAxisTableMachine.Matching E) (hr:UniformMatchingAxisTableMachine.InRange r E)
 (positive:2≤r) (hT:c.rows+3*M≤c.permutation)
 (hP:c.permutation+r≤c.widths) (hW:c.widths+r≤c.markers) (hU:c.markers+r≤c.axis)
 (hA:c.axis+4≤c.entry) (hD:c.entry+7≤B) (code:264≤B) (pc:s.pc=183)
 (wb:WordBound B s) : ∃u,
 BoundedExecution UniformDirectLeafCacheProgram.program n x B s
  (UniformMatchingAxisTableMachine.runtime r M+26) u ∧u.pc=263 ∧
 UniformLocalMatchingSlotDirectory.Entry c.entry c.time r c.pool (r-M) c.widths c.permutation kind u ∧
 UniformSectorPackingMachine.Rows [UniformMatchingAxisTableMachine.physicalAxis r c.widths c.permutation E hm hr positive] 0 c.axis u ∧
 UniformSectorPackingMachine.Widths [UniformMatchingAxisTableMachine.physicalAxis r c.widths c.permutation E hm hr positive] u ∧
 UniformSectorPackingMachine.Permutations [UniformMatchingAxisTableMachine.physicalAxis r c.widths c.permutation E hm hr positive] u ∧
 u.scalarHeap=s.scalarHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q<c.permutation→u.natHeap q=s.natHeap q) ∧
 (∀q,c.entry+7≤q→u.natHeap q=s.natHeap q) := by
 let start:=setPC s 0
 have swb:=changePC_bound B s 0 wb (by omega)
 have head:UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
  c.axis c.rows c.entry kind M start:=⟨args.time,args.radix,args.pool,args.permutation,args.widths,
   args.markers,args.axis,args.rows,args.directory,args.kind,args.count⟩
 obtain ⟨out,run,_budget,last,entry,rows,widths,perm,sh,_sr,outs,roots,low,high⟩:=
  UniformLocalMatchingSlotDirectory.execution_high x E start head edges hm hr positive hT hP hW hU hA hD
   (by omega) rfl swb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed directory_code
  (by rw[UniformLocalMatchingSlotDirectory.program_length];omega) (by omega) run
 rw[show placed 183 start=s by change {s with pc:=183}=s;rw[←pc]] at placedRun
 let u:=setPC out 263
 have halt:BoundedExecution UniformDirectLeafCacheProgram.program n x B u 1 u:=
  .halt placedRun.final_bound (by simp only[step,show u.pc=263 from rfl,UniformDirectLeafCacheProgram.halt_at])
 have entry':UniformLocalMatchingSlotDirectory.Entry c.entry c.time r c.pool (r-M) c.widths c.permutation kind u:=entry
 refine ⟨u,?_,rfl,entry',rows,widths,perm,sh,outs,roots,low,high⟩
 convert placedRun.executes halt using 1
end
end ExactFourierCircuits.UniformDirectLeafCacheFinish
