import UniformGlobalSectorDirectoryRetention
import UniformSameProgramSectorLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSameProgramSectorLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

lemma boot_heaps (s:State):(applyBlock boot s).natHeap=s.natHeap ∧
 (applyBlock boot s).scalarHeap=s.scalarHeap ∧(applyBlock boot s).scalarReg=s.scalarReg ∧
 (applyBlock boot s).outputs=s.outputs ∧(applyBlock boot s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩

/-- A real generated count and real five-word table drive the physical boot,
branch and row loader in the literal loop containing ONE actual C program.
All17 steps are charged. Execution stops immediately before that C code. -/
theorem entry_execution {W n frontier:ℕ}
 (as:List UniformSectorPackingMachine.PhysicalAxis)
 (g:UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states as))
 (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (num:s.natReg 464=(UniformProducedSectorChildABI.states as).length)
 (dir:s.natReg 4441=g.directory) (fresh:s.natReg 5801=frontier)
 (table:UniformAllSectorTransposeMachine.Table g s)
 (filled:UniformAllSectorTransposeMachine.Filled g v (UniformProducedSectorChildABI.states as).length s)
 (hi:0<(UniformProducedSectorChildABI.states as).length)
 (code:program.length≤g.B) (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedRuns program n x g.B s 17 u ∧u.pc=17 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((UniformProducedSectorChildABI.states as)[0]'hi).pairs
  (g.buffer+W*((UniformProducedSectorChildABI.states as)[0]'hi).start)
  ((UniformProducedSectorChildABI.states as)[0]'hi).width frontier u ∧
 u.natReg 4151=0 ∧u.natReg 4122=2^(u.natReg 4120) ∧
 UniformProducedSectorChildABI.GroupedSource W
  (g.buffer+W*((UniformProducedSectorChildABI.states as)[0]'hi).start)
  ((UniformProducedSectorChildABI.states as)[0]'hi).width
  (UniformAllSectorTransposeMachine.slice v ((UniformProducedSectorChildABI.states as)[0]'hi)) u ∧
 UniformAllSectorTransposeMachine.Table g u ∧
 Cursor (UniformProducedSectorChildABI.states as).length g.directory frontier 0 u ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 have small:20≤g.B:=by have:=code;rw[program_length] at this;omega
 have safe:=boot_safe wb small
 have first:=block_runs boot program 0 n g.B x s (boot_code _) pc wb
  (by rw[boot_length];omega) safe.1 safe.2
 let t:=applyBlock boot s
 have tp:t.pc=7:=by rw[applyBlock_pc,boot_length,pc]
 have cursor:Cursor (UniformProducedSectorChildABI.states as).length g.directory frontier 0 t:=boot_cursor _ _ _ s num dir fresh
 let ready:=setPC t 8
 have entered:BoundedRuns program n x g.B t 1 ready:=.next first.final_bound
  (by simp only[step,tp,program,branch_at,cursor.index,cursor.count,ite_eq_left hi];rfl)
  (.refl (changePC_bound _ _ 8 first.final_bound (by omega)))
 have readyCursor:Cursor (UniformProducedSectorChildABI.states as).length g.directory frontier 0 ready:=
  ⟨cursor.count,cursor.one,cursor.index,cursor.directory,cursor.fresh,cursor.zero,cursor.five⟩
 have row:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer 0
  ((UniformProducedSectorChildABI.states as)[0]'hi) ready:=table 0 hi
 have qBound:=((entered.final_bound).2.2.1 _ _ row.1).2
 have widthBound:=((entered.final_bound).2.2.1 _ _ row.2.1).2
 have baseBound:=((entered.final_bound).2.2.1 _ _ row.2.2.1).2
 have frontierBound:frontier≤g.B:=by rw[←fresh];exact wb.2.1 5801
 have second:=setup_execution ((UniformProducedSectorChildABI.states as)[0]'hi) x ready readyCursor hi
  g.entry row qBound widthBound baseBound frontierBound code rfl entered.final_bound
 let u:=applyBlock setup ready
 have up:u.pc=17:=by rw[applyBlock_pc,setup_length];rfl
 have countPow:=UniformSectorBatchDirectoryMachine.sector_width (UniformSectorPackingMachine.physicalAxes as) 0 hi
 have pow:u.natReg 4122=2^(u.natReg 4120):=by rw[second.2.1.width,second.2.1.exponent];exact countPow
 have heaps:=setup_heaps ready
 have scalars:u.scalarHeap=s.scalarHeap:=heaps.2.1
 have nat:u.natHeap=s.natHeap:=heaps.1
 refine ⟨u,?_,up,second.2.1,second.2.2,pow,?_,?_,?_,scalars,heaps.2.2.1,heaps.2.2.2.1,heaps.2.2.2.2⟩
 · simpa only[boot_length] using first.trans (entered.trans second.1)
 · intro r hr j hj
   rw[scalars]
   exact filled 0 hi hi r hr j hj
 · intro i bound
   exact table i bound
 · constructor <;>simp[u,setup,applyBlock,Op.apply,writeNat,next,readyCursor.count,readyCursor.one,
    readyCursor.index,readyCursor.directory,readyCursor.fresh,readyCursor.zero,readyCursor.five]

/- The17-step theorem does not execute its genuine C child. The unconditional
root theorem, finite sector induction and actual inverse scatter/packing are
still required before claiming a complete synchronized tensor kernel. -/
end
end ExactFourierCircuits.UniformSameProgramSectorLoop
