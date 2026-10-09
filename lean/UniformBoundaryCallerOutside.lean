import UniformBoundaryDiagonalCoreOutside
import UniformBoundaryDiagonalCaller
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryCallerOutside
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)
open UniformBoundaryDiagonalCaller
noncomputable section

theorem execution_outside {n B seedCell seed r time pool selected arena phase rows merged:ℕ}
 (q:Fin 3)(omega:ℂ)(x:Fin n→ℂ)(s:State)(args:C.Args seedCell q.val time pool arena s)
 (work:Workspace selected arena phase rows merged s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r)
 (original:UniformLocalSeedTableMachine.Compact r seed omega s)(positive:2≤r)
 (sourceBelow:seed+5*r≤pool)(sourceFit:seedCell+2≤B)(selectedFit:selected+2≤arena)
 (natFit:arena+3*r+11≤B)(poolFit:pool+9*r≤B)(code:138≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,Result n B r time pool selected arena phase rows merged positive q omega x s u ∧
 (∀j,(j<selected∨arena+3*r+11≤j)→u.natHeap j=s.natHeap j):=by
 obtain ⟨z,core⟩:=UniformBoundaryDiagonalOutside.execution_outside q omega x s args address width original positive
  sourceBelow sourceFit natFit poolFit (by omega) pc wb
 have moved:=UniformBoundedAssembly.boundedExecution_placed core_code
  (by rw[UniformBoundaryDiagonalMachine.program_length];omega) (by omega) core.execution
 rw[show placed 0 s=s by cases s;simp[placed]] at moved
 let b:=setPC z 127
 change BoundedRuns program n x B s (70*r+82) b at moved
 have workB:Workspace selected arena phase rows merged b:=work.transfer (by
  intro j lo hi
  apply UniformBoundaryDiagonalMachine.nat_frame core.execution j
  simp only[UniformBoundaryDiagonalMachine.written,List.mem_cons,List.not_mem_nil,or_false] at *
  omega)
 have head:C.FinalHeaders r arena b:=⟨core.headers.radix,core.headers.zero,core.headers.one,core.headers.descriptor⟩
 have safe:=footer_safe workB head moved.final_bound (by omega)
 have printRun:=block_runs footer program 127 n B x b footer_code rfl moved.final_bound
  (by rw[footer_length];omega) safe.1 safe.2
 let u:=applyBlock footer b
 have up:u.pc=137:=by rw[applyBlock_pc,footer_length];rfl
 have halt:BoundedExecution program n x B u 1 u:=.halt printRun.final_bound (by simp[step,up,halt_at])
 have run:BoundedExecution program n x B s (70*r+93) u:=by
  convert moved.executes (printRun.executes halt) using 1
  rw[footer_length]
 have unchanged (j:ℕ)(hj:arena≤j):u.natHeap j=z.natHeap j:=
  footer_outside workB head j (Or.inr (by omega))
 have entry:UniformLocalMatchingSlotDirectory.Entry (arena+3*r+4) time r pool r (arena+r) arena 1 u:=by
  rcases core.entry with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  exact ⟨(unchanged _ (by omega)).trans h0,(unchanged _ (by omega)).trans h1,
   (unchanged _ (by omega)).trans h2,(unchanged _ (by omega)).trans h3,
   (unchanged _ (by omega)).trans h4,(unchanged _ (by omega)).trans h5,(unchanged _ (by omega)).trans h6⟩
 have selectedRow:=footer_selected workB head pool
 have heaps:=footer_heaps b
 have pools:UniformGlobalDiagonalRowsMachine.Pools [C.poolEntry r pool positive omega q] u:=by
  apply UniformBoundaryDiagonalMachine.pools_of_written positive omega q u
  · intro j;exact (congrFun heaps.1 _).trans (core.copied j)
  · intro lane nonzero j;exact (congrFun heaps.1 _).trans (core.ones lane nonzero j)
 have rowsU:UniformSectorPackingMachine.Rows [C.axis r arena positive] 0 (arena+3*r) u:=by
  rcases core.row with ⟨h0,h1,h2,h3,tail⟩
  exact ⟨(unchanged _ (by omega)).trans h0,(unchanged _ (by omega)).trans h1,
   (unchanged _ (by omega)).trans h2,(unchanged _ (by omega)).trans h3,tail⟩
 have widthsU:UniformSectorPackingMachine.Widths [C.axis r arena positive] u:=by
  intro a ha j
  have eq:a=C.axis r arena positive:=by simpa only[List.mem_singleton] using ha
  subst a
  exact (unchanged _ (by change arena≤arena+r+j.val;omega)).trans (core.widths _ (by simp) j)
 have permutationU:UniformSectorPackingMachine.Permutations [C.axis r arena positive] u:=by
  intro a ha j
  have eq:a=C.axis r arena positive:=by simpa only[List.mem_singleton] using ha
  subst a
  exact (unchanged _ (by change arena≤arena+j.val;omega)).trans (core.permutation _ (by simp) j)
 refine ⟨u,⟨run,up,?_,selectedRow,?_,footer_inputs workB head,entry,pools,rowsU,widthsU,permutationU,?_,?_,?_⟩,?_⟩
 · simp[u,footer,applyBlock,Op.apply,writeNat,next]
 · exact ⟨entry.2.2.1,entry.2.2.2.1,entry.2.2.2.2.2.1,entry.2.2.2.2.2.2⟩
 · intro j below outside
   exact (footer_outside workB head j outside).trans (core.natPrefix j below)
 · intro j outside;exact (congrFun heaps.1 j).trans (core.scalarOutside j outside)
 · exact core.frame.trans ⟨heaps.2.2.1,heaps.2.2.2,fun j _ _=>congrFun heaps.2.1 j⟩

 · intro j outside
   exact (footer_outside workB head j (by omega)).trans (core.natOutside j (by omega))

theorem retained_execution_outside {n B time pool selected arena phase rows merged:ℕ}
 (j:Fin (UniformAllAxisSeedPreparation.axisCount n))(q:Fin 3)(x:Fin n→ℂ)(s:State)
 (retained:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (args:C.Args (UniformAllAxisSeedPreparation.directoryBase n+2*j.val) q.val time pool arena s)
 (work:Workspace selected arena phase rows merged s)
 (positive:2≤UniformAllAxisSeedPreparation.radix n j)
 (sourceBelow:UniformAllAxisSeedPreparation.axisBase n j.val+5*UniformAllAxisSeedPreparation.radix n j≤pool)
 (sourceFit:UniformAllAxisSeedPreparation.directoryBase n+2*j.val+2≤B)(selectedFit:selected+2≤arena)
 (natFit:arena+3*UniformAllAxisSeedPreparation.radix n j+11≤B)
 (poolFit:pool+9*UniformAllAxisSeedPreparation.radix n j≤B)(code:138≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,Result n B (UniformAllAxisSeedPreparation.radix n j) time pool selected arena phase rows merged positive q
  (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) x s u ∧
 (∀z,(z<selected∨arena+3*UniformAllAxisSeedPreparation.radix n j+11≤z)→u.natHeap z=s.natHeap z):=
 execution_outside q _ x s args work (retained.address j j.isLt) (retained.width j j.isLt)
  (retained.coefficients j j.isLt) positive sourceBelow sourceFit selectedFit natFit poolFit code pc wb
end
end ExactFourierCircuits.UniformBoundaryCallerOutside
