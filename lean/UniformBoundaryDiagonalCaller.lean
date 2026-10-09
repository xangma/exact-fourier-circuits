import UniformBoundaryDiagonalExecution
import UniformBoundaryDiagonalValues
import UniformGlobalCalendarDispatchBoot
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalCaller
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace C
export UniformBoundaryDiagonalMachine (Args Working ValueFrame CoreResult FinalHeaders axis family poolEntry)
end C
noncomputable section

/-- These are the real charged axis-workspace allocator's durable pointers. -/
structure Workspace (selected arena phase rows merged:ℕ)(s:State):Prop where
 selected:s.natReg 7050=selected
 arena:s.natReg 7051=arena
 phase:s.natReg 7052=phase
 rows:s.natReg 7053=rows
 merged:s.natReg 7057=merged
lemma Workspace.transfer {selected arena phase rows merged:ℕ}{s u:State}
 (h:Workspace selected arena phase rows merged s)
 (keep:∀j,7050≤j→j<7060→u.natReg j=s.natReg j):Workspace selected arena phase rows merged u:=
 ⟨(keep 7050 (by omega) (by omega)).trans h.selected,
  (keep 7051 (by omega) (by omega)).trans h.arena,
  (keep 7052 (by omega) (by omega)).trans h.phase,
  (keep 7053 (by omega) (by omega)).trans h.rows,
  (keep 7057 (by omega) (by omega)).trans h.merged⟩

def footer:List Op:=[.literal 6705 1,.putNat 7050 5848,.add 7012 7050 7003,.putNat 7012 7002,
 .add 6766 7050 7002,.add 6767 7003 7002,.add 6768 7007 7002,
 .add 6769 7057 7002,.add 6770 7053 7002,.add 6772 7052 7002]
def program:Program:=UniformBoundaryDiagonalMachine.program.map (relocate 0 127)++footer.map Op.code++[.halt]
lemma footer_length:footer.length=10:=rfl
lemma program_length:program.length=138:=by
 simp only[program,List.length_append,List.length_map,UniformBoundaryDiagonalMachine.program_length,
  footer_length,List.length_cons,List.length_nil]
lemma core_code:CodeAt UniformBoundaryDiagonalMachine.program program 0 127:=by
 exact UniformRankCrossPreparationMachine.segment_code [] (footer.map Op.code++[.halt]) _ 0 127 rfl
lemma footer_code:BlockAt footer program 127:=by
 exact UniformRankCrossPreparationMachine.block_of_segment footer
  (UniformBoundaryDiagonalMachine.program.map (relocate 0 127)) [.halt] 127
  (by rw[List.length_map,UniformBoundaryDiagonalMachine.program_length])
lemma halt_at:program[137]?=some .halt:=rfl

def written:List ℕ:=UniformBoundaryDiagonalMachine.written++[6705,6766,6767,6768,6769,6770,6772,7012]
lemma written_checked:program.all (fun i=>(UniformSyntacticNatFrame.natDst i).all (fun d=>decide (d∈written)))=true:=by decide +kernel
lemma avoids (j:ℕ)(hj:j∉written):UniformSyntacticNatFrame.Avoids program j:=by
 intro i hi bad
 have h:=List.all_eq_true.mp written_checked i hi
 rw[bad] at h
 simp only[Option.all_some,decide_eq_true_eq] at h
 exact hj h
lemma nat_frame {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)(j:ℕ)(hj:j∉written):u.natReg j=s.natReg j:=
 UniformSyntacticNatFrame.boundedExecution_preserves (avoids j hj) run
lemma workspace_frame {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)(j:ℕ)(lo:7050≤j)(hi:j<7060):u.natReg j=s.natReg j:=by
 apply nat_frame run j
 simp only[written,UniformBoundaryDiagonalMachine.written,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
 omega
lemma clock_frame {n B ticks:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)(j:ℕ)(lo:5920≤j)(hi:j<5940):u.natReg j=s.natReg j:=by
 apply nat_frame run j
 simp only[written,UniformBoundaryDiagonalMachine.written,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
 omega

def descriptor (r pool arena:ℕ):UniformGlobalCalendarDispatch.Descriptor where
 address:=arena+3*r+4
 elapsed:=0
 pool:=pool
 widthCount:=r
 permutation:=arena
 kind:=1

lemma footer_safe {selected arena phase rows merged r B:ℕ}{s:State}
 (h:Workspace selected arena phase rows merged s)(head:C.FinalHeaders r arena s)
 (wb:WordBound B s)(selectedFit:selected+2≤B):readable footer s ∧peak footer s≤B:=by
 have a:=wb.2.1 5848;have b:=wb.2.1 7007;have c:=wb.2.1 7057
 have d:=wb.2.1 7053;have e:=wb.2.1 7052
 simp only[head.descriptor,head.radix,h.merged,h.rows,h.phase] at a b c d e
 simp[footer,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.selected,h.merged,h.rows,h.phase,head.zero,head.one,head.radix,head.descriptor]
 omega
lemma footer_selected {selected arena phase rows merged r:ℕ}{s:State}
 (h:Workspace selected arena phase rows merged s)(head:C.FinalHeaders r arena s)(pool:ℕ):
 UniformGlobalCalendarDispatch.Selected selected 0 (descriptor r pool arena) (applyBlock footer s):=by
 simp[UniformGlobalCalendarDispatch.Selected,descriptor,footer,applyBlock,Op.apply,writeNat,next,
  h.selected,head.zero,head.one,head.descriptor,Function.update]
lemma footer_inputs {selected arena phase rows merged r:ℕ}{s:State}
 (h:Workspace selected arena phase rows merged s)(head:C.FinalHeaders r arena s):
 UniformGlobalCalendarDispatch.Inputs selected 1 r merged rows phase (applyBlock footer s):=by
 constructor <;>simp[footer,applyBlock,Op.apply,writeNat,next,
  h.selected,h.merged,h.rows,h.phase,head.zero,head.one,head.radix]
lemma footer_outside {selected arena phase rows merged r:ℕ}{s:State}
 (h:Workspace selected arena phase rows merged s)(head:C.FinalHeaders r arena s)(j:ℕ)
 (outside:j<selected ∨selected+2≤j):(applyBlock footer s).natHeap j=s.natHeap j:=by
 simp (disch:=omega) [footer,applyBlock,Op.apply,writeNat,next,Function.update,h.selected,head.zero,head.one]
 split_ifs <;>first|omega|rfl
lemma footer_heaps (s:State):(applyBlock footer s).scalarHeap=s.scalarHeap ∧
 (applyBlock footer s).scalarReg=s.scalarReg ∧(applyBlock footer s).outputs=s.outputs ∧
 (applyBlock footer s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩

structure Result (n B r time pool selected arena phase rows merged:ℕ)(positive:2≤r)
 (q:Fin 3)(omega:ℂ)(x:Fin n→ℂ)(s u:State):Prop where
 execution:BoundedExecution program n x B s (70*r+93) u
 pc:u.pc=137
 mode:u.natReg 6705=1
 selectedRow:UniformGlobalCalendarDispatch.Selected selected 0 (descriptor r pool arena) u
 stored:UniformGlobalCalendarDispatch.Stored (descriptor r pool arena) u
 inputs:UniformGlobalCalendarDispatch.Inputs selected 1 r merged rows phase u
 entry:UniformLocalMatchingSlotDirectory.Entry (arena+3*r+4) time r pool r (arena+r) arena 1 u
 pools:UniformGlobalDiagonalRowsMachine.Pools [C.poolEntry r pool positive omega q] u
 row:UniformSectorPackingMachine.Rows [C.axis r arena positive] 0 (arena+3*r) u
 widths:UniformSectorPackingMachine.Widths [C.axis r arena positive] u
 permutation:UniformSectorPackingMachine.Permutations [C.axis r arena positive] u
 natPrefix:∀j,j<arena→(j<selected ∨selected+2≤j)→u.natHeap j=s.natHeap j
 scalarOutside:∀j,(j<pool ∨pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j
 frame:C.ValueFrame s u

/-- This one literal138 reads the actual retained coefficient table, prepares
9r cells, prints a genuine kind1 ABI and its one selected row, and installs all
676x dispatcher inputs plus mode6705. Every helper return is a charged jump. -/
theorem execution {n B seedCell seed r time pool selected arena phase rows merged:ℕ}
 (q:Fin 3)(omega:ℂ)(x:Fin n→ℂ)(s:State)(args:C.Args seedCell q.val time pool arena s)
 (work:Workspace selected arena phase rows merged s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r)
 (original:UniformLocalSeedTableMachine.Compact r seed omega s)(positive:2≤r)
 (sourceBelow:seed+5*r≤pool)(sourceFit:seedCell+2≤B)(selectedFit:selected+2≤arena)
 (natFit:arena+3*r+11≤B)(poolFit:pool+9*r≤B)(code:138≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,Result n B r time pool selected arena phase rows merged positive q omega x s u:=by
 obtain ⟨z,core⟩:=UniformBoundaryDiagonalMachine.execution q omega x s args address width original positive
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
 refine ⟨u,run,up,?_,selectedRow,?_,footer_inputs workB head,entry,pools,rowsU,widthsU,permutationU,?_,?_,?_⟩
 · simp[u,footer,applyBlock,Op.apply,writeNat,next]
 · exact ⟨entry.2.2.1,entry.2.2.2.1,entry.2.2.2.2.2.1,entry.2.2.2.2.2.2⟩
 · intro j below outside
   exact (footer_outside workB head j outside).trans (core.natPrefix j below)
 · intro j outside;exact (congrFun heaps.1 j).trans (core.scalarOutside j outside)
 · exact core.frame.trans ⟨heaps.2.2.1,heaps.2.2.2,fun j _ _=>congrFun heaps.2.1 j⟩

/-- Public source boundary: the actual all-axis Retained result supplies both
loaded directory words and the five-lane coefficient family. -/
theorem retained_execution {n B time pool selected arena phase rows merged:ℕ}
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
  (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) x s u:=
 execution q _ x s args work (retained.address j j.isLt) (retained.width j j.isLt)
  (retained.coefficients j j.isLt) positive sourceBelow sourceFit selectedFit natFit poolFit code pc wb
end
end ExactFourierCircuits.UniformBoundaryDiagonalCaller
