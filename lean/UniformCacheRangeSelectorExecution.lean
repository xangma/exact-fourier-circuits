import UniformCacheRangeSelectorLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

def selections(r control rectangleCount tick:ℕ)(rectangle:ℕ → ℕ × ℕ)(nodes:List Range):List (ℕ × ℕ):=
 S.selected (control+3*r+4) (stride r) tick rectangle 0 rectangleCount++selectedRanges r tick nodes

/-- The actual fixed program reads both physical forest counts, scans the
rectangle range and every stored forward-node range, and retains true elapsed
phases. No selected-list, color, matching or action certificate is an input. -/
theorem execution {n r tasks control tick O rectangleCount B}(x:Fin n → ℂ)
 (rectangle:ℕ → ℕ × ℕ)(nodes:List Range)(s:State)
 (args:Args r tasks control tick O s)(source:RangeSource r tasks control rectangleCount rectangle nodes s.natHeap)
 (layout:Layout r tasks control rectangleCount O B nodes)
 (rectangleValues:∀j,j<rectangleCount → (rectangle j).1+28 ≤ B ∧ (rectangle j).2 ≤ B)
 (nodeValues:∀q∈nodes,∀j,j<q.count → (q.records j).1+28 ≤ B ∧ (q.records j).2 ≤ B)
 (code:90 ≤ B)(pc:s.pc=0)(wb:WordBound B s):∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ 21*(rectangleCount+total nodes)+16*nodes.length+31 ∧u.pc=89 ∧
 u.natReg 6705=(selections r control rectangleCount tick rectangle nodes).length ∧
 u.natReg 6703=tick ∧
 u.natHeap=S.writeSelections O 0 (selections r control rectangleCount tick rectangle nodes) s.natHeap:=by
 obtain ⟨a,bootRun,ap,bootControl,bootArgs,bootHeap⟩:=boot_stage x s args source pc wb code layout
 let ready:=setPC a 0
 have readyBound:=changePC_bound B a 0 bootRun.final_bound (by omega)
 have scanArgs:UniformGlobalCalendarSelector.Args (control+3*r+4) (stride r) rectangleCount tick O 0 ready:=
  ⟨bootArgs.directory,bootArgs.spacing,bootArgs.count,bootArgs.tick,bootArgs.output,bootArgs.used⟩
 have ob:O ≤ B:=by have:=layout.output;omega
 obtain ⟨t,b,scan,cost,done,heap⟩:=UniformGlobalCalendarSelector.execution x rectangle ready scanArgs rfl readyBound
  (by omega) (by change UniformGlobalCalendarSelector.Source _ _ _ _ a.natHeap;rw[bootHeap];exact source.rectangle) (layout.rectangle.trans ob) layout.rectangle rectangleValues (by have:=layout.output;omega)
 have first:=UniformBoundedAssembly.boundedExecution_placed rectangle_code
  (by rw[UniformGlobalCalendarSelector.program_length];omega) (by omega) scan
 rw[placed_zero a 21 ap] at first
 let begin:=setPC b 51
 have bh:= (selector_control scan (bootControl.withPC 0) done).withPC 51
 have retained:NodeSource r tasks 0 nodes begin.natHeap:=source.nodes.low (by simpa using layout.nodeRows) layout.nodes (by
  intro cell hc;change b.natHeap cell=s.natHeap cell;rw[heap];change S.writeSelections O 0 _ a.natHeap cell=s.natHeap cell;rw[writeSelections_low _ _ _ _ _ hc,bootHeap])
 have selectedBound: (S.selected (control+3*r+4) (stride r) tick rectangle 0 rectangleCount).length ≤ rectangleCount:=
  UniformGlobalCalendarSelector.selected_length _ _ _ _ _ _
 simp only[S.selected] at selectedBound
 obtain ⟨u,more,tail,cheap,up,uh,out⟩:=loop x nodes begin _ 0 bh (by omega) rfl first.final_bound code retained
  (by simpa using layout.nodeRows) ob layout.nodes nodeValues (by have:=layout.output;omega)
 have haltStep:step program n x u=.halted u:=by simp[step,up,code_89]
 refine ⟨u,21+t+more+1,((bootRun.trans first).trans tail).executes (.halt tail.final_bound haltStep),
  by omega,up,?_,uh.tick,?_⟩
 · simpa only[selections,List.length_append,Nat.zero_add] using uh.used
 · simp only[begin,setPC] at out
   rw[heap] at out
   simp only[ready,setPC,bootHeap] at out
   simpa only[selections,writeSelections_append,Nat.zero_add] using out
end
end ExactFourierCircuits.UniformCacheRangeSelector
