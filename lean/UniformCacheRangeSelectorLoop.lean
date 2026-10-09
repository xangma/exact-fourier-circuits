import UniformCacheRangeSelectorCycle
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPreparationRowTableMachine (control_run)
noncomputable section

theorem loop {n r tasks N tick O B}(x:Fin n → ℂ)(qs:List Range)(s:State)(used i:ℕ)
 (h:Control r tasks N tick O used i s)(ending:i+qs.length=N)(pc:s.pc=51)(wb:WordBound B s)(code:90 ≤ B)
 (source:NodeSource r tasks i qs s.natHeap)(banks:tasks+2*(i+qs.length)+2 ≤ O)(ob:O ≤ B)
 (fit:∀q∈qs,endAddress r q ≤ O)
 (values:∀q∈qs,∀j,j<q.count → (q.records j).1+28 ≤ B ∧ (q.records j).2 ≤ B)
 (output:O+2*(used+total qs) ≤ B):∃u ticks,
 BoundedRuns program n x B s ticks u ∧ticks ≤ 21*total qs+16*qs.length+1 ∧u.pc=89 ∧
 Control r tasks N tick O (used+(selectedRanges r tick qs).length) N u ∧
 u.natHeap=S.writeSelections O used (selectedRanges r tick qs) s.natHeap:=by
 induction qs generalizing used i s with
 | nil=>
  have ni:i=N:=by simpa using ending
  have stopStep:step program n x s=.running (setPC s 89):=by
   simp[step,pc,code_51,h.index,h.nodeCount,ni,setPC]
  have stop:=control_run program n B 89 x s wb (by omega) stopStep
  refine ⟨setPC s 89,1,stop,by simp[total],rfl,?_,rfl⟩
  simpa only[selectedRanges,List.length_nil,Nat.add_zero,ni] using h.withPC 89
 | cons q qs ih=>
  obtain ⟨a,b,c⟩:=source 0 (by simp)
  simp only[Nat.add_zero,List.getElem_cons_zero] at a b c
  have earlier:i<N:=by simp only[List.length_cons] at ending;omega
  have pf:tasks+2*(i+1)+2 ≤ B:=by
   have:=banks.trans ob
   simp only[List.length_cons] at this;omega
  have qfit:=fit q (by simp)
  have qvalues:=values q (by simp)
  have qout:O+2*(used+q.count) ≤ B:=by simp only[total] at output;omega
  obtain ⟨aState,t,run,cost,ap,ah,heap⟩:=cycle x q s h earlier pc wb code a b c pf qfit ob qvalues qout
  let add:ℕ:=(S.selected q.base (stride r) tick q.records 0 q.count).length
  have addBound:add ≤ q.count:=UniformGlobalCalendarSelector.selected_length _ _ _ _ _ _
  have retained:NodeSource r tasks i (q::qs) aState.natHeap:=source.low banks fit (by
   intro a ha;rw[heap];exact writeSelections_low _ _ _ _ _ ha)
  have tailFit:∀w∈qs,endAddress r w ≤ O:=by intro w hw;exact fit w (by simp[hw])
  have tailValues:∀w∈qs,∀j,j<w.count → (w.records j).1+28 ≤ B ∧ (w.records j).2 ≤ B:=by
   intro w hw;exact values w (by simp[hw])
  obtain ⟨u,more,tail,cheap,up,uh,out⟩:=ih aState (used+add) (i+1) ah
   (by simp only[List.length_cons] at ending;omega) ap run.final_bound retained.tail
   (by simp only[List.length_cons] at banks;omega) tailFit tailValues
   (by simp only[total] at output;omega)
  refine ⟨u,t+more,run.trans tail,?_,up,?_,?_⟩
  · simp only[total,List.length_cons];omega
  · simpa only[selectedRanges,List.length_append,Nat.add_assoc] using uh
  · rw[heap] at out
    rw[selectedRanges,writeSelections_append]
    exact out
end
end ExactFourierCircuits.UniformCacheRangeSelector
