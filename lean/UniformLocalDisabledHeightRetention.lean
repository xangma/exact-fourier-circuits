import UniformCacheRetentionRegions
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalDisabledHeightMachine.Retention
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformCrossHeightPreparationMachine UniformLocalDisabledHeightMachine
attribute [local irreducible] UniformCrossHeightPreparationMachine.program
noncomputable section
theorem execution (v:Parameters) (D F U J Z B m:ℕ)
 (ha:v.a ≤ widthOf v) (he:v.e ≤ widthOf v) (x:Fin m→ℂ) (s:State)
 (header:Header v s) (args:Args D F U J s)
 (source:Source v (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program s)
 (old:Processed v Z (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) s)
 (oldLayout:Layout v) (layout:Layout (disabled v D F U J))
 (before:recordBase v (height v) ≤ D)
 (budget:wordBudget (disabled v D F U J) ≤ B)
 (code:193 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u ticks,
 BoundedExecution program m x B s ticks u ∧
 ticks ≤ 4*v.K+34+height v*(64*gates v+200*(2*gates v+1)^2+56) ∧ u.pc=192 ∧
 Cursor (disabled v D F U J) (height v) u ∧
 Source v (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program u ∧
 Processed v Z (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) u ∧
 Processed (disabled v D F U J) Z
  (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) u ∧
 (∀q,q<D → u.natHeap q=s.natHeap q) ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 Outside (disabled v D F U J) s u := by
 have safe:=setup_safe B s hs
 have first:=block_runs setup program 0 m B x s setup_code pc hs
  (by rw [setup_length];omega) safe.1 safe.2
 let z:=applyBlock setup s
 have zp:z.pc=6:=by rw [applyBlock_pc,pc,setup_length]
 let entry:=setPC z 0
 have eb:=changePC_bound B z 0 first.final_bound (by omega)
 let w:=disabled v D F U J
 have wsource:Source w (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program entry:=
  (source_setup v D F U J _ s source).withPC
 have wh:Header w entry:=(setup_header v D F U J s header args).withPC _
 have gEq:(UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size=gates v:=cross_size v ha he
 have wge:(UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size=gates w:=gEq
 have high:height w-1 ≤ (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size:=by
  have h:=UniformCrossDepthReplayPreparation.cross_height_le_size v.K v.a v.e ha he
  dsimp only [w,disabled,height]
  omega
 obtain ⟨last,t,run,cost,lastPC,cursor,lastSource,done,outside,frame⟩:=
  UniformCrossHeightPreparationMachine.execution w Z B m
   (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program x entry wge layout
   (UniformCrossShearTableMachine.cross_good v.K v.a v.e ha he)
   (fun d _=>UniformCrossDepthReplayPreparation.cross_bucket_degree v.K v.a v.e d ha he false)
   high wh wsource rfl eb budget
 have call:=UniformBoundedAssembly.boundedExecution_placed height_code
  (by rw [UniformCrossHeightPreparationMachine.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero z 6 zp] at call
 let u:=setPC last 192
 have stop:BoundedExecution program m x B u 1 u:=.halt call.final_bound (by simp [step,u,setPC,halt_at])
 have nat:∀q,q<D → u.natHeap q=s.natHeap q:=by
  intro q hq
  exact (prefix_retained w entry last layout outside q hq).trans (congrFun (setup_heap s) q)
 have rowBefore:v.D ≤ recordBase v (height v):=by
  have:=oldLayout.rows;have:=oldLayout.colors;have:=oldLayout.palette
  unfold rowBase colorBase recordBase at *;omega
 refine ⟨u,6+t+1,?_,?_,rfl,cursor.withPC,?_,?_,done,nat,
  frame.1.trans (setup_scalar s),frame.2.1,frame.2.2.1,frame.2.2.2.1,?_,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using first.executes (call.executes stop)
 · simpa only [w,disabled,height,gates,widthOf,iterationBudget] using (show 6+t+1 ≤
    4*w.K+34+height w*iterationBudget w by omega)
 · exact source.transport gEq oldLayout (fun q hq=>nat q (lt_of_lt_of_le hq (rowBefore.trans before)))
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix v Z _ old gEq oldLayout
    (fun q hq=>nat q (lt_of_lt_of_le hq before))
 · intro q lo hi
   exact (saved_headers frame q ⟨lo,hi⟩).trans
    (setup_keeps s q (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega))
 · intro i hi hf hu hj
   exact (outside i hi hf hu hj).trans (congrFun (setup_heap s) i)

end
end ExactFourierCircuits.UniformLocalDisabledHeightMachine.Retention
