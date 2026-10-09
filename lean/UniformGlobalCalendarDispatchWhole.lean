import UniformGlobalCalendarDispatchLoop

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine
noncomputable section

lemma CachedEvent.widen {r O H T B : ℕ} {e : Event} {s : State}
 (h : CachedEvent r O H B e s) (extent : H ≤ T) : CachedEvent r O T B e s :=
 ⟨h.decoded,h.stored,h.source,h.entryFit.trans extent,h.sourcePool,h.sourceRows.trans extent,h.matching,h.values⟩

/-- Whole literal281 execution from dirty work memory. It prints the real
phase directory, initializes all9r scalar cells and folds every selected
physical cache entry; the final negative branch and halt are included. -/
theorem execution {n A N r O T phaseBank B : ℕ} (x : Fin n→ℂ) (s : State)
 (es : List Event) (h : Inputs A N r O T phaseBank s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 281 ≤ B) (count : es.length=N) (selection : Selections A 0 es s)
 (cached : ∀e∈es,CachedEvent r O phaseBank B e s)
 (selectionFit : A+2*N ≤ phaseBank) (phaseFit : phaseBank+56 ≤ T)
 (poolFit : O+9*r ≤ B) (rowFit : T+3*callTotal r es ≤ B) :
 ∃b u time, BoundedRuns program n x B s (45*r+189) b∧
 BoundedExecution program n x B s time u∧time ≤ 45*r+191+es.length*(9*r+48)∧u.pc=51∧
 Header A N r O T (callTotal r es) phaseBank N u∧
 UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words u∧
 (∀lane:Fin 9,∀i:Fin r,u.scalarHeap (O+lane.val*r+i.val)=some (UniformPairMachine.prepared
  (if lane.val=0 then foldValues es (fun _=>1) i.val else 1)))∧
 u.natHeap=foldRows r T 0 es b.natHeap∧
 (∀z,z<phaseBank→u.natHeap z=s.natHeap z)∧
 (∀z,z<O∨O+9*r ≤ z→u.scalarHeap z=s.scalarHeap z)∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 have tb : T ≤ B:=by omega
 obtain ⟨b,boot,bp,bh,decoder,pool,nf,sf,roots,outputs⟩:=boot_execution x s h pc wb code (by omega) poolFit
 have all : ∀e∈es,CachedEvent r O T B e b:=by
  intro e member
  exact ((cached e member).transfer nf (fun z hz=>sf z (Or.inl hz))).widen (by omega)
 have selected : Selections A 0 es b:=Selections.transfer 0 selection (by omega) selectionFit nf
 have target : UniformGlobalCalendarFactorMerge.Factors O r (fun _=>1) b.scalarHeap:=by
  intro i hi;exact pool i (by omega)
 obtain ⟨u,time,loop,cap,up,uh,out,heap,natFrame,scalarFrame,ur,uo⟩:=loop_execution x b es (fun _=>1) bh bp boot.final_bound code
  (by omega) selected all (by omega) phaseFit decoder target poolFit (by simpa only [Nat.zero_add] using rowFit)
 refine ⟨b,u,(45*r+189)+time,boot,boot.executes loop,by omega,up,(by simpa only [Nat.zero_add] using uh),?_,?_,heap,?_,?_,ur.trans roots,uo.trans outputs⟩
 · exact printed_transfer decoder phaseFit natFrame
 · intro lane i
   by_cases zero : lane.val=0
   · simpa [zero] using out i.val i.isLt
   · rw [ite_eq_right zero,scalarFrame _ (Or.inr ?_)]
     simpa only [Nat.add_assoc] using pool (lane.val*r+i.val) (by
      have mul : lane.val*r ≤ 8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
      have:=i.isLt;omega)
     have mul : r ≤ lane.val*r:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right r (by omega : 1 ≤ lane.val)
     omega
 · intro z below;exact (natFrame z (by omega)).trans (nf z below)
 · intro z outside
   exact (scalarFrame z (by rcases outside with lo|hi;exact Or.inl lo;exact Or.inr (by omega))).trans (sf z outside)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
