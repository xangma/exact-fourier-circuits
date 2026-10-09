import UniformGlobalCalendarDispatchEvents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine
noncomputable section

lemma callTotal_cons (r : ℕ) (e : Event) (es : List Event) :
 callTotal r (e::es)=callCount r e+callTotal r es:=rfl

/-- Every selected physical cache entry is visited by the literal281 program.
The accumulator and row heap are exactly the folds of the real selected
sources. The final negative loop test and halt are charged. -/
theorem loop_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (es : List Event) (g : ℕ→ℂ) (h : Header A N r O T used phaseBank j s)
 (pc : s.pc=10) (wb : WordBound B s) (code : 281 ≤ B) (ending : j+es.length=N)
 (selection : Selections A j es s) (cached : ∀e∈es,CachedEvent r O T B e s)
 (selectionFit : A+2*N ≤ T) (phaseFit : phaseBank+56 ≤ T)
 (printed : UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words s)
 (target : UniformGlobalCalendarFactorMerge.Factors O r g s.scalarHeap)
 (poolFit : O+9*r ≤ B) (rowFit : T+3*(used+callTotal r es) ≤ B) :
 ∃u time, BoundedExecution program n x B s time u∧time ≤ es.length*(9*r+48)+2∧u.pc=51∧
 Header A N r O T (used+callTotal r es) phaseBank N u∧
 UniformGlobalCalendarFactorMerge.Factors O r (foldValues es g) u.scalarHeap∧
 u.natHeap=foldRows r T used es s.natHeap∧
 (∀z,z<T→u.natHeap z=s.natHeap z)∧
 (∀z,z<O∨O+r ≤ z→u.scalarHeap z=s.scalarHeap z)∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 induction es generalizing j used s g with
 | nil=>
   have index:j=N:=by simpa only [List.length_nil,Nat.add_zero] using ending
   let u:State:={s with pc:=51}
   have run : BoundedRuns program n x B s 1 u:=control x s wb (by omega)
    (by simp [step,pc,code_10,h.index,h.count,index])
   have halted : step program n x u=.halted u:=by simp [step,u,code_51]
   refine ⟨u,2,run.executes (.halt run.final_bound halted),?_,rfl,?_,target,rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
   · simp only [List.length_nil,Nat.zero_mul,Nat.zero_add];exact le_rfl
   · simpa only [callTotal,List.map_nil,List.sum_nil,Nat.add_zero,index] using h.atPC 51
 | cons e es ih=>
   rcases selection with ⟨selected,rest⟩
   have cache:=cached e (by simp)
   have index:j<N:=by simp only [List.length_cons] at ending;omega
   have total:=callTotal_cons r e es
   have budget : T+3*((used+callCount r e)+callTotal r es) ≤ B:=by rw [total] at rowFit;omega
   have current : T+3*(used+callCount r e) ≤ B:=by omega
   have tb : T ≤ B:=by omega
   obtain ⟨u,time,cycle,cap,up,uh,out,heap,natFrame,scalarFrame,roots,outputs⟩:=cycle_execution x s e.descriptor e.phase
    e.factor g e.records h selected cache.stored cache.decoded pc wb code index
    (by omega) (by have:=cache.entryFit;omega) printed (by omega) cache.source target
    (by have:=cache.sourcePool;omega) cache.sourcePool (by omega)
    (by have:=cache.sourceRows;omega) cache.sourceRows cache.values current cache.matching
   have all : ∀a∈es,CachedEvent r O T B a u:=by
    intro a member
    exact (cached a (by simp [member])).transfer natFrame (fun z hz=>scalarFrame z (Or.inl hz))
   have remaining : Selections A (j+1) es u:=Selections.transfer (j+1) rest
    (by simp only [List.length_cons] at ending;omega) selectionFit natFrame
   have decoder:=printed_transfer printed phaseFit natFrame
   obtain ⟨v,tailTime,tail,tailCap,vp,vh,result,rows,nf,sf,vr,vo⟩:=ih u
    (fun i=>phaseFactor e.phase e.factor i*g i) uh up cycle.final_bound
    (by simp only [List.length_cons] at ending;omega) remaining all decoder out budget
   refine ⟨v,time+tailTime,cycle.executes tail,?_,vp,?_,result,?_,?_,?_,vr.trans roots,vo.trans outputs⟩
   · simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
   · simpa only [total,callCount,Nat.add_assoc] using vh
   · exact rows.trans (congrArg (foldRows r T (used+callCount r e) es) heap)
   · intro z hz;exact (nf z hz).trans (natFrame z hz)
   · intro z outside;exact (sf z outside).trans (scalarFrame z outside)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
