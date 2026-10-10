import DFTModelSavingNativePaddingExecutionResult

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingExecution
open UniformMachine DFTModelAdmissibilityControl UniformRecursivePaddingFrames
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursivePaddingRole (record roleCost)
open DFTModelSavingNativePaddingControl (parent_match printed_match)
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.residual DFTModelCacheRecords.unit

/-- The actual eleven-step initialization followed by the ascending role loop.
The internal role obligation is discharged by the same-program role theorem. -/
theorem execution (n B U R A F q w r stack depth stackTop saved start : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (handler : Handler DFTModelSavingRecords.Port)
    (roles : ∀(role : Fin R)(prior : ℕ)(a a0 : State)
      (X X0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar),
      StateMatch a a0→a.pc=P.address .paddingPatch→
      Parent (q*(w+1)+r) q A F r stack depth a→
      Metadata F U saved role.val R a→a.natReg 4175=role.val→
      Printed U (UniformRecursivePaddingControl.patchRecord (record w) q prior).data a→
      Present A R (2^(q*(w+1)+r)) X a→Present A R (2^(q*(w+1)+r)) X0 a0→
      UniformBinaryCStageMachine.Constants a→WordBound B a→
      ∃b b0 ticks Y Y0,DFTModelSavingNativePaddingRole.Result n B U R A F q w r
        stack depth stackTop saved R cost x role I handler a a0 b b0 ticks X X0 Y Y0)
    (s s0 : State) (f f0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .paddingInit)
    (parent : Parent (q*(w+1)+r) q A F r stack depth s)
    (savedHeader : s.natReg 2865=saved) (destHeader : s.natReg 2854=start)
    (countHeader : s.natReg 2855=R-start) (pointer : s.natHeap (F-2)=some U)
    (printed : Printed U ((record w).withColumns q).data s)
    (present : Present A R (2^(q*(w+1)+r)) f s)
    (present0 : Present A R (2^(q*(w+1)+r)) f0 s0)
    (startBound : start ≤ R) (unitEnd : U+(record w).data.length ≤ F-6)
    (recordAbove : stackTop ≤ U) (rolesBound : R ≤ B) (low : 6 ≤ F)
    (constants : UniformBinaryCStageMachine.Constants s)
    (bound : WordBound B s) (code : P.program.length ≤ B) :
    ∃u u0 ticks g g0 prior,
      Result n B U R A F q w r stack depth stackTop saved start cost x I handler
        s s0 u u0 ticks prior f f0 g g0 := by
  have endBound:start+(R-start) ≤ B:=by omega
  obtain ⟨a,init,ap,pa,ma,ifr⟩:=DFTModelSavingNativePaddingControl.init
    n B (q*(w+1)+r) q A F r stack depth U saved start (R-start) x s pc parent
      pointer savedHeader destHeader countHeader low bound code endBound
  obtain ⟨a0,init0,_,_,_,ifr0⟩:=DFTModelSavingNativePaddingControl.init
    n B (q*(w+1)+r) q A F r stack depth U saved start (R-start) (fun _=>0) s0
      (same.pc.trans pc) (parent_match same parent) (by rw [same.natHeap];exact pointer)
      (by rw [same.natReg];exact savedHeader) (by rw [same.natReg];exact destHeader)
      (by rw [same.natReg];exact countHeader) low (same.wordBound bound) code endBound
  have matched:=DFTModelSavingNativeControl.paired_runs init init0 same
  have metadata:Metadata F U saved start R a:=by
    simpa only [Nat.add_sub_of_le startBound] using ma
  have printA:Printed U (UniformRecursivePaddingControl.patchRecord (record w) q 0).data a:=by
    rw [←UniformRecursivePaddingExecution.record_columns]
    intro j hj
    have len:((record w).withColumns q).data.length=(record w).data.length:=by
      rw [UniformFixedNetworkScheduleMachine.Record.data_length,
        UniformFixedNetworkScheduleMachine.Record.data_length];rfl
    have less:U+j<F-6:=by rw [len] at hj;omega
    rw [ifr.natHeap _ (by simp only [List.mem_cons,List.mem_nil_iff,or_false];omega)]
    exact printed j hj
  have dataA:Present A R (2^(q*(w+1)+r)) f a:=by
    intro i z;rw [ifr.scalarHeap];exact present i z
  have dataA0:Present A R (2^(q*(w+1)+r)) f0 a0:=by
    intro i z;rw [ifr0.scalarHeap];exact present0 i z
  have ca:UniformBinaryCStageMachine.Constants a:=by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [ifr.scalarHeap];exact constants
  have visit:UniformRecursiveResidualDirectionLoop.Visit R start
      (UniformRecursivePaddingExecution.remaining R start startBound):=
    UniformRecursiveResidualDirectionLoop.indices_visit R start (R-start) (by omega)
  obtain ⟨u,u0,ut,g,g0,prior,loop⟩:=DFTModelSavingNativePaddingLoop.loop
    n B U R A F q w r stack depth stackTop saved start 0 cost x I handler
      (UniformRecursivePaddingExecution.remaining R start startBound) visit roles a a0 f f0
      matched ap pa metadata printA dataA dataA0 low ca init.final_bound code
  have length:=UniformRecursivePaddingExecution.remaining_length R start startBound
  have nh (z : ℕ) (hz : z<F) (away : z<stack+34*depth∨stackTop ≤ z)
      (a : z≠U+1) (b : z≠U+3) (c : z≠F-6) (d : z≠F-5) (e : z≠F-4) (f : z≠F-3) :
      u.natHeap z=s.natHeap z :=
    (loop.nat z hz away a b e).trans (ifr.natHeap z
      (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨c,d,e,f⟩))
  have nh0 (z : ℕ) (hz : z<F) (away : z<stack+34*depth∨stackTop ≤ z)
      (a : z≠U+1) (b : z≠U+3) (c : z≠F-6) (d : z≠F-5) (e : z≠F-4) (f : z≠F-3) :
      u0.natHeap z=s0.natHeap z :=
    (loop.zeroNat z hz away a b e).trans (ifr0.natHeap z
      (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or];exact ⟨c,d,e,f⟩))
  have unitLength:=UniformRecursivePaddingRole.record_length w
  refine ⟨u,u0,11+ut,g,g0,prior,?_⟩
  refine {
    run:=init.trans loop.run,zeroRun:=init0.trans loop.zeroRun,matched:=loop.matched,
    pc:=loop.pc,cursor:=loop.cursor,parent:=loop.parent,zeroParent:=loop.zeroParent,
    printed:=loop.printed,present:=loop.present,zeroPresent:=loop.zeroPresent,
    endPointer:=nh (F-1) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    zeroEndPointer:=nh0 (F-1) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    unitPointer:=nh (F-2) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    zeroUnitPointer:=nh0 (F-2) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    nat:=nh,zeroNat:=nh0,scalar:=?_,zeroScalar:=?_,constants:=loop.constants,zeroConstants:=loop.zeroConstants,
    roots:=loop.roots.trans ifr.roots,zeroRoots:=loop.zeroRoots.trans ifr0.roots,
    outputs:=loop.outputs.trans ifr.outputs,zeroOutputs:=loop.zeroOutputs.trans ifr0.outputs,
    time:=?_,value:=?_,values:=?_,zeroValues:=?_}
  · intro z hz away;exact (loop.scalar z hz away).trans (congrFun ifr.scalarHeap z)
  · intro z hz away;exact (loop.zeroScalar z hz away).trans (congrFun ifr0.scalarHeap z)
  · have time:=loop.time;rw [length] at time;omega
  · simpa only [length] using loop.value
  · intro i
    rw [congrFun loop.values i]
    exact UniformRecursivePaddingExecution.action_remaining q w r R start startBound _ i
  · intro i
    rw [congrFun loop.zeroValues i]
    exact UniformRecursivePaddingExecution.action_remaining q w r R start startBound _ i

end
end ExactFourierCircuits.DFTModelSavingNativePaddingExecution
