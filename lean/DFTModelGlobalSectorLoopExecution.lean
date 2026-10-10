import DFTModelGlobalSectorLoopStep
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorLoop
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformSameProgramSectorLoop (Cursor boot setup finish assembly)
open DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program DFTModelSavingProgram.program

/-- `trace` records the actual closed-root ticks in source sector order.
No tick or output is supplied to construct this result. -/
structure Result (n B F A E K volume : ℕ) (xs todo : List UniformSectorPacking.BlockState)
 (v v0 : ℕ→ℕ→Scalar) (x : Fin n→ℂ) (s s0 u u0 : State) (ticks overhead : ℕ)
 (trace : List ℕ) : Prop where
 actual : BoundedExecution UniformSameProgramSectorLoop.program n x B s ticks u
 baseline : BoundedExecution UniformSameProgramSectorLoop.program n (fun _=>0) B s0 ticks u0
 matched : StateMatch u u0
 pc : u.pc=19+child.length
 cursor : Cursor xs.length E F xs.length u
 table : Table W E A xs u
 completed : Completed A xs v v0 xs.length u u0
 constants : UniformBinaryCStageMachine.Constants u
 frame : Frame F A volume s s0 u u0
 calls : trace.length=todo.length
 exactTicks : ticks=trace.sum+12*todo.length+overhead
 work : (todo.map (bill v v0)).sum≤K*trace.sum

/-- Finite induction over the real remaining sector rows. Every child witness
is constructed by `iteration`, which invokes the closed recursive theorem. -/
theorem loop (remaining : List UniformSectorPacking.BlockState)
 {n B F A E K : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : Geometry W B F reserve A E xs) (x : Fin n→ℂ) (v v0 : ℕ→ℕ→Scalar)
 (code : UniformSameProgramSectorLoop.program.length≤B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K) :
 ∀i s s0,i≤xs.length→xs.drop i=remaining→Live B F A E xs v v0 i s s0→
 ∃u u0 ticks trace,Result n B F A E K g.volume xs remaining v v0 x s s0 u u0 ticks 2 trace := by
 induction remaining with
 | nil=>
   intro i s s0 le suffix h
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_nil] at length
   have eq:i=xs.length:=by omega
   subst i
   have code' : child.length+20≤B:=by rw[UniformSameProgramSectorLoop.program_length] at code;exact code
   have actual:=stop child x s h.cursor h.pc h.bound code'
   have control0 : Cursor xs.length E F xs.length s0:=by
    constructor <;>rw[h.matched.natReg]
    all_goals first|exact h.cursor.count|exact h.cursor.one|exact h.cursor.index|exact h.cursor.directory|
     exact h.cursor.fresh|exact h.cursor.zero|exact h.cursor.five
   have baseline:=stop child (fun _ : Fin n=>0) s0 control0 (h.matched.pc.trans h.pc)
     (h.matched.wordBound h.bound) code'
   refine ⟨setPC s (19+child.length),setPC s0 (19+child.length),2,[],?_,?_,
     h.matched.withPC _,rfl,cursor_withPC h.cursor _,h.table,h.completed,h.constants,
     ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,rfl,rfl⟩,rfl,by simp,by simp⟩
   · simpa only[UniformSameProgramSectorLoop.program] using actual
   · simpa only[UniformSameProgramSectorLoop.program] using baseline
 | cons st remaining ih=>
   intro i s s0 le suffix h
   have length:=congrArg List.length suffix
   simp only[List.length_drop,List.length_cons] at length
   have hi:i<xs.length:=by omega
   obtain ⟨equal,tail⟩:=List.cons.inj (suffix.symm.trans (List.drop_eq_getElem_cons hi))
   subst st
   obtain ⟨t,t0,rootTicks,first,first0,live,frame,cheap⟩:=iteration g x v v0 s s0 h hi code cap
   obtain ⟨u,u0,ticks,trace,last⟩:=ih (i+1) t t0 (by omega) tail.symm live
   refine ⟨u,u0,(rootTicks+12)+ticks,rootTicks::trace,
     first.executes last.actual,first0.executes last.baseline,last.matched,last.pc,last.cursor,
     last.table,last.completed,last.constants,frame.trans last.frame,?_,?_,?_⟩
   · simpa only[List.length_cons] using congrArg Nat.succ last.calls
   · simp only[List.sum_cons,List.length_cons]
     have eq:=last.exactTicks
     omega
   · simp only[List.map_cons,List.sum_cons]
     have tailWork:=last.work
     nlinarith

/-- The complete unchanged original finite sector-loop assembly, including
boot7 and the final branch/halt2. All gathered sectors have exact paired
Scalar/flag patches; all spectators below the real frontier are retained. -/
theorem execution {n B F A E K : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : Geometry W B F reserve A E xs) (x : Fin n→ℂ) (v v0 : ℕ→ℕ→Scalar)
 (s s0 : State) (same : StateMatch s s0)
 (code : UniformSameProgramSectorLoop.program.length≤B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K)
 (table : Table W E A xs s)
 (source : Pending A xs v 0 s) (source0 : Pending A xs v0 0 s0)
 (constants : UniformBinaryCStageMachine.Constants s)
 (count : s.natReg 464=xs.length) (dir : s.natReg 4441=E) (fresh : s.natReg 5801=F)
 (pc : s.pc=0) (wb : WordBound B s) :
 ∃u u0 ticks trace,Result n B F A E K g.volume xs xs v v0 x s s0 u u0 ticks 9 trace := by
 have code' : child.length+20≤B:=by rw[UniformSameProgramSectorLoop.program_length] at code;exact code
 have safe:=UniformSameProgramSectorLoop.boot_safe wb (by omega)
 have bootRun:=block_runs boot (assembly child) 0 n B x s (UniformSameProgramSectorLoop.boot_code child)
   pc wb (by rw[UniformSameProgramSectorLoop.boot_length];omega) safe.1 safe.2
 have safe0:=UniformSameProgramSectorLoop.boot_safe (same.wordBound wb) (by omega)
 have bootRun0:=block_runs boot (assembly child) 0 n B (fun _=>0) s0 (UniformSameProgramSectorLoop.boot_code child)
   (same.pc.trans pc) (same.wordBound wb) (by rw[UniformSameProgramSectorLoop.boot_length];omega) safe0.1 safe0.2
 let a:=applyBlock boot s
 let a0:=applyBlock boot s0
 have ap : a.pc=7:=by rw[applyBlock_pc,pc,UniformSameProgramSectorLoop.boot_length]
 have control:=UniformSameProgramSectorLoop.boot_cursor xs.length E F s count dir fresh
 have empty : Completed A xs v v0 0 a a0:=by intro j hj h;omega
 have live : Live B F A E xs v v0 0 a a0:=
  ⟨DFTModelSavingNativeControl.paired_runs bootRun bootRun0 same,ap,bootRun.final_bound,
   control,table,source,source0,empty,constants⟩
 obtain ⟨u,u0,ticks,trace,result⟩:=loop xs g x v v0 code cap 0 a a0 (by omega) (by simp) live
 refine ⟨u,u0,7+ticks,trace,?_,?_,result.matched,result.pc,result.cursor,result.table,
   result.completed,result.constants,
   ⟨result.frame.nat,result.frame.nat0,result.frame.scalar,result.frame.scalar0,
    result.frame.outputs,result.frame.outputs0,result.frame.roots,result.frame.roots0⟩,result.calls,?_,result.work⟩
 · have first : BoundedRuns UniformSameProgramSectorLoop.program n x B s 7 a:=by
     simpa only[UniformSameProgramSectorLoop.program,UniformSameProgramSectorLoop.boot_length] using bootRun
   exact first.executes result.actual
 · have first : BoundedRuns UniformSameProgramSectorLoop.program n (fun _=>0) B s0 7 a0:=by
     simpa only[UniformSameProgramSectorLoop.program,UniformSameProgramSectorLoop.boot_length] using bootRun0
   exact first.executes result.baseline
 · have eq:=result.exactTicks;omega

/-- The charged closed child work is bounded by the SAME complete native
witness. Early loop termination is exactly the empty-sector case, charged9. -/
theorem Result.work_native {n B F A E K volume ticks : ℕ}
 {xs : List UniformSectorPacking.BlockState} {v v0 : ℕ→ℕ→Scalar} {x : Fin n→ℂ}
 {s s0 u u0 : State} {trace : List ℕ}
 (h : Result n B F A E K volume xs xs v v0 x s s0 u u0 ticks 9 trace) :
 (xs.map (bill v v0)).sum≤K*ticks := by
 have eq:=h.exactTicks
 exact h.work.trans (Nat.mul_le_mul_left K (by omega))

end
end ExactFourierCircuits.DFTModelGlobalSectorLoop
