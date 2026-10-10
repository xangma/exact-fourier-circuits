import DFTModelGlobalSectorLoopCore
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorLoop
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformSameProgramSectorLoop (Cursor boot setup finish assembly)
open DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
open DFTModelGlobalSectorSaving (ready)
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program DFTModelSavingProgram.program

structure Live (B F A E : ℕ) (xs : List UniformSectorPacking.BlockState)
 (v v0 : ℕ→ℕ→Scalar) (i : ℕ) (s s0 : State) : Prop where
 matched : StateMatch s s0
 pc : s.pc=7
 bound : WordBound B s
 cursor : Cursor xs.length E F i s
 table : Table W E A xs s
 pending : Pending A xs v i s
 pending0 : Pending A xs v0 i s0
 completed : Completed A xs v v0 i s s0
 constants : UniformBinaryCStageMachine.Constants s

structure Frame (F A volume : ℕ) (s s0 u u0 : State) : Prop where
 nat : ∀z,z<F→u.natHeap z=s.natHeap z
 nat0 : ∀z,z<F→u0.natHeap z=s0.natHeap z
 scalar : ∀z,z<F→(z<A∨A+W*volume≤z)→u.scalarHeap z=s.scalarHeap z
 scalar0 : ∀z,z<F→(z<A∨A+W*volume≤z)→u0.scalarHeap z=s0.scalarHeap z
 outputs : u.outputs=s.outputs
 outputs0 : u0.outputs=s0.outputs
 roots : u.rootOrders=s.rootOrders
 roots0 : u0.rootOrders=s0.rootOrders

lemma Frame.refl (F A V : ℕ) (s s0 : State) : Frame F A V s s0 s s0 :=
 ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl,rfl,rfl⟩
lemma Frame.trans {F A V : ℕ} {s s0 u u0 t t0 : State}
 (a : Frame F A V s s0 u u0) (b : Frame F A V u u0 t t0) : Frame F A V s s0 t t0 :=
 ⟨fun z hz=>(b.nat z hz).trans (a.nat z hz),fun z hz=>(b.nat0 z hz).trans (a.nat0 z hz),
 fun z hz h=>(b.scalar z hz h).trans (a.scalar z hz h),
 fun z hz h=>(b.scalar0 z hz h).trans (a.scalar0 z hz h),
 b.outputs.trans a.outputs,b.outputs0.trans a.outputs0,b.roots.trans a.roots,b.roots0.trans a.roots0⟩

lemma branch {B n M E F i : ℕ} (x : Fin n→ℂ) (s : State)
 (h : Cursor M E F i s) (hi : i<M) (pc : s.pc=7) (wb : WordBound B s)
 (code : UniformSameProgramSectorLoop.program.length≤B) :
 BoundedRuns UniformSameProgramSectorLoop.program n x B s 1 (setPC s 8) := by
 have fit : 8≤B:=by rw[UniformSameProgramSectorLoop.program_length] at code;omega
 exact .next wb
  (by rw[UniformSameProgramSectorLoop.program]
      change step (assembly child) n x s=_
      simp[step,pc,UniformSameProgramSectorLoop.branch_at,h.index,h.count,hi,setPC])
  (.refl (changePC_bound B s 8 wb fit))

lemma return_runs {B n M E F i : ℕ} (x : Fin n→ℂ) (u : State)
 (h : Cursor M E F i u) (hi : i<M)
 (bound : WordBound B (setPC u (17+child.length)))
 (code : UniformSameProgramSectorLoop.program.length≤B) :
 BoundedRuns UniformSameProgramSectorLoop.program n x B (setPC u (17+child.length)) 2 (tick child u) := by
 have code' : child.length+20≤B:=by rw[UniformSameProgramSectorLoop.program_length] at code;exact code
 let r:=setPC u (17+child.length)
 have cr : Cursor M E F i r:=cursor_withPC h _
 have count : M≤B := by have:=bound.2.1 5890;change u.natReg 5890≤B at this;rw[h.count] at this;exact this
 have safe : readable finish r ∧peak finish r≤B:=by
  simp[finish,readable,peak,Op.readable,Op.peak,cr.index,cr.one];omega
 have first:=block_runs finish (assembly child) (17+child.length) n B x r (finish_code child)
  rfl bound (by rw[UniformSameProgramSectorLoop.finish_length];omega) safe.1 safe.2
 let a:=applyBlock finish r
 have pc : a.pc=18+child.length:=by
  rw[applyBlock_pc];simp only[r,setPC,UniformSameProgramSectorLoop.finish_length];omega
 have eq : tick child u=setPC a 7:=by
  simp[tick,a,r,finish,applyBlock,Op.apply,setPC,writeNat,next]
 have last : BoundedRuns (assembly child) n x B a 1 (tick child u):=by
  rw[eq]
  exact .next first.final_bound (by rw[step,pc,jump_at];rfl)
   (.refl (changePC_bound B a 7 first.final_bound (by omega)))
 rw[UniformSameProgramSectorLoop.program]
 change BoundedRuns (assembly child) n x B _ _ _
 simpa only[UniformSameProgramSectorLoop.finish_length] using first.trans last

/-- One actual branch, original setup9, the closed child, and increment/backedge.
Both mathematical source runs share the same literal sites and native tick count. -/
theorem iteration {n B F A E K i : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : Geometry W B F reserve A E xs) (x : Fin n→ℂ) (v v0 : ℕ→ℕ→Scalar)
 (s s0 : State) (h : Live B F A E xs v v0 i s s0) (hi : i<xs.length)
 (code : UniformSameProgramSectorLoop.program.length≤B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K) :
 ∃u u0 childTicks,
 BoundedRuns UniformSameProgramSectorLoop.program n x B s (childTicks+12) u ∧
 BoundedRuns UniformSameProgramSectorLoop.program n (fun _=>0) B s0 (childTicks+12) u0 ∧
 Live B F A E xs v v0 (i+1) u u0 ∧ Frame F A g.volume s s0 u u0 ∧
 bill v v0 (xs[i]'hi)≤K*childTicks := by
 let e:=setPC s 8
 let e0:=setPC s0 8
 have first:=branch x s h.cursor hi h.pc h.bound code
 have matched : StateMatch e e0:=h.matched.withPC 8
 have cursor : Cursor xs.length E F i e:=cursor_withPC h.cursor _
 have extent : A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs≤F:=by
  rw[←g.pow i hi]
  have fit:=Nat.mul_le_mul_left W (g.fits i hi);have bank:=g.bank;nlinarith
 obtain ⟨t,t0,childTicks,out,out0,run,run0,result⟩:=DFTModelGlobalSectorSaving.execution
  n B xs.length E A F i K (xs[i]'hi) x e e0 (input v (xs[i]'hi)) (input v0 (xs[i]'hi))
  matched cursor hi (h.table i hi) (g.pow i hi) (h.pending i hi (by omega))
  (h.pending0 i hi (by omega)) (by have:=g.low;omega) extent (g.directory.trans g.frontier)
  code (g.room i hi) (g.square i hi) cap h.constants rfl first.final_bound
 have tc:=DFTModelGlobalSectorSavingCallerFrame.cursor_after_root result.actual cursor
 have last:=return_runs x t tc hi run.final_bound code
 have tc0 : Cursor xs.length E F i t0:=by
  constructor <;>rw[result.matched.natReg]
  all_goals first|exact tc.count|exact tc.one|exact tc.index|exact tc.directory|exact tc.fresh|exact tc.zero|exact tc.five
 have last0:=return_runs (fun _ : Fin n=>0) t0 tc0 hi run0.final_bound code
 have cursor0 : Cursor xs.length E F i s0:=by
  constructor <;>rw[h.matched.natReg]
  all_goals first|exact h.cursor.count|exact h.cursor.one|exact h.cursor.index|exact h.cursor.directory|
   exact h.cursor.fresh|exact h.cursor.zero|exact h.cursor.five
 have first0:=branch (fun _ : Fin n=>0) s0 cursor0 hi (h.matched.pc.trans h.pc) (h.matched.wordBound h.bound) code
 have actual:=first.trans (run.trans last)
 have baseline:=first0.trans (run0.trans last0)
 have done : Completed A xs v v0 (i+1) t t0:=completed_step g hi v v0 s s0 t t0 h.completed
  ⟨out,out0,result.data,result.data0,result.compiled⟩ result.scalarHeap result.scalarHeap0
 refine ⟨tick child t,tick child t0,childTicks,?_,?_,?_,?_,result.work⟩
 · simpa only[Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual
 · simpa only[Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using baseline
 · refine ⟨DFTModelSavingNativeControl.paired_runs actual baseline h.matched,rfl,last.final_bound,
     tick_cursor child t tc,?_,?_,?_,done,result.constants⟩
   · exact table_transfer g (ready e) t h.table result.natHeap
   · exact pending_step g hi v s t h.pending result.scalarHeap
   · exact pending_step g hi v0 s0 t0 h.pending0 result.scalarHeap0
 · refine ⟨result.natHeap,result.natHeap0,?_,?_,result.outputs,result.outputs0,result.roots,result.roots0⟩
   · intro z hz outside
     exact result.scalarHeap z hz (by rw[←g.pow i hi];exact global_separate g hi z outside)
   · intro z hz outside
     exact result.scalarHeap0 z hz (by rw[←g.pow i hi];exact global_separate g hi z outside)

end
end ExactFourierCircuits.DFTModelGlobalSectorLoop
