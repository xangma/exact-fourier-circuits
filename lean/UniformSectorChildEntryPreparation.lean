import UniformSectorTransposeMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorChildEntryPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorTransposeMachine (Geometry Header Source Filled Outside)
/-- The actual34 gather, followed by four charged child-header moves. Nat4534
is an ordinary fresh frontier; q/base/2^q are physically loaded by the34.
This is an entry adapter, not a theorem executing the recursive child. -/
def setup:List Op:=[.add 4120 4556 4551,.add 4121 4558 4551,
 .add 4122 4557 4551,.add 4123 4534 4551]
def programFor (W:ℕ):Program:=(UniformSectorTransposeMachine.programFor W false).map (relocate 0 34)++
 setup.map Op.code++[.halt]
def program:Program:=programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W:ℕ):(programFor W).length=39:=rfl
lemma transpose_code (W:ℕ):CodeAt (UniformSectorTransposeMachine.programFor W false) (programFor W) 0 34:=by
 exact UniformRankCrossPreparationMachine.segment_code [] (setup.map Op.code++[.halt]) _ 0 34 rfl
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 34:=by
 intro i hi;change i < 4 at hi;interval_cases i <;>rfl
lemma halt_at (W:ℕ):(programFor W)[38]?=some .halt:=rfl
noncomputable section
structure ChildHeader (q base width frontier:ℕ) (s:State):Prop where
 exponent:s.natReg 4120=q
 base:s.natReg 4121=base
 width:s.natReg 4122=width
 frontier:s.natReg 4123=frontier

def Frame (s u:State):Prop:=u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q≠32 → u.scalarReg q=s.scalarReg q) ∧
 ∀q,(q < 147 ∨154 ≤ q)→(q < 4120 ∨4124 ≤ q)→(q < 4550 ∨4562 ≤ q)→u.natReg q=s.natReg q
lemma setup_frame (s:State):Frame s (applyBlock setup s):=by
 refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma frame_compose {s u v:State} (h:UniformSectorTransposeMachine.Frame s u) (k:Frame u v):Frame s v:=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 fun q hq=>(k.2.2.2.1 q hq).trans (h.2.2.2.1 q hq),
 fun q h0 h1 h2=>(k.2.2.2.2 q h0 h1 h2).trans (h.2.2.2.2 q h0 h2)⟩
lemma setup_header {W frontier:ℕ} {g:Geometry W false} {s:State}
 (h:UniformSectorTransposeMachine.Cursor g W s) (f:s.natReg 4534=frontier):
 ChildHeader g.sector.pairs (g.buffer+W*g.sector.start) g.sector.width frontier (applyBlock setup s):=by
 constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.zero,h.exponent,h.base,h.width,f]
lemma setup_safe {W frontier:ℕ} {g:Geometry W false} {s:State}
 (h:UniformSectorTransposeMachine.Cursor g W s) (f:s.natReg 4534=frontier) (fb:frontier ≤ g.B)
 (wb:WordBound g.B s):readable setup s ∧peak setup s ≤ g.B:=by
 have qb:=wb.2.1 4556
 have width:=wb.2.1 4557
 have base:=wb.2.1 4558
 rw[h.exponent] at qb
 rw[h.width] at width
 rw[h.base] at base
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.zero,h.exponent,h.base,h.width,f]
 omega

/-- No ready child headers or contiguous child bank are entry premises. The
actual generated record is consumed; every scalar is moved by the real34. -/
theorem execution {W n frontier:ℕ} (g:Geometry W false) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (h:Header g s) (cell:UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer g.ordinal g.sector s)
 (source:Source g v s) (f:s.natReg 4534=frontier) (fb:frontier ≤ g.B)
 (code:39 ≤ g.B) (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W) n x g.B s (W*(7*g.sector.width+12)+22) u ∧u.pc=38 ∧
 ChildHeader g.sector.pairs (g.buffer+W*g.sector.start) g.sector.width frontier u ∧
 Filled g v W u ∧Frame s u ∧Outside g s.scalarHeap u:=by
 obtain ⟨t,run,tp,cursor,filled,frame,out⟩:=UniformSectorTransposeMachine.execution g v x s h cell source pc wb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (transpose_code W)
  (by rw[UniformSectorTransposeMachine.program_length];omega) (by omega) run
 have zero:placed 0 s=s:=by cases s;simp[placed]
 rw[zero] at moved
 let ready:=setPC t 34
 have cr:UniformSectorTransposeMachine.Cursor g W ready:=cursor.withPC
 have fr:ready.natReg 4534=frontier:=(frame.2.2.2.2 4534 (Or.inr (by omega)) (Or.inl (by omega))).trans f
 have safe:=setup_safe cr fr fb moved.final_bound
 have start:=block_runs setup (programFor W) 34 n g.B x ready (setup_code W) rfl moved.final_bound
  (by change 34+4 ≤ g.B;omega) safe.1 safe.2
 let u:=applyBlock setup ready
 have up:u.pc=38:=by rw[applyBlock_pc];rfl
 have stop:BoundedExecution (programFor W) n x g.B u 1 u:=.halt start.final_bound
  (by rw[step,up,halt_at])
 refine ⟨u,?_,up,setup_header cr fr,filled,frame_compose frame (setup_frame ready),out⟩
 convert moved.executes (start.executes stop) using 1
 change W*(7*g.sector.width+12)+22=W*(7*g.sector.width+12)+17+(4+1)
 omega
lemma child_width {W frontier:ℕ} {g:Geometry W false} {s:State}
 (width:g.sector.width=2^g.sector.pairs)
 (h:ChildHeader g.sector.pairs (g.buffer+W*g.sector.start) g.sector.width frontier s):
 s.natReg 4122=2^(s.natReg 4120):=by rw[h.width,h.exponent,width]
end
end ExactFourierCircuits.UniformSectorChildEntryPreparation
