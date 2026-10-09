import UniformAxisCacheCallerInstaller
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePoolInstaller
open UniformMachine UniformTensorMonomialMachine
namespace I
export UniformAxisCacheCallerInstaller (ops forestOps destinations)
end I

/-- The optional tenth operation installs the allocated axis pool base.
Per-rectangle pool advancement belongs to the outer request driver. -/
def poolOp:Op:=.add 6160 6820 6830
def ops:List Op:=I.ops++[poolOp]
lemma ops_length:ops.length=10:=rfl
def program:Program:=ops.map Op.code++[.halt]
lemma program_length:program.length=11:=rfl
lemma ops_code:BlockAt ops program 0:=by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma halt_at:program[10]?=some .halt:=rfl
structure Installed(s u:State):Prop where
 caller:UniformAxisCacheCallerInstaller.Installed s u
 pool:u.natReg 6160=s.natReg 6820
structure Frame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 rootOrders:u.rootOrders=s.rootOrders
 registers:∀q,q≠6160→q∉I.destinations→u.natReg q=s.natReg q
lemma installed(s:State):Installed s (applyBlock ops s):=by
 constructor
 · constructor
   all_goals constructor <;>simp [ops,I.ops,UniformAxisCacheCallerInstaller.ops,
    UniformAxisCacheTimingInstaller.ops,I.forestOps,UniformAxisCacheCallerInstaller.forestOps,
    poolOp,applyBlock,Op.apply,writeNat,next]
 · simp [ops,I.ops,UniformAxisCacheCallerInstaller.ops,UniformAxisCacheTimingInstaller.ops,
    I.forestOps,UniformAxisCacheCallerInstaller.forestOps,poolOp,applyBlock,Op.apply,writeNat,next]
lemma frame(s:State):Frame s (applyBlock ops s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hp hq
 simp only [I.destinations,UniformAxisCacheCallerInstaller.destinations,List.mem_cons,
  List.not_mem_nil,or_false,not_or] at hq
 simp [ops,I.ops,UniformAxisCacheCallerInstaller.ops,UniformAxisCacheTimingInstaller.ops,
  I.forestOps,UniformAxisCacheCallerInstaller.forestOps,poolOp,applyBlock,Op.apply,writeNat,next,hp,
  hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2.1,hq.2.2.2.2.2.1,
  hq.2.2.2.2.2.2.1,hq.2.2.2.2.2.2.2.1,hq.2.2.2.2.2.2.2.2]
lemma safe(B:ℕ)(s:State)(hs:WordBound B s):readable ops s∧peak ops s≤B:=by
 have a:=hs.2.1 6816
 have b:=hs.2.1 6817
 have c:=hs.2.1 6818
 have d:=hs.2.1 6800
 have e:=hs.2.1 6810
 have f:=hs.2.1 6811
 have g:=hs.2.1 6812
 have h:=hs.2.1 6820
 constructor
 · simp [ops,I.ops,UniformAxisCacheCallerInstaller.ops,UniformAxisCacheTimingInstaller.ops,
    I.forestOps,UniformAxisCacheCallerInstaller.forestOps,poolOp,readable,Op.readable]
 · simp [ops,I.ops,UniformAxisCacheCallerInstaller.ops,UniformAxisCacheTimingInstaller.ops,
    I.forestOps,UniformAxisCacheCallerInstaller.forestOps,poolOp,peak,Op.peak,Op.apply,writeNat,next]
   all_goals omega

theorem ten(main:Program)(start n B:ℕ)(x:Fin n→ℂ)(s:State)
 (code:BlockAt ops main start)(hp:s.pc=start)(hs:WordBound B s)(extent:start+10≤B):
 BoundedRuns main n x B s 10 (applyBlock ops s)∧
 (applyBlock ops s).pc=start+10∧Installed s (applyBlock ops s)∧Frame s (applyBlock ops s):=by
 have bounds:=safe B s hs
 refine ⟨?_,?_,installed s,frame s⟩
 · simpa only [ops_length] using block_runs ops main start n B x s code hp hs
    (by simpa only [ops_length] using extent) bounds.1 bounds.2
 · rw [applyBlock_pc,hp,ops_length]

theorem execution(n B:ℕ)(x:Fin n→ℂ)(s:State)(hp:s.pc=0)(hs:WordBound B s)(code:11≤B):
 ∃u,BoundedExecution program n x B s 11 u∧u.pc=10∧Installed s u∧Frame s u:=by
 have h:=ten program 0 n B x s ops_code hp hs (by omega)
 have halt:BoundedExecution program n x B (applyBlock ops s) 1 (applyBlock ops s):=
  .halt h.1.final_bound (by simp [UniformMachine.step,h.2.1,halt_at])
 refine ⟨applyBlock ops s,?_,by simpa using h.2.1,h.2.2.1,h.2.2.2⟩
 simpa only [show 10+1=11 by rfl] using h.1.executes halt
end ExactFourierCircuits.UniformAxisCachePoolInstaller
