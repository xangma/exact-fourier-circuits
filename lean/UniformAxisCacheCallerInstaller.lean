import UniformAxisCacheTimingInstaller
import UniformLocalCacheTimingConductor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheCallerInstaller
open UniformMachine UniformTensorMonomialMachine
namespace I
export UniformAxisCacheTimingInstaller (ops)
end I

def forestOps:List Op:=[.add 4270 6800 6830,.literal 4271 0,.add 4272 6810 6830,
 .add 4273 6811 6830,.add 4274 6812 6830]
def ops:List Op:=I.ops++forestOps
lemma ops_length:ops.length=9:=rfl
def program:Program:=ops.map Op.code++[.halt]
lemma program_length:program.length=10:=rfl
lemma ops_code:BlockAt ops program 0:=by
 intro i hi;change i<9 at hi;interval_cases i <;>rfl
lemma halt_at:program[9]?=some .halt:=rfl

structure Installed(s u:State):Prop where
 timing:UniformAxisCacheTimingInstaller.Installed s u
 forest:UniformLocalCacheTreeIteration.Header (s.natReg 6800) 0 (s.natReg 6810) (s.natReg 6811) (s.natReg 6812) u
 allocation:UniformLocalCacheTimingConductor.Allocation (s.natReg 6816) (s.natReg 6817) (s.natReg 6818) u

def destinations:List ℕ:=[6830,6175,6176,6177,4270,4271,4272,4273,4274]
structure Frame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 rootOrders:u.rootOrders=s.rootOrders
 registers:∀q,q∉destinations→u.natReg q=s.natReg q

lemma installed(s:State):Installed s (applyBlock ops s):=by
 constructor
 all_goals constructor <;>simp [ops,I.ops,UniformAxisCacheTimingInstaller.ops,forestOps,applyBlock,Op.apply,writeNat,next]
lemma frame(s:State):Frame s (applyBlock ops s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q hq
 simp only [destinations,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
 simp [ops,I.ops,UniformAxisCacheTimingInstaller.ops,forestOps,applyBlock,Op.apply,writeNat,next,
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
 constructor
 · simp [ops,I.ops,UniformAxisCacheTimingInstaller.ops,forestOps,readable,Op.readable]
 · simp [ops,I.ops,UniformAxisCacheTimingInstaller.ops,forestOps,peak,Op.peak,Op.apply,writeNat,next]
   all_goals omega

/-- Exactly nine charged instructions install the actual forest Header and
301-conductor allocation from real axis output registers. -/
theorem nine(main:Program)(start n B:ℕ)(x:Fin n→ℂ)(s:State)
 (code:BlockAt ops main start)(hp:s.pc=start)(hs:WordBound B s)(extent:start+9≤B):
 BoundedRuns main n x B s 9 (applyBlock ops s)∧
 (applyBlock ops s).pc=start+9∧Installed s (applyBlock ops s)∧Frame s (applyBlock ops s):=by
 have bounds:=safe B s hs
 refine ⟨?_,?_,installed s,frame s⟩
 · simpa only [ops_length] using block_runs ops main start n B x s code hp hs
    (by simpa only [ops_length] using extent) bounds.1 bounds.2
 · rw [applyBlock_pc,hp,ops_length]

theorem execution(n B:ℕ)(x:Fin n→ℂ)(s:State)(hp:s.pc=0)(hs:WordBound B s)(code:10≤B):
 ∃u,BoundedExecution program n x B s 10 u∧u.pc=9∧Installed s u∧Frame s u:=by
 have h:=nine program 0 n B x s ops_code hp hs (by omega)
 have halt:BoundedExecution program n x B (applyBlock ops s) 1 (applyBlock ops s):=
  .halt h.1.final_bound (by simp [UniformMachine.step,h.2.1,halt_at])
 refine ⟨applyBlock ops s,?_,by simpa using h.2.1,h.2.2.1,h.2.2.2⟩
 simpa only [show 9+1=10 by rfl] using h.1.executes halt
end ExactFourierCircuits.UniformAxisCacheCallerInstaller
