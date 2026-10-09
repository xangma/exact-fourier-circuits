import UniformTensorMonomialMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTimingInstaller
open UniformMachine UniformTensorMonomialMachine

/-- Four charged instructions read the real axis allocator output words.
No destination pointer is supplied as an input premise. -/
def ops:List Op:=[.literal 6830 0,.add 6175 6816 6830,.add 6176 6817 6830,.add 6177 6818 6830]
lemma ops_length:ops.length=4:=rfl
def program:Program:=ops.map Op.code++[.halt]
lemma program_length:program.length=5:=rfl
lemma ops_code:BlockAt ops program 0:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma halt_at:program[4]?=some .halt:=rfl

structure Installed(s u:State):Prop where
 durations:u.natReg 6175=s.natReg 6816
 starts:u.natReg 6176=s.natReg 6817
 requests:u.natReg 6177=s.natReg 6818
 zero:u.natReg 6830=0
structure Frame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 rootOrders:u.rootOrders=s.rootOrders
 registers:∀q,q≠6175→q≠6176→q≠6177→q≠6830→u.natReg q=s.natReg q

lemma installed(s:State):Installed s (applyBlock ops s):=by
 constructor <;>simp [ops,applyBlock,Op.apply,writeNat,next]
lemma frame(s:State):Frame s (applyBlock ops s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q h5 h6 h7 hz
 simp [ops,applyBlock,Op.apply,writeNat,next,h5,h6,h7,hz]
lemma safe(B:ℕ)(s:State)(hs:WordBound B s):readable ops s∧peak ops s≤B:=by
 constructor
 · simp [ops,readable,Op.readable]
 · have a:=hs.2.1 6816
   have b:=hs.2.1 6817
   have c:=hs.2.1 6818
   simp [ops,peak,Op.peak,Op.apply,writeNat,next]
   all_goals omega

/-- Embedding API for exactly four charged installation instructions. -/
theorem four(main:Program)(start n B:ℕ)(x:Fin n→ℂ)(s:State)
 (code:BlockAt ops main start)(hp:s.pc=start)(hs:WordBound B s)(extent:start+4≤B):
 BoundedRuns main n x B s 4 (applyBlock ops s)∧
 (applyBlock ops s).pc=start+4∧Installed s (applyBlock ops s)∧Frame s (applyBlock ops s):=by
 have bounds:=safe B s hs
 refine ⟨?_,?_,installed s,frame s⟩
 · simpa only [ops_length] using block_runs ops main start n B x s code hp hs
    (by simpa only [ops_length] using extent) bounds.1 bounds.2
 · rw [applyBlock_pc,hp,ops_length]

/-- Standalone finite diagnostic includes one additional charged halt. -/
theorem execution(n B:ℕ)(x:Fin n→ℂ)(s:State)(hp:s.pc=0)(hs:WordBound B s)(code:5≤B):
 ∃u,BoundedExecution program n x B s 5 u∧u.pc=4∧Installed s u∧Frame s u:=by
 have h:=four program 0 n B x s ops_code hp hs (by omega)
 have halt:BoundedExecution program n x B (applyBlock ops s) 1 (applyBlock ops s):=
  .halt h.1.final_bound (by simp [UniformMachine.step,h.2.1,halt_at])
 refine ⟨applyBlock ops s,?_,by simpa using h.2.1,h.2.2.1,h.2.2.2⟩
 simpa only [show 4+1=5 by rfl] using h.1.executes halt
end ExactFourierCircuits.UniformAxisCacheTimingInstaller
