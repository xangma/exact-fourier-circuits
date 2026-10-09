import UniformAxisCacheSelectedPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheLoopTail
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformAxisCacheStartupMachine
open UniformTensorMonomialMachine (setPC)

/-- Relative2 enters the following nine-cell advance; relative11 is the
terminal halt after it. The current axis index itself is not changed here. -/
def ops:List Op:=[.binary .add 6908 6906 6901]
def program:Program:=ops.map Op.code++[.branchLT 6908 6905 2 11]
lemma program_length:program.length=2:=rfl
lemma ops_code:BlockAt ops program 0:=by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma branch_at:program[1]?=some (.branchLT 6908 6905 2 11):=rfl

noncomputable section
theorem execution (n j B:ℕ)(x:Fin n→ℂ)(s:State)(control:Control n j s)
 (index:j<C.ell n)(code:11≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedRuns program n x B s 2 u∧
 u.pc=(if j+1<C.ell n then 2 else 11)∧u.natReg 6908=j+1∧
 Control n j u∧u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧
 u.scalarReg=s.scalarReg∧u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀q,q≠6908→u.natReg q=s.natReg q):=by
 have count:=wb.2.1 6905
 rw [control.count] at count
 have safe:readable ops s∧peak ops s≤B:=by
  constructor
  · simp [ops,readable,Op.readable,evalNat]
  · simp [ops,peak,Op.peak,evalNat,control.one,control.index]
    omega
 have first:=block_runs ops program 0 n B x s ops_code pc wb (by simp [ops];omega) safe.1 safe.2
 let a:=applyBlock ops s
 have ap:a.pc=1:=by simp [a,ops,applyBlock,Op.apply,next,writeNat,pc]
 have value:a.natReg 6908=j+1:=by simp [a,ops,applyBlock,Op.apply,evalNat,writeNat,next,control.index,control.one]
 have ac:a.natReg 6905=C.ell n:=by simp [a,ops,applyBlock,Op.apply,writeNat,next,control.count]
 let target:=if j+1<C.ell n then 2 else 11
 let u:=setPC a target
 have targetBound:target≤B:=by dsimp [target];split_ifs <;>omega
 have uw:WordBound B u:=⟨targetBound,first.final_bound.2⟩
 have branch:step program n x a=.running u:=by
  rw [step,ap,branch_at]
  simp only [value,ac]
  rfl
 have last:BoundedRuns program n x B a 1 u:=.next first.final_bound branch (.refl uw)
 refine ⟨u,?_,rfl,value,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
 · simpa only [ops,List.length_cons,List.length_nil,Nat.add_zero] using first.trans last
 · constructor
   all_goals simp [u,setPC,a,ops,applyBlock,Op.apply,writeNat,next,control.zero,control.one,
    control.two,control.nine,control.source,control.count,control.index]
 · intro q hq
   simp [u,setPC,a,ops,applyBlock,Op.apply,writeNat,next,hq]

end
end ExactFourierCircuits.UniformAxisCacheLoopTail
