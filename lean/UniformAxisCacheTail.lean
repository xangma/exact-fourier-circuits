import UniformAxisCacheLoopTail
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTail
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformTensorMonomialMachine (setPC)
open UniformAxisCacheLoopTail (ops program)

/-- The two actual tail instructions execute at the final caller offset;
the next-axis branch enters advance9 and the last-axis branch skips it. -/
theorem execution (n j B base:ℕ)(p:Program)(code:CodeAt UniformAxisCacheLoopTail.program p base 0)
 (x:Fin n→ℂ)(s:State)(control:Control n j s)(index:j<C.ell n)
 (room:base+11≤B)(pc:s.pc=base)(wb:WordBound B s):
 ∃u,BoundedRuns p n x B s 2 u∧
 u.pc=(if j+1<C.ell n then base+2 else base+11)∧u.natReg 6908=j+1∧
 Control n j u∧u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧
 u.scalarReg=s.scalarReg∧u.outputs=s.outputs∧u.rootOrders=s.rootOrders∧
 (∀q,q≠6908→u.natReg q=s.natReg q):=by
 have opsCode:BlockAt ops p base:=by
  intro i hi
  change i<1 at hi
  have zero:i=0:=by omega
  subst i
  have h:=code 0 (by rw [UniformAxisCacheLoopTail.program_length];omega)
  simpa [UniformAxisCacheLoopTail.program,ops,Op.code,relocate] using h
 have branchCode:p[base+1]?=some (.branchLT 6908 6905 (base+2) (base+11)):=by
  have h:=code 1 (by rw [UniformAxisCacheLoopTail.program_length];omega)
  simpa only [UniformAxisCacheLoopTail.branch_at,Option.map_some,relocate] using h
 have count:=wb.2.1 6905
 rw [control.count] at count
 have safe:readable ops s∧peak ops s≤B:=by
  constructor
  · simp [ops,readable,Op.readable,evalNat]
  · simp [ops,peak,Op.peak,evalNat,control.one,control.index]
    omega
 have first:=block_runs ops p base n B x s opsCode pc wb (by simp [ops];omega) safe.1 safe.2
 let a:=applyBlock ops s
 have ap:a.pc=base+1:=by simp [a,ops,applyBlock,Op.apply,next,writeNat,pc]
 have value:a.natReg 6908=j+1:=by simp [a,ops,applyBlock,Op.apply,evalNat,writeNat,next,control.index,control.one]
 have ac:a.natReg 6905=C.ell n:=by simp [a,ops,applyBlock,Op.apply,writeNat,next,control.count]
 let target:=if j+1<C.ell n then base+2 else base+11
 let u:=setPC a target
 have targetBound:target≤B:=by dsimp [target];split_ifs <;>omega
 have uw:WordBound B u:=⟨targetBound,first.final_bound.2⟩
 have branch:step p n x a=.running u:=by
  rw [step,ap,branchCode]
  simp only [value,ac]
  rfl
 have last:BoundedRuns p n x B a 1 u:=.next first.final_bound branch (.refl uw)
 refine ⟨u,?_,rfl,value,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
 · simpa only [ops,List.length_cons,List.length_nil,Nat.add_zero] using first.trans last
 · constructor
   all_goals simp [u,setPC,a,ops,applyBlock,Op.apply,writeNat,next,control.zero,control.one,
    control.two,control.nine,control.source,control.count,control.index]
 · intro q hq
   simp [u,setPC,a,ops,applyBlock,Op.apply,writeNat,next,hq]

end ExactFourierCircuits.UniformAxisCacheTail
