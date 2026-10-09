import UniformDirectLeafCacheReader
import UniformGlobalMatchingPoolPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafFactorTail
open UniformMachine UniformTensorMonomialMachine UniformGlobalMatchingScaleMachine
noncomputable section

/-- Enter the actual existing factor-writer at29 after physically computing
its coefficient addresses. The unused rank-spectrum decoder is not executed. -/
theorem execution (mu : ℂ) (a b pool r D d e n B : ℕ) (x : Fin n→ℂ) (s : State)
 (args:UniformZeroFreePairShearMachine.Args 0 0 a b s)
 (source:UniformZeroFreePairShearMachine.Sources mu a b s)
 (constants:UniformHadamardPairMachine.Constants s)
 (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (hD:s.natReg 2140=D) (hi:s.natReg 2141=0)
 (hd:s.natHeap D=some d) (he:s.natHeap (D+1)=some e)
 (rowBound:D+1≤B) (dst:d<r) (src:e<r) (distinct:d≠e)
 (poolBound:pool+9*r≤B) (code:120≤B)
 (ones:UniformGlobalScalePoolMachine.Prefix pool (9*r) s)
 (pc:s.pc=29) (wb:WordBound B s) : ∃u,
 BoundedExecution rowProgram n x B s 91 u ∧u.pc=119 ∧
 FullFactorTable pool r d e mu u ∧u.natHeap=s.natHeap ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q)→u.scalarHeap q=s.scalarHeap q) ∧
 (∀q,PairOutside pool r d e q→u.scalarHeap q=s.scalarHeap q) := by
 obtain ⟨v,run,last,ready,heap,nh,outs,roots⟩:=prepared_tail mu a b pool r D 0 d e n B x s
  args source constants hp hr hD hi (by simpa using hd) (by simpa using he)
  (by omega) (by omega) (by omega) pc wb code
 have inactive:InactiveReady pool r d e v:=by
  intro lane side _ha
  have range:=UniformGlobalMatchingPoolPreparation.address_bound pool r d e dst src lane side
  have addressEq:address pool r d e lane side=pool+(address pool r d e lane side-pool):=by omega
  rw [heap,addressEq]
  exact ones _ (by omega)
 have safe:=stores_safe pool r d e B mu v ready dst src poolBound code
 let u:=applyBlock stores v
 have writes:=block_runs stores rowProgram 64 n B x v stores_code last run.final_bound
  (by change 64+55≤B;omega) safe.1 safe.2
 have up:u.pc=119:=by rw [applyBlock_pc,last];rfl
 have halt:BoundedExecution rowProgram n x B u 1 u:=.halt writes.final_bound
  (by simp only [step,up,row_halt])
 have frames:=stores_frames v
 refine ⟨u,?_,up,stores_complete pool r d e mu v ready dst src distinct inactive,
  frames.1.trans nh,frames.2.2.1.trans outs,frames.2.2.2.1.trans roots,?_,?_⟩
 · convert (run.trans writes).executes halt using 1
   simp only [stores_length]
 · intro q hq
   exact (stores_other pool r d e mu v ready dst src q hq).trans (congrFun heap q)
 · intro q hq
   exact (stores_other_pair pool r d e mu v ready q hq).trans (congrFun heap q)
end
end ExactFourierCircuits.UniformDirectLeafFactorTail
