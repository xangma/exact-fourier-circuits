import UniformFourierAxisPrepareMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareEpoch
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
noncomputable section
/-- The actual41 helper is executed at97, including its charged return to138. -/
theorem execution {n B d g:ℕ}(x:Fin n→ℂ)(s:State)(pc:s.pc=97)
 (epoch:s.natReg 5920=g)(source:s.natHeap (s.natReg 6816)=some d)
 (bound:WordBound B s)(code:389≤B)(fit:2*d+5≤B):
 ∃u t,BoundedRuns UniformFourierAxisPrepareMachine.program n x B s t u ∧t≤23∧u.pc=138∧
 UniformEpochSelectorMachine.Selected d g u∧UniformEpochSelectorMachine.Frame s u:=by
 let s0:=setPC s 0
 have sw:WordBound B s0:=⟨by change 0≤B;omega,bound.2⟩
 obtain ⟨z,t,run,time,selected,frame⟩:=UniformEpochSelectorMachine.execution n B d g x s0 rfl
  epoch source sw (by omega) fit
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed UniformFourierAxisPrepareMachine.epoch_code
  (by rw[UniformEpochSelectorMachine.program_length];omega) (by omega) run
 have start:placed 97 s0=s:=by
  simp only[s0,placed,setPC,Nat.add_zero]
  rw[←pc]
 rw[start] at placedRun
 refine ⟨setPC z 138,t,placedRun,time,rfl,selected,?_⟩
 exact ⟨frame.natHeap,frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots,frame.natReg⟩
end
end ExactFourierCircuits.UniformFourierAxisPrepareEpoch
