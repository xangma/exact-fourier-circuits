import UniformInitialCoreSeed
import UniformInitialCoreConjugateFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitialCoreRetention
open UniformMachine UniformAssembly
open UniformInitialPreparation (len)
open UniformAllAxisConjugatePreparation
open UniformPermutationInversePreparation (Metadata)
noncomputable section
attribute [local irreducible] UniformAllAxisSeedPreparation.fullProgram

/-- Same actual1460 empty-start program, retaining its physically produced
original Header, gathered alpha input and independent beta inverse. -/
theorem initial_execution_with_header {n:ℕ} (hn:0<n) (x:Fin n→ ℂ):∃t u,
 BoundedExecution fullProgram n x ((n+2)^19) initial
  (t+UniformAllAxisSeedPreparation.preparationRuntime n+1+preparationRuntime n+1) u∧
 t≤ UniformPermutationInversePreparation.preparationBudget n∧
 Retained n (UniformAllAxisSeedPreparation.axisCount n) u∧
 UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u∧
 Metadata n u∧UniformInitialPreparation.Operands n x u∧
 u.rootOrders=[UniformMasterRootMachine.order n]∧u.outputs=initial.outputs∧u.pc=1459∧
 t+UniformAllAxisSeedPreparation.preparationRuntime n+1+preparationRuntime n+1≤ fullBudget n∧
 UniformAllAxisSeedPreparation.Header n (UniformAllAxisSeedPreparation.axisCount n) u∧
 (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
  (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
   (UniformCRTTraversalCycle.alphaPermutation n j).val))∧
 UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
  u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm:=by
 obtain ⟨t,v,hv,hcost,hr,hm,ho,hinput,hbeta,hroots,hout,_,hbudget,header⟩:=
  UniformInitialCoreSeed.initial_execution_with_header hn x
 have hbig:=full_word_bound hn
 have start:=UniformBoundedAssembly.boundedExecution_placed original_code
  (by rw [UniformAllAxisSeedPreparation.fullProgram_length];omega :0+UniformAllAxisSeedPreparation.fullProgram.length≤ (n+2)^19)
  (by omega :935≤ (n+2)^19) hv
 change BoundedRuns fullProgram n x ((n+2)^19) initial
  (t+UniformAllAxisSeedPreparation.preparationRuntime n+1) {v with pc:=935} at start
 let e:State:={v with pc:=0}
 obtain ⟨u,hu,hnew,hru,hmu,hou,hf,_,_,hb⟩:=execution hn x e
  (hm.transport (fun _ _=>rfl) (fun _ _=>rfl)) (ho.transport rfl) hr.withPC rfl
  (changePC_bound _ v 0 hv.final_bound (by omega))
 have headerU:=UniformInitialCoreConjugateFrame.execution_header hu header.withPC
 have tail:=UniformBoundedAssembly.boundedExecution_placed driver_code
  (by rw [program_length];omega :935+program.length≤ (n+2)^19)
  (by omega :1459≤ (n+2)^19) hu
 have heq:placed 935 e={v with pc:=935}:=rfl
 rw [heq] at tail
 let final:State:={u with pc:=1459}
 have halt:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=.halt tail.final_bound
  (by simp [step,final,full_halt])
 have hbE:UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
  e.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm:=hbeta
 refine ⟨t,final,start.executes (tail.executes halt),hcost,hnew.withPC,hru.withPC,
  hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,
  hf.2.2.2.2.trans hroots,hf.2.2.2.1.trans hout,rfl,?_,headerU.withPC,?_,hf.protected.beta_inverse hbE⟩
 · unfold fullBudget
   omega
 · intro j
   exact (hf.protected.alpha_copied j).trans (hinput j)

end
end ExactFourierCircuits.UniformInitialCoreRetention
