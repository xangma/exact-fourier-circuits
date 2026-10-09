import UniformAllAxisConjugatePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitialCoreSeed
open UniformMachine UniformAssembly
open UniformInitialPreparation (len)
open UniformAllAxisSeedPreparation
open UniformPermutationInversePreparation (Metadata)
noncomputable section

/-- The original actual469 loop also returns its genuine completed Header. -/
theorem execution_with_header {n:ℕ} (hn:0<n) (x:Fin n→ ℂ) (s:State) (hm:Metadata n s)
 (ho:UniformInitialPreparation.Operands n x s) (hpc:s.pc=0) (hs:WordBound ((n+2)^19) s):
 ∃u,BoundedExecution UniformAllAxisSeedPreparation.program n x ((n+2)^19) s (preparationRuntime n) u∧
 Retained n (axisCount n) u∧Metadata n u∧UniformInitialPreparation.Operands n x u∧
 ProtectedFrame n s u∧u.pc=468∧preparationRuntime n≤ preparationBudget n∧Header n (axisCount n) u:=by
 obtain ⟨hc,_,hdir⟩:=word_setup hn
 have hboot:=UniformNewtonTableMachine.block_runs boot UniformAllAxisSeedPreparation.program 0 n ((n+2)^19) x s boot_code hpc hs
  (by change 7≤ (n+2)^19;omega) (by trivial) (boot_peak s hm hdir hc)
 let z:=UniformNewtonTableMachine.applyBlock boot s
 have h7:z.pc=7:=(UniformNewtonTableMachine.applyBlock_pc boot s).trans (by rw [hpc,boot_length])
 obtain ⟨v,hv,hiv,hfv,hpv⟩:=loop (k:=0) (f:=axisCount n) hn x z (boot_invariant s hm ho)
  (by omega) h7 hboot.final_bound
 let final:State:={v with pc:=468}
 have hfB:WordBound ((n+2)^19) final:=changePC_bound _ v 468 hv.final_bound (by omega)
 have hhalt:BoundedExecution UniformAllAxisSeedPreparation.program n x ((n+2)^19) final 1 final:=.halt hfB
  (by simp [step,final,halt_code])
 have hfinish:BoundedExecution UniformAllAxisSeedPreparation.program n x ((n+2)^19) v 2 final:=by
  refine .next hv.final_bound ?_ hhalt
  simp [step,hpv,branch_code,hiv.header.index,hiv.header.count,final]
 refine ⟨final,?_,hiv.retained.withPC,hiv.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),
  hiv.operands.transport rfl,(boot_frame n s).trans hfv,rfl,runtime_bound n,hiv.header.withPC⟩
 convert hboot.executes (hv.executes hfinish) using 1
 change preparationRuntime n=7+(loopCost n 0 (axisCount n)+2)
 unfold preparationRuntime
 omega

/-- Same actual935 startup; preserve its Header, alpha gather and beta inverse. -/
theorem initial_execution_with_header {n:ℕ} (hn:0<n) (x:Fin n→ ℂ):∃t u,
 BoundedExecution fullProgram n x ((n+2)^19) initial (t+preparationRuntime n+1) u∧
 t≤ UniformPermutationInversePreparation.preparationBudget n∧
 Retained n (axisCount n) u∧Metadata n u∧UniformInitialPreparation.Operands n x u∧
 (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
  (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
   (UniformCRTTraversalCycle.alphaPermutation n j).val))∧
 UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
  u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm∧
 u.rootOrders=[UniformMasterRootMachine.order n]∧u.outputs=initial.outputs∧
 u.pc=934∧t+preparationRuntime n+1≤ fullBudget n∧Header n (axisCount n) u:=by
 obtain ⟨t,v,hv,hm,ho,hinput,hbeta,hroots,houtputs,_,hcost⟩:=
  UniformPermutationInversePreparation.preparation_execution hn x
 have hbig:=full_word_bound hn
 have hstart:=UniformBoundedAssembly.boundedExecution_placed startup_code
  (by rw [UniformPermutationInversePreparation.program_length];omega :0+UniformPermutationInversePreparation.program.length≤ (n+2)^19)
  (by omega :465≤ (n+2)^19) hv
 change BoundedRuns fullProgram n x ((n+2)^19) initial t {v with pc:=465} at hstart
 let e:State:={v with pc:=0}
 obtain ⟨u,hu,hret,hmu,hou,hframe,_,_,header⟩:=execution_with_header hn x e
  (hm.transport (fun _ _=>rfl) (fun _ _=>rfl)) (ho.transport rfl) rfl
  (changePC_bound _ v 0 hv.final_bound (by omega))
 have htail:=UniformBoundedAssembly.boundedExecution_placed driver_code
  (by rw [UniformAllAxisSeedPreparation.program_length];omega :465+UniformAllAxisSeedPreparation.program.length≤ (n+2)^19) (by omega :934≤ (n+2)^19) hu
 have heq:placed 465 e={v with pc:=465}:=rfl
 rw [heq] at htail
 let final:State:={u with pc:=934}
 have hhalt:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=.halt htail.final_bound
  (by simp [step,final,full_halt])
 have hb:UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
  e.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm:=hbeta
 refine ⟨t,final,hstart.executes (htail.executes hhalt),hcost,hret.withPC,
  hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,?_,hframe.beta_inverse hb,
  hframe.2.2.2.2.trans hroots,hframe.2.2.2.1.trans houtputs,rfl,?_,header.withPC⟩
 · intro j
   exact (hframe.alpha_copied j).trans (hinput j)
 · unfold fullBudget
   omega

end
end ExactFourierCircuits.UniformInitialCoreSeed
