import UniformAllAxisSeedPreparation
import UniformSelectedDFSMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitialTraversalPreparation
open UniformMachine UniformAssembly
open UniformInitialPreparation (ell len copyBase)
noncomputable section

/-- Empty-state preparation and charged radix copying/traversal share one
literal program. No host dispatch or supplied radix/coefficient table occurs. -/
def head : Program := UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)
def program : Program := embed head UniformSelectedDFSMachine.program [.halt] 988
theorem head_length : head.length=935 := by
  simp only [head,List.length_map,UniformAllAxisSeedPreparation.fullProgram_length]
theorem program_length : program.length=989 := by
  rw [program,embed_length,head_length,UniformSelectedDFSMachine.program_length];rfl
theorem preparation_code : CodeAt UniformAllAxisSeedPreparation.fullProgram program 0 935 := by
  intro i hi
  have hi935:i<935:=by simpa only [UniformAllAxisSeedPreparation.fullProgram_length] using hi
  simp only [program,embed,head_length,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,head_length,List.length_map,
    UniformSelectedDFSMachine.program_length];omega)]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head,List.getElem?_map]
theorem traversal_code : CodeAt UniformSelectedDFSMachine.program program 935 988 := by
  simpa only [program,head_length] using embed_code head UniformSelectedDFSMachine.program [.halt] 988
theorem halt_at : program[988]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,head_length,List.length_map,
    UniformSelectedDFSMachine.program_length];omega)]
  simp [head_length,UniformSelectedDFSMachine.program_length]
def traversalRuntime (n : ℕ) : ℕ :=
  6*(ell n+1)+UniformDFSProgram.treeCost (UniformSelectedDFSMachine.selectedRadices n)+20
def preparationBudget (n : ℕ) : ℕ := UniformAllAxisSeedPreparation.fullBudget n+84*len n+7
theorem word_setup {n : ℕ} (hn:0<n) : 989≤(n+2)^19 := by
  have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
  norm_num at h;omega

/-- Every positive length starts with empty heaps and finishes with every
local seed, its directory, the actual ordered leaf addresses, both independent
CRT banks, all global operands and the sole original master-root request. -/
theorem initial_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution program n x ((n+2)^19) initial t u ∧
    UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
      (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
        (UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
      u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    (∀j,j<len n→u.natHeap (3*(ell n+1)+j)=some j) ∧
    u.natReg 8=len n ∧ u.rootOrders=[UniformMasterRootMachine.order n] ∧
    u.outputs=initial.outputs ∧ u.pc=988 ∧ t≤preparationBudget n := by
  obtain ⟨t,v,hv,hcost,hret,hm,ho,hinput,hbeta,hroots,houtputs,hpc,hbound⟩:=
    UniformAllAxisSeedPreparation.initial_execution hn x
  have hbig:=word_setup hn
  have first:=UniformBoundedAssembly.boundedExecution_placed preparation_code
    (by rw [UniformAllAxisSeedPreparation.fullProgram_length];omega :
      0+UniformAllAxisSeedPreparation.fullProgram.length≤(n+2)^19)
    (by omega :935≤(n+2)^19) hv
  change BoundedRuns program n x ((n+2)^19) initial
    (t+UniformAllAxisSeedPreparation.preparationRuntime n+1) {v with pc:=935} at first
  let e:State:={v with pc:=0}
  obtain ⟨u,hu,hpu,hcount,hleaves,hhigh,hmu,hou,hframe,hnat⟩:=
    UniformSelectedDFSMachine.selected_execution n hn x e rfl
      (hm.transport (fun _ _=>rfl) (fun _ _=>rfl)) (ho.transport rfl)
      (changePC_bound _ v 0 hv.final_bound (by omega))
  have second:=UniformBoundedAssembly.boundedExecution_placed traversal_code
    (by rw [UniformSelectedDFSMachine.program_length];omega :
      935+UniformSelectedDFSMachine.program.length≤(n+2)^19)
    (by omega :988≤(n+2)^19) hu
  have entry:placed 935 e={v with pc:=935}:=rfl
  rw [entry] at second
  let final:State:={u with pc:=988}
  have halt:BoundedExecution program n x ((n+2)^19) final 1 final:=
    .halt second.final_bound (by simp [step,final,halt_at])
  have retained:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) final := by
    constructor
    · intro j hj q l
      exact (congrFun hframe.1 _).trans (hret.coefficients j hj q l)
    · intro j hj
      exact (hhigh _ (by
        have hb:=UniformSelectedDFSMachine.workspace_before_protected n
        unfold UniformAllAxisSeedPreparation.directoryBase UniformPermutationInversePreparation.inverseBase;omega)).trans
        (hret.address j hj)
    · intro j hj
      exact (hhigh _ (by
        have hb:=UniformSelectedDFSMachine.workspace_before_protected n
        unfold UniformAllAxisSeedPreparation.directoryBase UniformPermutationInversePreparation.inverseBase;omega)).trans
        (hret.width j hj)
  refine ⟨t+UniformAllAxisSeedPreparation.preparationRuntime n+1+traversalRuntime n+1,
    final,?_,retained,hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,
    ?_,UniformSelectedDFSMachine.betaInverse_bank_retained hhigh hbeta,hleaves,hcount,
    hframe.2.2.2.trans hroots,hframe.2.2.1.trans houtputs,rfl,?_⟩
  · exact first.executes (second.executes halt)
  · intro j;exact (congrFun hframe.1 _).trans (hinput j)
  · have htr:=UniformSelectedDFSMachine.selected_runtime_linear n
    unfold preparationBudget traversalRuntime
    omega
end
end ExactFourierCircuits.UniformInitialTraversalPreparation
