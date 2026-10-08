import UniformGlobalLocalPreparation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ExactFourierCircuits.UniformInitialLocalPreparation
open UniformMachine UniformAssembly UniformPairMachine
open UniformInitialPreparation (ell len)
open UniformPermutationInversePreparation (Metadata inverseBase)
open UniformGlobalLocalPreparation (resultBase rootSource)
noncomputable section

def axis (n : ℕ) : Fin (ell n+1) := ⟨0,by omega⟩
abbrev radix (n : ℕ) := UniformGlobalLocalPreparation.radix n (axis n)
abbrev localTime (n : ℕ) := UniformReciprocalMachine.completeRuntime (radix n)+30

def head : Program := UniformPermutationInversePreparation.program.map (relocate 0 465)++[.natLiteral 110 0]
def program : Program := embed head UniformGlobalLocalPreparation.program [.halt] 765

theorem head_length : head.length=466 := by
  simp only [head,List.length_append,List.length_map,UniformPermutationInversePreparation.program_length];rfl

theorem program_length : program.length=766 := by
  rw [program,embed_length,head_length,UniformGlobalLocalPreparation.program_length];rfl

theorem startup_code : CodeAt UniformPermutationInversePreparation.program program 0 465 := by
  intro i hi
  have hi465:i<465:=by simpa only [UniformPermutationInversePreparation.program_length] using hi
  simp only [program,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    head_length,UniformGlobalLocalPreparation.program_length];omega)]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem argument_at : program[465]?=some (.natLiteral 110 0) := by
  simp only [program,embed]
  rw [List.getElem?_append_left (by simp [head_length,UniformGlobalLocalPreparation.program_length])]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head]
  rw [List.getElem?_append_right (by simp [UniformPermutationInversePreparation.program_length])]
  simp [UniformPermutationInversePreparation.program_length]

theorem local_code : CodeAt UniformGlobalLocalPreparation.program program 466 765 := by
  simpa only [program,head_length] using embed_code head UniformGlobalLocalPreparation.program [.halt] 765

theorem halt_at : program[765]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp [head_length,UniformGlobalLocalPreparation.program_length])]
  simp [head_length,UniformGlobalLocalPreparation.program_length]

def setAxis (s : State) : State := writeNat s 110 0

theorem setAxis_saved {n : ℕ} {s : State} (hm:Metadata n s) :
    UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n (ell n) (len n)
      (UniformMasterRootMachine.order n) (setAxis s) := by
  constructor
  · simpa [setAxis,writeNat,next] using hm.saved.nextPrime
  · simpa [setAxis,writeNat,next] using hm.saved.inputLength
  · simpa [setAxis,writeNat,next] using hm.saved.count
  · simpa [setAxis,writeNat,next] using hm.saved.workingLength
  · simpa [setAxis,writeNat,next] using hm.saved.masterRoot
  · simpa [setAxis,writeNat,next] using hm.saved.copyAddress
  · simpa [setAxis,writeNat,next] using hm.saved.copyLength

theorem setAxis_metadata {n : ℕ} {s : State} (hm:Metadata n s) : Metadata n (setAxis s) :=
  hm.transport_saved (setAxis_saved hm) (fun _ _=>rfl)

theorem word_setup {n : ℕ} (hn:0<n) : 766≤(n+2)^19 := by
  have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
  norm_num at h
  omega

def preparationBudget (n : ℕ) : ℕ :=
  UniformPermutationInversePreparation.preparationBudget n+494*(radix n)^2+2

/-- One fixed program starts from the actual empty machine, prepares all global
banks and independent CRT permutations, charges the axis-zero argument, and
produces that selected axis's Newton and reciprocal seed banks. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution program n x ((n+2)^19) initial (t+localTime n+2) u ∧
    t≤UniformPermutationInversePreparation.preparationBudget n ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
      (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
        (UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    UniformGlobalNatPreparation.PermutationBank (len n) (inverseBase n) u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    UniformNewtonTableMachine.PreparedOutputs (radix n) (OAI.ExactFourier.zeta (radix n))
      (resultBase n (radix n)) u ∧
    UniformReciprocalMachine.GPrefix (radix n) (rootSource n (radix n)+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n))) u ∧
    u.scalarHeap (rootSource n (radix n))=some (prepared (OAI.ExactFourier.zeta (radix n))) ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=765 ∧ t+localTime n+2≤preparationBudget n := by
  obtain ⟨t,v,hv,hm,ho,hinput,hbeta,hroots,houtputs,_hpc,hcost⟩:=
    UniformPermutationInversePreparation.preparation_execution hn x
  have hbig:=word_setup hn
  have hfirst:=UniformBoundedAssembly.boundedExecution_placed startup_code
    (by rw [UniformPermutationInversePreparation.program_length];omega :
      0+UniformPermutationInversePreparation.program.length≤(n+2)^19) (by omega :465≤(n+2)^19) hv
  change BoundedRuns program n x ((n+2)^19) initial t {v with pc:=465} at hfirst
  let s:State:={v with pc:=465}
  have hms:Metadata n s:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
  let z:=setAxis s
  have hz:WordBound ((n+2)^19) z:=writeNat_bound _ s 110 0 hfirst.final_bound (by change 466≤_;omega) (by omega)
  have harg:BoundedRuns program n x ((n+2)^19) s 1 z:=
    .next hfirst.final_bound (by simp [step,s,z,setAxis,argument_at]) (.refl hz)
  let e:State:={z with pc:=0}
  have hme:Metadata n e:=(setAxis_metadata hms).transport (fun _ _=>rfl) (fun _ _=>rfl)
  have heHeap:e.scalarHeap=v.scalarHeap:=rfl
  have hoe:UniformInitialPreparation.Operands n x e:=ho.transport heHeap
  obtain ⟨u,hu,hmu,hou,hprepared,hg,haxis,hframe,_hup⟩:=
    UniformGlobalLocalPreparation.preparation_execution_budget hn x (axis n) e hme hoe rfl
      (by simp [e,z,setAxis,writeNat,next,axis])
      (changePC_bound _ z 0 hz (by omega))
  have htail:=UniformBoundedAssembly.boundedExecution_placed local_code
    (by rw [UniformGlobalLocalPreparation.program_length];omega :
      466+UniformGlobalLocalPreparation.program.length≤(n+2)^19) (by omega :765≤(n+2)^19) hu
  have heq:placed 466 e=z:=by simp [placed,e,z,setAxis,s,writeNat,next]
  rw [heq] at htail
  let final:State:={u with pc:=765}
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=
    .halt htail.final_bound (by simp [step,final,halt_at])
  have hbetae:UniformGlobalNatPreparation.PermutationBank (len n) (inverseBase n) e.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm:=hbeta
  have hbetau:=hframe.beta_inverse hbetae
  refine ⟨t,final,?_,hcost,hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,
    ?_,hbetau,hprepared,hg,haxis,hframe.2.2.2.2.trans hroots,hframe.2.2.2.1.trans houtputs,rfl,?_⟩
  · convert (hfirst.trans harg).executes (htail.executes hhalt) using 1
    dsimp only [localTime,radix]
    omega
  · intro j
    exact (hframe.1 _ (by unfold UniformGlobalLocalPreparation.globalEnd;have hj:=j.isLt;omega)).trans (hinput j)
  · have hlocal:=UniformGlobalLocalPreparation.runtime_quadratic n (axis n)
    dsimp only [preparationBudget,localTime,radix]
    omega

/-- The startup term is O(n); the additional proved local term is at most
494 times the selected radix squared plus two charged composition instructions. -/
theorem startupBudget_isBigO_input :
    (fun n : ℕ => (UniformPermutationInversePreparation.preparationBudget n:ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
  UniformPermutationInversePreparation.preparationBudget_isBigO_input

end
end ExactFourierCircuits.UniformInitialLocalPreparation
