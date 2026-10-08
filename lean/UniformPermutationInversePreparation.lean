import UniformInputPermutationPreparation
import UniformPermutationInverseMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPermutationInversePreparation
open UniformMachine UniformAssembly
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
open UniformInitialPreparation (ell len copyBase alphaBase betaBase protectedView)
noncomputable section

def inverseBase (n : ℕ) : ℕ := copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)
def setup : List Op := [.literal 89 0,.add 81 103 89,.literal 90 6,.mul 82 102 90,
  .literal 90 5,.add 82 82 90,.add 82 82 103,.add 82 105 82,.add 83 105 106]
theorem setup_length : setup.length=9 := rfl
def program : Program := embed
  (UniformInputPermutationPreparation.program.map (relocate 0 445)++setup.map Op.code)
  UniformPermutationInverseMachine.program [.halt] 464
theorem program_length : program.length=465 := by
  rw [program,embed_length,List.length_append,List.length_map,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length,
    UniformPermutationInverseMachine.program_length];rfl
theorem input_code : CodeAt UniformInputPermutationPreparation.program program 0 445 := by
  intro i hi
  have hi445:i<445:=by simpa only [UniformInputPermutationPreparation.program_length] using hi
  simp only [program,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]
theorem setup_code : BlockAt setup program 445 := by
  intro i hi
  have hi9:i<9:=hi
  unfold program embed
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length,
    UniformPermutationInverseMachine.program_length];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_right (by simp [UniformInputPermutationPreparation.program_length])]
  simp only [List.length_map,UniformInputPermutationPreparation.program_length,Nat.add_sub_cancel_left,
    List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
theorem inverse_code : CodeAt UniformPermutationInverseMachine.program program 454 464 := by
  simpa only [program,List.length_append,List.length_map,
    UniformInputPermutationPreparation.program_length,setup_length] using
    embed_code (UniformInputPermutationPreparation.program.map (relocate 0 445)++setup.map Op.code)
      UniformPermutationInverseMachine.program [.halt] 464
theorem halt_at : program[464]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp [UniformInputPermutationPreparation.program_length,
    setup_length,UniformPermutationInverseMachine.program_length])]
  simp [UniformInputPermutationPreparation.program_length,setup_length,
    UniformPermutationInverseMachine.program_length]

/-- Persistent metadata uses only the saved registers and relocated heap.
Local producers are free to reuse the original low register/heap workspace. -/
structure Metadata (n : ℕ) (s : State) : Prop where
  saved : UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n)
    n (ell n) (len n) (UniformMasterRootMachine.order n) s
  primes : UniformWorkingMachine.PrimeTable (ell n) (protectedView n s)
  crt : UniformCRTHeaderMachine.CRTTable n (protectedView n s)
  alpha : UniformGlobalNatPreparation.PermutationBank (len n) (copyBase n+alphaBase n)
    s.natHeap (UniformCRTTraversalCycle.alphaPermutation n)
  beta : UniformGlobalNatPreparation.PermutationBank (len n) (copyBase n+betaBase n)
    s.natHeap (UniformCRTTraversalCycle.betaPermutation n)
  filled : ∀a,a<UniformGlobalNatPreparation.amount (ell n) (len n)→
    ∃v,s.natHeap (copyBase n+a)=some v

theorem Metadata.fromReady {n : ℕ} {x : Fin n→ℂ} {s : State}
    (h:UniformInitialPreparation.Ready n x s) : Metadata n s :=
  ⟨h.saved,h.protectedPrimes,h.protectedCRT,h.protectedAlpha,h.protectedBeta,h.protectedFilled⟩

theorem Metadata.transport_saved {n : ℕ} {s u : State} (h:Metadata n s)
    (hsaved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n)
      n (ell n) (len n) (UniformMasterRootMachine.order n) u)
    (hh:∀a,a<UniformGlobalNatPreparation.amount (ell n) (len n)→
      u.natHeap (copyBase n+a)=s.natHeap (copyBase n+a)) : Metadata n u := by
  refine ⟨hsaved,?_,?_,?_,?_,?_⟩
  · intro i hi
    exact (hh i (by unfold UniformGlobalNatPreparation.amount;omega)).trans (h.primes i hi)
  · intro i
    have hrow (f : ℕ) (hf:f≤3):(protectedView n u).natHeap
        (UniformCRTHeaderMachine.tableAddress (ell n) i.val f)=
        (protectedView n s).natHeap (UniformCRTHeaderMachine.tableAddress (ell n) i.val f):=by
      apply hh
      have hi:i.val<ell n+1:=i.isLt
      unfold UniformCRTHeaderMachine.tableAddress UniformGlobalNatPreparation.amount;omega
    exact ⟨(hrow 0 (by decide)).trans (h.crt i).1,(hrow 1 (by decide)).trans (h.crt i).2.1,
      (hrow 2 (by decide)).trans (h.crt i).2.2.1,(hrow 3 (by decide)).trans (h.crt i).2.2.2⟩
  · intro j
    have hj:=j.isLt
    have ha:alphaBase n+j.val<UniformGlobalNatPreparation.amount (ell n) (len n):=by
      unfold alphaBase UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase
        UniformGlobalNatPreparation.amount
      omega
    have he:=hh (alphaBase n+j.val) ha
    have he':u.natHeap (copyBase n+alphaBase n+j.val)=s.natHeap (copyBase n+alphaBase n+j.val):=by
      simpa only [Nat.add_assoc] using he
    exact he'.trans (h.alpha j)
  · intro j
    have hj:=j.isLt
    have hb:betaBase n+j.val<UniformGlobalNatPreparation.amount (ell n) (len n):=by
      unfold betaBase UniformCRTTraversalMachine.betaBase UniformCRTTraversalMachine.alphaBase
        UniformCRTTraversalMachine.digitBase UniformGlobalNatPreparation.amount
      omega
    have he:=hh (betaBase n+j.val) hb
    have he':u.natHeap (copyBase n+betaBase n+j.val)=s.natHeap (copyBase n+betaBase n+j.val):=by
      simpa only [Nat.add_assoc] using he
    exact he'.trans (h.beta j)
  · intro a ha
    obtain ⟨v,hv⟩:=h.filled a ha
    exact ⟨v,(hh a ha).trans hv⟩

theorem Metadata.transport {n : ℕ} {s u : State} (h:Metadata n s)
    (hr:∀r,100≤r→u.natReg r=s.natReg r)
    (hh:∀a,a<UniformGlobalNatPreparation.amount (ell n) (len n)→
      u.natHeap (copyBase n+a)=s.natHeap (copyBase n+a)) : Metadata n u :=
  h.transport_saved (UniformGlobalNatPreparation.SavedHeaders.transport h.saved hr) hh

theorem setup_nat (s : State) (r : ℕ) (hr:100≤r) : (applyBlock setup s).natReg r=s.natReg r := by
  simp (disch:=omega) [applyBlock,setup,Op.apply,writeNat,next]
theorem setup_heap (s : State) : (applyBlock setup s).scalarHeap=s.scalarHeap := rfl
theorem setup_natHeap (s : State) : (applyBlock setup s).natHeap=s.natHeap := rfl
theorem setup_outputs (s : State) : (applyBlock setup s).outputs=s.outputs := rfl
theorem setup_roots (s : State) : (applyBlock setup s).rootOrders=s.rootOrders := rfl
theorem setup_registers {n : ℕ} (s : State) (h:Metadata n s) :
    (applyBlock setup s).natReg 81=len n ∧
    (applyBlock setup s).natReg 82=copyBase n+betaBase n ∧
    (applyBlock setup s).natReg 83=inverseBase n := by
  simp [applyBlock,setup,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.copyAddress,h.saved.copyLength,inverseBase,betaBase,UniformCRTTraversalMachine.betaBase,
    UniformCRTTraversalMachine.alphaBase,UniformCRTTraversalMachine.digitBase,Nat.add_assoc]
  omega
theorem beta_fits (n : ℕ) : copyBase n+betaBase n+len n=inverseBase n := by
  unfold inverseBase betaBase UniformCRTTraversalMachine.betaBase UniformCRTTraversalMachine.alphaBase
    UniformCRTTraversalMachine.digitBase UniformGlobalNatPreparation.amount
  omega
theorem setup_peak {n : ℕ} (B : ℕ) (s : State) (h:Metadata n s)
    (hI:inverseBase n≤B) (hB:90≤B) : peak setup s≤B := by
  simp [peak,setup,Op.peak,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.copyAddress,h.saved.copyLength]
  dsimp only [inverseBase,copyBase,UniformGlobalNatPreparation.destination,
    UniformGlobalNatPreparation.amount,ell,len] at *
  omega

theorem word_setup {n : ℕ} (hn:0<n) : 465≤(n+2)^19 ∧ inverseBase n+len n≤(n+2)^19 := by
  have he:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:300≤(n+2)^18:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 18
    norm_num at h;omega
  have hb:300*(n+2)≤(n+2)^19:=by
    rw [pow_succ];exact Nat.mul_le_mul_right (n+2) hp
  dsimp only [inverseBase,copyBase,UniformGlobalNatPreparation.destination,
    UniformGlobalNatPreparation.amount,ell,len] at *
  omega
def preparationBudget (n : ℕ) : ℕ := UniformInputPermutationPreparation.preparationBudget n+28*n+14

/-- The beta inverse is produced from the actual protected beta table after
initial input preparation and alpha gather, with every setup instruction charged. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution program n x ((n+2)^19) initial t u ∧ Metadata n u ∧
    UniformInitialPreparation.Operands n x u ∧
    (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
      (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
        (UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    UniformGlobalNatPreparation.PermutationBank (len n) (inverseBase n) u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=464 ∧ t≤preparationBudget n := by
  obtain ⟨t,v,hv,hr,hinput,hpc,hcost⟩:=UniformInputPermutationPreparation.preparation_execution hn x
  have hm:Metadata n v:=Metadata.fromReady hr
  obtain ⟨h465,hI⟩:=word_setup hn
  have hfirst:=UniformBoundedAssembly.boundedExecution_placed input_code
    (by rw [UniformInputPermutationPreparation.program_length];omega :
      0+UniformInputPermutationPreparation.program.length≤(n+2)^19) (by omega : 445≤(n+2)^19) hv
  change BoundedRuns program n x ((n+2)^19) initial t {v with pc:=445} at hfirst
  let s:State:={v with pc:=445}
  have hms:Metadata n s:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hz:=block_runs setup program 445 n ((n+2)^19) x s setup_code rfl hfirst.final_bound
    (by rw [setup_length];omega) (by simp [readable,setup,Op.readable])
    (setup_peak ((n+2)^19) s hms (by omega) (by omega))
  let z:=applyBlock setup s
  let e:State:={z with pc:=0}
  have hme:Metadata n e:=hms.transport (setup_nat s) (fun a _=>congrFun (setup_natHeap s) _)
  obtain ⟨h81,h82,h83⟩:=setup_registers s hms
  obtain ⟨u,hu,hinverse,_hbeta,houtside,hframe,_hup,_h84⟩:=UniformPermutationInverseMachine.execution n x
    (len n) (copyBase n+betaBase n) (inverseBase n) ((n+2)^19)
    (UniformCRTTraversalCycle.betaPermutation n) e hme.beta (Or.inl (le_of_eq (beta_fits n)))
    (by rw [beta_fits];omega) hI (by omega) rfl h81 h82 h83
    (changePC_bound _ z 0 hz.final_bound (by omega))
  have htail:=UniformBoundedAssembly.boundedExecution_placed inverse_code
    (by rw [UniformPermutationInverseMachine.program_length];omega :
      454+UniformPermutationInverseMachine.program.length≤(n+2)^19) (by omega : 464≤(n+2)^19) hu
  have hpz:z.pc=454:=by rw [UniformReciprocalMachine.applyBlock_pc,setup_length]
  have heq:placed 454 e=z:=by change {z with pc:=454}=z;rw [←hpz]
  rw [heq] at htail
  let final:State:={u with pc:=464}
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=
    .halt htail.final_bound (by simp [step,final,halt_at])
  have hmu:Metadata n u:=hme.transport (hframe.saved_headers)
    (fun a ha=>houtside _ (Or.inl (by unfold inverseBase;omega)))
  have hscalar:u.scalarHeap=v.scalarHeap:=hframe.1
  refine ⟨t+9+(7*len n+4)+1,final,(hfirst.trans hz).executes (htail.executes hhalt),
    hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hr.operands.transport hscalar,?_,hinverse,
    hframe.2.2.2.1.trans hr.oneRoot,hframe.2.2.1.trans hr.outputs,rfl,?_⟩
  · intro j;exact (congrFun hscalar _).trans (hinput j)
  · unfold preparationBudget
    have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
    omega

theorem preparationBudget_isBigO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hl:(fun n : ℕ => (28*n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n:ℝ)) Filter.atTop).const_mul_left 28
  have hc:(fun _n : ℕ => (14:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (14:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [preparationBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    (UniformInputPermutationPreparation.preparationBudget_isBigO_input.add hl).add hc

end
end ExactFourierCircuits.UniformPermutationInversePreparation
