import UniformInitialPreparation
import UniformPermutationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformInputPermutationPreparation
open UniformMachine UniformAssembly UniformPairMachine
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
open UniformInitialPreparation (Ready Operands ell len copyBase alphaBase)
noncomputable section

def destination (n : ℕ) : ℕ := UniformNormalizationPreparation.normBase n+1
def setup : List Op := [.literal 85 0,.literal 86 1,.add 70 103 85,
  .literal 87 7,.add 71 102 87,.literal 88 2,.mul 87 101 88,.add 71 71 87,
  .add 72 27 86,.literal 88 6,.mul 73 102 88,.literal 87 5,.add 73 73 87,.add 73 105 73]
theorem setup_length : setup.length=14 := rfl
def program : Program := embed
  (UniformInitialPreparation.program.map (relocate 0 418)++setup.map Op.code)
  UniformPermutationMachine.program [.halt] 444
theorem program_length : program.length=445 := by
  rw [program,embed_length,List.length_append,List.length_map,List.length_map,
    UniformInitialPreparation.program_length,setup_length,UniformPermutationMachine.program_length];rfl

theorem initial_code : CodeAt UniformInitialPreparation.program program 0 418 := by
  intro i hi
  have hi418:i<418:=by simpa only [UniformInitialPreparation.program_length] using hi
  simp only [program,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInitialPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInitialPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]
theorem setup_code : BlockAt setup program 418 := by
  intro i hi
  have hi14:i<14:=hi
  unfold program embed
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInitialPreparation.program_length,setup_length,UniformPermutationMachine.program_length];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformInitialPreparation.program_length,setup_length];omega)]
  rw [List.getElem?_append_right (by simp [UniformInitialPreparation.program_length])]
  simp only [List.length_map,UniformInitialPreparation.program_length,Nat.add_sub_cancel_left,
    List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
theorem gather_code : CodeAt UniformPermutationMachine.program program 432 444 := by
  simpa only [program,List.length_append,List.length_map,
    UniformInitialPreparation.program_length,setup_length] using
    embed_code (UniformInitialPreparation.program.map (relocate 0 418)++setup.map Op.code)
      UniformPermutationMachine.program [.halt] 444
theorem halt_at : program[444]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp [UniformInitialPreparation.program_length,
    setup_length,UniformPermutationMachine.program_length])]
  simp [UniformInitialPreparation.program_length,setup_length,UniformPermutationMachine.program_length]

theorem setup_registers {n : ℕ} {x : Fin n→ℂ} (s : State) (h:Ready n x s) :
    (applyBlock setup s).natReg 70=len n ∧
    (applyBlock setup s).natReg 71=UniformPaddedInputPreparation.dataBase n ∧
    (applyBlock setup s).natReg 72=destination n ∧
    (applyBlock setup s).natReg 73=copyBase n+alphaBase n := by
  simp [applyBlock,setup,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.inputLength,h.normalizationAddress,h.saved.copyAddress,destination,
    UniformPaddedInputPreparation.dataBase,alphaBase,UniformCRTTraversalMachine.alphaBase,
    UniformCRTTraversalMachine.digitBase,Nat.add_assoc]
  omega
theorem setup_nat (s : State) (r : ℕ) (hr:r<50 ∨ 100≤r) :
    (applyBlock setup s).natReg r=s.natReg r := by
  simp (disch:=omega) [applyBlock,setup,Op.apply,writeNat,next]
theorem setup_heap (s : State) : (applyBlock setup s).scalarHeap=s.scalarHeap := rfl
theorem setup_natHeap (s : State) : (applyBlock setup s).natHeap=s.natHeap := rfl
theorem setup_outputs (s : State) : (applyBlock setup s).outputs=s.outputs := rfl
theorem setup_roots (s : State) : (applyBlock setup s).rootOrders=s.rootOrders := rfl

theorem ready_transport_below {n : ℕ} {x : Fin n→ℂ} {s u : State} (h:Ready n x s)
    (hnat:u.natHeap=s.natHeap) (hr:∀r,r<50 ∨ 100≤r→u.natReg r=s.natReg r)
    (hh:∀a,a≤UniformNormalizationPreparation.normBase n→u.scalarHeap a=s.scalarHeap a)
    (hroot:u.rootOrders=s.rootOrders) (hout:u.outputs=s.outputs) : Ready n x u := by
  have reg (r : ℕ) (hl:r<50) : u.natReg r=s.natReg r:=hr r (Or.inl hl)
  have hheader:=h.header
  obtain ⟨h0,h10,h11,h16,h17,h18,hprime⟩:=hheader
  have huheader:UniformCRTHeaderMachine.Header n u:=
    ⟨(reg 0 (by decide)).trans h0,(reg 10 (by decide)).trans h10,(reg 11 (by decide)).trans h11,
      (reg 16 (by decide)).trans h16,(reg 17 (by decide)).trans h17,(reg 18 (by decide)).trans h18,
      by simpa only [UniformWorkingMachine.PrimeTable,hnat] using hprime⟩
  have hops:Operands n x u:=by
    constructor
    · intro j
      exact (hh _ (by have hj:=j.isLt;dsimp [UniformNormalizationPreparation.normBase,
        UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase];omega)).trans (h.operands.constants j)
    · intro j
      have hj:j.val<UniformWorkingLength.axisCount n+1:=j.isLt
      have ha:6+j.val≤UniformNormalizationPreparation.normBase n:=by
        dsimp [UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
          UniformPaddedInputPreparation.dataBase]
        omega
      exact (hh _ ha).trans (h.operands.roots j)
    · intro j hj
      refine ⟨?_,?_⟩
      · exact (hh _ (by dsimp [UniformNormalizationPreparation.normBase,
          UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase];simp only [ell] at *;omega)).trans (h.operands.chirps j hj).1
      · exact (hh _ (by dsimp [UniformNormalizationPreparation.normBase,
          UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase];simp only [ell] at *;omega)).trans (h.operands.chirps j hj).2
    · intro j hj
      exact (hh _ (by dsimp [UniformNormalizationPreparation.normBase,
        UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase];simp only [len] at *;omega)).trans (h.operands.input j hj)
    · intro j hj
      exact (hh _ (by unfold UniformNormalizationPreparation.normBase;simp only [len] at *;omega)).trans (h.operands.kernel j hj)
    · exact (hh _ le_rfl).trans h.operands.normalization
  have hsaved:=UniformGlobalNatPreparation.SavedHeaders.transport h.saved
    (fun r hr' => hr r (Or.inr hr'))
  refine ⟨huheader,?_,(reg 24 (by decide)).trans h.order,(reg 8 (by decide)).trans h.inputLength,
    (reg 27 (by decide)).trans h.normalizationAddress,hops,hsaved,?_,?_,?_,?_,?_,?_,?_,
    hroot.trans h.oneRoot,hout.trans h.outputs⟩
  · simpa only [UniformCRTHeaderMachine.CRTTable,hnat] using h.crt
  · simpa only [UniformGlobalNatPreparation.PermutationBank,hnat] using h.alpha
  · simpa only [UniformGlobalNatPreparation.PermutationBank,hnat] using h.beta
  · simpa only [UniformGlobalNatPreparation.PermutationBank,hnat] using h.protectedAlpha
  · simpa only [UniformGlobalNatPreparation.PermutationBank,hnat] using h.protectedBeta
  · simpa only [UniformWorkingMachine.PrimeTable,UniformInitialPreparation.protectedView,hnat] using h.protectedPrimes
  · simpa only [UniformCRTHeaderMachine.CRTTable,UniformInitialPreparation.protectedView,hnat] using h.protectedCRT
  · intro a ha
    obtain ⟨v,hv⟩:=h.protectedFilled a ha
    exact ⟨v,(congrFun hnat _).trans hv⟩

theorem setup_peak {n : ℕ} {x : Fin n→ℂ} (B : ℕ) (s : State) (h:Ready n x s)
    (hd:destination n≤B) (hb:copyBase n+alphaBase n≤B) (hB:88≤B) : peak setup s≤B := by
  simp [peak,setup,Op.peak,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.inputLength,h.normalizationAddress,h.saved.copyAddress]
  dsimp [destination,UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
    UniformPaddedInputPreparation.dataBase] at hd
  dsimp [copyBase,alphaBase,UniformGlobalNatPreparation.destination,UniformGlobalNatPreparation.amount,
    UniformCRTTraversalMachine.alphaBase,UniformCRTTraversalMachine.digitBase] at hb
  dsimp only [ell,len] at *
  dsimp only [UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
    UniformPaddedInputPreparation.dataBase,UniformGlobalNatPreparation.destination,
    UniformGlobalNatPreparation.amount] at *
  omega

theorem word_setup {n : ℕ} (hn:0<n) : 445≤(n+2)^19 ∧
    destination n+len n≤(n+2)^19 ∧ copyBase n+alphaBase n+len n≤(n+2)^19 := by
  obtain ⟨h418,_ht,hcopy⟩:=UniformInitialPreparation.word_setup hn
  have hnrm:=UniformNormalizationPreparation.word_setup hn
  have hb:=UniformGlobalNatPreparation.destination_fits (ell n) (len n)
  have he:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:300≤(n+2)^18:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 18
    norm_num at h;omega
  have hbig:300*(n+2)≤(n+2)^19:=by
    rw [pow_succ];exact Nat.mul_le_mul_right (n+2) hp
  dsimp [destination,UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
    UniformPaddedInputPreparation.dataBase,copyBase,alphaBase,UniformGlobalNatPreparation.destination,
    UniformGlobalNatPreparation.amount,UniformCRTTraversalMachine.alphaBase,
    UniformCRTTraversalMachine.digitBase]
  dsimp only [ell,len] at *
  omega

def preparationBudget (n : ℕ) : ℕ := UniformInitialPreparation.preparationBudget n+36*n+19

/-- The first transform's input coordinates are gathered through the actual
protected alpha table. Every source and prepared startup bank is retained. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution program n x ((n+2)^19) initial t u ∧ Ready n x u ∧
    (∀j:Fin (len n),u.scalarHeap (destination n+j.val)=some
      (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
        (UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    u.pc=444 ∧ t≤preparationBudget n := by
  obtain ⟨t,v,hv,hr,hpc,hcost⟩:=UniformInitialPreparation.preparation_execution hn x
  obtain ⟨h445,hd,hb⟩:=word_setup hn
  have hfirst:=UniformBoundedAssembly.boundedExecution_placed initial_code
    (by rw [UniformInitialPreparation.program_length];omega : 0+UniformInitialPreparation.program.length≤(n+2)^19)
    (by omega : 418≤(n+2)^19) hv
  change BoundedRuns program n x ((n+2)^19) initial t {v with pc:=418} at hfirst
  let s:State:={v with pc:=418}
  have hrs:Ready n x s:=ready_transport_below hr rfl (fun _ _=>rfl) (fun _ _=>rfl) rfl rfl
  have hz:=block_runs setup program 418 n ((n+2)^19) x s setup_code rfl hfirst.final_bound
    (by rw [setup_length];omega) (by simp [readable,setup,Op.readable])
    (setup_peak ((n+2)^19) s hrs (by omega) (by omega) (by omega))
  let z:=applyBlock setup s
  let e:State:={z with pc:=0}
  have hre:Ready n x e:=ready_transport_below hrs (setup_natHeap s) (setup_nat s)
    (fun a _=>congrFun (setup_heap s) a) (setup_roots s) (setup_outputs s)
  obtain ⟨h70,h71,h72,h73⟩:=setup_registers s hrs
  have hsrc:UniformPermutationMachine.Source (len n) (UniformPaddedInputPreparation.dataBase n) e.scalarHeap:=by
    intro j
    exact ⟨_,hre.operands.input j.val j.isLt⟩
  have hsourceBound:UniformPaddedInputPreparation.dataBase n+len n≤destination n:=by
    dsimp only [len]
    unfold destination UniformNormalizationPreparation.normBase UniformChirpKernelPreparation.kernelBase
    omega
  have hdis:UniformPermutationMachine.Disjoint (UniformPaddedInputPreparation.dataBase n) (destination n) (len n):=by
    exact Or.inl hsourceBound
  obtain ⟨u,hu,hgather,_hsource,houtside,hframe,_hup,_h74⟩:=UniformPermutationMachine.execution n x
    (len n) (UniformPaddedInputPreparation.dataBase n) (destination n) (copyBase n+alphaBase n)
    ((n+2)^19) (UniformCRTTraversalCycle.alphaPermutation n) e hre.protectedAlpha hsrc hdis
    (by omega) hd hb (by omega) rfl h70 h71 h72 h73
    (changePC_bound _ z 0 hz.final_bound (by omega))
  have htail:=UniformBoundedAssembly.boundedExecution_placed gather_code
    (by rw [UniformPermutationMachine.program_length];omega : 432+UniformPermutationMachine.program.length≤(n+2)^19)
    (by omega : 444≤(n+2)^19) hu
  have hpz:z.pc=432:=by rw [UniformReciprocalMachine.applyBlock_pc,setup_length]
  have heq:placed 432 e=z:=by change {z with pc:=432}=z;rw [←hpz]
  rw [heq] at htail
  let final:State:={u with pc:=444}
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=
    .halt htail.final_bound (by simp [step,final,halt_at])
  have hur:Ready n x u:=ready_transport_below hre hframe.1
    (fun r hr' => hframe.2.2.2.2 r (by rcases hr' with hr'|hr' <;> omega))
    (fun a ha => houtside a (Or.inl (by unfold destination;omega))) hframe.2.2.1 hframe.2.1
  refine ⟨t+14+(9*len n+4)+1,final,(hfirst.trans hz).executes (htail.executes hhalt),
    ready_transport_below hur rfl (fun _ _=>rfl) (fun _ _=>rfl) rfl rfl,?_,rfl,?_⟩
  · intro j
    exact (hgather j).trans (hre.operands.input _ (UniformCRTTraversalCycle.alphaPermutation n j).isLt)
  · unfold preparationBudget
    have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
    omega

theorem preparationBudget_isBigO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hl:(fun n : ℕ => (36*n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n:ℝ)) Filter.atTop).const_mul_left 36
  have hc:(fun _n : ℕ => (19:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (19:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [preparationBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    (UniformInitialPreparation.preparationBudget_isBigO_input.add hl).add hc

end
end ExactFourierCircuits.UniformInputPermutationPreparation
