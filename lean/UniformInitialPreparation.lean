import UniformNormalizationPreparation
import UniformCRTTraversalCycle
import UniformGlobalNatPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitialPreparation
open UniformMachine UniformAssembly UniformPairMachine
noncomputable section

def head : Program :=
  UniformNormalizationPreparation.fullProgram.map (relocate 0 337) ++
  UniformCRTTraversalMachine.program.map (relocate 337 385)
def program : Program := embed head UniformGlobalNatPreparation.program [.halt] 417

theorem head_length : head.length=385 := by
  simp only [head,List.length_append,List.length_map,
    UniformNormalizationPreparation.fullProgram_length,UniformCRTTraversalMachine.program_length]
theorem program_length : program.length=418 := by
  rw [program,embed_length,head_length,UniformGlobalNatPreparation.program_length];rfl
theorem normalization_code : CodeAt UniformNormalizationPreparation.fullProgram program 0 337 := by
  intro i hi
  have hi337:i<337:=by simpa only [UniformNormalizationPreparation.fullProgram_length] using hi
  simp only [program,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,head_length];omega)]
  rw [List.getElem?_append_left (by rw [head_length];rw [UniformNormalizationPreparation.fullProgram_length] at hi;omega)]
  simp only [head]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]
theorem traversal_code : CodeAt UniformCRTTraversalMachine.program program 337 385 := by
  intro i hi
  have hi48:i<48:=by simpa only [UniformCRTTraversalMachine.program_length] using hi
  simp only [program,embed]
  rw [List.getElem?_append_left (by simp only [List.length_append,head_length,List.length_map];omega)]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head]
  rw [List.getElem?_append_right (by simp [UniformNormalizationPreparation.fullProgram_length])]
  simp only [List.length_map,UniformNormalizationPreparation.fullProgram_length,
    Nat.add_sub_cancel_left,List.getElem?_map]
theorem metadata_code : CodeAt UniformGlobalNatPreparation.program program 385 417 := by
  simpa only [program,head_length] using
    embed_code head UniformGlobalNatPreparation.program [.halt] 417
theorem halt_at : program[417]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp [head_length,UniformGlobalNatPreparation.program_length])]
  simp [head_length,UniformGlobalNatPreparation.program_length]

abbrev ell (n : ℕ) := UniformWorkingLength.axisCount n
abbrev len (n : ℕ) := UniformWorkingLength.workingLength n
abbrev copyBase (n : ℕ) := UniformGlobalNatPreparation.destination (ell n) (len n)
abbrev alphaBase (n : ℕ) := UniformCRTTraversalMachine.alphaBase (ell n)
abbrev betaBase (n : ℕ) := UniformCRTTraversalMachine.betaBase (ell n) (len n)
def protectedView (n : ℕ) (s : State) : State :=
  {s with natHeap:=fun a=>s.natHeap (copyBase n+a)}

structure Operands (n : ℕ) (x : Fin n→ℂ) (s : State) : Prop where
  constants : ∀j:Fin 6,s.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))
  roots : ∀j:Fin (ell n+1),s.scalarHeap (6+j.val)=some
    (prepared (OAI.ExactFourier.zeta (UniformSelectedCRT.radices n j)))
  chirps : UniformChirpTableMachine.Partial (ell n+7) n (OAI.ExactFourier.zeta (2*n)) s
  input : UniformPaddedInputMachine.Partial (UniformPaddedInputPreparation.dataBase n)
    (len n) (OAI.ExactFourier.zeta (2*n)) x s
  kernel : UniformChirpKernelMachine.Partial (UniformChirpKernelPreparation.kernelBase n)
    (len n) n (len n) (OAI.ExactFourier.zeta (2*n)) s
  normalization : s.scalarHeap (UniformNormalizationPreparation.normBase n)=some (prepared (len n:ℂ)⁻¹)

theorem Operands.transport {n : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Operands n x s) (hh:u.scalarHeap=s.scalarHeap) : Operands n x u := by
  cases h
  constructor <;> simp only [UniformChirpTableMachine.Partial,UniformPaddedInputMachine.Partial,
    UniformChirpKernelMachine.Partial,hh] <;> assumption

structure Ready (n : ℕ) (x : Fin n→ℂ) (s : State) : Prop where
  header : UniformCRTHeaderMachine.Header n s
  crt : UniformCRTHeaderMachine.CRTTable n s
  order : s.natReg 24=UniformMasterRootMachine.order n
  inputLength : s.natReg 8=n
  normalizationAddress : s.natReg 27=UniformNormalizationPreparation.normBase n
  operands : Operands n x s
  saved : UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n)
    n (ell n) (len n) (UniformMasterRootMachine.order n) s
  alpha : UniformGlobalNatPreparation.PermutationBank (len n) (alphaBase n) s.natHeap
    (UniformCRTTraversalCycle.alphaPermutation n)
  beta : UniformGlobalNatPreparation.PermutationBank (len n) (betaBase n) s.natHeap
    (UniformCRTTraversalCycle.betaPermutation n)
  protectedAlpha : UniformGlobalNatPreparation.PermutationBank (len n) (copyBase n+alphaBase n)
    s.natHeap (UniformCRTTraversalCycle.alphaPermutation n)
  protectedBeta : UniformGlobalNatPreparation.PermutationBank (len n) (copyBase n+betaBase n)
    s.natHeap (UniformCRTTraversalCycle.betaPermutation n)
  protectedPrimes : UniformWorkingMachine.PrimeTable (ell n) (protectedView n s)
  protectedCRT : UniformCRTHeaderMachine.CRTTable n (protectedView n s)
  protectedFilled : ∀a,a<UniformGlobalNatPreparation.amount (ell n) (len n)→
    ∃v,s.natHeap (copyBase n+a)=some v
  oneRoot : s.rootOrders=[UniformMasterRootMachine.order n]
  outputs : s.outputs=initial.outputs

theorem word_setup {n : ℕ} (hn:0<n) : 418≤(n+2)^19 ∧
    128+10*ell n+4*len n≤(n+2)^19 ∧
    UniformGlobalNatPreparation.wordBudget (ell n) (len n)≤(n+2)^19 := by
  have he:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:300≤(n+2)^18:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 18
    norm_num at h;omega
  have hb:300*(n+2)≤(n+2)^19:=by
    rw [pow_succ];exact Nat.mul_le_mul_right (n+2) hp
  unfold UniformGlobalNatPreparation.wordBudget
  omega

def preparationBudget (n : ℕ) : ℕ :=
  UniformNormalizationPreparation.fullPreparationBudget n+400*n+100

/-- One fixed initial-state program constructs every startup operand and both
independent CRT address tables, then copies all Nat metadata out of local-row
workspace. The Fourier transforms and their charged scheduler remain separate. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution program n x ((n+2)^19) initial t u ∧
    Ready n x u ∧ u.pc=417 ∧ t≤preparationBudget n := by
  obtain ⟨t,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hchirp,hdata,hkernel,hnorm,h27,hroot,hout,hpc,hcost⟩:=
    UniformNormalizationPreparation.preparation_execution hn x
  have hops:Operands n x v:=⟨hbank,hroots,hchirp,hdata,hkernel,hnorm⟩
  obtain ⟨h418,htraversal,hcopy⟩:=word_setup hn
  have hfirst:=UniformBoundedAssembly.boundedExecution_placed normalization_code
    (by rw [UniformNormalizationPreparation.fullProgram_length];omega :
      0+UniformNormalizationPreparation.fullProgram.length≤(n+2)^19) (by omega : 337≤(n+2)^19) hv
  change BoundedRuns program n x ((n+2)^19) initial t {v with pc:=337} at hfirst
  let s:State:={v with pc:=0}
  obtain ⟨c,w,hw,hc,hh,hC,hT,hsource,hf,hwp⟩:=UniformCRTTraversalCycle.initialized_execution_source
    hn ((n+2)^19) x s rfl hheader hcrt
    (changePC_bound _ v 0 hv.final_bound (by omega)) htraversal
  have hsecond:=UniformBoundedAssembly.boundedExecution_placed traversal_code
    (by rw [UniformCRTTraversalMachine.program_length];omega :
      337+UniformCRTTraversalMachine.program.length≤(n+2)^19) (by omega : 385≤(n+2)^19) hw
  change BoundedRuns program n x ((n+2)^19) {v with pc:=337} c {w with pc:=385} at hsecond
  have hnats:∀r,r<50→w.natReg r=v.natReg r:=hf.2.2.2.2.1
  have wh:UniformGlobalNatPreparation.Headers (UniformWorkingLength.nextPrime n) n (ell n)
      (len n) (UniformMasterRootMachine.order n) w:=
    ⟨hh.1,(hnats 8 (by decide)).trans h8,hh.2.1,hh.2.2.2.2.1,(hnats 24 (by decide)).trans horder⟩
  let e:State:={w with pc:=0}
  have src:UniformNatCopyMachine.Source (UniformGlobalNatPreparation.amount (ell n) (len n)) 0 e.natHeap:=by
    simpa only [UniformNatCopyMachine.Source,UniformGlobalNatPreparation.amount,
      UniformCRTTraversalCycle.FilledPrefix,UniformCRTTraversalCycle.prefixSize,Nat.zero_add] using hsource
  obtain ⟨u,hu,hsaved,hheaders,hprotected,hpreserve,_houtside,hframe,hNatFrame⟩:=
    UniformGlobalNatPreparation.execution n x (UniformWorkingLength.nextPrime n) (ell n) (len n)
      (UniformMasterRootMachine.order n) ((n+2)^19) e wh.withPC src rfl hcopy
      (changePC_bound _ w 0 hw.final_bound (by omega))
  have hthird:=UniformBoundedAssembly.boundedExecution_placed metadata_code
    (by rw [UniformGlobalNatPreparation.program_length];omega :
      385+UniformGlobalNatPreparation.program.length≤(n+2)^19) (by omega : 417≤(n+2)^19) hu
  change BoundedRuns program n x ((n+2)^19) {w with pc:=385}
    (7*UniformGlobalNatPreparation.amount (ell n) (len n)+26) {u with pc:=417} at hthird
  let final:State:={u with pc:=417}
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=
    .halt hthird.final_bound (by simp [step,final,halt_at])
  have hregs:∀r,r<50→u.natReg r=w.natReg r:=fun r hr =>
    hNatFrame r (Or.inl (by omega)) (Or.inl (by omega))
  have huheader:UniformCRTHeaderMachine.Header n u:=by
    obtain ⟨h0,h10,h11,h16,h17,h18,hprime⟩:=hh
    refine ⟨(hregs 0 (by decide)).trans h0,(hregs 10 (by decide)).trans h10,
      (hregs 11 (by decide)).trans h11,(hregs 16 (by decide)).trans h16,
      (hregs 17 (by decide)).trans h17,(hregs 18 (by decide)).trans h18,?_⟩
    intro i hi
    change i<ell n at hi
    exact (hpreserve i (by unfold UniformGlobalNatPreparation.amount;omega)).trans (hprime i hi)
  have hucrt:UniformCRTHeaderMachine.CRTTable n u:=by
    intro i
    have hrow (f : ℕ) (hf:f≤3):u.natHeap (UniformCRTHeaderMachine.tableAddress (ell n) i.val f)=
        w.natHeap (UniformCRTHeaderMachine.tableAddress (ell n) i.val f):=by
      apply hpreserve
      have hi:=i.isLt
      change i.val<ell n+1 at hi
      unfold UniformCRTHeaderMachine.tableAddress UniformGlobalNatPreparation.amount;omega
    exact ⟨(hrow 0 (by decide)).trans (hC i).1,(hrow 1 (by decide)).trans (hC i).2.1,
      (hrow 2 (by decide)).trans (hC i).2.2.1,(hrow 3 (by decide)).trans (hC i).2.2.2⟩
  have hperms:=UniformCRTTraversalCycle.tables_permutations n w hT
  have hprotcrt:UniformCRTHeaderMachine.CRTTable n (protectedView n u):=by
    intro i
    have hrow (f : ℕ) (hf:f≤3):(protectedView n u).natHeap
        (UniformCRTHeaderMachine.tableAddress (ell n) i.val f)=
        w.natHeap (UniformCRTHeaderMachine.tableAddress (ell n) i.val f):=by
      apply hprotected
      have hi:i.val<ell n+1:=i.isLt
      unfold UniformCRTHeaderMachine.tableAddress UniformGlobalNatPreparation.amount;omega
    exact ⟨(hrow 0 (by decide)).trans (hC i).1,(hrow 1 (by decide)).trans (hC i).2.1,
      (hrow 2 (by decide)).trans (hC i).2.2.1,(hrow 3 (by decide)).trans (hC i).2.2.2⟩
  have hprotprime:UniformWorkingMachine.PrimeTable (ell n) (protectedView n u):=by
    intro i hi
    exact (hprotected i (by unfold UniformGlobalNatPreparation.amount;omega)).trans
      (hh.2.2.2.2.2.2 i hi)
  have hprotfilled:∀a,a<UniformGlobalNatPreparation.amount (ell n) (len n)→
      ∃v,u.natHeap (copyBase n+a)=some v:=by
    intro a ha
    obtain ⟨v,hv⟩:=hsource a ha
    exact ⟨v,(hprotected a ha).trans hv⟩
  have hap:UniformGlobalNatPreparation.PermutationBank (len n) (alphaBase n) w.natHeap
      (UniformCRTTraversalCycle.alphaPermutation n):=fun j=>(hperms j).1
  have hbp:UniformGlobalNatPreparation.PermutationBank (len n) (betaBase n) w.natHeap
      (UniformCRTTraversalCycle.betaPermutation n):=fun j=>(hperms j).2
  have ha:alphaBase n+len n≤UniformGlobalNatPreparation.amount (ell n) (len n):=by
    unfold alphaBase UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase
      UniformGlobalNatPreparation.amount;omega
  have hb:betaBase n+len n≤UniformGlobalNatPreparation.amount (ell n) (len n):=by
    unfold betaBase UniformCRTTraversalMachine.betaBase UniformCRTTraversalMachine.alphaBase
      UniformCRTTraversalMachine.digitBase UniformGlobalNatPreparation.amount;omega
  have ha':UniformGlobalNatPreparation.PermutationBank (len n) (alphaBase n) u.natHeap
      (UniformCRTTraversalCycle.alphaPermutation n):=by
    intro j;exact (hpreserve _ (by have hj:=j.isLt;omega)).trans (hap j)
  have hb':UniformGlobalNatPreparation.PermutationBank (len n) (betaBase n) u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n):=by
    intro j;exact (hpreserve _ (by have hj:=j.isLt;omega)).trans (hbp j)
  have he:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  refine ⟨t+c+(7*UniformGlobalNatPreparation.amount (ell n) (len n)+26)+1,final,
    ((hfirst.trans hsecond).trans hthird).executes hhalt,?_,rfl,?_⟩
  · refine ⟨huheader,hucrt,hheaders.masterRoot,hheaders.inputLength,
      (hregs 27 (by decide)).trans ((hnats 27 (by decide)).trans h27),
      hops.transport (hframe.1.trans hf.2.1),hsaved.withPC,ha',hb',?_,?_,
      hprotprime,hprotcrt,hprotfilled,
      hframe.2.2.2.trans (hf.2.2.2.1.trans hroot),hframe.2.2.1.trans (hf.2.2.1.trans hout)⟩
    · exact UniformGlobalNatPreparation.protected_permutation (ell n) (len n) (alphaBase n)
        (len n) w.natHeap u (UniformCRTTraversalCycle.alphaPermutation n) hprotected ha hap
    · exact UniformGlobalNatPreparation.protected_permutation (ell n) (len n) (betaBase n)
        (len n) w.natHeap u (UniformCRTTraversalCycle.betaPermutation n) hprotected hb hbp
  · unfold preparationBudget UniformGlobalNatPreparation.amount
    change c<46*len n+5*ell n+21 at hc
    omega

theorem preparationBudget_isBigO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hl:(fun n : ℕ => (400*n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n:ℝ)) Filter.atTop).const_mul_left 400
  have hc:(fun _n : ℕ => (100:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (100:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [preparationBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    (UniformNormalizationPreparation.fullPreparationBudget_isBigO_input.add hl).add hc

end
end ExactFourierCircuits.UniformInitialPreparation
