import UniformPermutationInversePreparation
import UniformTensorAddressMachine

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ExactFourierCircuits.UniformGlobalLocalPreparation
open UniformMachine UniformAssembly UniformPairMachine
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
noncomputable section

abbrev radix (n : ℕ) (j : Fin (ell n+1)) := UniformSelectedCRT.radices n j
def globalEnd (n : ℕ) : ℕ := UniformInputPermutationPreparation.destination n+len n
def resultBase (n r : ℕ) : ℕ := globalEnd n+8*r+5
def scratchBase (n r : ℕ) : ℕ := resultBase n r+8*r+3
def rootSource (n r : ℕ) : ℕ := scratchBase n r+6
def bank (n : ℕ) (j : Fin 6) : Scalar := prepared (UniformCConstantsMachine.bank n j)

theorem radix_pos (n : ℕ) (j : Fin (ell n+1)) : 0<radix n j := UniformSelectedCRT.radix_pos n j
theorem radix_le_length (n : ℕ) (j : Fin (ell n+1)) : radix n j ≤ len n := by
  have hP:=UniformCRTTraversalCycle.place_pos (UniformSelectedCRT.radices n) (UniformSelectedCRT.radix_pos n) j.val
  have hQ:=UniformTensorAddressMachine.upperCount_pos (UniformSelectedCRT.radices n) (UniformSelectedCRT.radix_pos n) j
  have h1:radix n j ≤ UniformCRTTraversalCycle.place (UniformSelectedCRT.radices n) j.val*radix n j:=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (radix n j) (show 1 ≤ _ by omega)
  have h2:=Nat.mul_le_mul h1 (show 1 ≤ UniformTensorAddressMachine.upperCount (UniformSelectedCRT.radices n) j by omega)
  simpa only [Nat.mul_one,UniformTensorAddressMachine.selected_layout] using h2

theorem layout (n r : ℕ) : UniformNewtonTableMachine.Layout r (resultBase n r)
    (scratchBase n r) (rootSource n r) := by
  constructor <;> dsimp [resultBase,scratchBase,rootSource] <;> omega

def pointer : List Op := [.literal 107 4,.mul 108 110 107,.add 108 102 108,.add 108 105 108]
def setup : List Op := [
  .literal 107 6,.add 108 110 107,.getScalar 20 108,
  .literal 107 7,.add 111 102 107,.literal 107 2,.mul 112 101 107,.add 111 111 112,
  .add 111 111 103,.add 111 111 103,.literal 107 1,.add 111 111 107,.add 111 111 103,
  .literal 107 8,.mul 112 16 107,.add 17 111 112,.literal 107 5,.add 17 17 107,
  .add 19 17 112,.literal 107 3,.add 19 19 107,.literal 107 6,.add 18 19 107,.putScalar 18 20]
theorem pointer_length : pointer.length=4 := rfl
theorem setup_length : setup.length=24 := rfl
def head : Program := pointer.map Op.code++[.loadNat 16 108]++setup.map Op.code
def program : Program := embed head UniformReciprocalMachine.completeProgram [.halt] 298
theorem head_length : head.length=29 := rfl
theorem program_length : program.length=299 := by
  rw [program,embed_length,head_length,UniformReciprocalMachine.completeProgram_length];rfl
theorem pointer_code : BlockAt pointer program 0 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem load_code : program[4]?=some (.loadNat 16 108) := rfl
theorem setup_code : BlockAt setup program 5 := by
  intro i hi;change i<24 at hi;interval_cases i <;> rfl
theorem reciprocal_code : CodeAt UniformReciprocalMachine.completeProgram program 29 298 := by
  simpa only [program,head_length] using embed_code head UniformReciprocalMachine.completeProgram [.halt] 298
theorem halt_at : program[298]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by simp [head_length,UniformReciprocalMachine.completeProgram_length])]
  simp [head_length,UniformReciprocalMachine.completeProgram_length]

def loaded (s : State) (r : ℕ) : State := writeNat (applyBlock pointer s) 16 r
def initialized (s : State) (r : ℕ) : State := applyBlock setup (loaded s r)

theorem pointer_address {n : ℕ} (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) : (applyBlock pointer s).natReg 108=
      copyBase n+UniformCRTHeaderMachine.tableAddress (ell n) j.val 0 := by
  simp [pointer,applyBlock,Op.apply,writeNat,next,h.saved.count,h.saved.copyAddress,hj,
    UniformCRTHeaderMachine.tableAddress,Nat.mul_comm,Nat.add_assoc]

theorem initialized_registers {n : ℕ} (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (_hj:s.natReg 110=j.val) :
    (initialized s (radix n j)).natReg 16=radix n j ∧
    (initialized s (radix n j)).natReg 17=resultBase n (radix n j) ∧
    (initialized s (radix n j)).natReg 18=rootSource n (radix n j) ∧
    (initialized s (radix n j)).natReg 19=scratchBase n (radix n j) := by
  simp [initialized,loaded,pointer,setup,applyBlock,Op.apply,writeNat,writeScalar,next,
    h.saved.count,h.saved.inputLength,h.saved.workingLength,resultBase,scratchBase,rootSource,
    globalEnd,UniformInputPermutationPreparation.destination,UniformNormalizationPreparation.normBase,
    UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,Nat.mul_comm,Nat.add_assoc]

theorem initialized_nat (s : State) (r i : ℕ) (hi : 100  ≤  i) (hiUpper : i  ≤  106) :
    (initialized s r).natReg i=s.natReg i := by
  simp (disch:=omega) [initialized,loaded,pointer,setup,applyBlock,Op.apply,writeNat,writeScalar,next]
theorem initialized_natHeap (s : State) (r : ℕ) : (initialized s r).natHeap=s.natHeap := rfl
theorem initialized_outputs (s : State) (r : ℕ) : (initialized s r).outputs=s.outputs := rfl
theorem initialized_roots (s : State) (r : ℕ) : (initialized s r).rootOrders=s.rootOrders := rfl

theorem initialized_heap {n : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (ho:UniformInitialPreparation.Operands n x s) :
    (initialized s (radix n j)).scalarHeap=Function.update s.scalarHeap
      (rootSource n (radix n j)) (some (prepared (OAI.ExactFourier.zeta (radix n j)))) := by
  have hroot:=ho.roots j
  have hroot':s.scalarHeap (j.val+6)=some (prepared (OAI.ExactFourier.zeta (radix n j))):=by
    simpa only [Nat.add_comm] using hroot
  simp [initialized,loaded,pointer,setup,applyBlock,Op.apply,writeNat,writeScalar,next,
    h.saved.count,h.saved.inputLength,h.saved.workingLength,hj,hroot',resultBase,scratchBase,rootSource,
    globalEnd,UniformInputPermutationPreparation.destination,UniformNormalizationPreparation.normBase,
    UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,Nat.mul_comm,Nat.add_assoc]

theorem globalEnd_formula (n : ℕ) : globalEnd n=ell n+8+2*n+3*len n := by
  dsimp [globalEnd,UniformInputPermutationPreparation.destination,UniformNormalizationPreparation.normBase,
    UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase]
  simp only [ell,len]
  omega

theorem initialized_below {n : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (ho:UniformInitialPreparation.Operands n x s) (i : ℕ) (hi:i<globalEnd n) :
    (initialized s (radix n j)).scalarHeap i=s.scalarHeap i := by
  rw [initialized_heap x j s h hj ho,Function.update_of_ne]
  dsimp [rootSource,scratchBase,resultBase];omega

theorem initialized_bank {n : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (ho:UniformInitialPreparation.Operands n x s) :
    UniformNewtonTableMachine.Bank (bank n) (initialized s (radix n j)) := by
  intro q
  rw [initialized_below x j s h hj ho q.val (by rw [globalEnd_formula];have hq:=q.isLt;omega)]
  exact ho.constants q

theorem initialized_axis {n : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1)) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (ho:UniformInitialPreparation.Operands n x s) :
    (initialized s (radix n j)).scalarHeap (rootSource n (radix n j))=
      some (prepared (OAI.ExactFourier.zeta (radix n j))) := by
  rw [initialized_heap x j s h hj ho];simp

theorem setup_readable {n : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1)) (s : State)
    (hj:s.natReg 110=j.val) (ho:UniformInitialPreparation.Operands n x s) :
    readable setup (loaded s (radix n j)) := by
  have hroot':s.scalarHeap (j.val+6)=some (prepared (OAI.ExactFourier.zeta (radix n j))):=by
    simpa only [Nat.add_comm] using ho.roots j
  simp [readable,setup,loaded,pointer,applyBlock,Op.readable,Op.apply,writeNat,next,hj,hroot']

theorem pointer_peak {n : ℕ} (j : Fin (ell n+1)) (B : ℕ) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (hcopy:copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ B)
    (hcode:299 ≤ B) : peak pointer s ≤ B := by
  have hjb:=j.isLt
  simp [peak,pointer,Op.peak,Op.apply,writeNat,next,h.saved.count,h.saved.copyAddress,hj]
  unfold UniformGlobalNatPreparation.amount at hcopy
  simp only [copyBase] at hcopy
  omega

theorem setup_peak {n : ℕ} (j : Fin (ell n+1)) (B : ℕ) (s : State) (h:Metadata n s)
    (hj:s.natReg 110=j.val) (hB:UniformReciprocalMachine.completeWordBudget (radix n j)
      (resultBase n (radix n j)) (rootSource n (radix n j)) ≤ B) :
    peak setup (loaded s (radix n j)) ≤ B := by
  have hjb:=j.isLt
  simp [peak,setup,loaded,pointer,Op.peak,Op.apply,applyBlock,writeNat,writeScalar,next,
    h.saved.count,h.saved.inputLength,h.saved.workingLength,hj]
  dsimp only [UniformReciprocalMachine.completeWordBudget,resultBase,rootSource,scratchBase] at hB
  rw [globalEnd_formula] at hB
  omega

theorem operands_transport_below {n : ℕ} {x : Fin n→ℂ} {s u : State}
    (ho:UniformInitialPreparation.Operands n x s)
    (hh:∀i,i<globalEnd n→u.scalarHeap i=s.scalarHeap i) : UniformInitialPreparation.Operands n x u := by
  have hb:∀i,i ≤ UniformNormalizationPreparation.normBase n→u.scalarHeap i=s.scalarHeap i:=by
    intro i hi;apply hh;unfold globalEnd UniformInputPermutationPreparation.destination;omega
  constructor
  · intro q;exact (hh q.val (by rw [globalEnd_formula];have hq:=q.isLt;omega)).trans (ho.constants q)
  · intro q
    exact (hh _ (by rw [globalEnd_formula];have hq:=q.isLt;omega)).trans (ho.roots q)
  · intro k hk
    constructor
    · exact (hb _ (by dsimp [UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
        UniformPaddedInputPreparation.dataBase];simp only [ell] at *;omega)).trans (ho.chirps k hk).1
    · exact (hb _ (by dsimp [UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase,
        UniformPaddedInputPreparation.dataBase];simp only [ell] at *;omega)).trans (ho.chirps k hk).2
  · intro k hk
    exact (hb _ (by
      dsimp [UniformNormalizationPreparation.normBase,UniformChirpKernelPreparation.kernelBase]
      simp only [len] at *
      omega)).trans (ho.input k hk)
  · intro k hk
    exact (hb _ (by unfold UniformNormalizationPreparation.normBase;simp only [len] at *;omega)).trans (ho.kernel k hk)
  · exact (hb _ le_rfl).trans ho.normalization

theorem initialized_saved {n : ℕ} (s : State) (r : ℕ) (h:Metadata n s) :
    UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n (ell n) (len n)
      (UniformMasterRootMachine.order n) (initialized s r) := by
  constructor
  · exact (initialized_nat s r 100 (by decide) (by decide)).trans h.saved.nextPrime
  · exact (initialized_nat s r 101 (by decide) (by decide)).trans h.saved.inputLength
  · exact (initialized_nat s r 102 (by decide) (by decide)).trans h.saved.count
  · exact (initialized_nat s r 103 (by decide) (by decide)).trans h.saved.workingLength
  · exact (initialized_nat s r 104 (by decide) (by decide)).trans h.saved.masterRoot
  · exact (initialized_nat s r 105 (by decide) (by decide)).trans h.saved.copyAddress
  · exact (initialized_nat s r 106 (by decide) (by decide)).trans h.saved.copyLength

theorem word_setup {n : ℕ} (hn:0<n) (j : Fin (ell n+1)) :
    299 ≤ (n+2)^19 ∧ copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ (n+2)^19 ∧
    UniformReciprocalMachine.completeWordBudget (radix n j) (resultBase n (radix n j))
      (rootSource n (radix n j)) ≤ (n+2)^19 := by
  have he:ell n ≤ 2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n;unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hr:=radix_le_length n j
  have hp:300 ≤ (n+2)^18:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 18;norm_num at h;omega
  have hb:300*(n+2) ≤ (n+2)^19:=by rw [pow_succ];exact Nat.mul_le_mul_right (n+2) hp
  have hi:=UniformPermutationInversePreparation.word_setup hn
  dsimp only [UniformPermutationInversePreparation.inverseBase] at hi
  refine ⟨by omega,by omega,?_⟩
  dsimp only [UniformReciprocalMachine.completeWordBudget,resultBase,rootSource,scratchBase]
  rw [globalEnd_formula]
  omega

/-- Local Nat row writes are below the protected global prefix; local scalar
writes are above every global operand and gathered-input bank. -/
def Frame (n : ℕ) (s u : State) : Prop :=
  (∀ i : ℕ, i < globalEnd n → u.scalarHeap i = s.scalarHeap i) ∧
  (∀ i : ℕ, copyBase n ≤ i → u.natHeap i = s.natHeap i) ∧
  (∀ k : ℕ, 100 ≤ k → k ≤ 106 → u.natReg k = s.natReg k) ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders

theorem Frame.permutation {n K b : ℕ} {s u : State} {phi : Fin K≃Fin K}
    (h:Frame n s u) (hb:copyBase n ≤ b)
    (hp:UniformGlobalNatPreparation.PermutationBank K b s.natHeap phi) :
    UniformGlobalNatPreparation.PermutationBank K b u.natHeap phi := by
  intro j;exact (h.2.1 _ (by omega)).trans (hp j)

/-- Original beta and the independently produced beta inverse remain available.
This preservation corollary never identifies alpha with beta.symm. -/
theorem Frame.beta_inverse {n : ℕ} {s u : State} (h:Frame n s u)
    (hp:UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm) :
    UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm :=
  h.permutation (by unfold UniformPermutationInversePreparation.inverseBase;omega) hp

/-- A real selected-axis setup and the frozen269-instruction Newton/reciprocal
producer. No ready local rows, primitive-root premise or caller layout remains. -/
theorem preparation_execution {n : ℕ} (_hn:0<n) (x : Fin n→ℂ) (j : Fin (ell n+1))
    (B : ℕ) (s : State) (hm:Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hpc:s.pc=0) (hj:s.natReg 110=j.val)
    (hcopy:copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ B)
    (hWord:UniformReciprocalMachine.completeWordBudget (radix n j) (resultBase n (radix n j))
      (rootSource n (radix n j)) ≤ B) (hcode:299 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (UniformReciprocalMachine.completeRuntime (radix n j)+30) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    UniformNewtonTableMachine.PreparedOutputs (radix n j) (OAI.ExactFourier.zeta (radix n j))
      (resultBase n (radix n j)) u ∧
    UniformReciprocalMachine.GPrefix (radix n j) (rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n j))) u ∧
    u.scalarHeap (rootSource n (radix n j))=some (prepared (OAI.ExactFourier.zeta (radix n j))) ∧
    Frame n s u ∧ u.pc=298 := by
  let r:=radix n j
  have hr:0<r:=radix_pos n j
  have hrL:r ≤ len n:=radix_le_length n j
  have hLB:len n ≤ B:=by rw [←hm.saved.workingLength];exact hs.2.1 103
  have hptr:=block_runs pointer program 0 n B x s pointer_code hpc hs
    (by rw [pointer_length];omega) (by simp [readable,pointer,Op.readable])
    (pointer_peak j B s hm hj hcopy hcode)
  have hp4:(applyBlock pointer s).pc=4:=by rw [UniformReciprocalMachine.applyBlock_pc,hpc,pointer_length]
  have hload:(applyBlock pointer s).natHeap ((applyBlock pointer s).natReg 108)=some r:=by
    rw [pointer_address j s hm hj,UniformReciprocalMachine.applyBlock_natHeap]
    exact (hm.crt j).1
  have hloaded:WordBound B (loaded s r):=writeNat_bound B (applyBlock pointer s) 16 r hptr.final_bound
    (by rw [hp4];omega) (by omega)
  have hstep:step program n x (applyBlock pointer s)=.running (loaded s r):=by
    simp [step,hp4,load_code,hload,loaded]
  have hloadRuns:BoundedRuns program n x B (applyBlock pointer s) 1 (loaded s r):=
    .next hptr.final_bound hstep (.refl hloaded)
  have hp5:(loaded s r).pc=5:=by simp [loaded,writeNat,next,hp4]
  have hset:=block_runs setup program 5 n B x (loaded s r) setup_code hp5 hloaded
    (by rw [setup_length];omega) (setup_readable x j s hj ho) (setup_peak j B s hm hj hWord)
  let z:=initialized s (radix n j)
  let e:State:={z with pc:=0}
  have hbefore:BoundedRuns program n x B s 29 z:=by
    convert (hptr.trans hloadRuns).trans hset using 1 <;> rfl
  have heB:WordBound B e:=changePC_bound B z 0 hset.final_bound (by omega)
  obtain ⟨h16,h17,h18,h19⟩:=initialized_registers j s hm hj
  have hroot:IsPrimitiveRoot (OAI.ExactFourier.zeta r) r:=Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hr)
  have heNat : e.natReg = (initialized s (radix n j)).natReg := rfl
  have heHeap : e.scalarHeap = (initialized s (radix n j)).scalarHeap := rfl
  have he16 : e.natReg 16 = r := (congrFun heNat 16).trans h16
  have he17 : e.natReg 17 = resultBase n r := (congrFun heNat 17).trans h17
  have he18 : e.natReg 18 = rootSource n r := (congrFun heNat 18).trans h18
  have he19 : e.natReg 19 = scratchBase n r := (congrFun heNat 19).trans h19
  have hebank : UniformNewtonTableMachine.Bank (bank n) e := by
    intro q
    exact (congrFun heHeap q.val).trans (initialized_bank x j s hm hj ho q)
  have heaxis : e.scalarHeap (rootSource n r) = some (prepared (OAI.ExactFourier.zeta r)) :=
    (congrFun heHeap _).trans (initialized_axis x j s hm hj ho)
  obtain ⟨u,hu,hg,hprepared,hbank,haxis,houtputs,hroots,hrows,hother⟩:=
    UniformReciprocalMachine.complete_execution n x r (resultBase n r) (scratchBase n r) (rootSource n r)
      B (OAI.ExactFourier.zeta r) (bank n) e hr hroot (layout n r) rfl he16 he17 he18 he19
      hebank heaxis hWord heB
  have hscalar:∀i,i<globalEnd n→u.scalarHeap i=s.scalarHeap i:=by
    intro i hi
    by_cases hi6:i<6
    · have hbu:=hbank ⟨i,hi6⟩
      exact hbu.trans (ho.constants ⟨i,hi6⟩).symm
    · exact (hother i (by omega)
        (Or.inl (by unfold resultBase;omega))
        (Or.inl (by unfold scratchBase resultBase;omega))
        (Or.inl (by unfold rootSource scratchBase resultBase;omega))).trans (initialized_below x j s hm hj ho i hi)
  have hnat:∀i,copyBase n ≤ i→u.natHeap i=s.natHeap i:=by
    intro i hi
    rw [hrows,UniformNewtonTableMachine.putWords_after]
    · rfl
    · rw [UniformGlobalNatPreparation.rowBytes_length]
      have h:=UniformGlobalNatPreparation.destination_above_rows (ell n) (len n) r hrL
      simp only [Nat.zero_add]
      change UniformGlobalNatPreparation.destination (ell n) (len n) ≤ i at hi
      omega
  have hsaved : ∀ i : ℕ, 100 ≤ i → i ≤ 106 → u.natReg i = s.natReg i := by
    intro i hi hiUpper
    exact (UniformNewtonTableMachine.Executes.keeps_nat hu.executes
      (UniformGlobalNatPreparation.reciprocal_keeps_high i hi)).trans (initialized_nat s r i hi hiUpper)
  have heSaved : UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
      (ell n) (len n) (UniformMasterRootMachine.order n) e :=
    (initialized_saved s (radix n j) hm).transport (fun i _ => congrFun heNat i)
  have hsaved':=UniformGlobalNatPreparation.saved_after_actual_reciprocal hu.executes heSaved
  have hmeta:Metadata n u:=hm.transport_saved hsaved' (fun i _=>hnat _ (by omega))
  have htail:=UniformBoundedAssembly.boundedExecution_placed reciprocal_code
    (by rw [UniformReciprocalMachine.completeProgram_length];omega :
      29+UniformReciprocalMachine.completeProgram.length ≤ B) (by omega :298 ≤ B) hu
  have hpz : z.pc = 29 :=
    (UniformReciprocalMachine.applyBlock_pc setup (loaded s (radix n j))).trans
      (by rw [show (loaded s (radix n j)).pc = 5 from hp5,setup_length])
  have heq:placed 29 e=z:=by change {z with pc:=29}=z;rw [←hpz]
  rw [heq] at htail
  let final:State:={u with pc:=298}
  have hhalt:BoundedExecution program n x B final 1 final:=.halt htail.final_bound (by simp [step,final,halt_at])
  refine ⟨final,?_,hmeta.transport (fun _ _ => rfl) (fun _ _ => rfl),
    (operands_transport_below ho hscalar).transport rfl,hprepared,hg,haxis,
    ⟨hscalar,hnat,hsaved,houtputs,hroots⟩,rfl⟩
  convert hbefore.executes (htail.executes hhalt) using 1
  simp only [r]
  omega

theorem preparation_execution_budget {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (ell n+1))
    (s : State) (hm:Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hpc:s.pc=0) (hj:s.natReg 110=j.val) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s (UniformReciprocalMachine.completeRuntime (radix n j)+30) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    UniformNewtonTableMachine.PreparedOutputs (radix n j) (OAI.ExactFourier.zeta (radix n j))
      (resultBase n (radix n j)) u ∧
    UniformReciprocalMachine.GPrefix (radix n j) (rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n j))) u ∧
    u.scalarHeap (rootSource n (radix n j))=some (prepared (OAI.ExactFourier.zeta (radix n j))) ∧
    Frame n s u ∧ u.pc=298 := by
  obtain ⟨hcode,hcopy,hWord⟩:=word_setup hn j
  exact preparation_execution hn x j _ s hm ho hpc hj hcopy hWord hcode hs

theorem runtime_bound (n : ℕ) (j : Fin (ell n+1)) :
    UniformReciprocalMachine.completeRuntime (radix n j)+30 ≤ 23*(radix n j)^2+252*(radix n j)+219 := by
  have h:=UniformReciprocalMachine.completeRuntime_bound _ (radix_pos n j);omega

theorem runtime_quadratic (n : ℕ) (j : Fin (ell n+1)) :
    UniformReciprocalMachine.completeRuntime (radix n j)+30 ≤ 494*(radix n j)^2 := by
  have h:=runtime_bound n j
  have hr:=radix_pos n j
  nlinarith

end
end ExactFourierCircuits.UniformGlobalLocalPreparation
