import UniformPermutationInversePreparation
import UniformBoundedAssembly

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, CRT tables and linear index traversal surrounding (5.5),
PDF p.22 (`eq:crt-fourier`), using the prefix bound (4.1), PDF p.18.

Literal integer/table/traversal bookkeeping refines that argument. The paper
does not specify this register layout or these frames; semantic and charged
execution obligations are separate declarations below.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCRTTransferMachine
open UniformMachine UniformAssembly
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
open UniformInitialPreparation (ell len copyBase alphaBase)
noncomputable section

/-- Caller registers 201/202/203 identify the native source, canonical scratch,
and next alpha-ordered destination. All permutation headers are computed from
the actual protected startup metadata. -/
def setup : List Op := [.literal 210 0,.add 200 103 210,.add 204 105 106,
  .literal 211 6,.mul 205 102 211,.literal 211 5,.add 205 205 211,.add 205 105 205,
  .add 70 200 210,.add 71 201 210,.add 72 202 210,.add 73 204 210]
def nextSetup : List Op := [.add 70 200 210,.add 71 202 210,
  .add 72 203 210,.add 73 205 210]
def program : Program := setup.map Op.code ++
  UniformPermutationMachine.program.map (relocate 12 24) ++ nextSetup.map Op.code ++
  UniformPermutationMachine.program.map (relocate 28 40) ++ [.halt]

theorem setup_length : setup.length=12 := rfl
theorem nextSetup_length : nextSetup.length=4 := rfl
theorem program_length : program.length=41 := rfl
theorem setup_code : BlockAt setup program 0 := by
  intro i hi;change i<12 at hi;interval_cases i <;> rfl
theorem nextSetup_code : BlockAt nextSetup program 24 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem inverse_code : CodeAt UniformPermutationMachine.program program 12 24 := by
  intro i hi;change i<12 at hi;interval_cases i <;> rfl
theorem alpha_code : CodeAt UniformPermutationMachine.program program 28 40 := by
  intro i hi;change i<12 at hi;interval_cases i <;> rfl
theorem halt_at : program[40]?=some .halt := rfl

theorem setup_registers {n : ℕ} (s : State)
    (h:UniformPermutationInversePreparation.Metadata n s) :
    (applyBlock setup s).natReg 70=len n ∧
    (applyBlock setup s).natReg 71=s.natReg 201 ∧
    (applyBlock setup s).natReg 72=s.natReg 202 ∧
    (applyBlock setup s).natReg 73=UniformPermutationInversePreparation.inverseBase n ∧
    (applyBlock setup s).natReg 205=copyBase n+alphaBase n ∧
    (applyBlock setup s).natReg 200=len n ∧
    (applyBlock setup s).natReg 210=0 := by
  simp [applyBlock,setup,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.copyAddress,h.saved.copyLength,UniformPermutationInversePreparation.inverseBase,
    alphaBase,UniformCRTTraversalMachine.alphaBase,UniformCRTTraversalMachine.digitBase,
    Nat.add_assoc]
  omega

theorem setup_saved (s : State) (r : ℕ) (hr:100≤r ∧ r≤106) :
    (applyBlock setup s).natReg r=s.natReg r := by
  simp (disch:=omega) [applyBlock,setup,Op.apply,writeNat,next]
theorem setup_caller (s : State) (r : ℕ) (hr:r=201 ∨ r=202 ∨ r=203) :
    (applyBlock setup s).natReg r=s.natReg r := by
  rcases hr with rfl|rfl|rfl <;> rfl
theorem nextSetup_saved (s : State) (r : ℕ) (hr:100≤r) :
    (applyBlock nextSetup s).natReg r=s.natReg r := by
  simp (disch:=omega) [applyBlock,nextSetup,Op.apply,writeNat,next]

theorem setup_peak {n : ℕ} (B : ℕ) (s : State)
    (h:UniformPermutationInversePreparation.Metadata n s)
    (hI:UniformPermutationInversePreparation.inverseBase n≤B)
    (hA:copyBase n+alphaBase n≤B) (hL:len n≤B) (hB:211≤B)
    (hc:∀r,r=201 ∨ r=202 ∨ r=203→s.natReg r≤B) : peak setup s≤B := by
  have hc1:=hc 201 (Or.inl rfl)
  have hc2:=hc 202 (Or.inr (Or.inl rfl))
  simp [peak,setup,Op.peak,Op.apply,writeNat,next,h.saved.workingLength,h.saved.count,
    h.saved.copyAddress,h.saved.copyLength]
  unfold UniformPermutationInversePreparation.inverseBase at hI
  unfold alphaBase UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase at hA
  unfold copyBase at hI hA
  omega

theorem nextSetup_registers (s : State) (L T D A : ℕ)
    (h200:s.natReg 200=L) (h202:s.natReg 202=T) (h203:s.natReg 203=D)
    (h205:s.natReg 205=A) (h210:s.natReg 210=0) :
    (applyBlock nextSetup s).natReg 70=L ∧ (applyBlock nextSetup s).natReg 71=T ∧
    (applyBlock nextSetup s).natReg 72=D ∧ (applyBlock nextSetup s).natReg 73=A := by
  simp [applyBlock,nextSetup,Op.apply,writeNat,next,h200,h202,h203,h205,h210]
theorem nextSetup_peak (B : ℕ) (s : State) (h210:s.natReg 210=0)
    (hs:WordBound B s) : peak nextSetup s≤B := by
  have h0:=hs.2.1 200
  have h1:=hs.2.1 202
  have h2:=hs.2.1 203
  have h3:=hs.2.1 205
  simp [peak,nextSetup,Op.peak,Op.apply,writeNat,next,h210];omega

/-- Both gathers run in one fixed program. The inverse-beta table is an actual
initialized bank retained by startup; alpha and beta are independent. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (S T D B : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (hI:UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm)
    (hsrc:UniformPermutationMachine.Source (len n) S s.scalarHeap)
    (hST:UniformPermutationMachine.Disjoint S T (len n))
    (hTD:UniformPermutationMachine.Disjoint T D (len n))
    (hS:S+len n≤B) (hT:T+len n≤B) (hD:D+len n≤B)
    (hIb:UniformPermutationInversePreparation.inverseBase n+len n≤B)
    (hAb:copyBase n+alphaBase n+len n≤B) (hcode:211≤B)
    (hpc:s.pc=0) (h201:s.natReg 201=S) (h202:s.natReg 202=T)
    (h203:s.natReg 203=D) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (18*len n+25) u ∧ u.pc=40 ∧
    (∀j:Fin (len n),u.scalarHeap (D+j.val)=
      s.scalarHeap (S+((UniformCRTTraversalCycle.betaPermutation n).symm
        (UniformCRTTraversalCycle.alphaPermutation n j)).val)) ∧
    u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,100≤r ∧ r≤106→u.natReg r=s.natReg r) ∧
    UniformPermutationInversePreparation.Metadata n u ∧
    (∀a,(a<T ∨ T+len n≤a)→(a<D ∨ D+len n≤a)→u.scalarHeap a=s.scalarHeap a) := by
  have boot:=block_runs setup program 0 n B x s setup_code hpc hs
    (by rw [setup_length];omega) (by simp [readable,setup,Op.readable])
    (setup_peak B s hm (by omega) (by omega) (by omega) hcode (by
      intro r hr;rcases hr with rfl|rfl|rfl <;> simp only [h201,h202,h203] <;> omega))
  let z:=applyBlock setup s
  let e:State:={z with pc:=0}
  obtain ⟨h70,h71,h72,h73,h205,h200,h210⟩:=setup_registers s hm
  obtain ⟨v,hv,hvval,_,hvo,hvf,_,_⟩:=UniformPermutationMachine.execution n x (len n)
    S T (UniformPermutationInversePreparation.inverseBase n) B
    (UniformCRTTraversalCycle.betaPermutation n).symm e hI hsrc hST hS hT hIb
    (by omega) rfl (by exact h70) (by simpa [h201] using h71)
    (by simpa [h202] using h72) h73
    (changePC_bound B z 0 boot.final_bound (by omega))
  have first:=UniformBoundedAssembly.boundedExecution_placed inverse_code
    (by change 12+12≤B;omega) (by omega :24≤B) hv
  have zpc:z.pc=12:=by rw [UniformReciprocalMachine.applyBlock_pc,hpc,setup_length]
  have entry:placed 12 e=z:=by change {z with pc:=12}=z;rw [←zpc]
  rw [entry] at first
  let w:State:={v with pc:=24}
  have persist (r : ℕ) (hr:81≤r) : w.natReg r=z.natReg r:=hvf.2.2.2.2 r (Or.inr hr)
  have secondBoot:=block_runs nextSetup program 24 n B x w nextSetup_code rfl
    first.final_bound (by rw [nextSetup_length];omega)
    (by simp [readable,nextSetup,Op.readable])
    (nextSetup_peak B w ((persist 210 (by omega)).trans h210) first.final_bound)
  let y:=applyBlock nextSetup w
  let f:State:={y with pc:=0}
  have caller (r : ℕ) (hr:r=201 ∨ r=202 ∨ r=203) : w.natReg r=s.natReg r :=
    (persist r (by rcases hr with rfl|rfl|rfl <;> omega)).trans (setup_caller s r hr)
  obtain ⟨k70,k71,k72,k73⟩:=nextSetup_registers w (len n) T D (copyBase n+alphaBase n)
    ((persist 200 (by omega)).trans h200) ((caller 202 (by simp)).trans h202)
    ((caller 203 (by simp)).trans h203) ((persist 205 (by omega)).trans h205)
    ((persist 210 (by omega)).trans h210)
  have table:UniformGlobalNatPreparation.PermutationBank (len n) (copyBase n+alphaBase n)
      f.natHeap (UniformCRTTraversalCycle.alphaPermutation n):=by
    intro j;exact (congrFun hvf.1 _).trans (hm.alpha j)
  have source:UniformPermutationMachine.Source (len n) T f.scalarHeap:=by
    intro j
    obtain ⟨a,ha⟩:=hsrc ((UniformCRTTraversalCycle.betaPermutation n).symm j)
    exact ⟨a,(hvval j).trans ha⟩
  obtain ⟨u,hu,huval,_,huo,huf,_,_⟩:=UniformPermutationMachine.execution n x (len n)
    T D (copyBase n+alphaBase n) B (UniformCRTTraversalCycle.alphaPermutation n) f
    table source hTD hT hD hAb (by omega) rfl k70 k71 k72 k73
    (changePC_bound B y 0 secondBoot.final_bound (by omega))
  have second:=UniformBoundedAssembly.boundedExecution_placed alpha_code
    (by change 28+12≤B;omega) (by omega :40≤B) hu
  have ypc:y.pc=28:=by rw [UniformReciprocalMachine.applyBlock_pc,nextSetup_length]
  have entry2:placed 28 f=y:=by change {y with pc:=28}=y;rw [←ypc]
  rw [entry2] at second
  let final:State:={u with pc:=40}
  have halt:BoundedExecution program n x B final 1 final:=
    .halt second.final_bound (by simp [step,final,halt_at])
  have savedFrame (r : ℕ) (hr:100≤r ∧ r≤106) : final.natReg r=s.natReg r :=
    (huf.2.2.2.2 r (Or.inr (by omega))).trans
      ((nextSetup_saved w r hr.1).trans ((persist r (by omega)).trans (setup_saved s r hr)))
  have saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n)
      n (ell n) (len n) (UniformMasterRootMachine.order n) final := by
    rcases hm.saved with ⟨a,b,c,d,e,f,g⟩
    exact ⟨(savedFrame 100 (by omega)).trans a,(savedFrame 101 (by omega)).trans b,
      (savedFrame 102 (by omega)).trans c,(savedFrame 103 (by omega)).trans d,
      (savedFrame 104 (by omega)).trans e,(savedFrame 105 (by omega)).trans f,
      (savedFrame 106 (by omega)).trans g⟩
  refine ⟨final,?_,rfl,?_,?_,?_,?_,savedFrame,?_,?_⟩
  · convert boot.executes (first.executes (secondBoot.executes (second.executes halt))) using 1
    rw [setup_length,nextSetup_length];omega
  · intro j;exact (huval j).trans (hvval (UniformCRTTraversalCycle.alphaPermutation n j))
  · exact huf.1.trans hvf.1
  · exact huf.2.1.trans hvf.2.1
  · exact huf.2.2.1.trans hvf.2.2.1
  · exact hm.transport_saved saved (fun _ _=>congrFun (huf.1.trans hvf.1) _)
  · intro a ha hb;exact (huo a hb).trans (hvo a ha)

/-- Native beta-coordinate scalars become precisely the next alpha input,
including their unchanged dependency tags. -/
theorem transfer_values {n S D : ℕ} (s u : State) (v : Fin (len n)→Scalar)
    (hsource:∀j:Fin (len n),s.scalarHeap (S+j.val)=some
      (v (UniformCRTTraversalCycle.betaPermutation n j)))
    (hcopy:∀j:Fin (len n),u.scalarHeap (D+j.val)=s.scalarHeap
      (S+((UniformCRTTraversalCycle.betaPermutation n).symm
        (UniformCRTTraversalCycle.alphaPermutation n j)).val)) :
    ∀j:Fin (len n),u.scalarHeap (D+j.val)=some
      (v (UniformCRTTraversalCycle.alphaPermutation n j)) := by
  intro j
  simpa only [Equiv.apply_symm_apply] using (hcopy j).trans
    (hsource ((UniformCRTTraversalCycle.betaPermutation n).symm
      (UniformCRTTraversalCycle.alphaPermutation n j)))

theorem runtime_linear (n : ℕ) :18*len n+25≤43*(len n+1) := by omega

/-- The selected helper retains the unchanged global logarithmic-word budget.
Only caller array placement and the actual retained inverse bank remain entry
premises; neither a ready composed table nor a host-side permutation is used. -/
theorem selected_execution (n : ℕ) (hn:0<n) (x : Fin n→ℂ) (S T D : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (hI:UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm)
    (hsrc:UniformPermutationMachine.Source (len n) S s.scalarHeap)
    (hST:UniformPermutationMachine.Disjoint S T (len n))
    (hTD:UniformPermutationMachine.Disjoint T D (len n))
    (hS:S+len n≤(n+2)^19) (hT:T+len n≤(n+2)^19) (hD:D+len n≤(n+2)^19)
    (hpc:s.pc=0) (h201:s.natReg 201=S) (h202:s.natReg 202=T)
    (h203:s.natReg 203=D) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s (18*len n+25) u ∧ u.pc=40 ∧
    (∀j:Fin (len n),u.scalarHeap (D+j.val)=
      s.scalarHeap (S+((UniformCRTTraversalCycle.betaPermutation n).symm
        (UniformCRTTraversalCycle.alphaPermutation n j)).val)) ∧
    u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,100≤r ∧ r≤106→u.natReg r=s.natReg r) ∧
    UniformPermutationInversePreparation.Metadata n u ∧
    (∀a,(a<T ∨ T+len n≤a)→(a<D ∨ D+len n≤a)→u.scalarHeap a=s.scalarHeap a) := by
  have hi:=UniformPermutationInversePreparation.word_setup hn
  have ha:=UniformInputPermutationPreparation.word_setup hn
  exact execution n x S T D ((n+2)^19) s hm hI hsrc hST hTD hS hT hD hi.2
    ha.2.2 (by omega) hpc h201 h202 h203 hs
end
end ExactFourierCircuits.UniformCRTTransferMachine
