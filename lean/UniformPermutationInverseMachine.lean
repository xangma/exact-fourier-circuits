import UniformPermutationMachine
import UniformNatCopyMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPermutationInverseMachine
open UniformMachine UniformAssembly
open UniformGlobalNatPreparation (PermutationBank)

/-- Nat81=length,82=original permutation bank,83=inverse bank. Only Nat84..88
are written. Each source-table load, inverse-table store, address operation,
branch and halt is a literal charged instruction. -/
def program : Program := [
  .natLiteral 84 0,.natLiteral 85 1,.branchLT 84 81 3 9,
  .natBinary .add 86 82 84,.loadNat 87 86,.natBinary .add 88 83 87,
  .storeNat 88 84,.natBinary .add 84 84 85,.jump 2,.halt]

theorem program_length : program.length=10 := rfl

noncomputable section

def Disjoint (a d L : ℕ) : Prop := a+L≤d ∨ d+L≤a
def Outside (d L : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop :=
  ∀j,(j<d ∨ d+L≤j) → s.natHeap j=heap j

/-- All scalars, outputs, root requests and registers outside84..88 survive. -/
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀r,(r<84 ∨ 88<r) → u.natReg r=s.natReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

structure Invariant (L a d k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option ℕ) (s : State) : Prop where
  length : s.natReg 81=L
  source : s.natReg 82=a
  destination : s.natReg 83=d
  index : s.natReg 84=k
  one : s.natReg 85=1
  written : ∀j:Fin L,j.val<k → s.natHeap (d+(phi j).val)=some j.val
  outside : Outside d L heap s

def sourceAddress (s : State) : State :=
  writeNat {s with pc:=3} 86 (s.natReg 82+s.natReg 84)
def loaded (s : State) (digit : ℕ) : State := writeNat (sourceAddress s) 87 digit
def destinationAddress (s : State) (digit : ℕ) : State :=
  writeNat (loaded s digit) 88 (s.natReg 83+digit)
def stored (s : State) (digit : ℕ) : State :=
  {next (destinationAddress s digit) with natHeap:=(Function.update s.natHeap
    (s.natReg 83+digit) (some (s.natReg 84)))}
def advanced (s : State) (digit : ℕ) : State := writeNat (stored s digit) 84 (s.natReg 84+1)
def iterationEnd (s : State) (digit : ℕ) : State := {advanced s digit with pc:=2}

theorem iteration_heap (s : State) (digit : ℕ) :
    (iterationEnd s digit).natHeap=Function.update s.natHeap
      (s.natReg 83+digit) (some (s.natReg 84)) := rfl

theorem iteration_frame (s : State) (digit : ℕ) : Frame s (iterationEnd s digit) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next,
    show r≠84 by omega,show r≠86 by omega,show r≠87 by omega,show r≠88 by omega]

theorem disjoint_source (a d L : ℕ) (hd:Disjoint a d L) (j : Fin L) :
    a+j.val<d ∨ d+L≤a+j.val := by unfold Disjoint at hd;omega

/-- Injectivity of the actually supplied permutation ensures that earlier
inverse entries are never overwritten by a later scatter. -/
theorem iteration_invariant (L a d k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option ℕ) (s : State) (hi:Invariant L a d k phi heap s) (hk:k<L) :
    Invariant L a d (k+1) phi heap (iterationEnd s (phi ⟨k,hk⟩).val) := by
  constructor
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next] using hi.destination
  · simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next] using hi.one
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index]
    by_cases he:j=⟨k,hk⟩
    · subst j;simp
    · rw [Function.update_of_ne]
      · exact hi.written j (by have hne:j.val≠k:=fun h=>he (Fin.ext h);omega)
      · intro heq
        apply he
        apply phi.injective
        apply Fin.ext
        omega
  · intro j hj
    have hdigit: (phi ⟨k,hk⟩).val<L:=(phi ⟨k,hk⟩).isLt
    rw [iteration_heap,hi.destination,Function.update_of_ne (by omega)]
    exact hi.outside j hj

/-- One complete seven-instruction scatter with an actual successful load. -/
theorem iteration (n : ℕ) (x : Fin n→ℂ) (L a d k B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option ℕ) (s : State) (hi:Invariant L a d k phi heap s)
    (hTable:PermutationBank L a heap phi) (hk:k<L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hcode:9≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 7 u ∧ Invariant L a d (k+1) phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  let j:Fin L:=⟨k,hk⟩
  let digit:ℕ:=(phi j).val
  have hdigit:digit<L:=(phi j).isLt
  have hload:s.natHeap (a+k)=some digit:=
    (hi.outside _ (disjoint_source a d L hd j)).trans (hTable j)
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have h1:WordBound B (sourceAddress s):=writeNat_bound B {s with pc:=3} 86 _ he
    (by change 3+1≤B;omega) (by rw [hi.source,hi.index];omega)
  have h2:WordBound B (loaded s digit):=writeNat_bound B (sourceAddress s) 87 digit h1
    (by change 4+1≤B;omega) (by omega)
  have h3:WordBound B (destinationAddress s digit):=writeNat_bound B (loaded s digit) 88 _ h2
    (by change 5+1≤B;omega) (by rw [hi.destination];omega)
  have h4:WordBound B (stored s digit):=UniformNatCopyMachine.store_bound B (destinationAddress s digit)
    (s.natReg 83+digit) (s.natReg 84) h3 (by change 6+1≤B;omega)
    (by rw [hi.destination];omega) (by rw [hi.index];omega)
  have h5:WordBound B (advanced s digit):=writeNat_bound B (stored s digit) 84 _ h4
    (by change 7+1≤B;omega) (by rw [hi.index];omega)
  have h6:WordBound B (iterationEnd s digit):=changePC_bound B _ 2 h5 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=3}=.running (sourceAddress s):=by
    simp [step,program,sourceAddress,evalNat]
  have t2:step program n x (sourceAddress s)=.running (loaded s digit):=by
    simp [step,program,loaded,sourceAddress,writeNat,next,hi.source,hi.index,hload]
  have t3:step program n x (loaded s digit)=.running (destinationAddress s digit):=by
    simp [step,program,destinationAddress,loaded,sourceAddress,writeNat,next,evalNat]
  have t4:step program n x (destinationAddress s digit)=.running (stored s digit):=by
    simp [step,program,stored,destinationAddress,loaded,sourceAddress,writeNat,next]
  have t5:step program n x (stored s digit)=.running (advanced s digit):=by
    simp [step,program,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next,hi.one,evalNat]
  have t6:step program n x (advanced s digit)=.running (iterationEnd s digit):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next]
  exact ⟨iterationEnd s digit,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.refl h6))))))),
    iteration_invariant L a d k phi heap s hi hk,rfl,iteration_frame s digit⟩

theorem loop (n : ℕ) (x : Fin n→ℂ) (L a d k fuel B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option ℕ) (s : State) (hi:Invariant L a d k phi heap s)
    (hTable:PermutationBank L a heap phi) (hk:k+fuel=L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hcode:9≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (7*fuel) u ∧ Invariant L a d L phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  induction fuel generalizing k s with
  | zero =>
    have he:k=L:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hframe⟩:=iteration n x L a d k B phi heap s hi hTable (by omega)
      hd haB hdB hcode hpc hs
    obtain ⟨v,hv,hiv,hpv,hfr⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨v,?_,hiv,hpv,hframe.trans hfr⟩
    convert hu.trans hv using 1;omega

def zeroState (s : State) : State := writeNat s 84 0
def initialized (s : State) : State := writeNat (zeroState s) 85 1

theorem initialize_invariant (L a d : ℕ) (phi : Fin L≃Fin L) (s : State)
    (h81:s.natReg 81=L) (h82:s.natReg 82=a) (h83:s.natReg 83=d) :
    Invariant L a d 0 phi s.natHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h81,h82,h83,Outside]

theorem initialize_frame (s : State) : Frame s (initialized s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp [initialized,zeroState,writeNat,next,show r≠84 by omega,show r≠85 by omega]

/-- Compute an inverse from the original table, not from an assumed inverse
array. The destination may be dirty and disjoint on either side of the source. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (L a d B : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L a s.natHeap phi) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hcode:9≤B)
    (hpc:s.pc=0) (h81:s.natReg 81=L) (h82:s.natReg 82=a) (h83:s.natReg 83=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (7*L+4) u ∧
    PermutationBank L d u.natHeap phi.symm ∧
    PermutationBank L a u.natHeap phi ∧
    Outside d L s.natHeap u ∧ Frame s u ∧ u.pc=9 ∧ u.natReg 84=L := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 84 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 85 1 hz
    (by change s.pc+1+1≤B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=.next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hframe⟩:=loop n x L a d 0 L B phi s.natHeap (initialized s)
    (initialize_invariant L a d phi s h81 h82 h83) hTable (by omega) hd haB hdB hcode hp hi
  let v:State:={u with pc:=9}
  have hv:WordBound B v:=changePC_bound B u 9 hu.final_bound hcode
  have halt:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ halt
    simp [step,program,hpu,hiu.index,hiu.length,v]
  refine ⟨v,?_,?_,?_,hiu.outside,(initialize_frame s).trans hframe,rfl,hiu.index⟩
  · convert hb.executes (hu.executes he) using 1;omega
  · intro j
    simpa only [Equiv.apply_symm_apply] using hiu.written (phi.symm j) (phi.symm j).isLt
  · intro j
    exact (hiu.outside _ (disjoint_source a d L hd j)).trans (hTable j)

theorem runtime_bound (L : ℕ) : 7*L+4≤11*(L+1) := by omega

def wordBudget (L a d : ℕ) : ℕ := max (max (a+L) (d+L)) 89

theorem wordBudget_polynomial (L a d : ℕ) : wordBudget L a d≤89*(a+d+L+1) := by
  unfold wordBudget;omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (L a d : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L a s.natHeap phi) (hd:Disjoint a d L)
    (hpc:s.pc=0) (h81:s.natReg 81=L) (h82:s.natReg 82=a) (h83:s.natReg 83=d)
    (hs:WordBound (wordBudget L a d) s) : ∃u,
    BoundedExecution program n x (wordBudget L a d) s (7*L+4) u ∧
    PermutationBank L d u.natHeap phi.symm ∧ PermutationBank L a u.natHeap phi ∧
    Outside d L s.natHeap u ∧ Frame s u ∧ u.pc=9 ∧ u.natReg 84=L :=
  execution n x L a d _ phi s hTable hd (by unfold wordBudget;omega)
    (by unfold wordBudget;omega) (by unfold wordBudget;omega) hpc h81 h82 h83 hs

/-- A missing actual table entry fails at the literal load instruction. -/
theorem missing_load (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=4) (hm:s.natHeap (s.natReg 86)=none) : step program n x s=.failed := by
  simp [step,program,hpc,hm]

/-- In particular, the saved global headers100..106 are never written. -/
theorem Frame.saved_headers {s u : State} (h:Frame s u) (r : ℕ) (hr:100≤r) :
    u.natReg r=s.natReg r := h.2.2.2.2 r (Or.inr (by omega))

/-- The outside frame gives literal source-word preservation, independently
of its interpretation as a permutation table. -/
theorem Outside.source {a d L : ℕ} {heap : ℕ→Option ℕ} {u : State}
    (h:Outside d L heap u) (hd:Disjoint a d L) (j : Fin L) :
    u.natHeap (a+j.val)=heap (a+j.val) := h _ (disjoint_source a d L hd j)

/-- Any other disjoint permutation bank, for example the independent alpha
bank, survives production of the beta inverse. -/
theorem Outside.bank {L d K b : ℕ} {heap : ℕ→Option ℕ} {u : State} {phi : Fin K≃Fin K}
    (h:Outside d L heap u) (hd:b+K≤d ∨ d+L≤b) (hb:PermutationBank K b heap phi) :
    PermutationBank K b u.natHeap phi := by
  intro j
  exact (h _ (by omega)).trans (hb j)

/-- Produce the actual beta inverse from its generated, protected table.
The independently generated alpha table is never substituted for beta.symm. -/
theorem beta_execution (n : ℕ) (x : Fin n→ℂ) (d B : ℕ) (original s : State)
    (ht:UniformCRTTraversalCycle.Tables n (UniformCRTTraversalCycle.len n) original)
    (hp:UniformGlobalNatPreparation.Protected (UniformCRTTraversalCycle.ell n)
      (UniformCRTTraversalCycle.len n) original.natHeap s)
    (hd:Disjoint (UniformPermutationMachine.protectedBeta n) d (UniformCRTTraversalCycle.len n))
    (haB:UniformPermutationMachine.protectedBeta n+UniformCRTTraversalCycle.len n≤B)
    (hdB:d+UniformCRTTraversalCycle.len n≤B) (hcode:9≤B)
    (hpc:s.pc=0) (h81:s.natReg 81=UniformCRTTraversalCycle.len n)
    (h82:s.natReg 82=UniformPermutationMachine.protectedBeta n) (h83:s.natReg 83=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (7*UniformCRTTraversalCycle.len n+4) u ∧
    PermutationBank (UniformCRTTraversalCycle.len n) d u.natHeap
      (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    PermutationBank (UniformCRTTraversalCycle.len n) (UniformPermutationMachine.protectedBeta n)
      u.natHeap (UniformCRTTraversalCycle.betaPermutation n) ∧
    Outside d (UniformCRTTraversalCycle.len n) s.natHeap u ∧ Frame s u ∧ u.pc=9 ∧
    u.natReg 84=UniformCRTTraversalCycle.len n :=
  execution n x _ _ d B _ s (UniformPermutationMachine.protected_banks n original s ht hp).2
    hd haB hdB hcode hpc h81 h82 h83 hs

end
end ExactFourierCircuits.UniformPermutationInverseMachine
