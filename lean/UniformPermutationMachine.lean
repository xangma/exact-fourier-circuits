import UniformCRTTraversalCycle
import UniformGlobalNatPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPermutationMachine
open UniformMachine UniformAssembly
open UniformGlobalNatPreparation (PermutationBank)
open scoped BigOperators

/-- Nat70=length,71=scalar source,72=scalar destination,73=Nat permutation bank.
The loop writes Nat74..80 and Scalar20; each real load/store/address operation
and control instruction is charged. -/
def program : Program := [
  .natLiteral 74 0,.natLiteral 75 1,.branchLT 74 70 3 11,
  .natBinary .add 77 73 74,.loadNat 78 77,
  .natBinary .add 79 71 78,.loadScalar 20 79,
  .natBinary .add 80 72 74,.storeScalar 80 20,
  .natBinary .add 74 74 75,.jump 2,.halt]

theorem program_length : program.length=12 := rfl

noncomputable section

def Source (L a : ℕ) (heap : ℕ→Option Scalar) : Prop :=
  ∀j:Fin L,∃v,heap (a+j.val)=some v

def Disjoint (a d L : ℕ) : Prop := a+L≤d ∨ d+L≤a

def Outside (d L : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop :=
  ∀j,(j<d ∨ d+L≤j) → s.scalarHeap j=heap j

/-- Original metadata, saved high headers, outputs and root requests are retained. -/
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,r≠20 → u.scalarReg r=s.scalarReg r) ∧
  ∀r,(r<74 ∨ 80<r) → u.natReg r=s.natReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

structure Invariant (L a d b k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) : Prop where
  length : s.natReg 70=L
  source : s.natReg 71=a
  destination : s.natReg 72=d
  permutation : s.natReg 73=b
  index : s.natReg 74=k
  one : s.natReg 75=1
  table : PermutationBank L b s.natHeap phi
  copied : ∀j:Fin L,j.val<k → s.scalarHeap (d+j.val)=heap (a+(phi j).val)
  outside : Outside d L heap s

/-- The following names expand only actual individual machine instructions. -/
def tableAddress (s : State) : State :=
  writeNat {s with pc:=3} 77 (s.natReg 73+s.natReg 74)
def tableLoaded (s : State) (digit : ℕ) : State := writeNat (tableAddress s) 78 digit
def sourceAddress (s : State) (digit : ℕ) : State :=
  writeNat (tableLoaded s digit) 79 (s.natReg 71+digit)
def scalarLoaded (s : State) (digit : ℕ) (v : Scalar) : State := writeScalar (sourceAddress s digit) 20 v
def destinationAddress (s : State) (digit : ℕ) (v : Scalar) : State :=
  writeNat (scalarLoaded s digit v) 80 (s.natReg 72+s.natReg 74)
def stored (s : State) (digit : ℕ) (v : Scalar) : State :=
  {next (destinationAddress s digit v) with scalarHeap:=(Function.update s.scalarHeap
    (s.natReg 72+s.natReg 74) (some v))}
def advanced (s : State) (digit : ℕ) (v : Scalar) : State :=
  writeNat (stored s digit v) 74 (s.natReg 74+1)
def iterationEnd (s : State) (digit : ℕ) (v : Scalar) : State := {advanced s digit v with pc:=2}

theorem store_bound (B : ℕ) (s : State) (address : ℕ) (v : Scalar) (hs:WordBound B s)
    (hp:s.pc+1≤B) (ha:address≤B) :
    WordBound B {next s with scalarHeap:=Function.update s.scalarHeap address (some v)} := by
  refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro j v hj
  by_cases he:j=address
  · subst j;exact ha
  · exact hs.2.2.2.1 j v (by simpa [he] using hj)

theorem iteration_heap (s : State) (digit : ℕ) (v : Scalar) :
    (iterationEnd s digit v).scalarHeap=Function.update s.scalarHeap
      (s.natReg 72+s.natReg 74) (some v) := rfl

theorem iteration_frame (s : State) (digit : ℕ) (v : Scalar) : Frame s (iterationEnd s digit v) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hr]
  · intro r hr
    simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,show r≠74 by omega,show r≠77 by omega,
      show r≠78 by omega,show r≠79 by omega,show r≠80 by omega]

theorem disjoint_source (a d L : ℕ) (hd:Disjoint a d L) (j : Fin L) :
    a+j.val<d ∨ d+L≤a+j.val := by unfold Disjoint at hd;omega

theorem iteration_invariant (L a d b k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (v : Scalar)
    (hi:Invariant L a d b k phi heap s) (hk:k<L)
    (hv:heap (a+(phi ⟨k,hk⟩).val)=some v) :
    Invariant L a d b (k+1) phi heap (iterationEnd s (phi ⟨k,hk⟩).val v) := by
  constructor
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.destination
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.permutation
  · simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.one
  · exact hi.table
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index]
    by_cases he:j.val=k
    · have he':j=⟨k,hk⟩:=Fin.ext he
      subst j
      simp [hv]
    · rw [Function.update_of_ne (by omega)]
      exact hi.copied j (by omega)
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index,Function.update_of_ne (by omega)]
    exact hi.outside j hj

/-- One real nine-instruction iteration, including the branch and both loads. -/
theorem iteration (n : ℕ) (x : Fin n→ℂ) (L a d b k B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant L a d b k phi heap s)
    (hsrc:Source L a heap) (hk:k<L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 9 u ∧ Invariant L a d b (k+1) phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  let j:Fin L:=⟨k,hk⟩
  let digit:ℕ:=(phi j).val
  obtain ⟨v,hv⟩:=hsrc (phi j)
  have hload:s.scalarHeap (a+digit)=some v:=
    (hi.outside _ (disjoint_source a d L hd (phi j))).trans hv
  have hdigit:digit<L:=(phi j).isLt
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have h1:WordBound B (tableAddress s):=writeNat_bound B {s with pc:=3} 77 _ he
    (by change 3+1≤B;omega) (by rw [hi.permutation,hi.index];omega)
  have h2:WordBound B (tableLoaded s digit):=writeNat_bound B (tableAddress s) 78 digit h1
    (by change 4+1≤B;omega) (by omega)
  have h3:WordBound B (sourceAddress s digit):=writeNat_bound B (tableLoaded s digit) 79 _ h2
    (by change 5+1≤B;omega) (by rw [hi.source];omega)
  have h4:WordBound B (scalarLoaded s digit v):=writeScalar_bound B (sourceAddress s digit) 20 v h3
    (by change 6+1≤B;omega)
  have h5:WordBound B (destinationAddress s digit v):=writeNat_bound B (scalarLoaded s digit v) 80 _ h4
    (by change 7+1≤B;omega) (by rw [hi.destination,hi.index];omega)
  have h6:WordBound B (stored s digit v):=store_bound B (destinationAddress s digit v) (s.natReg 72+s.natReg 74) v h5
    (by change 8+1≤B;omega) (by rw [hi.destination,hi.index];omega)
  have h7:WordBound B (advanced s digit v):=writeNat_bound B (stored s digit v) 74 _ h6
    (by change 9+1≤B;omega) (by rw [hi.index];omega)
  have h8:WordBound B (iterationEnd s digit v):=changePC_bound B _ 2 h7 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=3}=.running (tableAddress s):=by
    simp [step,program,tableAddress,evalNat]
  have t2:step program n x (tableAddress s)=.running (tableLoaded s digit):=by
    simp [step,program,tableLoaded,tableAddress,writeNat,next,hi.permutation,hi.index,hi.table j,digit,j]
  have t3:step program n x (tableLoaded s digit)=.running (sourceAddress s digit):=by
    simp [step,program,sourceAddress,tableLoaded,tableAddress,writeNat,next,evalNat]
  have t4:step program n x (sourceAddress s digit)=.running (scalarLoaded s digit v):=by
    simp [step,program,scalarLoaded,sourceAddress,tableLoaded,tableAddress,writeNat,next,hi.source,hload]
  have t5:step program n x (scalarLoaded s digit v)=.running (destinationAddress s digit v):=by
    simp [step,program,destinationAddress,scalarLoaded,sourceAddress,tableLoaded,tableAddress,
      writeNat,writeScalar,next,evalNat]
  have t6:step program n x (destinationAddress s digit v)=.running (stored s digit v):=by
    simp [step,program,stored,destinationAddress,scalarLoaded,sourceAddress,tableLoaded,
      tableAddress,writeNat,writeScalar,next]
  have t7:step program n x (stored s digit v)=.running (advanced s digit v):=by
    simp [step,program,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hi.one,evalNat]
  have t8:step program n x (advanced s digit v)=.running (iterationEnd s digit v):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next]
  exact ⟨iterationEnd s digit v,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.next h6 t7 (.next h7 t8 (.refl h8))))))))),
    iteration_invariant L a d b k phi heap s v hi hk hv,rfl,iteration_frame s digit v⟩


/-- The entire loop runs actual instructions, including the final failed test. -/
theorem loop (n : ℕ) (x : Fin n→ℂ) (L a d b k fuel B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant L a d b k phi heap s)
    (hsrc:Source L a heap) (hk:k+fuel=L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (9*fuel) u ∧ Invariant L a d b L phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  induction fuel generalizing k s with
  | zero =>
    have he:k=L:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hframe⟩:=iteration n x L a d b k B phi heap s hi hsrc (by omega)
      hd haB hdB hbB hcode hpc hs
    obtain ⟨v,hv,hiv,hpv,hfr⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨v,?_,hiv,hpv,hframe.trans hfr⟩
    convert hu.trans hv using 1;omega

def zeroState (s : State) : State := writeNat s 74 0
def initialized (s : State) : State := writeNat (zeroState s) 75 1

theorem initialize_invariant (L a d b : ℕ) (phi : Fin L≃Fin L) (s : State)
    (h70:s.natReg 70=L) (h71:s.natReg 71=a) (h72:s.natReg 72=d) (h73:s.natReg 73=b)
    (hTable:PermutationBank L b s.natHeap phi) : Invariant L a d b 0 phi s.scalarHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h70,h71,h72,h73,Outside,hTable]

theorem initialize_frame (s : State) : Frame s (initialized s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr
  simp [initialized,zeroState,writeNat,next,show r≠74 by omega,show r≠75 by omega]

/-- Gather into a disjoint possibly dirty destination using the actually read
Nat permutation table. No action or runtime certificate is assumed. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (L a d b B : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L b s.natHeap phi) (hsrc:Source L a s.scalarHeap) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=0) (h70:s.natReg 70=L) (h71:s.natReg 71=a) (h72:s.natReg 72=d) (h73:s.natReg 73=b)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*L+4) u ∧
    (∀j:Fin L,u.scalarHeap (d+j.val)=s.scalarHeap (a+(phi j).val)) ∧
    (∀j:Fin L,u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d L s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧ u.natReg 74=L := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 74 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 75 1 hz
    (by change s.pc+1+1≤B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=.next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hframe⟩:=loop n x L a d b 0 L B phi s.scalarHeap (initialized s)
    (initialize_invariant L a d b phi s h70 h71 h72 h73 hTable) hsrc (by omega)
    hd haB hdB hbB hcode hp hi
  let v:State:={u with pc:=11}
  have hv:WordBound B v:=changePC_bound B u 11 hu.final_bound hcode
  have hh:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ hh
    simp [step,program,hpu,hiu.index,hiu.length,v]
  refine ⟨v,?_,fun j=>hiu.copied j j.isLt,?_,hiu.outside,(initialize_frame s).trans hframe,rfl,hiu.index⟩
  · convert hb.executes (hu.executes he) using 1;omega
  · intro j
    exact hiu.outside _ (disjoint_source a d L hd j)

theorem runtime_bound (L : ℕ) : 9*L+4≤13*(L+1) := by omega

/-- One unchanged word bound includes every table/scalar address and private
instruction value. All other initialized banks must fit the same ambient bound. -/
def wordBudget (L a d b : ℕ) : ℕ := max (max (a+L) (d+L)) (max (b+L) 81)

theorem wordBudget_polynomial (L a d b : ℕ) : wordBudget L a d b≤81*(a+d+b+L+1) := by
  unfold wordBudget;omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (L a d b : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L b s.natHeap phi) (hsrc:Source L a s.scalarHeap) (hd:Disjoint a d L)
    (hpc:s.pc=0) (h70:s.natReg 70=L) (h71:s.natReg 71=a) (h72:s.natReg 72=d) (h73:s.natReg 73=b)
    (hs:WordBound (wordBudget L a d b) s) : ∃u,
    BoundedExecution program n x (wordBudget L a d b) s (9*L+4) u ∧
    (∀j:Fin L,u.scalarHeap (d+j.val)=s.scalarHeap (a+(phi j).val)) ∧
    (∀j:Fin L,u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d L s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧ u.natReg 74=L :=
  execution n x L a d b _ phi s hTable hsrc hd (by unfold wordBudget;omega)
    (by unfold wordBudget;omega) (by unfold wordBudget;omega) (by unfold wordBudget;omega)
    hpc h70 h71 h72 h73 hs

/-- An inverse COORDINATE identity for this same gather; it does not assume an
inverse table or identify two independently produced CRT permutations. -/
theorem inverse_coordinates {L a d : ℕ} (phi : Fin L≃Fin L) (s u : State)
    (h:∀j:Fin L,u.scalarHeap (d+j.val)=s.scalarHeap (a+(phi j).val)) (j : Fin L) :
    u.scalarHeap (d+(phi.symm j).val)=s.scalarHeap (a+j.val) := by
  simpa only [Equiv.apply_symm_apply] using h (phi.symm j)

/-- Prepared and data-dependent source scalars retain their actual flags. -/
theorem gathered_values {L a d : ℕ} (phi : Fin L≃Fin L) (s u : State) (v : Fin L→Scalar)
    (hsource:∀j,s.scalarHeap (a+j.val)=some (v j))
    (h:∀j:Fin L,u.scalarHeap (d+j.val)=s.scalarHeap (a+(phi j).val)) (j : Fin L) :
    u.scalarHeap (d+j.val)=some (v (phi j)) := (h j).trans (hsource (phi j))


/-- Both actual banks, independently: no relation alpha.symm=beta is assumed. -/
theorem traversal_banks (n : ℕ) (s : State)
    (ht:UniformCRTTraversalCycle.Tables n (UniformCRTTraversalCycle.len n) s) :
    PermutationBank (UniformCRTTraversalCycle.len n)
      (UniformCRTTraversalMachine.alphaBase (UniformCRTTraversalCycle.ell n)) s.natHeap
      (UniformCRTTraversalCycle.alphaPermutation n) ∧
    PermutationBank (UniformCRTTraversalCycle.len n)
      (UniformCRTTraversalMachine.betaBase (UniformCRTTraversalCycle.ell n) (UniformCRTTraversalCycle.len n)) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n) :=
  ⟨fun j=>(UniformCRTTraversalCycle.tables_permutations n s ht j).1,
    fun j=>(UniformCRTTraversalCycle.tables_permutations n s ht j).2⟩

def protectedAlpha (n : ℕ) : ℕ :=
  UniformGlobalNatPreparation.destination (UniformCRTTraversalCycle.ell n) (UniformCRTTraversalCycle.len n)+
    UniformCRTTraversalMachine.alphaBase (UniformCRTTraversalCycle.ell n)
def protectedBeta (n : ℕ) : ℕ :=
  UniformGlobalNatPreparation.destination (UniformCRTTraversalCycle.ell n) (UniformCRTTraversalCycle.len n)+
    UniformCRTTraversalMachine.betaBase (UniformCRTTraversalCycle.ell n) (UniformCRTTraversalCycle.len n)

/-- Instantiate only the single-bank protected_permutation transfer for each
actual CRT bank; the optional phi/phi.symm certificate is not used. -/
theorem protected_banks (n : ℕ) (original s : State)
    (ht:UniformCRTTraversalCycle.Tables n (UniformCRTTraversalCycle.len n) original)
    (hp:UniformGlobalNatPreparation.Protected (UniformCRTTraversalCycle.ell n)
      (UniformCRTTraversalCycle.len n) original.natHeap s) :
    PermutationBank (UniformCRTTraversalCycle.len n) (protectedAlpha n) s.natHeap
      (UniformCRTTraversalCycle.alphaPermutation n) ∧
    PermutationBank (UniformCRTTraversalCycle.len n) (protectedBeta n) s.natHeap
      (UniformCRTTraversalCycle.betaPermutation n) := by
  obtain ⟨hA,hD⟩:=traversal_banks n original ht
  constructor
  · exact UniformGlobalNatPreparation.protected_permutation _ _ _ _ _ s _ hp
      (UniformGlobalNatPreparation.traversal_alpha_fits _ _) hA
  · exact UniformGlobalNatPreparation.protected_permutation _ _ _ _ _ s _ hp
      (by rw [UniformGlobalNatPreparation.amount_eq_traversal_end]) hD

/-- Literal input-coordinate gather through the actual protected alpha bank. -/
theorem alpha_execution (n : ℕ) (x : Fin n→ℂ) (a d B : ℕ) (original s : State)
    (ht:UniformCRTTraversalCycle.Tables n (UniformCRTTraversalCycle.len n) original)
    (hp:UniformGlobalNatPreparation.Protected (UniformCRTTraversalCycle.ell n)
      (UniformCRTTraversalCycle.len n) original.natHeap s)
    (hsrc:Source (UniformCRTTraversalCycle.len n) a s.scalarHeap)
    (hd:Disjoint a d (UniformCRTTraversalCycle.len n))
    (haB:a+UniformCRTTraversalCycle.len n≤B) (hdB:d+UniformCRTTraversalCycle.len n≤B)
    (hbB:protectedAlpha n+UniformCRTTraversalCycle.len n≤B) (hcode:11≤B)
    (hpc:s.pc=0) (h70:s.natReg 70=UniformCRTTraversalCycle.len n)
    (h71:s.natReg 71=a) (h72:s.natReg 72=d) (h73:s.natReg 73=protectedAlpha n)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*UniformCRTTraversalCycle.len n+4) u ∧
    (∀j:Fin (UniformCRTTraversalCycle.len n),u.scalarHeap (d+j.val)=
      s.scalarHeap (a+(UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    (∀j:Fin (UniformCRTTraversalCycle.len n),u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d (UniformCRTTraversalCycle.len n) s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧
    u.natReg 74=UniformCRTTraversalCycle.len n :=
  execution n x _ a d _ B _ s (protected_banks n original s ht hp).1 hsrc hd haB hdB hbB
    hcode hpc h70 h71 h72 h73 hs

/-- Independent output-coordinate gather through the actual protected beta
bank. Its inverse-coordinate identity is beta.symm, not alpha. -/
theorem beta_execution (n : ℕ) (x : Fin n→ℂ) (a d B : ℕ) (original s : State)
    (ht:UniformCRTTraversalCycle.Tables n (UniformCRTTraversalCycle.len n) original)
    (hp:UniformGlobalNatPreparation.Protected (UniformCRTTraversalCycle.ell n)
      (UniformCRTTraversalCycle.len n) original.natHeap s)
    (hsrc:Source (UniformCRTTraversalCycle.len n) a s.scalarHeap)
    (hd:Disjoint a d (UniformCRTTraversalCycle.len n))
    (haB:a+UniformCRTTraversalCycle.len n≤B) (hdB:d+UniformCRTTraversalCycle.len n≤B)
    (hbB:protectedBeta n+UniformCRTTraversalCycle.len n≤B) (hcode:11≤B)
    (hpc:s.pc=0) (h70:s.natReg 70=UniformCRTTraversalCycle.len n)
    (h71:s.natReg 71=a) (h72:s.natReg 72=d) (h73:s.natReg 73=protectedBeta n)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*UniformCRTTraversalCycle.len n+4) u ∧
    (∀j:Fin (UniformCRTTraversalCycle.len n),u.scalarHeap (d+j.val)=
      s.scalarHeap (a+(UniformCRTTraversalCycle.betaPermutation n j).val)) ∧
    (∀j:Fin (UniformCRTTraversalCycle.len n),u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d (UniformCRTTraversalCycle.len n) s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧
    u.natReg 74=UniformCRTTraversalCycle.len n :=
  execution n x _ a d _ B _ s (protected_banks n original s ht hp).2 hsrc hd haB hdB hbB
    hcode hpc h70 h71 h72 h73 hs

/-- The read-only Nat tables, including both independent CRT banks, survive
any completed gather and can be reused for later stages. -/
theorem Frame.permutation {L b : ℕ} {phi : Fin L≃Fin L} {s u : State}
    (hf:Frame s u) (hp:PermutationBank L b s.natHeap phi) : PermutationBank L b u.natHeap phi := by
  rw [hf.1];exact hp

/-- Actual generated table values give the precise standard-root tensor phase.
The Fourier symmetry presents beta as output row and alpha as input column. -/
theorem crt_output_input_phase (n : ℕ) (j k : Fin (UniformCRTTraversalCycle.len n)) :
    OAI.ExactFourier.fourierMatrix (UniformCRTTraversalCycle.len n)
      (UniformCRTTraversalCycle.betaPermutation n k) (UniformCRTTraversalCycle.alphaPermutation n j)=
    ∏i,OAI.ExactFourier.zeta (UniformCRTTraversalCycle.radices n i)^
      ((UniformCRTTraversalCycle.ordinalEquiv n j i).val*(UniformCRTTraversalCycle.ordinalEquiv n k i).val) := by
  change OAI.ExactFourier.zeta _^
    ((UniformCRTTraversalCycle.betaPermutation n k).val*(UniformCRTTraversalCycle.alphaPermutation n j).val)=_
  rw [Nat.mul_comm]
  exact UniformCRTTraversalCycle.permutation_fourier_entry n j k

end
end ExactFourierCircuits.UniformPermutationMachine
