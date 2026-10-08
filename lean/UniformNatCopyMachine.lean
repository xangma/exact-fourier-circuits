import UniformMachineRuns

set_option autoImplicit false
namespace ExactFourierCircuits.UniformNatCopyMachine
open UniformMachine

/-- Nat53=length, Nat54=source, Nat55=destination. The literal program only
writes Nat56..60. Each load, store, address operation, branch and halt is charged. -/
def program : Program := [
  .natLiteral 56 0,.natLiteral 57 1,.branchLT 56 53 3 9,
  .natBinary .add 58 54 56,.loadNat 59 58,.natBinary .add 60 55 56,
  .storeNat 60 59,.natBinary .add 56 56 57,.jump 2,.halt]

theorem program_length : program.length=10 := rfl

noncomputable section

def Source (m a : ℕ) (heap : ℕ→Option ℕ) : Prop :=
  ∀j,j < m→∃v,heap (a+j)=some v

def Outside (d m : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop :=
  ∀i,(i < d ∨ d+m ≤ i)→s.natHeap i=heap i

structure Invariant (m a d k : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop where
  length : s.natReg 53=m
  source : s.natReg 54=a
  destination : s.natReg 55=d
  index : s.natReg 56=k
  one : s.natReg 57=1
  copied : ∀j,j < k→s.natHeap (d+j)=heap (a+j)
  outside : Outside d m heap s

/-- Even scalar registers are preserved; no scalar instruction occurs. -/
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.trans h.2.2.2⟩

theorem Invariant.withPC {m a d k pc : ℕ} {heap : ℕ→Option ℕ} {s : State}
    (h:Invariant m a d k heap s) : Invariant m a d k heap {s with pc:=pc} := by
  cases h;constructor <;> assumption

def sourceAddress (s : State) : State :=
  writeNat {s with pc:=3} 58 (s.natReg 54+s.natReg 56)
def loaded (s : State) (v : ℕ) : State := writeNat (sourceAddress s) 59 v
def destinationAddress (s : State) (v : ℕ) : State :=
  writeNat (loaded s v) 60 (s.natReg 55+s.natReg 56)
def stored (s : State) (v : ℕ) : State :=
  {next (destinationAddress s v) with natHeap:=(Function.update s.natHeap
    (s.natReg 55+s.natReg 56) (some v))}
def advanced (s : State) (v : ℕ) : State := writeNat (stored s v) 56 (s.natReg 56+1)
def iterationEnd (s : State) (v : ℕ) : State := {advanced s v with pc:=2}

theorem store_bound (B : ℕ) (s : State) (address value : ℕ) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (ha:address ≤ B) (hv:value ≤ B) :
    WordBound B {next s with natHeap:=Function.update s.natHeap address (some value)} := by
  refine ⟨hp,hs.2.1,?_,hs.2.2.2⟩
  intro j v hj
  by_cases he:j=address
  · subst j;simp at hj
    subst v;exact ⟨ha,hv⟩
  · exact hs.2.2.1 j v (by simpa [he] using hj)

theorem iteration_heap (s : State) (v : ℕ) :
    (iterationEnd s v).natHeap=Function.update s.natHeap
      (s.natReg 55+s.natReg 56) (some v) := rfl

theorem iteration_frame (s : State) (v : ℕ) : Frame s (iterationEnd s v) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem iteration_invariant (m a d k : ℕ) (heap : ℕ→Option ℕ) (s : State) (v : ℕ)
    (hi:Invariant m a d k heap s) (hk:k < m) (hv:heap (a+k)=some v) :
    Invariant m a d (k+1) heap (iterationEnd s v) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next] using hi.destination
  · simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next] using hi.one
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index]
    by_cases he:j=k
    · subst j;simp [hv]
    · rw [Function.update_of_ne (by omega)]
      exact hi.copied j (by omega)
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index,Function.update_of_ne (by omega)]
    exact hi.outside j hj

def NatFrame (s u : State) : Prop := ∀i,(i < 53 ∨ 61 ≤ i)→u.natReg i=s.natReg i

theorem NatFrame.trans {s u v : State} (h:NatFrame s u) (h':NatFrame u v) : NatFrame s v :=
  fun i hi=>(h' i hi).trans (h i hi)

theorem iteration_nat (s : State) (v : ℕ) : NatFrame s (iterationEnd s v) := by
  intro i hi
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,next,
    show i≠56 by omega,show i≠58 by omega,show i≠59 by omega,show i≠60 by omega]


/-- Seven real instructions copy one present source word and advance the loop. -/
theorem iteration (n : ℕ) (x : Fin n→ℂ) (m a d k B : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k < m) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 7 u ∧ Invariant m a d (k+1) heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  obtain ⟨v,hv⟩:=hsrc k hk
  have hload:s.natHeap (a+k)=some v:=(hi.outside (a+k) (Or.inl (by omega))).trans hv
  have hvB:v ≤ B:=(hs.2.2.1 (a+k) v hload).2
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have h1:WordBound B (sourceAddress s):=writeNat_bound B {s with pc:=3} 58 _ he
    (by change 3+1 ≤ B;omega) (by rw [hi.source,hi.index];omega)
  have h2:WordBound B (loaded s v):=writeNat_bound B (sourceAddress s) 59 v h1
    (by change 4+1 ≤ B;omega) hvB
  have h3:WordBound B (destinationAddress s v):=writeNat_bound B (loaded s v) 60 _ h2
    (by change 5+1 ≤ B;omega) (by rw [hi.destination,hi.index];omega)
  have h4:WordBound B (stored s v):=store_bound B (destinationAddress s v) (s.natReg 55+s.natReg 56) v h3
    (by change 6+1 ≤ B;omega) (by rw [hi.destination,hi.index];omega) hvB
  have h5:WordBound B (advanced s v):=writeNat_bound B (stored s v) 56 _ h4
    (by change 7+1 ≤ B;omega) (by rw [hi.index];omega)
  have h6:WordBound B (iterationEnd s v):=changePC_bound B _ 2 h5 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=3}=.running (sourceAddress s):=by
    simp [step,program,sourceAddress,evalNat]
  have t2:step program n x (sourceAddress s)=.running (loaded s v):=by
    simp [step,program,loaded,sourceAddress,writeNat,next,hi.source,hi.index,hload]
  have t3:step program n x (loaded s v)=.running (destinationAddress s v):=by
    simp [step,program,destinationAddress,loaded,sourceAddress,writeNat,next,evalNat]
  have t4:step program n x (destinationAddress s v)=.running (stored s v):=by
    simp [step,program,stored,destinationAddress,loaded,sourceAddress,writeNat,next]
  have t5:step program n x (stored s v)=.running (advanced s v):=by
    simp [step,program,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next,hi.one,evalNat]
  have t6:step program n x (advanced s v)=.running (iterationEnd s v):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,next]
  exact ⟨iterationEnd s v,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.refl h6))))))),
    iteration_invariant m a d k heap s v hi hk hv,rfl,iteration_frame s v,iteration_nat s v⟩


/-- All loop iterations execute the literal program. A source value is never
selected by an uncharged copying primitive. -/
theorem loop (n : ℕ) (x : Fin n→ℂ) (m a d k fuel B : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k+fuel=m) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (7*fuel) u ∧ Invariant m a d m heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,rfl⟩,fun i _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=iteration n x m a d k B heap s hi hsrc (by omega)
      hd hB hcode hpc hs
    obtain ⟨w,hw,hiw,hpw,hfw,hnw⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hiw,hpw,hfu.trans hfw,hnu.trans hnw⟩
    convert hu.trans hw using 1;omega


def zeroState (s : State) : State := writeNat s 56 0
def initialized (s : State) : State := writeNat (zeroState s) 57 1

theorem initialize_invariant (m a d : ℕ) (s : State) (h53:s.natReg 53=m)
    (h54:s.natReg 54=a) (h55:s.natReg 55=d) :
    Invariant m a d 0 s.natHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h53,h54,h55,Outside]

theorem initialize_frame (s : State) : Frame s (initialized s) := ⟨rfl,rfl,rfl,rfl⟩
theorem initialize_nat (s : State) : NatFrame s (initialized s) := by
  intro i hi
  simp [initialized,zeroState,writeNat,next,show i≠56 by omega,show i≠57 by omega]

/-- Complete fixed RAM copy with the original source as its specification.
Every source word is explicitly present. The destination can be dirty. The word
budget is identical at every step, and no scalar/root/output instruction is used. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (m a d B : ℕ) (s : State)
    (hsrc:Source m a s.natHeap) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=0) (h53:s.natReg 53=m) (h54:s.natReg 54=a) (h55:s.natReg 55=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (7*m+4) u ∧
    (∀j,j < m→u.natHeap (d+j)=s.natHeap (a+j)) ∧
    (∀j,j < m→u.natHeap (a+j)=s.natHeap (a+j)) ∧
    Outside d m s.natHeap u ∧ Frame s u ∧ NatFrame s u := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 56 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 57 1 hz
    (by change s.pc+1+1 ≤ B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=
    .next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=loop n x m a d 0 m B s.natHeap (initialized s)
    (initialize_invariant m a d s h53 h54 h55) hsrc (by omega) hd hB hcode hp hi
  let v:State:={u with pc:=9}
  have hv:WordBound B v:=changePC_bound B u 9 hu.final_bound hcode
  have halt:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ halt
    simp [step,program,hpu,hiu.index,hiu.length,v]
  refine ⟨v,?_,hiu.copied,?_,hiu.outside,(initialize_frame s).trans hfu,
    (initialize_nat s).trans hnu⟩
  · convert hb.executes (hu.executes he) using 1;omega
  · intro j hj
    exact hiu.outside (a+j) (Or.inl (by omega))

theorem runtime_bound (m : ℕ) : 7*m+4 ≤ 11*(m+1) := by omega

/-- Optional explicit address bound; unrelated initial banks must fit it too.
The execution theorem also accepts any larger ambient WordBound unchanged. -/
def wordBudget (d m : ℕ) : ℕ := max (d+m) 61

theorem wordBudget_polynomial (d m : ℕ) : wordBudget d m ≤ 61*(d+m+1) := by
  unfold wordBudget
  omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (m a d : ℕ) (s : State)
    (hsrc:Source m a s.natHeap) (hd:a+m ≤ d)
    (hpc:s.pc=0) (h53:s.natReg 53=m) (h54:s.natReg 54=a) (h55:s.natReg 55=d)
    (hs:WordBound (wordBudget d m) s) : ∃u,
    BoundedExecution program n x (wordBudget d m) s (7*m+4) u ∧
    (∀j,j < m→u.natHeap (d+j)=s.natHeap (a+j)) ∧
    (∀j,j < m→u.natHeap (a+j)=s.natHeap (a+j)) ∧
    Outside d m s.natHeap u ∧ Frame s u ∧ NatFrame s u :=
  execution n x m a d _ s hsrc hd (le_max_left _ _) (by unfold wordBudget;omega)
    hpc h53 h54 h55 hs

def isScalar : UniformMachine.Instruction→Bool
  | .scalarLiteral _ _ | .fieldBinary _ _ _ _ | .input _ _ | .root _ _ |
    .loadScalar _ _ | .storeScalar _ _ | .output _ _=>true
  | _=>false

theorem no_scalar_input_root_output : program.any isScalar=false := rfl

end
end ExactFourierCircuits.UniformNatCopyMachine
