import UniformMachineRuns

set_option autoImplicit false
namespace ExactFourierCircuits.UniformScalarCopyMachine
open UniformMachine

/-- Nat147=length, Nat148=source, Nat149=destination. The literal program only
writes Nat150..153 and Scalar32. Each load, store, address operation, branch and halt is charged. -/
def program : Program := [
  .natLiteral 150 0,.natLiteral 151 1,.branchLT 150 147 3 9,
  .natBinary .add 152 148 150,.loadScalar 32 152,.natBinary .add 153 149 150,
  .storeScalar 153 32,.natBinary .add 150 150 151,.jump 2,.halt]

theorem program_length : program.length=10 := rfl

noncomputable section

def Source (m a : ℕ) (heap : ℕ→Option Scalar) : Prop :=
  ∀j,j < m→∃v,heap (a+j)=some v

def Outside (d m : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop :=
  ∀i,(i < d ∨ d+m ≤ i)→s.scalarHeap i=heap i

structure Invariant (m a d k : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop where
  length : s.natReg 147=m
  source : s.natReg 148=a
  destination : s.natReg 149=d
  index : s.natReg 150=k
  one : s.natReg 151=1
  copied : ∀j,j < k→s.scalarHeap (d+j)=heap (a+j)
  outside : Outside d m heap s

/-- Metadata, outputs, root requests and all other scalar registers are retained. -/
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ ∀r,r≠32 → u.scalarReg r=s.scalarReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2 r hr).trans (h.2.2.2 r hr)⟩

theorem Invariant.withPC {m a d k pc : ℕ} {heap : ℕ→Option Scalar} {s : State}
    (h:Invariant m a d k heap s) : Invariant m a d k heap {s with pc:=pc} := by
  cases h;constructor <;> assumption

def sourceAddress (s : State) : State :=
  writeNat {s with pc:=3} 152 (s.natReg 148+s.natReg 150)
def loaded (s : State) (v : Scalar) : State := writeScalar (sourceAddress s) 32 v
def destinationAddress (s : State) (v : Scalar) : State :=
  writeNat (loaded s v) 153 (s.natReg 149+s.natReg 150)
def stored (s : State) (v : Scalar) : State :=
  {next (destinationAddress s v) with scalarHeap:=(Function.update s.scalarHeap
    (s.natReg 149+s.natReg 150) (some v))}
def advanced (s : State) (v : Scalar) : State := writeNat (stored s v) 150 (s.natReg 150+1)
def iterationEnd (s : State) (v : Scalar) : State := {advanced s v with pc:=2}

theorem store_bound (B : ℕ) (s : State) (address : ℕ) (value : Scalar) (hs:WordBound B s)
    (hp:s.pc+1≤B) (ha:address≤B) :
    WordBound B {next s with scalarHeap:=Function.update s.scalarHeap address (some value)} := by
  refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro j v hj
  by_cases he:j=address
  · subst j;exact ha
  · exact hs.2.2.2.1 j v (by simpa [he] using hj)

theorem iteration_heap (s : State) (v : Scalar) :
    (iterationEnd s v).scalarHeap=Function.update s.scalarHeap
      (s.natReg 149+s.natReg 150) (some v) := rfl

theorem iteration_frame (s : State) (v : Scalar) : Frame s (iterationEnd s v) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro r hr
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,writeScalar,next,hr]

theorem iteration_invariant (m a d k : ℕ) (heap : ℕ→Option Scalar) (s : State) (v : Scalar)
    (hi:Invariant m a d k heap s) (hk:k < m) (hv:heap (a+k)=some v) :
    Invariant m a d (k+1) heap (iterationEnd s v) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next] using hi.destination
  · simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next] using hi.one
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index]
    by_cases he:j=k
    · subst j;simp [hv]
    · rw [Function.update_of_ne (by omega)]
      exact hi.copied j (by omega)
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index,Function.update_of_ne (by omega)]
    exact hi.outside j hj

def NatFrame (s u : State) : Prop := ∀i,(i < 147 ∨ 154 ≤ i)→u.natReg i=s.natReg i

theorem NatFrame.trans {s u v : State} (h:NatFrame s u) (h':NatFrame u v) : NatFrame s v :=
  fun i hi=>(h' i hi).trans (h i hi)

theorem iteration_nat (s : State) (v : Scalar) : NatFrame s (iterationEnd s v) := by
  intro i hi
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,writeNat,writeScalar,next,
    show i≠150 by omega,show i≠152 by omega,show i≠153 by omega]


/-- Seven real instructions copy one present source scalar and advance the loop. -/
theorem iteration (n : ℕ) (x : Fin n→ℂ) (m a d k B : ℕ) (heap : ℕ→Option Scalar)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k < m) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 7 u ∧ Invariant m a d (k+1) heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  obtain ⟨v,hv⟩:=hsrc k hk
  have hload:s.scalarHeap (a+k)=some v:=(hi.outside (a+k) (Or.inl (by omega))).trans hv
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have h1:WordBound B (sourceAddress s):=writeNat_bound B {s with pc:=3} 152 _ he
    (by change 3+1 ≤ B;omega) (by rw [hi.source,hi.index];omega)
  have h2:WordBound B (loaded s v):=writeScalar_bound B (sourceAddress s) 32 v h1
    (by change 4+1 ≤ B;omega)
  have h3:WordBound B (destinationAddress s v):=writeNat_bound B (loaded s v) 153 _ h2
    (by change 5+1 ≤ B;omega) (by rw [hi.destination,hi.index];omega)
  have h4:WordBound B (stored s v):=store_bound B (destinationAddress s v) (s.natReg 149+s.natReg 150) v h3
    (by change 6+1 ≤ B;omega) (by rw [hi.destination,hi.index];omega)
  have h5:WordBound B (advanced s v):=writeNat_bound B (stored s v) 150 _ h4
    (by change 7+1 ≤ B;omega) (by rw [hi.index];omega)
  have h6:WordBound B (iterationEnd s v):=changePC_bound B _ 2 h5 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=3}=.running (sourceAddress s):=by
    simp [step,program,sourceAddress,evalNat]
  have t2:step program n x (sourceAddress s)=.running (loaded s v):=by
    simp [step,program,loaded,sourceAddress,writeNat,writeScalar,next,hi.source,hi.index,hload]
  have t3:step program n x (loaded s v)=.running (destinationAddress s v):=by
    simp [step,program,destinationAddress,loaded,sourceAddress,writeNat,writeScalar,next,evalNat]
  have t4:step program n x (destinationAddress s v)=.running (stored s v):=by
    simp [step,program,stored,destinationAddress,loaded,sourceAddress,writeNat,writeScalar,next]
  have t5:step program n x (stored s v)=.running (advanced s v):=by
    simp [step,program,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next,hi.one,evalNat]
  have t6:step program n x (advanced s v)=.running (iterationEnd s v):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,
      writeNat,writeScalar,next]
  exact ⟨iterationEnd s v,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.refl h6))))))),
    iteration_invariant m a d k heap s v hi hk hv,rfl,iteration_frame s v,iteration_nat s v⟩


/-- All loop iterations execute the literal program. A source value is never
selected by an uncharged copying primitive. -/
theorem loop (n : ℕ) (x : Fin n→ℂ) (m a d k fuel B : ℕ) (heap : ℕ→Option Scalar)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k+fuel=m) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (7*fuel) u ∧ Invariant m a d m heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,fun _ _=>rfl⟩,fun i _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=iteration n x m a d k B heap s hi hsrc (by omega)
      hd hB hcode hpc hs
    obtain ⟨w,hw,hiw,hpw,hfw,hnw⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hiw,hpw,hfu.trans hfw,hnu.trans hnw⟩
    convert hu.trans hw using 1;omega


def zeroState (s : State) : State := writeNat s 150 0
def initialized (s : State) : State := writeNat (zeroState s) 151 1

theorem initialize_invariant (m a d : ℕ) (s : State) (h147:s.natReg 147=m)
    (h148:s.natReg 148=a) (h149:s.natReg 149=d) :
    Invariant m a d 0 s.scalarHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h147,h148,h149,Outside]

theorem initialize_frame (s : State) : Frame s (initialized s) := ⟨rfl,rfl,rfl,fun _ _=>rfl⟩
theorem initialize_nat (s : State) : NatFrame s (initialized s) := by
  intro i hi
  simp [initialized,zeroState,writeNat,next,show i≠150 by omega,show i≠151 by omega]

/-- Complete fixed RAM copy with the original source as its specification.
Every source scalar is explicitly present. The destination can be dirty. The word
budget is identical at every step, and both exact values and dependency flags are copied without arithmetic. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (m a d B : ℕ) (s : State)
    (hsrc:Source m a s.scalarHeap) (hd:a+m ≤ d) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=0) (h147:s.natReg 147=m) (h148:s.natReg 148=a) (h149:s.natReg 149=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (7*m+4) u ∧
    (∀j,j < m→u.scalarHeap (d+j)=s.scalarHeap (a+j)) ∧
    (∀j,j < m→u.scalarHeap (a+j)=s.scalarHeap (a+j)) ∧
    Outside d m s.scalarHeap u ∧ Frame s u ∧ NatFrame s u := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 150 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 151 1 hz
    (by change s.pc+1+1 ≤ B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=
    .next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=loop n x m a d 0 m B s.scalarHeap (initialized s)
    (initialize_invariant m a d s h147 h148 h149) hsrc (by omega) hd hB hcode hp hi
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
def wordBudget (d m : ℕ) : ℕ := max (d+m) 154

theorem wordBudget_polynomial (d m : ℕ) : wordBudget d m ≤ 154*(d+m+1) := by
  unfold wordBudget
  omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (m a d : ℕ) (s : State)
    (hsrc:Source m a s.scalarHeap) (hd:a+m ≤ d)
    (hpc:s.pc=0) (h147:s.natReg 147=m) (h148:s.natReg 148=a) (h149:s.natReg 149=d)
    (hs:WordBound (wordBudget d m) s) : ∃u,
    BoundedExecution program n x (wordBudget d m) s (7*m+4) u ∧
    (∀j,j < m→u.scalarHeap (d+j)=s.scalarHeap (a+j)) ∧
    (∀j,j < m→u.scalarHeap (a+j)=s.scalarHeap (a+j)) ∧
    Outside d m s.scalarHeap u ∧ Frame s u ∧ NatFrame s u :=
  execution n x m a d _ s hsrc hd (le_max_left _ _) (by unfold wordBudget;omega)
    hpc h147 h148 h149 hs

end
end ExactFourierCircuits.UniformScalarCopyMachine
