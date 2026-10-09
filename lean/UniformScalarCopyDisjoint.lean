import UniformScalarCopyMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformScalarCopyMachine
open UniformMachine
noncomputable section
/- The exact original10-instruction program is unchanged. The following
proofs admit either separate bank orientation, with both address ends
explicitly bounded. Data values and dependency tags are copied literally. -/
theorem iteration_disjoint (n : ℕ) (x : Fin n→ℂ) (m a d k B : ℕ) (heap : ℕ→Option Scalar)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k < m) (haB:a+m ≤ B) (hd:a+m ≤ d ∨ d+m ≤ a) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 7 u ∧ Invariant m a d (k+1) heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  obtain ⟨v,hv⟩:=hsrc k hk
  have separate:a+k < d ∨ d+m ≤ a+k:=by
    rcases hd with h|h
    · left;omega
    · right;omega
  have hload:s.scalarHeap (a+k)=some v:=(hi.outside (a+k) separate).trans hv
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
theorem loop_disjoint (n : ℕ) (x : Fin n→ℂ) (m a d k fuel B : ℕ) (heap : ℕ→Option Scalar)
    (s : State) (hi:Invariant m a d k heap s) (hsrc:Source m a heap)
    (hk:k+fuel=m) (haB:a+m ≤ B) (hd:a+m ≤ d ∨ d+m ≤ a) (hB:d+m ≤ B) (hcode:9 ≤ B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (7*fuel) u ∧ Invariant m a d m heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,fun _ _=>rfl⟩,fun i _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩ :=iteration_disjoint n x m a d k B heap s hi hsrc (by omega)
      haB hd hB hcode hpc hs
    obtain ⟨w,hw,hiw,hpw,hfw,hnw⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hiw,hpw,hfu.trans hfw,hnu.trans hnw⟩
    convert hu.trans hw using 1;omega

theorem execution_disjoint (n : ℕ) (x : Fin n→ℂ) (m a d B : ℕ) (s : State)
    (hsrc:Source m a s.scalarHeap) (haB:a+m ≤ B) (hd:a+m ≤ d ∨ d+m ≤ a) (hB:d+m ≤ B) (hcode:9 ≤ B)
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
  obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=loop_disjoint n x m a d 0 m B s.scalarHeap (initialized s)
    (initialize_invariant m a d s h147 h148 h149) hsrc (by omega) haB hd hB hcode hp hi
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
    apply hiu.outside
    rcases hd with h|h
    · left;omega
    · right;omega

end
end ExactFourierCircuits.UniformScalarCopyMachine
