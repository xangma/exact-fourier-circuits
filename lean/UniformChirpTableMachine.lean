import UniformChirp
import UniformPairMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ExactFourierCircuits.UniformChirpTableMachine
open UniformMachine UniformPairMachine
noncomputable section

/-- Nat0 is the count, Nat9 the table base; Scalar0 is a prepared nonzero root.
Each iteration writes the next chirp and its inverse, with two ratio updates. -/
def program : Program :=
  [.natLiteral 2 1,.natLiteral 1 0,.scalarLiteral 1 1,.scalarLiteral 2 1,
   .scalarLiteral 3 1,.fieldBinary .div 3 3 0,
   .fieldBinary .mul 4 0 0,.fieldBinary .mul 5 3 3,
   .branchLT 1 0 9 19,.storeScalar 9 1,.natBinary .add 9 9 2,
   .storeScalar 9 2,.natBinary .add 9 9 2,
   .fieldBinary .mul 1 1 0,.fieldBinary .mul 2 2 3,
   .fieldBinary .mul 0 0 4,.fieldBinary .mul 3 3 5,
   .natBinary .add 1 1 2,.jump 8,.halt]

theorem program_length : program.length=20 := rfl

def initOne (s : State) := writeNat s 2 1
def initIndex (s : State) := writeNat (initOne s) 1 0
def initChirp (s : State) := writeScalar (initIndex s) 1 (prepared 1)
def initInverseChirp (s : State) := writeScalar (initChirp s) 2 (prepared 1)
def initNumerator (s : State) := writeScalar (initInverseChirp s) 3 (prepared 1)
def initInverse (s : State) (eta : ℂ) := writeScalar (initNumerator s) 3 (prepared eta⁻¹)
def initSquare (s : State) (eta : ℂ) := writeScalar (initInverse s eta) 4 (prepared (eta^2))
def initialized (s : State) (eta : ℂ) :=
  writeScalar (initSquare s eta) 5 (prepared ((eta⁻¹)^2))

structure Data (r a j : ℕ) (eta : ℂ) (s : State) : Prop where
  pc : s.pc=8
  count : s.natReg 0=r
  index : s.natReg 1=j
  one : s.natReg 2=1
  address : s.natReg 9=a+2*j
  ratio : s.scalarReg 0=prepared (UniformChirp.ratio eta j)
  chirp : s.scalarReg 1=prepared (UniformChirp.chirp eta j)
  inverseChirp : s.scalarReg 2=prepared (UniformChirp.chirp eta⁻¹ j)
  inverseRatio : s.scalarReg 3=prepared (UniformChirp.ratio eta⁻¹ j)
  square : s.scalarReg 4=prepared (eta^2)
  inverseSquare : s.scalarReg 5=prepared ((eta⁻¹)^2)

def entered (s : State) : State := {s with pc:=9}
def storedChirp (s : State) : State :=
  {next (entered s) with
    scalarHeap:=Function.update s.scalarHeap (s.natReg 9) (some (s.scalarReg 1))}
def secondAddress (s : State) := writeNat (storedChirp s) 9 (s.natReg 9+1)
def storedInverse (s : State) : State :=
  {next (secondAddress s) with
    scalarHeap:=Function.update (secondAddress s).scalarHeap (s.natReg 9+1) (some (s.scalarReg 2))}
def advancedAddress (s : State) := writeNat (storedInverse s) 9 (s.natReg 9+2)
def advancedChirp (s : State) (eta : ℂ) (j : ℕ) :=
  writeScalar (advancedAddress s) 1 (prepared (UniformChirp.chirp eta (j+1)))
def advancedInverseChirp (s : State) (eta : ℂ) (j : ℕ) :=
  writeScalar (advancedChirp s eta j) 2 (prepared (UniformChirp.chirp eta⁻¹ (j+1)))
def advancedRatio (s : State) (eta : ℂ) (j : ℕ) :=
  writeScalar (advancedInverseChirp s eta j) 0 (prepared (UniformChirp.ratio eta (j+1)))
def advancedInverseRatio (s : State) (eta : ℂ) (j : ℕ) :=
  writeScalar (advancedRatio s eta j) 3 (prepared (UniformChirp.ratio eta⁻¹ (j+1)))
def rowEnd (s : State) (eta : ℂ) (j : ℕ) : State :=
  {writeNat (advancedInverseRatio s eta j) 1 (j+1) with pc:=8}

theorem initialized_data (r a : ℕ) (eta : ℂ) (s : State)
    (hp : s.pc=0) (hr : s.natReg 0=r) (ha : s.natReg 9=a)
    (he : s.scalarReg 0=prepared eta) : Data r a 0 eta (initialized s eta) := by
  constructor <;> simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,
    initChirp,initIndex,initOne,writeNat,writeScalar,next,hp,hr,ha,he,
    UniformChirp.chirp_zero,UniformChirp.ratio_zero]

theorem startup_runs (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State) (eta : ℂ)
    (hp : s.pc=0) (he : s.scalarReg 0=prepared eta) (hnz : eta≠0)
    (hB : 20≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 8 (initialized s eta) := by
  have h1:=writeNat_bound B (s) 2 1 hs (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega) (by omega)
  have h2:=writeNat_bound B (initOne s) 1 0 h1 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega) (by omega)
  have h3:=writeScalar_bound B (initIndex s) 1 (prepared 1) h2 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  have h4:=writeScalar_bound B (initChirp s) 2 (prepared 1) h3 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  have h5:=writeScalar_bound B (initInverseChirp s) 3 (prepared 1) h4 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  have h6:=writeScalar_bound B (initNumerator s) 3 (prepared eta⁻¹) h5 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  have h7:=writeScalar_bound B (initInverse s eta) 4 (prepared (eta^2)) h6 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  have h8:=writeScalar_bound B (initSquare s eta) 5 (prepared ((eta⁻¹)^2)) h7 (by simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp];omega)
  refine .next hs (u:=initOne s) ?_ (.next h1 (u:=initIndex s) ?_ (.next h2 (u:=initChirp s) ?_ (.next h3 (u:=initInverseChirp s) ?_ (.next h4 (u:=initNumerator s) ?_ (.next h5 (u:=initInverse s eta) ?_ (.next h6 (u:=initSquare s eta) ?_ (.next h7 (u:=initialized s eta) ?_ (.refl h8))))))))
  all_goals simp [step,program,initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,initIndex,initOne,writeNat,writeScalar,next,hp,he,hnz,evalField,prepared,pow_two]

theorem row_data (r a j : ℕ) (eta : ℂ) (s : State) (h : Data r a j eta s) :
    Data r a (j+1) eta (rowEnd s eta j) := by
  obtain ⟨hp,hr,hj,h1,ha,h0,hc,hi,h3,h4,h5⟩:=h
  constructor <;> simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,
    advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,
    writeNat,writeScalar,next,hp,hr,hj,h1,ha,h0,hc,hi,h3,h4,h5] <;> omega

theorem row_heap (s : State) (eta : ℂ) (j : ℕ) :
    (rowEnd s eta j).scalarHeap=Function.update
      (Function.update s.scalarHeap (s.natReg 9) (some (s.scalarReg 1)))
      (s.natReg 9+1) (some (s.scalarReg 2)) := rfl

theorem row_runs (n : ℕ) (x : Fin n → ℂ) (B r a j : ℕ) (eta : ℂ) (s : State)
    (h : Data r a j eta s) (hj : j<r) (hB : 20≤B)
    (ha : a+2*r≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 11 (rowEnd s eta j) := by
  obtain ⟨hp,hr,hi,h1,hadr,h0,hc,hic,h3,h4,h5⟩:=h
  have hrB:r≤B:=by simpa [hr] using hs.2.1 0
  have hbr:WordBound B (entered s):=changePC_bound B s 9 hs (by omega)
  have hb1:=UniformInPlaceMachine.storeScalar_bound B (entered s) (s.natReg 9) (s.scalarReg 1) hbr (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega) (by rw [hadr];omega)
  have hb2:=writeNat_bound B (storedChirp s) 9 (s.natReg 9+1) hb1 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega) (by rw [hadr];omega)
  have hb3:=UniformInPlaceMachine.storeScalar_bound B (secondAddress s) (s.natReg 9+1) (s.scalarReg 2) hb2 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega) (by rw [hadr];omega)
  have hb4:=writeNat_bound B (storedInverse s) 9 (s.natReg 9+2) hb3 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega) (by rw [hadr];omega)
  have hb5:=writeScalar_bound B (advancedAddress s) 1 (prepared (UniformChirp.chirp eta (j+1))) hb4 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega)
  have hb6:=writeScalar_bound B (advancedChirp s eta j) 2 (prepared (UniformChirp.chirp eta⁻¹ (j+1))) hb5 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega)
  have hb7:=writeScalar_bound B (advancedInverseChirp s eta j) 0 (prepared (UniformChirp.ratio eta (j+1))) hb6 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega)
  have hb8:=writeScalar_bound B (advancedRatio s eta j) 3 (prepared (UniformChirp.ratio eta⁻¹ (j+1))) hb7 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega)
  have hb9:=writeNat_bound B (advancedInverseRatio s eta j) 1 (j+1) hb8 (by simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp];omega) (by omega)
  have hf:WordBound B (rowEnd s eta j):=changePC_bound B _ 8 hb9 (by omega)
  refine .next hs (u:=entered s) ?_ (.next hbr (u:=storedChirp s) ?_ (.next hb1 (u:=secondAddress s) ?_ (.next hb2 (u:=storedInverse s) ?_ (.next hb3 (u:=advancedAddress s) ?_ (.next hb4 (u:=advancedChirp s eta j) ?_ (.next hb5 (u:=advancedInverseChirp s eta j) ?_ (.next hb6 (u:=advancedRatio s eta j) ?_ (.next hb7 (u:=advancedInverseRatio s eta j) ?_ (.next hb8 (u:=writeNat (advancedInverseRatio s eta j) 1 (j+1)) ?_ (.next hb9 ?_ (.refl hf)))))))))))
  all_goals simp [step,program,rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,hp,hr,hi,h1,hadr,h0,hc,hic,h3,h4,h5,hj,evalNat,evalField,prepared,UniformChirp.chirp_succ,UniformChirp.ratio_succ]

/-- Prefix correctness records actual written table cells, not an entry premise. -/
def Partial (a j : ℕ) (eta : ℂ) (s : State) : Prop := ∀ k,k<j →
  s.scalarHeap (a+2*k)=some (prepared (UniformChirp.chirp eta k)) ∧
  s.scalarHeap (a+2*k+1)=some (prepared (UniformChirp.chirp eta⁻¹ k))

def Frame (a r : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<a ∨ a+2*r≤b → u.scalarHeap b=s.scalarHeap b) ∧
  u.natReg 0=s.natReg 0 ∧ (∀ b,3≤b → b≠9 → u.natReg b=s.natReg b) ∧
  ∀ b,6≤b → u.scalarReg b=s.scalarReg b

theorem frame_trans (a r : ℕ) (s u v : State)
    (hu : Frame a r s u) (hv : Frame a r u v) : Frame a r s v := by
  exact ⟨hv.1.trans hu.1,hv.2.1.trans hu.2.1,hv.2.2.1.trans hu.2.2.1,
    fun b hb => (hv.2.2.2.1 b hb).trans (hu.2.2.2.1 b hb),
    hv.2.2.2.2.1.trans hu.2.2.2.2.1,
    fun b hb h9 => (hv.2.2.2.2.2.1 b hb h9).trans (hu.2.2.2.2.2.1 b hb h9),
    fun b hb => (hv.2.2.2.2.2.2 b hb).trans (hu.2.2.2.2.2.2 b hb)⟩

theorem initialized_frame (a r : ℕ) (s : State) (eta : ℂ) :
    Frame a r s (initialized s eta) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,rfl,?_,?_⟩
  · intro b hb h9
    simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,
      initIndex,initOne,writeNat,writeScalar,next,show b≠1 by omega,show b≠2 by omega]
  · intro b hb
    simp [initialized,initSquare,initInverse,initNumerator,initInverseChirp,initChirp,
      initIndex,initOne,writeNat,writeScalar,next,show b≠1 by omega,show b≠2 by omega,
      show b≠3 by omega,show b≠4 by omega,show b≠5 by omega]

theorem row_frame (r a j : ℕ) (eta : ℂ) (s : State) (h : Data r a j eta s)
    (hj : j<r) : Frame a r s (rowEnd s eta j) := by
  refine ⟨rfl,rfl,rfl,?_,rfl,?_,?_⟩
  · intro b hb
    rw [row_heap,h.address]
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  · intro b hb h9
    simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,
      advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,
      h9,show b≠1 by omega]
  · intro b hb
    simp [rowEnd,advancedInverseRatio,advancedRatio,advancedInverseChirp,advancedChirp,
      advancedAddress,storedInverse,secondAddress,storedChirp,entered,writeNat,writeScalar,next,
      show b≠0 by omega,show b≠1 by omega,show b≠2 by omega,show b≠3 by omega]

theorem row_partial (r a j : ℕ) (eta : ℂ) (s : State) (h : Data r a j eta s)
    (hp : Partial a j eta s) : Partial a (j+1) eta (rowEnd s eta j) := by
  intro k hk
  rw [row_heap,h.address,h.chirp,h.inverseChirp]
  by_cases he:k=j
  · subst k
    constructor
    · rw [Function.update_of_ne (by omega),Function.update_self]
    · exact Function.update_self _ _ _
  · have hkj:k<j:=by omega
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hp k hkj

theorem loop_execution (n : ℕ) (x : Fin n → ℂ) (B r a : ℕ) (eta : ℂ)
    (hB : 20≤B) (ha : a+2*r≤B) (t : ℕ) : ∀ j s,
    j+t=r → Data r a j eta s → Partial a j eta s → WordBound B s → ∃ u,
    BoundedExecution program n x B s (11*t+2) u ∧ Partial a r eta u ∧
    Frame a r s u ∧ u.pc=19 := by
  induction t with
  | zero =>
    intro j s hj hd hp hs
    have he:j=r:=by omega
    let u:State:={s with pc:=19}
    have hu:WordBound B u:=changePC_bound B s 19 hs (by omega)
    refine ⟨u,?_,?_,?_,rfl⟩
    · refine .next hs (u:=u) ?_ (.halt hu ?_)
      · simp [step,program,hd.pc,hd.index,hd.count,he,u]
      · simp [step,program,u]
    · simpa [he,u,Partial] using hp
    · exact ⟨rfl,rfl,rfl,fun _ _=>rfl,rfl,fun _ _ _=>rfl,fun _ _=>rfl⟩
  | succ t ih =>
    intro j s hj hd hp hs
    have hjr:j<r:=by omega
    have he:=row_runs n x B r a j eta s hd hjr hB ha hs
    obtain ⟨u,hu,hp',hf,hpc⟩:=ih (j+1) (rowEnd s eta j) (by omega)
      (row_data r a j eta s hd) (row_partial r a j eta s hd hp) he.final_bound
    refine ⟨u,?_,hp',frame_trans a r s (rowEnd s eta j) u (row_frame r a j eta s hd hjr) hf,hpc⟩
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he.executes hu

/-- One fixed literal program writes the complete chirp/inverse table. The
count includes setup, each branch/store/update, and the final halt. -/
theorem table_execution (n : ℕ) (x : Fin n → ℂ) (B r a : ℕ) (eta : ℂ) (s : State)
    (hnz : eta≠0) (hp : s.pc=0) (hr : s.natReg 0=r) (ha : s.natReg 9=a)
    (he : s.scalarReg 0=prepared eta) (hB : 20≤B) (hspace : a+2*r≤B)
    (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (11*r+10) u ∧ Partial a r eta u ∧
    Frame a r s u ∧ u.pc=19 := by
  have hstart:=startup_runs n x B s eta hp he hnz hB hs
  obtain ⟨u,hu,ht,hf,hpc⟩:=loop_execution n x B r a eta hB hspace r 0 (initialized s eta)
    (by omega) (initialized_data r a eta s hp hr ha he) (by intro k hk;omega) hstart.final_bound
  refine ⟨u,?_,ht,frame_trans a r s (initialized s eta) u (initialized_frame a r s eta) hf,hpc⟩
  convert hstart.executes hu using 1 <;> omega

theorem inverse_chirp_value (eta : ℂ) (j : ℕ) :
    UniformChirp.chirp eta⁻¹ j=(UniformChirp.chirp eta j)⁻¹ := by
  simp [UniformChirp.chirp,inv_pow]

/-- The standard half-angle root is supplied from the one master-root bank. -/
theorem specified_table_execution (n : ℕ) (x : Fin n → ℂ) (B a : ℕ) (s : State)
    (hp : s.pc=0) (hr : s.natReg 0=n) (ha : s.natReg 9=a)
    (he : s.scalarReg 0=prepared (OAI.ExactFourier.zeta (2*n))) (hB : 20≤B)
    (hspace : a+2*n≤B) (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (11*n+10) u ∧
    (∀ j : Fin n,
      u.scalarHeap (a+2*j.val)=some (prepared
        (OAI.ExactFourier.zeta (2*n)^((j.val:ℤ)^2))) ∧
      u.scalarHeap (a+2*j.val+1)=some (prepared
        (OAI.ExactFourier.zeta (2*n)^(-((j.val:ℤ)^2))))) ∧
    Frame a n s u ∧ u.pc=19 := by
  obtain ⟨u,hu,ht,hf,hpc⟩:=table_execution n x B n a _ s
    (UniformRoots.specifiedRoot_ne_zero _) hp hr ha he hB hspace hs
  refine ⟨u,hu,?_,hf,hpc⟩
  intro j
  have hj:=ht j.val j.isLt
  simpa [UniformChirp.chirp,inverse_chirp_value,inv_pow,zpow_neg,
    ← zpow_natCast,show ((j.val^2:ℕ):ℤ)=(j.val:ℤ)^2 by simp] using hj

theorem bank_preserved (a r : ℕ) (s u : State) (hf : Frame a r s u)
    (ha : 6≤a) (j : Fin 6) : u.scalarHeap j.val=s.scalarHeap j.val :=
  hf.2.2.2.1 j.val (Or.inl (by have hj:=j.isLt;omega))

theorem linear_cost (r : ℕ) (hr : 0<r) : 11*r+10≤21*r := by omega

theorem contextFree : UniformContext.ContextFree program := by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program]

end
end ExactFourierCircuits.UniformChirpTableMachine
