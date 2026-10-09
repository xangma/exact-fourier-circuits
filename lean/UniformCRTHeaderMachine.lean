import UniformCRTMachine
import UniformSelectedCRT
import UniformCConstantsMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, CRT tables and linear index traversal surrounding (5.5),
PDF p.22 (`eq:crt-fourier`), using the prefix bound (4.1), PDF p.18.

Literal integer/table/traversal bookkeeping refines that argument. The paper
does not specify this register layout or these frames; semantic and charged
execution obligations are separate declarations below.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCRTHeaderMachine
open UniformMachine
open scoped BigOperators
noncomputable section

/- Header10=ell,17=L,18=binary. Scratch30=index,31=one,32=axis count,
34=table pointer,35=q,36=cofactor,37=inverse,38=idempotent,39=zero,
40=four,41=saved nextPrime. The existing inverse uses only0..5. -/
def head : Program := [
  .natLiteral 39 0,.natLiteral 31 1,.natLiteral 40 4,
  .natBinary .add 41 0 39,.natLiteral 30 0,
  .natBinary .add 32 10 31,.natBinary .add 34 10 39,
  .branchLT 30 32 8 40,.branchLT 30 10 9 11,
  .loadNat 35 30,.jump 12,.natBinary .add 35 18 39,
  .natBinary .div 36 17 35,.branchLT 31 35 14 42,
  .natBinary .add 0 36 39,.natBinary .add 1 35 39,.jump 17]

def tail : Program := [
  .natBinary .add 37 3 39,.natBinary .mul 38 36 37,
  .storeNat 34 35,.natBinary .add 34 34 31,
  .storeNat 34 36,.natBinary .add 34 34 31,
  .storeNat 34 37,.natBinary .add 34 34 31,
  .storeNat 34 38,.natBinary .add 34 34 31,
  .natBinary .add 30 30 31,.jump 7,
  .natBinary .add 0 41 39,.halt,.natLiteral 37 0,.jump 29]

def program : Program := UniformAssembly.embed head UniformCRTMachine.program tail 28

theorem inverse_code : UniformAssembly.CodeAt UniformCRTMachine.program program 17 28 :=
  UniformAssembly.embed_code head UniformCRTMachine.program tail 28

theorem program_length : program.length=44 := by decide

def tableAddress (ell i field : ℕ) : ℕ := ell+4*i+field

def CRTTable (n : ℕ) (s : State) : Prop :=
  ∀ i : Fin (UniformWorkingLength.axisCount n+1),
    s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 0)=
        some (UniformSelectedCRT.radices n i) ∧
    s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 1)=
        some (UniformCRT.cofactor (UniformSelectedCRT.radices n) i) ∧
    s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 2)=
        some (UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i) ∧
    s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 3)=
        some (UniformCRT.idempotent (UniformSelectedCRT.radices n) i)

/-- The selected header after table population omits the obsolete empty-tail
heap clause of WorkingCompletion.PreparedState. -/
def Header (n : ℕ) (s : State) : Prop :=
  s.natReg 0=UniformWorkingLength.nextPrime n ∧
  s.natReg 10=UniformWorkingLength.axisCount n ∧
  s.natReg 11=UniformWorkingLength.oddProduct n ∧
  s.natReg 16=UniformWorkingLength.doublingExponent n ∧
  s.natReg 17=UniformWorkingLength.workingLength n ∧
  s.natReg 18=UniformWorkingLength.binaryFactor n ∧
  UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s

def Frame (ell : ℕ) (s u : State) : Prop :=
  u.scalarReg=s.scalarReg ∧ u.scalarHeap=s.scalarHeap ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ a,a<ell → u.natHeap a=s.natHeap a) ∧
  ∀ r,6≤r → r<30 ∨ 41<r → u.natReg r=s.natReg r

theorem frame_refl (ell : ℕ) (s : State) : Frame ell s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩

theorem frame_trans (ell : ℕ) (s u v : State) (h : Frame ell s u)
    (h' : Frame ell u v) : Frame ell s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun a ha => (h'.2.2.2.2.1 a ha).trans (h.2.2.2.2.1 a ha),
    fun r hr hs => (h'.2.2.2.2.2 r hr hs).trans (h.2.2.2.2.2 r hr hs)⟩

/-- Relocated helper PCs remain within the literal code extent, so placement
does not inflate the integer-word bound at every loop iteration. -/
theorem execution_placed_same {p q : Program} {base ret n B t : ℕ}
    {x : Fin n → ℂ} {s u : State}
    (code : UniformAssembly.CodeAt p q base ret) (hcode : base+p.length≤B)
    (hret : ret≤B) (h : BoundedExecution p n x B s t u) :
    BoundedRuns q n x B (UniformAssembly.placed base s) t {u with pc:=ret} := by
  induction h with
  | halt hb hs =>
      have hp := UniformAssembly.halted_pc hs
      have hplaced : WordBound B (UniformAssembly.placed base _) :=
        changePC_bound B _ _ hb (by omega)
      exact .next hplaced (UniformAssembly.halted_placed code hs)
        (.refl (changePC_bound B _ ret hb hret))
  | next hb hs _ ih =>
      have hp := UniformAssembly.running_pc hs
      have hplaced : WordBound B (UniformAssembly.placed base _) :=
        changePC_bound B _ _ hb (by omega)
      exact .next hplaced (UniformAssembly.running_placed code hs) ih

theorem inverse_step_high (n : ℕ) (x : Fin n → ℂ) (s u : State)
    (r : ℕ) (hr : 6≤r)
    (h : step UniformCRTMachine.program n x s=.running u) :
    u.natReg r=s.natReg r := by
  have hp := UniformAssembly.running_pc h
  have hl : UniformCRTMachine.program.length=11 := rfl
  rw [hl] at hp
  have h2 : r≠2 := by omega
  have h3 : r≠3 := by omega
  have h4 : r≠4 := by omega
  have h5 : r≠5 := by omega
  interval_cases hc : s.pc <;>
    simp [step,UniformCRTMachine.program,hc,writeNat,next] at h
  all_goals simp_all [evalNat]
  all_goals repeat' (first | (subst u; simp_all) | (split at h <;> simp_all))

theorem inverse_high (n : ℕ) (x : Fin n → ℂ) (s u : State) (t : ℕ)
    (r : ℕ) (hr : 6≤r) (h : Executes UniformCRTMachine.program n x s t u) :
    u.natReg r=s.natReg r := by
  induction h with
  | halt _ => rfl
  | next hs _ ih => exact ih.trans (inverse_step_high n x _ _ r hr hs)

def stored (s : State) (address value : ℕ) : State :=
  {next s with natHeap:=Function.update s.natHeap address (some value)}

theorem stored_bound (B : ℕ) (s : State) (address value : ℕ)
    (hs : WordBound B s) (hp : s.pc+1≤B) (ha : address≤B) (hv : value≤B) :
    WordBound B (stored s address value) := by
  obtain ⟨_,hr,hh,hscalar,hout,hroot⟩ := hs
  refine ⟨hp,hr,?_,hscalar,hout,hroot⟩
  intro a v h
  by_cases he : a=address
  · subst a
    have hval : v=value := by simpa [stored] using h.symm
    subst v; exact ⟨ha,hv⟩
  · exact hh a v (by simpa [stored,he] using h)

theorem literal_runs (n B dst value : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hp : s.pc+1≤B) (hv : value≤B)
    (hc : program[s.pc]?=some (.natLiteral dst value)) :
    BoundedRuns program n x B s 1 (writeNat s dst value) :=
  .next hs (by simp [step,hc]) (.refl (writeNat_bound B s dst value hs hp hv))

theorem binary_runs (n B dst left right value : ℕ) (op : NatOp)
    (x : Fin n → ℂ) (s : State) (hs : WordBound B s) (hp : s.pc+1≤B)
    (hv : value≤B) (hc : program[s.pc]?=some (.natBinary op dst left right))
    (he : evalNat op (s.natReg left) (s.natReg right)=some value) :
    BoundedRuns program n x B s 1 (writeNat s dst value) :=
  .next hs (by simp [step,hc,he]) (.refl (writeNat_bound B s dst value hs hp hv))

theorem branch_runs (n B left right yes no : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hy : yes≤B) (hn : no≤B)
    (hc : program[s.pc]?=some (.branchLT left right yes no)) :
    BoundedRuns program n x B s 1
      {s with pc:=if s.natReg left<s.natReg right then yes else no} := by
  refine .next hs (by simp [step,hc]) (.refl ?_)
  apply changePC_bound B _ _ hs
  split_ifs <;> assumption

theorem jump_runs (n B target : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (ht : target≤B) (hc : program[s.pc]?=some (.jump target)) :
    BoundedRuns program n x B s 1 {s with pc:=target} :=
  .next hs (by simp [step,hc]) (.refl (changePC_bound B s target hs ht))

theorem load_runs (n B dst address value : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hp : s.pc+1≤B)
    (hc : program[s.pc]?=some (.loadNat dst address))
    (he : s.natHeap (s.natReg address)=some value) :
    BoundedRuns program n x B s 1 (writeNat s dst value) :=
  .next hs (by simp [step,hc,he])
    (.refl (writeNat_bound B s dst value hs hp (hs.2.2.1 _ _ he).2))

theorem store_runs (n B address src : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hp : s.pc+1≤B)
    (hc : program[s.pc]?=some (.storeNat address src)) :
    BoundedRuns program n x B s 1 (stored s (s.natReg address) (s.natReg src)) :=
  .next hs (by simp [step,hc,stored])
    (.refl (stored_bound B s _ _ hs hp (hs.2.1 _) (hs.2.1 _)))

def initialized (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 39 0)
    31 1) 40 4) 41 (s.natReg 0)) 30 0) 32 (s.natReg 10+1)) 34 (s.natReg 10)

structure LoopData (n saved i : ℕ) (s : State) : Prop where
  index : s.natReg 30=i
  one : s.natReg 31=1
  axes : s.natReg 32=UniformWorkingLength.axisCount n+1
  pointer : s.natReg 34=tableAddress (UniformWorkingLength.axisCount n) i 0
  zero : s.natReg 39=0
  savedPrime : s.natReg 41=saved
  count : s.natReg 10=UniformWorkingLength.axisCount n
  length : s.natReg 17=UniformWorkingLength.workingLength n
  binary : s.natReg 18=UniformWorkingLength.binaryFactor n

theorem initialized_data (n : ℕ) (s : State)
    (h10 : s.natReg 10=UniformWorkingLength.axisCount n)
    (h17 : s.natReg 17=UniformWorkingLength.workingLength n)
    (h18 : s.natReg 18=UniformWorkingLength.binaryFactor n) :
    LoopData n (s.natReg 0) 0 (initialized s) := by
  constructor <;> simp [initialized,writeNat,next,tableAddress,h10,h17,h18]

theorem initialized_frame (ell : ℕ) (s : State) : Frame ell s (initialized s) := by
  refine ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl,?_⟩
  intro r hr hs
  have h30 : r≠30 := by omega
  have h31 : r≠31 := by omega
  have h32 : r≠32 := by omega
  have h34 : r≠34 := by omega
  have h39 : r≠39 := by omega
  have h40 : r≠40 := by omega
  have h41 : r≠41 := by omega
  simp [initialized,writeNat,next,h30,h31,h32,h34,h39,h40,h41]

theorem startup_runs (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hp : s.pc=0) (hB : 44≤B)
    (hell : s.natReg 10+1≤B) :
    BoundedRuns program n x B s 7 (initialized s) := by
  let s1 := writeNat s 39 0
  let s2 := writeNat s1 31 1
  let s3 := writeNat s2 40 4
  let s4 := writeNat s3 41 (s.natReg 0)
  let s5 := writeNat s4 30 0
  let s6 := writeNat s5 32 (s.natReg 10+1)
  have h1 := literal_runs n B 39 0 x s hs (by omega) (by omega)
    (by simpa [hp] using (show program[0]?=some (.natLiteral 39 0) by decide))
  have h2 := literal_runs n B 31 1 x s1 h1.final_bound
    (by simp [s1,writeNat,next,hp]; omega) (by omega)
    (by simp [s1,writeNat,next,hp,program,head,UniformAssembly.embed])
  have h3 := literal_runs n B 40 4 x s2 h2.final_bound
    (by simp [s2,s1,writeNat,next,hp]; omega) (by omega)
    (by simp [s2,s1,writeNat,next,hp,program,head,UniformAssembly.embed])
  have h4 := binary_runs n B 41 0 39 (s.natReg 0) .add x s3 h3.final_bound
    (by simp [s3,s2,s1,writeNat,next,hp]; omega) (hs.2.1 _)
    (by simp [s3,s2,s1,writeNat,next,hp,program,head,UniformAssembly.embed])
    (by simp [s3,s2,s1,writeNat,next,evalNat])
  have h5 := literal_runs n B 30 0 x s4 h4.final_bound
    (by simp [s4,s3,s2,s1,writeNat,next,hp]; omega) (by omega)
    (by simp [s4,s3,s2,s1,writeNat,next,hp,program,head,UniformAssembly.embed])
  have h6 := binary_runs n B 32 10 31 (s.natReg 10+1) .add x s5 h5.final_bound
    (by simp [s5,s4,s3,s2,s1,writeNat,next,hp]; omega) hell
    (by simp [s5,s4,s3,s2,s1,writeNat,next,hp,program,head,UniformAssembly.embed])
    (by simp [s5,s4,s3,s2,s1,writeNat,next,evalNat])
  have h7 := binary_runs n B 34 10 39 (s.natReg 10) .add x s6 h6.final_bound
    (by simp [s6,s5,s4,s3,s2,s1,writeNat,next,hp]; omega) (hs.2.1 _)
    (by simp [s6,s5,s4,s3,s2,s1,writeNat,next,hp,program,head,UniformAssembly.embed])
    (by simp [s6,s5,s4,s3,s2,s1,writeNat,next,evalNat])
  exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7

/-- Eight actual store/increment instructions populate one four-field row. -/
def savePrefix (s : State) : ℕ → State
  | 0 => s
  | j+1 => writeNat (stored (savePrefix s j) (s.natReg 34+j) (s.natReg (35+j)))
      34 (s.natReg 34+j+1)

theorem savePrefix_reg (s : State) (j r : ℕ) (hr : r≠34) :
    (savePrefix s j).natReg r=s.natReg r := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [savePrefix,stored,writeNat,next,hr] using ih

theorem savePrefix_pointer (s : State) (j : ℕ) :
    (savePrefix s j).natReg 34=s.natReg 34+j := by
  cases j <;> simp [savePrefix,writeNat,next,Nat.add_assoc]

theorem savePrefix_pc (s : State) (j : ℕ) : (savePrefix s j).pc=s.pc+2*j := by
  induction j with
  | zero => simp [savePrefix]
  | succ j ih => simp [savePrefix,stored,writeNat,next,ih]; omega

theorem savePrefix_bound (_n B j : ℕ) (s : State) (hs : WordBound B s)
    (hj : j≤4) (hp : s.pc=30) (hB : 44≤B) (hptr : s.natReg 34+4≤B) :
    WordBound B (savePrefix s j) := by
  induction j with
  | zero => exact hs
  | succ j ih =>
      have hold := ih (by omega)
      have hpc := savePrefix_pc s j
      have hstored := stored_bound B (savePrefix s j) (s.natReg 34+j)
        (s.natReg (35+j)) hold (by omega) (by omega) (hs.2.1 (35+j))
      exact writeNat_bound B _ 34 _ hstored
        (by simp [stored,next,hpc,hp]; omega) (by omega)

theorem savePrefix_runs (n B j : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : WordBound B s) (hj : j≤4) (hp : s.pc=30) (hone : s.natReg 31=1)
    (hB : 44≤B) (hptr : s.natReg 34+4≤B) :
    BoundedRuns program n x B s (2*j) (savePrefix s j) := by
  induction j with
  | zero => exact .refl hs
  | succ j ih =>
      have hj4 : j<4 := by omega
      have hc : program[30+2*j]?=some (.storeNat 34 (35+j)) := by
        interval_cases j <;> decide
      have hc' : program[31+2*j]?=some (.natBinary .add 34 34 31) := by
        interval_cases j <;> decide
      have hold := savePrefix_bound n B j s hs (by omega) hp hB hptr
      have hp' : (savePrefix s j).pc=30+2*j := by rw [savePrefix_pc,hp]
      have hstore := store_runs n B 34 (35+j) x (savePrefix s j) hold
        (by omega) (by rw [hp']; exact hc)
      have hptr' := savePrefix_pointer s j
      have hsrc := savePrefix_reg s j (35+j) (by omega)
      have he : stored (savePrefix s j) ((savePrefix s j).natReg 34)
          ((savePrefix s j).natReg (35+j)) =
          stored (savePrefix s j) (s.natReg 34+j) (s.natReg (35+j)) := by rw [hptr',hsrc]
      rw [he] at hstore
      have hadd := binary_runs n B 34 34 31 (s.natReg 34+j+1) .add x _ hstore.final_bound
        (by simp [stored,next,hp']; omega) (by omega)
        (by
          have hpc : (stored (savePrefix s j) (s.natReg 34+j) (s.natReg (35+j))).pc=
              31+2*j := by simp only [stored,next,hp']; omega
          rw [hpc]; exact hc')
        (by simp [stored,next,evalNat,hptr',savePrefix_reg s j 31 (by decide),hone])
      convert (ih (by omega)).trans (hstore.trans hadd) using 1
      simp [savePrefix]

theorem savePrefix_before (s : State) (j a : ℕ) (ha : a<s.natReg 34) :
    (savePrefix s j).natHeap a=s.natHeap a := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hne : a≠s.natReg 34+j := by omega
      simpa [savePrefix,stored,writeNat,next,hne] using ih

theorem savePrefix_fields (s : State) (q : Fin 4) :
    (savePrefix s 4).natHeap (s.natReg 34+q.val)=some (s.natReg (35+q.val)) := by
  fin_cases q <;> simp [savePrefix,stored,writeNat,next]

theorem writeNat_frame (ell : ℕ) (s : State) (dst value : ℕ)
    (hd : dst<6 ∨ 30≤dst ∧ dst≤41) : Frame ell s (writeNat s dst value) := by
  refine ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl,?_⟩
  intro r hr hp
  have hne : r≠dst := by omega
  simp [writeNat,next,hne]

theorem pc_frame (ell pc : ℕ) (s : State) : Frame ell s {s with pc:=pc} :=
  frame_refl ell s

theorem LoopData.high {n saved i : ℕ} {s u : State} (hs : LoopData n saved i s)
    (hh : ∀ r,6≤r → u.natReg r=s.natReg r) : LoopData n saved i u := by
  constructor
  · exact (hh 30 (by decide)).trans hs.index
  · exact (hh 31 (by decide)).trans hs.one
  · exact (hh 32 (by decide)).trans hs.axes
  · exact (hh 34 (by decide)).trans hs.pointer
  · exact (hh 39 (by decide)).trans hs.zero
  · exact (hh 41 (by decide)).trans hs.savedPrime
  · exact (hh 10 (by decide)).trans hs.count
  · exact (hh 17 (by decide)).trans hs.length
  · exact (hh 18 (by decide)).trans hs.binary

def selectedState (s : State) (q : ℕ) : State :=
  {writeNat s 35 q with pc:=12}

def cofactorState (s : State) (q : ℕ) : State :=
  writeNat (selectedState s q) 36 (s.natReg 17/q)

theorem selected_data {n saved i : ℕ} {s : State} (hs : LoopData n saved i s) (q : ℕ) :
    LoopData n saved i (cofactorState s q) := by
  constructor <;> simp [cofactorState,selectedState,writeNat,next,
    hs.index,hs.one,hs.axes,hs.pointer,hs.zero,hs.savedPrime,hs.count,hs.length,hs.binary]

theorem selected_frame (ell : ℕ) (s : State) (q : ℕ) :
    Frame ell s (cofactorState s q) := by
  have h1 := writeNat_frame ell s 35 q (by omega)
  have h2 := pc_frame ell 12 (writeNat s 35 q)
  have h3 := writeNat_frame ell (selectedState s q) 36 (s.natReg 17/q) (by omega)
  exact frame_trans ell s _ _ (frame_trans ell s _ _ h1 h2) h3

theorem radix_bound (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n+1)) :
    UniformSelectedCRT.radices n i≤UniformWorkingLength.workingLength n ∧
      UniformCRT.cofactor (UniformSelectedCRT.radices n) i≤UniformWorkingLength.workingLength n := by
  have hp := UniformSelectedCRT.radix_pos n
  have hco : 0<UniformCRT.cofactor (UniformSelectedCRT.radices n) i :=
    Finset.prod_pos (fun j _ => hp j)
  have he := UniformCRT.cofactor_mul (UniformSelectedCRT.radices n) i
  rw [UniformSelectedCRT.radices_product] at he
  constructor <;> nlinarith [hp i]

theorem select_runs (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (i : Fin (UniformWorkingLength.axisCount n+1))
    (hs : LoopData n saved i.val s) (hp : s.pc=7)
    (ht : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s)
    (hb : WordBound B s) (hB : 44≤B)
    (hL : UniformWorkingLength.workingLength n≤B) : ∃ t,
    BoundedRuns program n x B s t (cofactorState s (UniformSelectedCRT.radices n i)) ∧ t≤5 := by
  let q := UniformSelectedCRT.radices n i
  have hqB : q≤B := (radix_bound n i).1.trans hL
  have hcoB : s.natReg 17/q≤B := (Nat.div_le_self _ _).trans (hb.2.1 17)
  have hgo : s.natReg 30<s.natReg 32 := by rw [hs.index,hs.axes]; exact i.isLt
  have hbranch := branch_runs n B 30 32 8 40 x s hb (by omega) (by omega)
    (by simpa [hp] using (show program[7]?=some (.branchLT 30 32 8 40) by decide))
  simp only [ite_eq_left hgo] at hbranch
  by_cases hi : i.val<UniformWorkingLength.axisCount n
  · have hodd : s.natReg 30<s.natReg 10 := by rw [hs.index,hs.count]; exact hi
    have hsel := branch_runs n B 30 10 9 11 x {s with pc:=8}
      hbranch.final_bound (by omega) (by omega)
      (by change program[8]?=some (.branchLT 30 10 9 11); decide)
    simp only [ite_eq_left hodd] at hsel
    have hval : s.natHeap (s.natReg 30)=some q := by
      rw [hs.index,ht i.val hi]
      simp [q,UniformSelectedCRT.radices,Fin.snoc,hi]
    have hload := load_runs n B 35 30 q x {s with pc:=9} hsel.final_bound
      (by simp; omega) (by change program[9]?=some (.loadNat 35 30); decide) hval
    have hjump := jump_runs n B 12 x (writeNat {s with pc:=9} 35 q) hload.final_bound
      (by omega) (by simp [writeNat,next]; decide)
    have hdiv := binary_runs n B 36 17 35 (s.natReg 17/q) .div x
      (selectedState s q) hjump.final_bound (by simp [selectedState]; omega) hcoB
      (by simp [selectedState]; decide)
      (by simp [selectedState,writeNat,next,evalNat, show q≠0 from (UniformSelectedCRT.radix_pos n i).ne'])
    refine ⟨5,?_,by omega⟩
    exact (((hbranch.trans hsel).trans hload).trans hjump).trans hdiv
  · have he : i=Fin.last (UniformWorkingLength.axisCount n) :=
      Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    have hbin : q=s.natReg 18 := by
      change UniformSelectedCRT.radices n i=s.natReg 18
      rw [he]; simp [UniformSelectedCRT.radices,hs.binary]
    have hodd : ¬s.natReg 30<s.natReg 10 := by rw [hs.index,hs.count]; exact hi
    have hsel := branch_runs n B 30 10 9 11 x {s with pc:=8}
      hbranch.final_bound (by omega) (by omega)
      (by change program[8]?=some (.branchLT 30 10 9 11); decide)
    simp only [ite_eq_right hodd] at hsel
    have hcopy := binary_runs n B 35 18 39 q .add x {s with pc:=11}
      hsel.final_bound (by simp; omega) hqB
      (by change program[11]?=some (.natBinary .add 35 18 39); decide)
      (by simp [evalNat,hs.zero,hbin])
    have hdiv := binary_runs n B 36 17 35 (s.natReg 17/q) .div x
      (selectedState s q) hcopy.final_bound (by simp [selectedState]; omega) hcoB
      (by simp [selectedState]; decide)
      (by simp [selectedState,writeNat,next,evalNat, show q≠0 from (UniformSelectedCRT.radix_pos n i).ne'])
    exact ⟨4,((hbranch.trans hsel).trans hcopy).trans hdiv,by omega⟩

theorem selected_values (n : ℕ) (saved : ℕ) (s : State)
    (i : Fin (UniformWorkingLength.axisCount n+1)) (hs : LoopData n saved i.val s) :
    (cofactorState s (UniformSelectedCRT.radices n i)).pc=13 ∧
    (cofactorState s (UniformSelectedCRT.radices n i)).natReg 35=UniformSelectedCRT.radices n i ∧
    (cofactorState s (UniformSelectedCRT.radices n i)).natReg 36=
      UniformCRT.cofactor (UniformSelectedCRT.radices n) i := by
  have he := UniformCRT.cofactor_eq_div (UniformSelectedCRT.radices n) i
    (UniformSelectedCRT.radix_pos n i)
  rw [UniformSelectedCRT.radices_product] at he
  simp [cofactorState,selectedState,writeNat,next,hs.length,he]

theorem inverse_phase (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (i : Fin (UniformWorkingLength.axisCount n+1))
    (hs : LoopData n saved i.val s) (hp : s.pc=13)
    (hQ : s.natReg 35=UniformSelectedCRT.radices n i)
    (hA : s.natReg 36=UniformCRT.cofactor (UniformSelectedCRT.radices n) i)
    (hb : WordBound B s)
    (hB : 3*UniformWorkingLength.workingLength n+
      5*UniformWorkingLength.axisCount n+128≤B) : ∃ t u,
    BoundedRuns program n x B s t u ∧ u.pc=29 ∧ LoopData n saved i.val u ∧
    u.natReg 35=UniformSelectedCRT.radices n i ∧
    u.natReg 36=UniformCRT.cofactor (UniformSelectedCRT.radices n) i ∧
    u.natReg 37=UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i ∧
    u.natHeap=s.natHeap ∧
    Frame (UniformWorkingLength.axisCount n) s u ∧
    t≤7*UniformSelectedCRT.radices n i+13 := by
  let q := UniformSelectedCRT.radices n i
  let a := UniformCRT.cofactor (UniformSelectedCRT.radices n) i
  have hqB : q≤B := (radix_bound n i).1.trans (by omega)
  have haB : a≤B := (radix_bound n i).2.trans (by omega)
  have hguard := branch_runs n B 31 35 14 42 x s hb (by omega) (by omega)
    (by simpa [hp] using (show program[13]?=some (.branchLT 31 35 14 42) by decide))
  by_cases hq : 1<q
  · have hgo : s.natReg 31<s.natReg 35 := by rw [hs.one,hQ]; exact hq
    simp only [ite_eq_left hgo] at hguard
    let s0 := writeNat {s with pc:=14} 0 a
    let s1 := writeNat s0 1 q
    have h0 := binary_runs n B 0 36 39 a .add x {s with pc:=14} hguard.final_bound
      (by simp; omega) haB (by change program[14]?=some (.natBinary .add 0 36 39); decide)
      (by simp [evalNat,hs.zero,hA,a])
    have h1 := binary_runs n B 1 35 39 q .add x s0 h0.final_bound
      (by simp [s0,writeNat,next]; omega) hqB
      (by simp [s0,writeNat,next]; decide)
      (by simp [s0,writeNat,next,evalNat,hs.zero,hQ,q])
    have hj := jump_runs n B 17 x s1 h1.final_bound (by omega)
      (by simp [s1,s0,writeNat,next]; decide)
    let entry := {s1 with pc:=0}
    have heB : WordBound B entry := changePC_bound B s1 0 h1.final_bound (by omega)
    have hiB : 3*(∏ j,UniformSelectedCRT.radices n j)+11≤B := by
      rw [UniformSelectedCRT.radices_product]; omega
    obtain ⟨v,hv,hdigit,hcost,hframe⟩ := UniformCRTMachine.crt_inverse_bounded n x
      (UniformSelectedCRT.radices n) (UniformSelectedCRT.radix_pos n)
      (UniformSelectedCRT.radices_pairwise n) i hq B entry hiB rfl
      (by simp [entry,s1,s0,writeNat,next,a])
      (by simp [entry,s1,writeNat,next,q]) heB
    have hplaced := execution_placed_same inverse_code
      (by change 17+11≤B; omega) (by omega : 28≤B) hv
    have he : UniformAssembly.placed 17 entry={s1 with pc:=17} := by
      simp [UniformAssembly.placed,entry]
    rw [he] at hplaced
    have hhigh : ∀ r,6≤r → v.natReg r=s.natReg r := by
      intro r hr
      exact (inverse_high n x entry v _ r hr hv.executes).trans
        (by have hne0 : r≠0 := by omega
            have hne1 : r≠1 := by omega
            simp [entry,s1,s0,writeNat,next,hne0,hne1])
    have hvData := hs.high hhigh
    have hvFrame : Frame (UniformWorkingLength.axisCount n) s {v with pc:=28} := by
      refine ⟨?_,?_,?_,?_,?_,fun r hr _ => hhigh r hr⟩
      · simpa [entry,s1,s0,writeNat,next] using hframe.1
      · simpa [entry,s1,s0,writeNat,next] using hframe.2.2.1
      · simpa [entry,s1,s0,writeNat,next] using hframe.2.2.2.1
      · simpa [entry,s1,s0,writeNat,next] using hframe.2.2.2.2
      · intro z _; simpa [entry,s1,s0,writeNat,next] using congrFun hframe.2.1 z
    let u := writeNat {v with pc:=28} 37 (UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i)
    have hcopy := binary_runs n B 37 3 39
      (UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i) .add x {v with pc:=28}
      hplaced.final_bound (by simp; omega)
      ((UniformCRT.inverseDigit_lt _ i (UniformSelectedCRT.radix_pos n i)).le.trans hqB)
      (by change program[28]?=some (.natBinary .add 37 3 39); decide)
      (by simp [evalNat,hdigit,hvData.zero])
    refine ⟨_,u,((((hguard.trans h0).trans h1).trans hj).trans hplaced).trans hcopy,
      rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · constructor <;> simp [u,writeNat,next,hvData.index,hvData.one,hvData.axes,
        hvData.pointer,hvData.zero,hvData.savedPrime,hvData.count,hvData.length,hvData.binary]
    · simpa [u,writeNat,next] using (hhigh 35 (by decide)).trans hQ
    · simpa [u,writeNat,next] using (hhigh 36 (by decide)).trans hA
    · simp [u,writeNat,next]
    · simpa [u,entry,s1,s0,writeNat,next] using hframe.2.1
    · exact frame_trans _ s _ u hvFrame (writeNat_frame _ _ 37 _ (by omega))
    · dsimp; omega
  · have hqone : q=1 := by have := UniformSelectedCRT.radix_pos n i; omega
    have hstop : ¬s.natReg 31<s.natReg 35 := by rw [hs.one,hQ]; omega
    simp only [ite_eq_right hstop] at hguard
    have hdigit : UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i=0 := by
      have h := UniformCRT.inverseDigit_lt (UniformSelectedCRT.radices n) i
        (UniformSelectedCRT.radix_pos n i)
      change _<q at h; omega
    have hz := literal_runs n B 37 0 x {s with pc:=42} hguard.final_bound
      (by simp; omega) (by omega)
      (by change program[42]?=some (.natLiteral 37 0); decide)
    have hj := jump_runs n B 29 x (writeNat {s with pc:=42} 37 0) hz.final_bound
      (by omega) (by simp [writeNat,next]; decide)
    let u := {writeNat s 37 0 with pc:=29}
    refine ⟨3,u,(hguard.trans hz).trans hj,rfl,?_,?_,?_,?_,rfl,?_,by omega⟩
    · constructor <;> simp [u,writeNat,next,hs.index,hs.one,hs.axes,hs.pointer,
        hs.zero,hs.savedPrime,hs.count,hs.length,hs.binary]
    · simpa [u,writeNat,next] using hQ
    · simpa [u,writeNat,next] using hA
    · simp [u,writeNat,next,hdigit]
    · exact writeNat_frame _ s 37 0 (by omega)

def RowTable (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n+1)) (s : State) : Prop :=
  s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 0)=
      some (UniformSelectedCRT.radices n i) ∧
  s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 1)=
      some (UniformCRT.cofactor (UniformSelectedCRT.radices n) i) ∧
  s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 2)=
      some (UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i) ∧
  s.natHeap (tableAddress (UniformWorkingLength.axisCount n) i.val 3)=
      some (UniformCRT.idempotent (UniformSelectedCRT.radices n) i)

def PartialTable (n j : ℕ) (s : State) : Prop :=
  ∀ i : Fin (UniformWorkingLength.axisCount n+1),i.val<j → RowTable n i s

def finishedRow (s : State) (i idem : ℕ) : State :=
  {writeNat (savePrefix (writeNat s 38 idem) 4) 30 (i+1) with pc:=7}

theorem save_phase (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (i : Fin (UniformWorkingLength.axisCount n+1))
    (hs : LoopData n saved i.val s) (hp : s.pc=29)
    (hQ : s.natReg 35=UniformSelectedCRT.radices n i)
    (hA : s.natReg 36=UniformCRT.cofactor (UniformSelectedCRT.radices n) i)
    (hI : s.natReg 37=UniformCRT.inverseDigit (UniformSelectedCRT.radices n) i)
    (hb : WordBound B s)
    (hB : 3*UniformWorkingLength.workingLength n+
      5*UniformWorkingLength.axisCount n+128≤B) :
    let u := finishedRow s i.val (UniformCRT.idempotent (UniformSelectedCRT.radices n) i)
    BoundedRuns program n x B s 11 u ∧ u.pc=7 ∧
    LoopData n saved (i.val+1) u ∧ RowTable n i u ∧
    (∀ a,a<tableAddress (UniformWorkingLength.axisCount n) i.val 0 → u.natHeap a=s.natHeap a) ∧
    Frame (UniformWorkingLength.axisCount n) s u := by
  let idem := UniformCRT.idempotent (UniformSelectedCRT.radices n) i
  let d := writeNat s 38 idem
  let z := savePrefix d 4
  have hidB : idem≤B := by
    have h := UniformCRT.idempotent_lt (UniformSelectedCRT.radices n)
      (UniformSelectedCRT.radix_pos n) i
    rw [UniformSelectedCRT.radices_product] at h
    dsimp [idem]; omega
  have hptr : d.natReg 34+4≤B := by
    have := i.isLt
    simp only [d,writeNat,next,Function.update_of_ne (by decide : (34:ℕ)≠38),hs.pointer,tableAddress]
    omega
  have hpD : d.pc=30 := by simp [d,writeNat,next,hp]
  have hprod := binary_runs n B 38 36 37 idem .mul x s hb (by omega) hidB
    (by simpa [hp] using (show program[29]?=some (.natBinary .mul 38 36 37) by decide))
    (by simp [evalNat,idem,UniformCRT.idempotent,hA,hI])
  have hsave := savePrefix_runs n B 4 x d hprod.final_bound (le_refl _)
    hpD (by simp [d,writeNat,next,hs.one]) (by omega) hptr
  have hzPC : z.pc=38 := by simpa [hpD] using savePrefix_pc d 4
  have hzIndex : z.natReg 30=i.val := by rw [savePrefix_reg d 4 30 (by decide)]; simp [d,writeNat,next,hs.index]
  have hzOne : z.natReg 31=1 := by rw [savePrefix_reg d 4 31 (by decide)]; simp [d,writeNat,next,hs.one]
  have hiB : i.val+1≤B := by have := i.isLt; omega
  have hindex := binary_runs n B 30 30 31 (i.val+1) .add x z hsave.final_bound
    (by omega) hiB (by simpa [hzPC] using
      (show program[38]?=some (.natBinary .add 30 30 31) by decide))
    (by simp [evalNat,hzIndex,hzOne])
  have hjump := jump_runs n B 7 x (writeNat z 30 (i.val+1)) hindex.final_bound (by omega)
    (by simp [writeNat,next,hzPC]; decide)
  refine ⟨(hprod.trans hsave).trans (hindex.trans hjump),rfl,?_,?_,?_,?_⟩
  · constructor
    · simp [finishedRow,writeNat,next]
    · change z.natReg 31=1
      exact hzOne
    · change z.natReg 32=UniformWorkingLength.axisCount n+1
      rw [savePrefix_reg d 4 32 (by decide)]
      simpa [d,writeNat,next] using hs.axes
    · change z.natReg 34=tableAddress (UniformWorkingLength.axisCount n) (i.val+1) 0
      rw [savePrefix_pointer]
      simp [d,writeNat,next,hs.pointer,tableAddress]
      omega
    · change z.natReg 39=0
      rw [savePrefix_reg d 4 39 (by decide)]
      simpa [d,writeNat,next] using hs.zero
    · change z.natReg 41=saved
      rw [savePrefix_reg d 4 41 (by decide)]
      simpa [d,writeNat,next] using hs.savedPrime
    · change z.natReg 10=UniformWorkingLength.axisCount n
      rw [savePrefix_reg d 4 10 (by decide)]
      simpa [d,writeNat,next] using hs.count
    · change z.natReg 17=UniformWorkingLength.workingLength n
      rw [savePrefix_reg d 4 17 (by decide)]
      simpa [d,writeNat,next] using hs.length
    · change z.natReg 18=UniformWorkingLength.binaryFactor n
      rw [savePrefix_reg d 4 18 (by decide)]
      simpa [d,writeNat,next] using hs.binary
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [RowTable,finishedRow,d,writeNat,next,hs.pointer,tableAddress,hQ] using savePrefix_fields d 0
    · simpa [RowTable,finishedRow,d,writeNat,next,hs.pointer,tableAddress,hA,Nat.add_assoc] using savePrefix_fields d 1
    · simpa [RowTable,finishedRow,d,writeNat,next,hs.pointer,tableAddress,hI,Nat.add_assoc] using savePrefix_fields d 2
    · simpa [RowTable,finishedRow,d,writeNat,next,hs.pointer,tableAddress,idem,Nat.add_assoc] using savePrefix_fields d 3
  · intro a ha
    exact savePrefix_before d 4 a (by simpa [d,writeNat,next,hs.pointer] using ha)
  · have hdf := writeNat_frame (UniformWorkingLength.axisCount n) s 38 idem (by omega)
    have hzf : Frame (UniformWorkingLength.axisCount n) d z := by
      refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
      · intro a ha
        exact savePrefix_before d 4 a (by simp [d,writeNat,next,hs.pointer,tableAddress]; omega)
      · intro r hr hp
        exact savePrefix_reg d 4 r (by omega)
    exact frame_trans _ s z _ (frame_trans _ s d z hdf hzf)
      (writeNat_frame _ z 30 (i.val+1) (by omega))

theorem row_runs (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (i : Fin (UniformWorkingLength.axisCount n+1))
    (hs : LoopData n saved i.val s) (hp : s.pc=7)
    (ht : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s)
    (hpartial : PartialTable n i.val s) (hb : WordBound B s)
    (hB : 3*UniformWorkingLength.workingLength n+
      5*UniformWorkingLength.axisCount n+128≤B) : ∃ t u,
    BoundedRuns program n x B s t u ∧ u.pc=7 ∧ LoopData n saved (i.val+1) u ∧
    PartialTable n (i.val+1) u ∧ Frame (UniformWorkingLength.axisCount n) s u ∧
    t≤7*UniformSelectedCRT.radices n i+29 := by
  obtain ⟨ts,hsel,hcs⟩ := select_runs n B saved x s i hs hp ht hb (by omega) (by omega)
  have hd := selected_data hs (UniformSelectedCRT.radices n i)
  obtain ⟨hpc,hq,ha⟩ := selected_values n saved s i hs
  obtain ⟨ti,v,hiv,hvp,hvd,hvq,hva,hvi,hheap,hvf,hci⟩ := inverse_phase n B saved x _ i
    hd hpc hq ha hsel.final_bound hB
  obtain ⟨hsv,hup,hud,hrow,hbefore,huf⟩ := save_phase n B saved x v i hvd hvp hvq hva hvi
    hiv.final_bound hB
  refine ⟨ts+ti+11,_,(hsel.trans hiv).trans hsv,hup,hud,?_,?_,by omega⟩
  · intro j hj
    by_cases he : j=i
    · subst j; exact hrow
    · have hji : j.val < i.val := by
        have hne : j.val≠i.val := fun h => he (Fin.ext h)
        omega
      have hold := hpartial j hji
      have heq (field : ℕ) (hf : field≤3) :
          (finishedRow v i.val (UniformCRT.idempotent (UniformSelectedCRT.radices n) i)).natHeap
            (tableAddress (UniformWorkingLength.axisCount n) j.val field)=
            s.natHeap (tableAddress (UniformWorkingLength.axisCount n) j.val field) := by
        rw [hbefore _ (by simp [tableAddress]; omega),hheap]
        rfl
      simpa only [RowTable,heq 0 (by decide),heq 1 (by decide),heq 2 (by decide),heq 3 (by decide)] using hold
  · exact frame_trans _ s _ _ (frame_trans _ s _ _
      (selected_frame _ s (UniformSelectedCRT.radices n i)) hvf) huf

def rowBudget (n : ℕ) : ℕ := 7*(128*(UniformWorkingLength.axisCount n+2)^2)+29
def preparationBudget (n : ℕ) : ℕ := 1000*(UniformWorkingLength.axisCount n+2)^3

theorem terminal_execution (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (hs : LoopData n saved (UniformWorkingLength.axisCount n+1) s) (hp : s.pc=7)
    (hpartial : PartialTable n (UniformWorkingLength.axisCount n+1) s)
    (hb : WordBound B s) (hB : 44≤B) : ∃ u,
    BoundedExecution program n x B s 3 u ∧ u.pc=41 ∧ u.natReg 0=saved ∧
    CRTTable n u ∧ Frame (UniformWorkingLength.axisCount n) s u := by
  have hstop : ¬s.natReg 30<s.natReg 32 := by rw [hs.index,hs.axes]; omega
  have hg := branch_runs n B 30 32 8 40 x s hb (by omega) (by omega)
    (by simpa [hp] using (show program[7]?=some (.branchLT 30 32 8 40) by decide))
  simp only [ite_eq_right hstop] at hg
  have hcopy := binary_runs n B 0 41 39 saved .add x {s with pc:=40} hg.final_bound
    (by simp; omega) (by rw [← hs.savedPrime]; exact hb.2.1 41)
    (by change program[40]?=some (.natBinary .add 0 41 39); decide)
    (by simp [evalNat,hs.savedPrime,hs.zero])
  let u := writeNat {s with pc:=40} 0 saved
  have hc41 : program[41]?=some .halt := by decide
  have hh : BoundedExecution program n x B u 1 u := .halt hcopy.final_bound
    (by simp [step,u,writeNat,next,hc41])
  refine ⟨u,hg.executes (hcopy.executes hh),rfl,?_,?_,?_⟩
  · simp [u,writeNat,next]
  · intro i
    exact hpartial i i.isLt
  · exact writeNat_frame _ s 0 saved (by omega)

/-- Proof fuel is absent from the literal program; its guard stops at the
stored axis count. Every row reads and writes actual heap addresses. -/
theorem loop_execution {n : ℕ} (hn : 0<n) (B saved : ℕ) (x : Fin n → ℂ)
    (fuel i : ℕ) (s : State) (hi : i≤UniformWorkingLength.axisCount n+1)
    (hf : UniformWorkingLength.axisCount n+1-i≤fuel)
    (hs : LoopData n saved i s) (hp : s.pc=7)
    (ht : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s)
    (hpartial : PartialTable n i s) (hb : WordBound B s)
    (hB : 3*UniformWorkingLength.workingLength n+
      5*UniformWorkingLength.axisCount n+128≤B) : ∃ t u,
    BoundedExecution program n x B s t u ∧ u.pc=41 ∧ u.natReg 0=saved ∧
    CRTTable n u ∧ Frame (UniformWorkingLength.axisCount n) s u ∧
    t≤(UniformWorkingLength.axisCount n+1-i)*rowBudget n+3 := by
  induction fuel generalizing i s with
  | zero =>
      have he : i=UniformWorkingLength.axisCount n+1 := by omega
      subst i
      obtain ⟨u,hu,hpc,h0,htab,hfr⟩ := terminal_execution n B saved x s hs hp hpartial hb (by omega)
      exact ⟨3,u,hu,hpc,h0,htab,hfr,by simp⟩
  | succ fuel ih =>
      by_cases he : i=UniformWorkingLength.axisCount n+1
      · subst i
        obtain ⟨u,hu,hpc,h0,htab,hfr⟩ := terminal_execution n B saved x s hs hp hpartial hb (by omega)
        exact ⟨3,u,hu,hpc,h0,htab,hfr,by simp⟩
      · have hi' : i<UniformWorkingLength.axisCount n+1 := by omega
        let index : Fin (UniformWorkingLength.axisCount n+1) := ⟨i,hi'⟩
        obtain ⟨tr,v,hr,hvp,hvd,hvt,hvr,hcr⟩ := row_runs n B saved x s index hs hp ht hpartial hb hB
        have ht' : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) v := by
          intro j hj
          rw [hvr.2.2.2.2.1 j hj]
          exact ht j hj
        obtain ⟨tt,u,hu,hup,h0,htab,huf,hct⟩ := ih (i+1) v (by omega) (by omega)
          hvd hvp ht' hvt hr.final_bound
        refine ⟨tr+tt,u,hr.executes hu,hup,h0,htab,frame_trans _ s v u hvr huf,?_⟩
        have hq := UniformSelectedCRT.radix_quadratic hn index
        have hrB : tr≤rowBudget n := by dsimp [rowBudget]; omega
        have hadd := Nat.add_le_add hrB hct
        have heq : rowBudget n+((UniformWorkingLength.axisCount n+1-(i+1))*rowBudget n+3)=
            (UniformWorkingLength.axisCount n+1-i)*rowBudget n+3 := by
          rw [show UniformWorkingLength.axisCount n+1-i=
            (UniformWorkingLength.axisCount n+1-(i+1))+1 by omega,Nat.add_mul]
          simp; omega
        exact hadd.trans_eq heq

theorem preparation_cost (n : ℕ) :
    7+(UniformWorkingLength.axisCount n+1)*rowBudget n+3≤preparationBudget n := by
  let p := UniformWorkingLength.axisCount n+2
  have hp : 2≤p := by omega
  have hp2 : 4≤p^2 := by nlinarith
  have hc : rowBudget n≤925*p^2 := by
    change 7*(128*p^2)+29≤925*p^2
    nlinarith
  have hm : (UniformWorkingLength.axisCount n+1)*rowBudget n≤925*p^3 := calc
    _ ≤ p*rowBudget n := Nat.mul_le_mul_right _ (by omega)
    _ ≤ p*(925*p^2) := Nat.mul_le_mul_left p hc
    _ = _ := by ring
  have hp3 : 8≤p^3 := by
    have h := Nat.pow_le_pow_left hp 3
    norm_num at h
    exact h
  dsimp [preparationBudget]
  change 7+_+3≤1000*p^3
  nlinarith

/-- Actual post-header execution, without a prepared CRT-table premise. The
entry-only empty-tail predicate is replaced by Header plus populated CRTTable. -/
theorem post_header_execution {n : ℕ} (hn : 0<n) (B : ℕ) (x : Fin n → ℂ)
    (s : State) (hwork : UniformWorkingCompletion.PreparedState n s) (hp : s.pc=0)
    (hb : WordBound B s) (hB : 3*UniformWorkingLength.workingLength n+
      5*UniformWorkingLength.axisCount n+128≤B) : ∃ t u,
    BoundedExecution program n x B s t u ∧ Header n u ∧ CRTTable n u ∧
    Frame (UniformWorkingLength.axisCount n) s u ∧ u.pc=41 ∧ t≤preparationBudget n := by
  have h10 := hwork.1.2.1
  have h17 := hwork.2.2.2
  have h18 := hwork.2.2.1
  have hstart := startup_runs n B x s hb hp (by omega) (by rw [h10]; omega)
  have hd := initialized_data n s h10 h17 h18
  have hpc : (initialized s).pc=7 := by simp [initialized,writeNat,next,hp]
  have htab : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) (initialized s) :=
    hwork.1.2.2.2.1
  obtain ⟨tl,u,hu,hup,h0,hcrt,hfr,hcost⟩ := loop_execution hn B (s.natReg 0) x
    (UniformWorkingLength.axisCount n+1) 0 (initialized s) (by omega) (by omega)
    hd hpc htab (by intro i hi; omega) hstart.final_bound hB
  have hf := frame_trans _ s (initialized s) u (initialized_frame _ s) hfr
  refine ⟨7+tl,u,hstart.executes hu,?_,hcrt,hf,hup,?_⟩
  · refine ⟨h0.trans hwork.1.1,?_,?_,?_,?_,?_,?_⟩
    · exact (hf.2.2.2.2.2 10 (by decide) (by omega)).trans h10
    · exact (hf.2.2.2.2.2 11 (by decide) (by omega)).trans hwork.1.2.2.1
    · exact (hf.2.2.2.2.2 16 (by decide) (by omega)).trans hwork.2.1
    · exact (hf.2.2.2.2.2 17 (by decide) (by omega)).trans h17
    · exact (hf.2.2.2.2.2 18 (by decide) (by omega)).trans h18
    · intro j hj
      rw [hf.2.2.2.2.1 j hj]
      exact hwork.1.2.2.2.1 j hj
  · have hc := preparation_cost n
    simp only [Nat.sub_zero] at hcost
    omega

theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hb : (fun n : ℕ => (preparationBudget n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^3) := by
    apply Asymptotics.IsBigO.of_bound 1000
    filter_upwards [] with n
    simp [preparationBudget]
  have hlog := hb.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 3)
  have hlittle : (fun n : ℕ => Real.log (n:ℝ)^3) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact hlog.trans_isLittleO hlittle

theorem post_wordBound_setup {n : ℕ} (hn : 0<n) :
    3*UniformWorkingLength.workingLength n+5*UniformWorkingLength.axisCount n+128≤(n+2)^14 := by
  have hL := UniformWorkingLength.workingLength_upper hn
  have hell : UniformWorkingLength.axisCount n≤2*n := by
    have h := UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have h13 : 128≤(n+2)^13 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 13
    norm_num at h
    omega
  have hp := Nat.mul_le_mul_left (n+2) h13
  rw [show (n+2)^14=(n+2)*(n+2)^13 by ring] 
  nlinarith

/-- One fixed program starts from the actual initial state, retains the single
master-root/constant preparation, and then populates the CRT header. -/
def fullProgram : Program := UniformAssembly.embed
  (UniformCConstantsMachine.program.map (UniformAssembly.relocate 0 105))
  program [.halt] 149

theorem constants_code : UniformAssembly.CodeAt UniformCConstantsMachine.program fullProgram 0 105 := by
  intro i hi
  simp only [fullProgram,UniformAssembly.embed,Nat.zero_add]
  rw [List.getElem?_append_left (by
    simp only [List.length_append,List.length_map]; omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem header_code : UniformAssembly.CodeAt program fullProgram 105 149 :=
  UniformAssembly.embed_code _ _ _ _

theorem fullProgram_length : fullProgram.length=150 := by
  rw [fullProgram,UniformAssembly.embed_length,List.length_map,
    UniformCConstantsMachine.program_length,program_length]
  rfl

theorem full_finish_code : fullProgram[149]?=some .halt := by
  simp only [fullProgram,UniformAssembly.embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformCConstantsMachine.program_length,program_length]; omega)]
  simp only [List.length_append,List.length_map,UniformCConstantsMachine.program_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def fullPreparationBudget (n : ℕ) : ℕ :=
  UniformCConstantsMachine.preparationBudget n+preparationBudget n+1

theorem full_wordBound_setup {n : ℕ} (hn : 0<n) :
    105+(n+2)^14≤(n+2)^15 ∧ 150≤(n+2)^15 := by
  have h14 : 105≤(n+2)^14 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 14
    norm_num at h
    omega
  rw [show (n+2)^15=(n+2)^14*(n+2) from pow_succ _ 14]
  constructor <;> nlinarith

/-- Closed actual initial-state execution. No table, inverse, factorization or
prepared-value premise is supplied by the caller. All header operations and
both composition jumps are included in the charged trace. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^15) initial t u ∧
    Header n u ∧ CRTTable n u ∧ u.natReg 24=UniformMasterRootMachine.order n ∧
    u.natReg 8=n ∧
    (∀ j : Fin 6,u.scalarHeap j.val=some (UniformPairMachine.prepared
      (UniformCConstantsMachine.bank n j))) ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=149 ∧ t≤fullPreparationBudget n := by
  obtain ⟨hBC,hfinishB⟩ := full_wordBound_setup hn
  obtain ⟨tc,v,hv,hwork,horder,h8,_ha,_hb,hbank,hroots,hout,_hpc,hcost⟩ :=
    UniformCConstantsMachine.preparation_execution hn x
  let entry := {v with pc:=0}
  have heB : WordBound ((n+2)^14) entry := changePC_bound _ v 0 hv.final_bound (by omega)
  obtain ⟨th,u,hu,hheader,hcrt,hframe,_hup,hbudget⟩ := post_header_execution hn ((n+2)^14)
    x entry hwork rfl heB (post_wordBound_setup hn)
  have hprefix : BoundedRuns fullProgram n x ((n+2)^15) initial tc {v with pc:=105} := by
    have h := UniformAssembly.BoundedExecution.placed constants_code
      (by omega : 0+(n+2)^14≤(n+2)^15) (by omega : 105≤(n+2)^15) hv
    simpa [UniformAssembly.placed,initial] using h
  have htail : BoundedRuns fullProgram n x ((n+2)^15) {v with pc:=105} th {u with pc:=149} := by
    have h := UniformAssembly.BoundedExecution.placed header_code hBC (by omega : 149≤(n+2)^15) hu
    simpa [UniformAssembly.placed,entry] using h
  let final := {u with pc:=149}
  have hc := full_finish_code
  have hh : BoundedExecution fullProgram n x ((n+2)^15) final 1 final :=
    .halt htail.final_bound (by simp [step,final,hc])
  refine ⟨tc+th+1,final,(hprefix.trans htail).executes hh,hheader,hcrt,?_,?_,?_,?_,?_,rfl,?_⟩
  · exact (hframe.2.2.2.2.2 24 (by decide) (by omega)).trans horder
  · exact (hframe.2.2.2.2.2 8 (by decide) (by omega)).trans h8
  · intro j
    change u.scalarHeap j.val=_
    rw [hframe.2.1]
    exact hbank j
  · exact hframe.2.2.2.1.trans hroots
  · exact hframe.2.2.1.trans hout
  · dsimp [fullPreparationBudget]; omega

theorem fullPreparationBudget_isLittleO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have h1 : (fun _n : ℕ => (1:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (1:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  have h := (UniformCConstantsMachine.preparationBudget_isLittleO_input.add
    preparationBudget_isLittleO_input).add h1
  simpa [fullPreparationBudget,Nat.cast_add] using h

end
end ExactFourierCircuits.UniformCRTHeaderMachine
