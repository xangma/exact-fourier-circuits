import UniformPairDiagonalMachine
import UniformCConstantsMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformHadamardPairMachine
open UniformMachine UniformAssembly UniformPairMachine
noncomputable section

def rightProgram : Program :=
  [.scalarLiteral 0 1,.natLiteral 2 4,.loadScalar 1 2,.halt]

def loadProgram (left right : ℕ) : Program :=
  [.natLiteral 2 left,.loadScalar 0 2,.natLiteral 2 right,.loadScalar 1 2,.halt]

def rightState (s : State) : State :=
  writeScalar (writeNat (writeScalar s 0 (prepared 1)) 2 4) 1 (prepared Complex.I)

def loadState (s : State) (left right : ℕ) (c d : ℂ) : State :=
  writeScalar (writeNat (writeScalar (writeNat s 2 left) 0 (prepared c)) 2 right) 1 (prepared d)

theorem right_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=0) (hi : s.scalarHeap 4=some (prepared Complex.I))
    (hB : 4≤B) (hs : WordBound B s) :
    BoundedExecution rightProgram n x B s 4 (rightState s) := by
  have h1 := writeScalar_bound B s 0 (prepared 1) hs (by omega)
  have h2 := writeNat_bound B (writeScalar s 0 (prepared 1)) 2 4 h1
    (by simp [writeScalar,next,hp];omega) hB
  have h3 := writeScalar_bound B (writeNat (writeScalar s 0 (prepared 1)) 2 4)
    1 (prepared Complex.I) h2 (by simp [writeScalar,writeNat,next,hp];omega)
  refine .next hs (u:=writeScalar s 0 (prepared 1)) ?_
    (.next h1 (u:=writeNat (writeScalar s 0 (prepared 1)) 2 4) ?_
      (.next h2 (u:=rightState s) ?_ (.halt h3 ?_)))
  all_goals simp [step,rightProgram,rightState,writeScalar,writeNat,next,hp,hi,prepared]

theorem load_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (left right : ℕ) (c d : ℂ) (hp : s.pc=0)
    (hc : s.scalarHeap left=some (prepared c)) (hd : s.scalarHeap right=some (prepared d))
    (hB : 5≤B) (hl : left≤B) (hr : right≤B) (hs : WordBound B s) :
    BoundedExecution (loadProgram left right) n x B s 5 (loadState s left right c d) := by
  have h1 := writeNat_bound B s 2 left hs (by omega) hl
  have h2 := writeScalar_bound B (writeNat s 2 left) 0 (prepared c) h1
    (by simp [writeNat,next,hp];omega)
  have h3 := writeNat_bound B (writeScalar (writeNat s 2 left) 0 (prepared c)) 2 right h2
    (by simp [writeNat,writeScalar,next,hp];omega) hr
  have h4 := writeScalar_bound B
    (writeNat (writeScalar (writeNat s 2 left) 0 (prepared c)) 2 right) 1 (prepared d) h3
    (by simp [writeNat,writeScalar,next,hp];omega)
  refine .next hs (u:=writeNat s 2 left) ?_
    (.next h1 (u:=writeScalar (writeNat s 2 left) 0 (prepared c)) ?_
      (.next h2 (u:=writeNat (writeScalar (writeNat s 2 left) 0 (prepared c)) 2 right) ?_
        (.next h3 (u:=loadState s left right c d) ?_ (.halt h4 ?_))))
  all_goals simp [step,loadProgram,loadState,writeNat,writeScalar,next,hp,hc,hd]

def program : Program :=
  rightProgram.map (relocate 0 4) ++
  UniformPairDiagonalMachine.program.map (relocate 4 11) ++
  (loadProgram 1 2).map (relocate 11 16) ++
  UniformPairMachine.program.map (relocate 16 27) ++
  (loadProgram 3 5).map (relocate 27 32) ++
  UniformPairDiagonalMachine.program.map (relocate 32 39) ++ [.halt]

theorem program_length : program.length=40 := rfl

theorem right_code : CodeAt rightProgram program 0 4 := by
  intro i hi; change i<4 at hi; interval_cases i <;> rfl

theorem first_diagonal_code : CodeAt UniformPairDiagonalMachine.program program 4 11 := by
  intro i hi; change i<7 at hi; interval_cases i <;> rfl

theorem C_load_code : CodeAt (loadProgram 1 2) program 11 16 := by
  intro i hi; change i<5 at hi; interval_cases i <;> rfl

theorem C_code : CodeAt UniformPairMachine.program program 16 27 := by
  intro i hi; change i<11 at hi; interval_cases i <;> rfl

theorem diagonal_load_code : CodeAt (loadProgram 3 5) program 27 32 := by
  intro i hi; change i<5 at hi; interval_cases i <;> rfl

theorem last_diagonal_code : CodeAt UniformPairDiagonalMachine.program program 32 39 := by
  intro i hi; change i<7 at hi; interval_cases i <;> rfl


/-- Everything outside the pair, including the persistent constant bank, is framed. -/
def Protected (s t : State) : Prop :=
  (∀ r, r≠2 → t.natReg r=s.natReg r) ∧ t.natHeap=s.natHeap ∧
  t.outputs=s.outputs ∧ t.rootOrders=s.rootOrders ∧
  (∀ i, i≠s.natReg 0 → i≠s.natReg 1 → t.scalarHeap i=s.scalarHeap i) ∧
  ∀ r, 8≤r → t.scalarReg r=s.scalarReg r

def reset (s : State) : State := {s with pc:=0}

def Constants (s : State) : Prop :=
  s.scalarHeap 1=some (prepared a) ∧ s.scalarHeap 2=some (prepared b) ∧
  s.scalarHeap 3=some (prepared a⁻¹) ∧ s.scalarHeap 4=some (prepared Complex.I) ∧
  s.scalarHeap 5=some (prepared (Complex.I*a⁻¹))

theorem protected_reset (s : State) : Protected s (reset s) := by
  simp [Protected,reset]

theorem Protected.trans {s t u : State} (h : Protected s t) (h' : Protected t u) :
    Protected s u := by
  obtain ⟨hn,hh,ho,hr,hheap,hs⟩:=h
  obtain ⟨hn',hh',ho',hr',hheap',hs'⟩:=h'
  refine ⟨fun r h=> (hn' r h).trans (hn r h),hh'.trans hh,ho'.trans ho,
    hr'.trans hr,?_,fun r h=> (hs' r h).trans (hs r h)⟩
  intro i h0 h1
  rw [hheap' i (by simpa [hn 0 (by decide)] using h0)
    (by simpa [hn 1 (by decide)] using h1),hheap i h0 h1]

theorem protected_right (s : State) : Protected s (rightState s) := by
  simp [Protected,rightState,writeScalar,writeNat,next]
  constructor
  · intro r hr; simp [hr]
  · intro r hr; simp [show r≠0 by omega,show r≠1 by omega]

theorem protected_load (s : State) (left right : ℕ) (c d : ℂ) :
    Protected s (loadState s left right c d) := by
  simp [Protected,loadState,writeScalar,writeNat,next]
  constructor
  · intro r hr; simp [hr]
  · intro r hr; simp [show r≠0 by omega,show r≠1 by omega]

theorem protected_diagonal (s : State) (c d : ℂ) (u v : Scalar) :
    Protected s (UniformPairDiagonalMachine.finalState s c d u v) := by
  have hf:=UniformPairDiagonalMachine.final_frame s c d u v
  refine ⟨fun r _=> congrFun hf.1 r,hf.2.1,hf.2.2.1,hf.2.2.2.1,
    UniformPairDiagonalMachine.untouched s c d u v,?_⟩
  intro r hr;exact hf.2.2.2.2 r (Or.inr (by omega))

theorem protected_C (s : State) (c d : ℂ) (u v : Scalar) :
    Protected s (UniformPairMachine.finalState s c d u v) := by
  have hf:=UniformPairMachine.final_frame s c d u v
  exact ⟨fun r _=> congrFun hf.1 r,hf.2.1,hf.2.2.1,hf.2.2.2.1,
    UniformPairMachine.untouched s c d u v,fun r hr=>hf.2.2.2.2 r (Or.inr hr)⟩

theorem Constants.protected {s t : State} (h : Constants s) (hf : Protected s t)
    (h0 : 6 ≤ s.natReg 0) (h1 : 6 ≤ s.natReg 1) : Constants t := by
  obtain ⟨ha,hb,hc,hi,hd⟩:=h
  have hp (i : ℕ) (hi : i<6) : t.scalarHeap i=s.scalarHeap i :=
    hf.2.2.2.2.1 i (by omega) (by omega)
  simpa only [Constants,hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    hp 4 (by decide),hp 5 (by decide)] using (show Constants s from ⟨ha,hb,hc,hi,hd⟩)

theorem factorization : diagonal a⁻¹ (Complex.I*a⁻¹)*C*S=H := by
  have hd : diagonal a⁻¹ (Complex.I*a⁻¹)=a⁻¹ • S := by
    ext i j;fin_cases i <;> fin_cases j <;> simp [diagonal,S]
    ring
  rw [hd,Matrix.smul_mul,Matrix.smul_mul,S_C_S,smul_smul,
    inv_mul_cancel₀ a_ne_zero,one_smul]

theorem left_value (u v : Scalar) :
    product a⁻¹ (combine a b (product 1 u) (product Complex.I v)) =
      ⟨u.value+v.value,u.dependent || v.dependent⟩ := by
  have h:=congrFun (congrArg (fun M : Mat2=>M.mulVec ![u.value,v.value]) factorization) 0
  simpa [← Matrix.mulVec_mulVec,diagonal,C,S,H,Matrix.mulVec,dotProduct,
    Fin.sum_univ_two,product,combine,mul_add,mul_assoc] using congrArg (fun z : ℂ=>
      (⟨z,u.dependent || v.dependent⟩ : Scalar)) h

theorem right_value (u v : Scalar) :
    product (Complex.I*a⁻¹) (combine b a (product 1 u) (product Complex.I v)) =
      ⟨u.value-v.value,u.dependent || v.dependent⟩ := by
  have h:=congrFun (congrArg (fun M : Mat2=>M.mulVec ![u.value,v.value]) factorization) 1
  simpa [← Matrix.mulVec_mulVec,diagonal,C,S,H,Matrix.mulVec,dotProduct,
    Fin.sum_univ_two,product,combine,sub_eq_add_neg,mul_add,mul_assoc] using congrArg (fun z : ℂ=>
      (⟨z,u.dependent || v.dependent⟩ : Scalar)) h


/-- The same fixed program works for every input length and arbitrary initialized
pair data, with all bank loads and continuation jumps included in its forty steps. -/
theorem bounded_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (u v : Scalar) (hp : s.pc=0) (hc : Constants s) (hs : WordBound B s) (hB : 11≤B)
    (h0 : 6 ≤ s.natReg 0) (h1 : 6 ≤ s.natReg 1) (hne : s.natReg 0≠s.natReg 1)
    (hu : s.scalarHeap (s.natReg 0)=some u) (hv : s.scalarHeap (s.natReg 1)=some v) :
    ∃ t, BoundedExecution program n x (B+40) s 40 t ∧ Protected s t ∧ Constants t ∧
      t.scalarHeap (s.natReg 0)=some ⟨u.value+v.value,u.dependent || v.dependent⟩ ∧
      t.scalarHeap (s.natReg 1)=some ⟨u.value-v.value,u.dependent || v.dependent⟩ ∧ t.pc=39 := by
  let s1:=rightState s
  have ex1:=right_execution n x B s hp hc.2.2.2.1 (by omega) hs
  have f1 : Protected s s1:=protected_right s
  let t1:=reset s1
  have hb1 : WordBound B t1:=changePC_bound B s1 0 ex1.final_bound (by omega)
  have hn1 : t1.natReg 0≠t1.natReg 1 := by
    simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hne
  have hr1 : Ready 1 Complex.I u v t1 := by
    constructor
    · rfl
    · simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hu
    · simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hv
    · simp [t1,s1,reset,rightState,writeScalar,writeNat,next]
    · simp [t1,s1,reset,rightState,writeScalar,writeNat,next]
  let s2:=UniformPairDiagonalMachine.finalState t1 1 Complex.I u v
  have ex2:=UniformPairDiagonalMachine.bounded_execution n x B t1 1 Complex.I u v hr1 (by omega) hb1
  have f2 : Protected s s2:=(f1.trans (protected_reset s1)).trans (protected_diagonal _ _ _ _ _)
  have c2:=hc.protected f2 h0 h1
  have hv2 : s2.scalarHeap (s.natReg 0)=some (product 1 u) ∧
      s2.scalarHeap (s.natReg 1)=some (product Complex.I v) := by
    simpa [s2,t1,s1,reset,rightState,writeScalar,writeNat,next] using
      UniformPairDiagonalMachine.final_values t1 1 Complex.I u v hn1
  let t2:=reset s2
  let s3:=loadState t2 1 2 a b
  have hb2 : WordBound B t2:=changePC_bound B s2 0 ex2.final_bound (by omega)
  have ex3:=load_execution n x B t2 1 2 a b rfl c2.1 c2.2.1 (by omega) (by omega) (by omega) hb2
  have f3 : Protected s s3:=(f2.trans (protected_reset s2)).trans (protected_load _ _ _ _ _)
  let t3:=reset s3
  have hb3 : WordBound B t3:=changePC_bound B s3 0 ex3.final_bound (by omega)
  have hn3 : t3.natReg 0≠t3.natReg 1 := by
    simpa [t3,reset,f3.1 0 (by decide),f3.1 1 (by decide)] using hne
  have hr3 : Ready a b (product 1 u) (product Complex.I v) t3 := by
    constructor
    · rfl
    · simpa [t3,s3,t2,reset,loadState,writeScalar,writeNat,next,f2.1 0 (by decide)] using hv2.1
    · simpa [t3,s3,t2,reset,loadState,writeScalar,writeNat,next,f2.1 1 (by decide)] using hv2.2
    · simp [t3,s3,reset,loadState,writeScalar,writeNat,next]
    · simp [t3,s3,reset,loadState,writeScalar,writeNat,next]
  let U:=combine a b (product 1 u) (product Complex.I v)
  let V:=combine b a (product 1 u) (product Complex.I v)
  let s4:=UniformPairMachine.finalState t3 a b (product 1 u) (product Complex.I v)
  have ex4:=UniformPairMachine.bounded_execution n x B t3 a b
    (product 1 u) (product Complex.I v) hr3 hB hb3
  have f4 : Protected s s4:=(f3.trans (protected_reset s3)).trans (protected_C _ _ _ _ _)
  have c4:=hc.protected f4 h0 h1
  have hv4 : s4.scalarHeap (s.natReg 0)=some U ∧ s4.scalarHeap (s.natReg 1)=some V := by
    simpa [s4,U,V,t3,reset,f3.1 0 (by decide),f3.1 1 (by decide)] using
      UniformPairMachine.final_values t3 a b (product 1 u) (product Complex.I v) hn3
  let t4:=reset s4
  let s5:=loadState t4 3 5 a⁻¹ (Complex.I*a⁻¹)
  have hb4 : WordBound B t4:=changePC_bound B s4 0 ex4.final_bound (by omega)
  have ex5:=load_execution n x B t4 3 5 a⁻¹ (Complex.I*a⁻¹) rfl c4.2.2.1 c4.2.2.2.2
    (by omega) (by omega) (by omega) hb4
  have f5 : Protected s s5:=(f4.trans (protected_reset s4)).trans (protected_load _ _ _ _ _)
  let t5:=reset s5
  have hb5 : WordBound B t5:=changePC_bound B s5 0 ex5.final_bound (by omega)
  have hn5 : t5.natReg 0≠t5.natReg 1 := by
    simpa [t5,reset,f5.1 0 (by decide),f5.1 1 (by decide)] using hne
  have hr5 : Ready a⁻¹ (Complex.I*a⁻¹) U V t5 := by
    constructor
    · rfl
    · simpa [t5,s5,t4,reset,loadState,writeScalar,writeNat,next,f4.1 0 (by decide)] using hv4.1
    · simpa [t5,s5,t4,reset,loadState,writeScalar,writeNat,next,f4.1 1 (by decide)] using hv4.2
    · simp [t5,s5,reset,loadState,writeScalar,writeNat,next]
    · simp [t5,s5,reset,loadState,writeScalar,writeNat,next]
  let s6:=UniformPairDiagonalMachine.finalState t5 a⁻¹ (Complex.I*a⁻¹) U V
  have ex6:=UniformPairDiagonalMachine.bounded_execution n x B t5 a⁻¹ (Complex.I*a⁻¹) U V
    hr5 (by omega) hb5
  have f6 : Protected s s6:=(f5.trans (protected_reset s5)).trans (protected_diagonal _ _ _ _ _)
  have hv6 : s6.scalarHeap (s.natReg 0)=some (product a⁻¹ U) ∧
      s6.scalarHeap (s.natReg 1)=some (product (Complex.I*a⁻¹) V) := by
    simpa [s6,t5,reset,f5.1 0 (by decide),f5.1 1 (by decide)] using
      UniformPairDiagonalMachine.final_values t5 a⁻¹ (Complex.I*a⁻¹) U V hn5
  have r1 : BoundedRuns program n x (B+40) s 4 {s1 with pc:=4} := by
    simpa [placed] using UniformAssembly.BoundedExecution.placed right_code
      (by omega : 0+B≤B+40) (by omega : 4≤B+40) ex1
  have r2 : BoundedRuns program n x (B+40) {s1 with pc:=4} 7 {s2 with pc:=11} := by
    simpa [placed,s2,t1,reset] using UniformAssembly.BoundedExecution.placed first_diagonal_code
      (by omega : 4+B≤B+40) (by omega : 11≤B+40) ex2
  have r3 : BoundedRuns program n x (B+40) {s2 with pc:=11} 5 {s3 with pc:=16} := by
    simpa [placed,s3,t2,reset] using UniformAssembly.BoundedExecution.placed C_load_code
      (by omega : 11+B≤B+40) (by omega : 16≤B+40) ex3
  have r4 : BoundedRuns program n x (B+40) {s3 with pc:=16} 11 {s4 with pc:=27} := by
    simpa [placed,s4,t3,reset] using UniformAssembly.BoundedExecution.placed C_code
      (by omega : 16+B≤B+40) (by omega : 27≤B+40) ex4
  have r5 : BoundedRuns program n x (B+40) {s4 with pc:=27} 5 {s5 with pc:=32} := by
    simpa [placed,s5,t4,reset] using UniformAssembly.BoundedExecution.placed diagonal_load_code
      (by omega : 27+B≤B+40) (by omega : 32≤B+40) ex5
  have r6 : BoundedRuns program n x (B+40) {s5 with pc:=32} 7 {s6 with pc:=39} := by
    simpa [placed,s6,t5,reset] using UniformAssembly.BoundedExecution.placed last_diagonal_code
      (by omega : 32+B≤B+40) (by omega : 39≤B+40) ex6
  have hhalt : BoundedExecution program n x (B+40) {s6 with pc:=39} 1 {s6 with pc:=39} :=
    .halt r6.final_bound (by rfl)
  refine ⟨{s6 with pc:=39},(((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).executes hhalt,
    f6,hc.protected f6 h0 h1,?_,?_,rfl⟩
  · exact hv6.1.trans (congrArg some (left_value u v))
  · exact hv6.2.trans (congrArg some (right_value u v))


theorem contextFree : UniformContext.ContextFree program := by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program,rightProgram,
    loadProgram,UniformPairMachine.program,UniformPairDiagonalMachine.program,relocate]

theorem constants_from_bank (n : ℕ) (s : State)
    (h : ∀ j : Fin 6,s.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) :
    Constants s := ⟨h 1,h 2,h 3,h 4,h 5⟩

/-- The bank consumed by the pair program is produced by the actual initial-state
preparation program with the original single master-root request. -/
theorem preparation_constants {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t s,
    BoundedExecution UniformCConstantsMachine.program n x ((n+2)^14) initial t s ∧
      Constants s ∧ s.rootOrders=[UniformMasterRootMachine.order n] ∧
      t≤UniformCConstantsMachine.preparationBudget n := by
  obtain ⟨t,s,he,_,_,_,_,_,hb,hr,_,_,hc⟩:=UniformCConstantsMachine.preparation_execution hn x
  exact ⟨t,s,he,constants_from_bank n s hb,hr,hc⟩

end
end ExactFourierCircuits.UniformHadamardPairMachine
