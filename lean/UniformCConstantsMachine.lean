import UniformCKernelPreparation

set_option autoImplicit false

namespace ExactFourierCircuits.UniformCConstantsMachine
open UniformMachine UniformPairMachine OAI.ExactFourier
noncomputable section

/-- Fixed prepared constants are saved outside the scalar-register temporaries.
Heap0 remains the master root; heaps1..5 hold a,b,a^-1,i,i*a^-1. -/
def suffix : Program :=
  [.scalarLiteral 6 1,.fieldBinary .div 6 6 0,
   .fieldBinary .sub 7 0 1,.fieldBinary .mul 8 7 6,
   .natLiteral 31 1,.storeScalar 31 0,
   .natLiteral 31 2,.storeScalar 31 1,
   .natLiteral 31 3,.storeScalar 31 6,
   .natLiteral 31 4,.storeScalar 31 7,
   .natLiteral 31 5,.storeScalar 31 8,.halt]

def oneState (s : State) : State := writeScalar s 6 (prepared 1)
def inverseState (s : State) : State := writeScalar (oneState s) 6 (prepared a⁻¹)
def iState (s : State) : State := writeScalar (inverseState s) 7 (prepared Complex.I)
def arithmeticState (s : State) : State := writeScalar (iState s) 8 (prepared (Complex.I*a⁻¹))

def save (s : State) (address register : ℕ) : State :=
  {next (writeNat s 31 address) with
    scalarHeap:=Function.update s.scalarHeap address (some (s.scalarReg register))}

def savedA (s : State) : State := save (arithmeticState s) 1 0
def savedB (s : State) : State := save (savedA s) 2 1
def savedInverse (s : State) : State := save (savedB s) 3 6
def savedI (s : State) : State := save (savedInverse s) 4 7
def finalState (s : State) : State := save (savedI s) 5 8

theorem suffix_length : suffix.length=15 := rfl

theorem a_sub_b : a-b=Complex.I := by unfold a b;ring

theorem save_bound (B : ℕ) (s : State) (address register : ℕ)
    (hs : WordBound B s) (hp : s.pc+2≤B) (ha : address≤B) : WordBound B (save s address register) := by
  have hn := writeNat_bound B s 31 address hs (by omega) ha
  exact UniformInPlaceMachine.storeScalar_bound B (writeNat s 31 address) address (s.scalarReg register)
    hn (by simp [writeNat,next];omega) ha

theorem suffix_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=0) (ha : s.scalarReg 0=prepared a) (hb : s.scalarReg 1=prepared b)
    (hB : 15≤B) (hs : WordBound B s) :
    BoundedExecution suffix n x B s 15 (finalState s) := by
  have h1 := writeScalar_bound B s 6 (prepared 1) hs (by omega)
  have h2 := writeScalar_bound B (oneState s) 6 (prepared a⁻¹) h1
    (by simp [oneState,writeScalar,next,hp];omega)
  have h3 := writeScalar_bound B (inverseState s) 7 (prepared Complex.I) h2
    (by simp [inverseState,oneState,writeScalar,next,hp];omega)
  have h4 := writeScalar_bound B (iState s) 8 (prepared (Complex.I*a⁻¹)) h3
    (by simp [iState,inverseState,oneState,writeScalar,next,hp];omega)
  have h5 := save_bound B (arithmeticState s) 1 0 h4
    (by simp [arithmeticState,iState,inverseState,oneState,writeScalar,next,hp];omega) (by omega)
  have h6 := save_bound B (savedA s) 2 1 h5
    (by simp [savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h7 := save_bound B (savedB s) 3 6 h6
    (by simp [savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h8 := save_bound B (savedInverse s) 4 7 h7
    (by simp [savedInverse,savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h9 := save_bound B (savedI s) 5 8 h8
    (by simp [savedI,savedInverse,savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h5n := writeNat_bound B (arithmeticState s) 31 1 h4
    (by simp [arithmeticState,iState,inverseState,oneState,writeScalar,next,hp];omega) (by omega)
  have h6n := writeNat_bound B (savedA s) 31 2 h5
    (by simp [savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h7n := writeNat_bound B (savedB s) 31 3 h6
    (by simp [savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h8n := writeNat_bound B (savedInverse s) 31 4 h7
    (by simp [savedInverse,savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  have h9n := writeNat_bound B (savedI s) 31 5 h8
    (by simp [savedI,savedInverse,savedB,savedA,save,arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp];omega) (by omega)
  refine .next hs (u:=oneState s) ?_ (.next h1 (u:=inverseState s) ?_
    (.next h2 (u:=iState s) ?_ (.next h3 (u:=arithmeticState s) ?_
      (.next h4 (u:=writeNat (arithmeticState s) 31 1) ?_ (.next h5n (u:=savedA s) ?_
        (.next h5 (u:=writeNat (savedA s) 31 2) ?_ (.next h6n (u:=savedB s) ?_
          (.next h6 (u:=writeNat (savedB s) 31 3) ?_ (.next h7n (u:=savedInverse s) ?_
            (.next h7 (u:=writeNat (savedInverse s) 31 4) ?_ (.next h8n (u:=savedI s) ?_
              (.next h8 (u:=writeNat (savedI s) 31 5) ?_ (.next h9n (u:=finalState s) ?_
                (.halt h9 ?_))))))))))))))
  all_goals simp [step,suffix,finalState,savedI,savedInverse,savedB,savedA,save,
    arithmeticState,iState,inverseState,oneState,writeScalar,writeNat,next,hp,ha,hb,
    evalField,prepared,a_ne_zero,a_sub_b,one_div]

theorem final_frame (s : State) :
    (finalState s).natHeap=s.natHeap ∧ (finalState s).outputs=s.outputs ∧
      (finalState s).rootOrders=s.rootOrders ∧
      (∀ r,r≠31 → (finalState s).natReg r=s.natReg r) ∧
      (∀ r,r<6 → (finalState s).scalarReg r=s.scalarReg r) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp [finalState,savedI,savedInverse,savedB,savedA,save,arithmeticState,iState,
      inverseState,oneState,writeScalar,writeNat,next,hr]
  · intro r hr
    simp [finalState,savedI,savedInverse,savedB,savedA,save,arithmeticState,iState,
      inverseState,oneState,writeScalar,writeNat,next,show r≠6 by omega,show r≠7 by omega,show r≠8 by omega]

theorem final_heap (s : State) (ha : s.scalarReg 0=prepared a) (hb : s.scalarReg 1=prepared b) :
    (finalState s).scalarHeap=Function.update
      (Function.update (Function.update (Function.update (Function.update s.scalarHeap 1
        (some (prepared a))) 2 (some (prepared b))) 3 (some (prepared a⁻¹))) 4
          (some (prepared Complex.I))) 5 (some (prepared (Complex.I*a⁻¹))) := by
  simp [finalState,savedI,savedInverse,savedB,savedA,save,arithmeticState,iState,
    inverseState,oneState,writeScalar,writeNat,next,ha,hb]

def program : Program :=
  UniformCKernelPreparation.program.map (UniformAssembly.relocate 0 89) ++
    suffix.map (UniformAssembly.relocate 89 104) ++ [.halt]

theorem program_length : program.length=105 := by decide

theorem preparation_code : UniformAssembly.CodeAt UniformCKernelPreparation.program program 0 89 := by
  intro i hi
  simp only [program,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,suffix_length];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem suffix_code : UniformAssembly.CodeAt suffix program 89 104 := by
  intro i hi
  rw [suffix_length] at hi
  simp only [program]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,
    UniformCKernelPreparation.program_length,suffix_length];omega)]
  rw [List.getElem?_append_right (by simp only [List.length_map,UniformCKernelPreparation.program_length];omega)]
  simp only [List.length_map,UniformCKernelPreparation.program_length,Nat.add_sub_cancel_left,
    List.getElem?_map]

def preparationBudget (n : ℕ) : ℕ := UniformCKernelPreparation.preparationBudget n+16

theorem wordBound_setup {n : ℕ} (hn : 0<n) :
    105≤(n+2)^13 ∧ 89+(n+2)^13≤(n+2)^14 := by
  have h : 1594323≤(n+2)^13 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 13
    norm_num at h
    exact h
  refine ⟨by omega,?_⟩
  rw [show (n+2)^14=(n+2)^13*(n+2) from pow_succ (n+2) 13]
  nlinarith

def bank (n : ℕ) : Fin 6 → ℂ :=
  ![zeta (UniformMasterRootMachine.order n),a,b,a⁻¹,Complex.I,Complex.I*a⁻¹]

/-- The actual initial-state program stores every fixed Hadamard/C constant,
requests exactly the original master root and preserves the working header. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x ((n+2)^14) initial t u ∧
      UniformWorkingCompletion.PreparedState n u ∧
      u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
      u.scalarReg 0=prepared a ∧ u.scalarReg 1=prepared b ∧
      (∀ j : Fin 6,u.scalarHeap j.val=some (prepared (bank n j))) ∧
      u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
      u.pc=104 ∧ t≤preparationBudget n := by
  obtain ⟨hB,hBC⟩ := wordBound_setup hn
  obtain ⟨t,v,hv,hwork,horder,h8,ha,hb,hheap,hroot,hout,hpc,hcost⟩ :=
    UniformCKernelPreparation.preparation_execution hn x
  let entry := {v with pc:=0}
  have heB : WordBound ((n+2)^13) entry := changePC_bound _ v 0 hv.final_bound (by omega)
  have he := suffix_execution n x ((n+2)^13) entry rfl ha hb (by omega) heB
  have hprefix : BoundedRuns program n x ((n+2)^14) initial t {v with pc:=89} := by
    have h := UniformAssembly.BoundedExecution.placed preparation_code
      (by omega : 0+(n+2)^13≤(n+2)^14) (by omega : 89≤(n+2)^14) hv
    simpa [UniformAssembly.placed,initial] using h
  have htail : BoundedRuns program n x ((n+2)^14) {v with pc:=89} 15
      {finalState entry with pc:=104} := by
    have h := UniformAssembly.BoundedExecution.placed suffix_code hBC (by omega : 104≤(n+2)^14) he
    simpa [UniformAssembly.placed,entry] using h
  let u := {finalState entry with pc:=104}
  have huB : WordBound ((n+2)^14) u := htail.final_bound
  have hc : program[104]?=some .halt := by decide
  have hhalt : BoundedExecution program n x ((n+2)^14) u 1 u := .halt huB (by simp [step,u,hc])
  have hf := final_frame entry
  have hh := final_heap entry ha hb
  have hheader : UniformCKernelPreparation.HeaderFrame v u := by
    refine ⟨hf.1,?_⟩
    intro r hr
    exact hf.2.2.2.1 r (by rcases hr with h|⟨h5,h30,h31⟩ <;> omega)
  refine ⟨t+16,u,?_,hheader.prepared hwork,?_,?_,?_,?_,?_,?_,?_,rfl,?_⟩
  · exact (hprefix.trans htail).executes hhalt
  · exact (hf.2.2.2.1 24 (by decide)).trans horder
  · exact (hf.2.2.2.1 8 (by decide)).trans h8
  · exact (hf.2.2.2.2 0 (by decide)).trans ha
  · exact (hf.2.2.2.2 1 (by decide)).trans hb
  · intro j
    change (finalState entry).scalarHeap j.val=some (prepared (bank n j))
    rw [hh]
    have hh0 : entry.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n))) := by
      change v.scalarHeap 0=_
      rw [hheap]
      rfl
    fin_cases j <;> simp [bank,hh0]
  · exact hf.2.2.1.trans hroot
  · exact hf.2.1.trans hout
  · dsimp [preparationBudget]
    omega

theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hc : (fun _n : ℕ => (16:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (16:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  have h := UniformCKernelPreparation.preparationBudget_isLittleO_input.add hc
  simpa [preparationBudget,Nat.cast_add] using h

end
end ExactFourierCircuits.UniformCConstantsMachine
