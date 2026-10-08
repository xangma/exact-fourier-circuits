import UniformRadixTwoMachine
import UniformPermutationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRadixPowerBankMachine
open UniformMachine
noncomputable section

/-- Nat130=N>0, Nat131=P, Scalar30=prepared omega. Only the consumed
power references are written; no unneeded product-DAG cells are assumed. -/
def program : Program := [
  .natLiteral 132 0,.natLiteral 133 1,.natLiteral 134 5,.natLiteral 135 2,
  .scalarLiteral 31 1,.natBinary .add 136 131 133,.storeScalar 136 31,
  .fieldBinary .mul 31 31 30,.natBinary .add 132 132 133,
  .branchLT 132 130 10 17,.natBinary .mul 136 132 134,
  .natBinary .sub 136 136 135,.natBinary .add 136 131 136,
  .storeScalar 136 31,.fieldBinary .mul 31 31 30,
  .natBinary .add 132 132 133,.jump 9,.halt]

theorem program_length : program.length=18 := rfl

def powerRefIndex (j : ℕ) : ℕ := if j=0 then 1 else 5*j-2

theorem powerRefIndex_lt {N j : ℕ} (hj:j<N) : powerRefIndex j<5*N+3 := by
  unfold powerRefIndex
  split_ifs <;> omega

theorem powerRefIndex_injective : Function.Injective powerRefIndex := by
  intro i j h
  unfold powerRefIndex at h
  split_ifs at h <;> omega

theorem powerRefIndex_newton (j : ℕ) :
    (UniformNewton.Preparation.powerRef j).val=powerRefIndex j := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [UniformNewton.Preparation.powerRef,Fin.val_castSucc,Fin.val_last,
      UniformNewton.Preparation.productCount_formula,powerRefIndex,Nat.succ_ne_zero,ite_false]
    omega

theorem coefficientAddress_eq (k c : ℕ) (hc:c<UniformRadixTwoDAG.width k) :
    UniformRadixTwoMachine.coefficientAddress k c=
      UniformRadixTwoMachine.prepBase k+powerRefIndex c := by
  simp only [UniformRadixTwoMachine.coefficientAddress,dite_eq_left hc,
    UniformRadixTwoDAG.powers,UniformNewton.Preparation.productLift,Fin.val_castLE]
  rw [powerRefIndex_newton]

def prepared (z : ℂ) : Scalar := ⟨z,false⟩
def Bank (N P : ℕ) (omega : ℂ) (s : State) : Prop :=
  ∀j,j<N → s.scalarHeap (P+powerRefIndex j)=some (prepared (omega^j))
def Outside (N P : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop :=
  ∀a,(a<P ∨ P+5*N+3≤a) → s.scalarHeap a=heap a
def Frame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,r≠31 → u.scalarReg r=s.scalarReg r) ∧
  ∀r,(r<132 ∨ 136<r) → u.natReg r=s.natReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

structure Invariant (N P j : ℕ) (omega : ℂ) (heap : ℕ→Option Scalar) (s : State) : Prop where
  pc : s.pc=9
  count : s.natReg 130=N
  base : s.natReg 131=P
  index : s.natReg 132=j
  one : s.natReg 133=1
  five : s.natReg 134=5
  two : s.natReg 135=2
  root : s.scalarReg 30=prepared omega
  power : s.scalarReg 31=prepared (omega^j)
  written : ∀i,i<j → s.scalarHeap (P+powerRefIndex i)=some (prepared (omega^i))
  outside : Outside N P heap s

def init0 (s : State) := writeNat s 132 0
def init1 (s : State) := writeNat (init0 s) 133 1
def init5 (s : State) := writeNat (init1 s) 134 5
def init2 (s : State) := writeNat (init5 s) 135 2
def initPower (s : State) := writeScalar (init2 s) 31 (prepared 1)
def initAddress (s : State) := writeNat (initPower s) 136 (s.natReg 131+1)
def store (s : State) : State :=
  {next s with scalarHeap:=Function.update s.scalarHeap (s.natReg 136) (some (s.scalarReg 31))}
def initStore (s : State) := store (initAddress s)
def initRoot (s : State) (omega : ℂ) := writeScalar (initStore s) 31 (prepared omega)
def initialized (s : State) (omega : ℂ) := writeNat (initRoot s omega) 132 1

theorem initialized_frame (s : State) (omega : ℂ) : Frame s (initialized s omega) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,
      writeNat,writeScalar,next,hr]
  · intro r hr
    simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,
      writeNat,writeScalar,next,show r≠132 by omega,show r≠133 by omega,
      show r≠134 by omega,show r≠135 by omega,show r≠136 by omega]

theorem initialized_invariant (N P : ℕ) (omega : ℂ) (s : State)
    (hp:s.pc=0) (hN:0<N) (hn:s.natReg 130=N) (ha:s.natReg 131=P)
    (hr:s.scalarReg 30=prepared omega) : Invariant N P 1 omega s.scalarHeap (initialized s omega) := by
  constructor
  · simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next,hp]
  · simpa [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next] using hn
  · simpa [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next] using ha
  · simp [initialized,writeNat]
  · simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next]
  · simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next]
  · simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next]
  · simpa [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next] using hr
  · simp [initialized,initRoot,writeNat,writeScalar,next,prepared]
  · intro i hi
    have hz:i=0:=by omega
    subst i
    simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next,ha,powerRefIndex,prepared]
  · intro a hab
    have he:a≠P+1:=by omega
    simp [initialized,initRoot,initStore,store,initAddress,initPower,init2,init5,init1,init0,writeNat,writeScalar,next,ha,he]

theorem startup (n : ℕ) (x : Fin n→ℂ) (N P B : ℕ) (omega : ℂ) (s : State)
    (hp:s.pc=0) (hN:0<N) (hn:s.natReg 130=N) (ha:s.natReg 131=P)
    (hr:s.scalarReg 30=prepared omega) (hcode:18≤B) (hmem:P+5*N+3≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 9 (initialized s omega) := by
  have b0:=writeNat_bound B s 132 0 hs (by omega) (by omega)
  have b1:=writeNat_bound B (init0 s) 133 1 b0 (by change s.pc+2≤B;omega) (by omega)
  have b5:=writeNat_bound B (init1 s) 134 5 b1 (by change s.pc+3≤B;omega) (by omega)
  have b2:=writeNat_bound B (init5 s) 135 2 b5 (by change s.pc+4≤B;omega) (by omega)
  have bp:=writeScalar_bound B (init2 s) 31 (prepared 1) b2 (by change s.pc+5≤B;omega)
  have ba:=writeNat_bound B (initPower s) 136 (s.natReg 131+1) bp
    (by change s.pc+6≤B;omega) (by rw [ha];omega)
  have bs:=UniformPermutationMachine.store_bound B (initAddress s) (s.natReg 131+1)
    (prepared 1) ba (by change s.pc+7≤B;omega) (by rw [ha];omega)
  have br:=writeScalar_bound B (initStore s) 31 (prepared omega) bs (by change s.pc+8≤B;omega)
  have bi:=writeNat_bound B (initRoot s omega) 132 1 br (by change s.pc+9≤B;omega) (by omega)
  refine .next hs (u:=init0 s) ?_ (.next b0 (u:=init1 s) ?_ (.next b1 (u:=init5 s) ?_
    (.next b5 (u:=init2 s) ?_ (.next b2 (u:=initPower s) ?_ (.next bp (u:=initAddress s) ?_
      (.next ba (u:=initStore s) ?_ (.next bs (u:=initRoot s omega) ?_ (.next br ?_ (.refl bi)))))))))
  all_goals simp [step,program,initialized,initRoot,initStore,store,initAddress,initPower,
    init2,init5,init1,init0,writeNat,writeScalar,next,hp,ha,hr,prepared,evalNat,evalField]

def product (s : State) := writeNat {s with pc:=10} 136 (5*s.natReg 132)
def subtract (s : State) := writeNat (product s) 136 (5*s.natReg 132-2)
def address (s : State) := writeNat (subtract s) 136 (s.natReg 131+(5*s.natReg 132-2))
def stored (s : State) := store (address s)
def multiplied (s : State) (omega : ℂ) (j : ℕ) := writeScalar (stored s) 31 (prepared (omega^(j+1)))
def advanced (s : State) (omega : ℂ) (j : ℕ) := writeNat (multiplied s omega j) 132 (j+1)
def iterationEnd (s : State) (omega : ℂ) (j : ℕ) : State := {advanced s omega j with pc:=9}

theorem iteration_frame (s : State) (omega : ℂ) (j : ℕ) : Frame s (iterationEnd s omega j) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next,hr]
  · intro r hr
    simp [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next,
      show r≠132 by omega,show r≠136 by omega]

theorem iteration_heap (s : State) (omega : ℂ) (j : ℕ) :
    (iterationEnd s omega j).scalarHeap=Function.update s.scalarHeap
      (s.natReg 131+(5*s.natReg 132-2)) (some (s.scalarReg 31)) := rfl

theorem iteration_invariant (N P j : ℕ) (omega : ℂ) (heap : ℕ→Option Scalar) (s : State)
    (hi:Invariant N P j omega heap s) (hj:0<j) (hjN:j<N) :
    Invariant N P (j+1) omega heap (iterationEnd s omega j) := by
  constructor
  · rfl
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.count
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.base
  · simp [iterationEnd,advanced,writeNat]
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.one
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.five
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.two
  · simpa [iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next] using hi.root
  · simp [iterationEnd,advanced,multiplied,writeNat,writeScalar,next]
  · intro i hi'
    rw [iteration_heap,hi.base,hi.index,hi.power]
    have href:powerRefIndex j=5*j-2:=by simp [powerRefIndex,Nat.ne_of_gt hj]
    by_cases he:i=j
    · subst i; simp [href]
    · have hne:P+powerRefIndex i≠P+(5*j-2):=by
        intro h; exact he (powerRefIndex_injective (by omega : powerRefIndex i=powerRefIndex j))
      rw [Function.update_of_ne hne]
      exact hi.written i (by omega)
  · intro a ha
    rw [iteration_heap,hi.base,hi.index,Function.update_of_ne (by omega)]
    exact hi.outside a ha

theorem iteration (n : ℕ) (x : Fin n→ℂ) (N P j B : ℕ) (omega : ℂ)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant N P j omega heap s)
    (hj:0<j) (hjN:j<N) (hcode:18≤B) (hmem:P+5*N+3≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 8 (iterationEnd s omega j) := by
  have b0:=changePC_bound B s 10 hs (by omega)
  have b1:=writeNat_bound B {s with pc:=10} 136 (5*s.natReg 132) b0
    (by change 11≤B;omega) (by rw [hi.index];omega)
  have b2:=writeNat_bound B (product s) 136 (5*s.natReg 132-2) b1
    (by change 12≤B;omega) (by rw [hi.index];omega)
  have b3:=writeNat_bound B (subtract s) 136 (s.natReg 131+(5*s.natReg 132-2)) b2
    (by change 13≤B;omega) (by rw [hi.index,hi.base];omega)
  have b4:=UniformPermutationMachine.store_bound B (address s)
    (s.natReg 131+(5*s.natReg 132-2)) (s.scalarReg 31) b3
    (by change 14≤B;omega) (by rw [hi.index,hi.base];omega)
  have b5:=writeScalar_bound B (stored s) 31 (prepared (omega^(j+1))) b4 (by change 15≤B;omega)
  have b6:=writeNat_bound B (multiplied s omega j) 132 (j+1) b5 (by change 16≤B;omega) (by omega)
  have b7:=changePC_bound B (advanced s omega j) 9 b6 (by omega)
  have t0:step program n x s=.running {s with pc:=10}:=by
    simp [step,program,hi.pc,hi.index,hi.count,hjN]
  have t1:step program n x {s with pc:=10}=.running (product s):=by
    simp [step,program,product,evalNat,Nat.mul_comm,hi.five]
  have t2:step program n x (product s)=.running (subtract s):=by
    simp [step,program,subtract,product,writeNat,next,evalNat,hi.two]
  have t3:step program n x (subtract s)=.running (address s):=by
    simp [step,program,address,subtract,product,writeNat,next,evalNat]
  have t4:step program n x (address s)=.running (stored s):=by
    simp [step,program,stored,store,address,subtract,product,writeNat,next]
  have t5:step program n x (stored s)=.running (multiplied s omega j):=by
    simp [step,program,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next,
      hi.power,hi.root,prepared,evalField,pow_succ]
  have t6:step program n x (multiplied s omega j)=.running (advanced s omega j):=by
    simp [step,program,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next,
      hi.index,hi.one,evalNat]
  have t7:step program n x (advanced s omega j)=.running (iterationEnd s omega j):=by
    simp [step,program,iterationEnd,advanced,multiplied,stored,store,address,subtract,product,writeNat,writeScalar,next]
  exact .next hs t0 (.next b0 t1 (.next b1 t2 (.next b2 t3 (.next b3 t4
    (.next b4 t5 (.next b5 t6 (.next b6 t7 (.refl b7))))))))

theorem loop (n : ℕ) (x : Fin n→ℂ) (N P j fuel B : ℕ) (omega : ℂ)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant N P j omega heap s)
    (hj:0<j) (hf:j+fuel=N) (hcode:18≤B) (hmem:P+5*N+3≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (8*fuel) u ∧ Invariant N P N omega heap u ∧ Frame s u := by
  induction fuel generalizing j s with
  | zero =>
    have he:j=N:=by omega
    subst j
    exact ⟨s,.refl hs,hi,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩⟩
  | succ fuel ih =>
    let u:=iterationEnd s omega j
    have hu:=iteration n x N P j B omega heap s hi hj (by omega) hcode hmem hs
    have hiu:=iteration_invariant N P j omega heap s hi hj (by omega)
    obtain ⟨v,hv,hiv,hfr⟩:=ih (j+1) u hiu (by omega) (by omega) hu.final_bound
    refine ⟨v,?_,hiv,(iteration_frame s omega j).trans hfr⟩
    convert hu.trans hv using 1;omega

/-- Actual sparse prepared powers, linear charged work, dirty heaps allowed. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (N P B : ℕ) (omega : ℂ) (s : State)
    (hp:s.pc=0) (hN:0<N) (hn:s.natReg 130=N) (ha:s.natReg 131=P)
    (hr:s.scalarReg 30=prepared omega) (hcode:18≤B) (hmem:P+5*N+3≤B)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (8*N+3) u ∧ Bank N P omega u ∧
    Outside N P s.scalarHeap u ∧ Frame s u ∧ u.pc=17 := by
  have hb:=startup n x N P B omega s hp hN hn ha hr hcode hmem hs
  have hi:=initialized_invariant N P omega s hp hN hn ha hr
  obtain ⟨u,hu,hiu,hfr⟩:=loop n x N P 1 (N-1) B omega s.scalarHeap (initialized s omega)
    hi (by omega) (by omega) hcode hmem hb.final_bound
  let v:State:={u with pc:=17}
  have hv:=changePC_bound B u 17 hu.final_bound (by omega)
  have hh:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ hh
    simp [step,program,hiu.pc,hiu.index,hiu.count,v]
  refine ⟨v,?_,hiu.written,hiu.outside,(initialized_frame s omega).trans hfr,rfl⟩
  convert hb.executes (hu.executes he) using 1;omega

/-- Matches precisely the powers consumed by the shifted FFT row printer. -/
theorem radix_bank (k A : ℕ) (omega : ℂ) (s : State)
    (h:Bank (UniformRadixTwoDAG.width k) (A+UniformRadixTwoMachine.prepBase k) omega s)
    (c : Fin (UniformRadixTwoDAG.width k)) :
    s.scalarHeap (A+UniformRadixTwoMachine.coefficientAddress k c.val)=
      some (UniformRadixTwoMachine.preparedScalar
        ((UniformRadixTwoDAG.powers k).run (UniformNewton.Preparation.roots omega)
          (UniformRadixTwoDAG.powers_admissible k omega) c)) := by
  rw [coefficientAddress_eq k c.val c.isLt,UniformRadixTwoDAG.powers_run]
  simpa only [Nat.add_assoc,prepared,UniformRadixTwoMachine.preparedScalar] using h c.val c.isLt

end
end ExactFourierCircuits.UniformRadixPowerBankMachine
