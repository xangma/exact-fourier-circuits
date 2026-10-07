import UniformChirpPreparation
import UniformCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace ExactFourierCircuits.UniformPaddedInputMachine
open UniformMachine UniformPairMachine
noncomputable section

/-- Nat0=n, Nat1=L, Nat2=chirp-table base, Nat9=data base. The loop reads
actual input coordinates, multiplies by prepared coefficients, and pads with zero. -/
def program : Program :=
  [.natLiteral 3 1,.natLiteral 4 2,.natLiteral 5 0,
   .branchLT 5 1 4 17,.branchLT 5 0 5 12,.input 0 5,
   .natBinary .mul 6 5 4,.natBinary .add 6 2 6,.loadScalar 1 6,
   .fieldBinary .mul 0 1 0,.jump 13,.jump 13,.scalarLiteral 0 0,
   .storeScalar 9 0,.natBinary .add 9 9 3,.natBinary .add 5 5 3,.jump 3,.halt]

theorem program_length : program.length=18 := rfl

def paddedScalar {n : ℕ} (eta : ℂ) (x : Fin n → ℂ) (j : ℕ) : Scalar :=
  if hj:j<n then ⟨UniformChirp.chirp eta j*x ⟨j,hj⟩,true⟩ else prepared 0

structure Data (n L a d j : ℕ) (s : State) : Prop where
  pc : s.pc=3
  count : s.natReg 0=n
  width : s.natReg 1=L
  bank : s.natReg 2=a
  one : s.natReg 3=1
  two : s.natReg 4=2
  index : s.natReg 5=j
  address : s.natReg 9=d+j

def Coefficients (n a : ℕ) (eta : ℂ) (s : State) : Prop := ∀ j,j<n →
  s.scalarHeap (a+2*j)=some (prepared (UniformChirp.chirp eta j))

def initOne (s : State) := writeNat s 3 1
def initTwo (s : State) := writeNat (initOne s) 4 2
def initialized (s : State) := writeNat (initTwo s) 5 0

theorem initialized_data {n : ℕ} (L a d : ℕ) (s : State)
    (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d) : Data n L a d 0 (initialized s) := by
  constructor <;> simp [initialized,initTwo,initOne,writeNat,next,hp,hn,hL,ha,hd]

theorem startup_runs {n : ℕ} (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=0) (hB : 32≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 3 (initialized s) := by
  have h1:=writeNat_bound B s 3 1 hs (by omega) (by omega)
  have h2:=writeNat_bound B (initOne s) 4 2 h1
    (by simp [initOne,writeNat,next,hp];omega) (by omega)
  have h3:=writeNat_bound B (initTwo s) 5 0 h2
    (by simp [initTwo,initOne,writeNat,next,hp];omega) (by omega)
  refine .next hs (u:=initOne s) ?_ (.next h1 (u:=initTwo s) ?_
    (.next h2 (u:=initialized s) ?_ (.refl h3)))
  all_goals simp [step,program,initialized,initTwo,initOne,writeNat,next,hp]

def entered (s : State) : State := {s with pc:=4}
def positiveBranch (s : State) : State := {s with pc:=5}
def readInput {n : ℕ} (s : State) (x : Fin n → ℂ) (j : ℕ) (hj : j<n) :=
  writeScalar (positiveBranch s) 0 ⟨x ⟨j,hj⟩,true⟩
def doubleIndex {n : ℕ} (s : State) (x : Fin n → ℂ) (j : ℕ) (hj : j<n) :=
  writeNat (readInput s x j hj) 6 (2*j)
def coefficientAddress {n : ℕ} (s : State) (x : Fin n → ℂ) (a j : ℕ) (hj : j<n) :=
  writeNat (doubleIndex s x j hj) 6 (a+2*j)
def coefficientLoaded {n : ℕ} (s : State) (x : Fin n → ℂ) (eta : ℂ) (a j : ℕ) (hj : j<n) :=
  writeScalar (coefficientAddress s x a j hj) 1 (prepared (UniformChirp.chirp eta j))
def positiveResult {n : ℕ} (s : State) (x : Fin n → ℂ) (eta : ℂ) (a j : ℕ) (hj : j<n) : State :=
  {writeScalar (coefficientLoaded s x eta a j hj) 0 (paddedScalar eta x j) with pc:=13}
def zeroResult (s : State) : State := writeScalar {s with pc:=12} 0 (prepared 0)
def stored (s : State) : State :=
  {next s with
    scalarHeap:=Function.update s.scalarHeap (s.natReg 9) (some (s.scalarReg 0))}
def advanceAddress (s : State) := writeNat (stored s) 9 (s.natReg 9+1)
def rowEnd (s : State) (j : ℕ) : State :=
  {writeNat (advanceAddress s) 5 (j+1) with pc:=3}

theorem positive_runs {n : ℕ} (x : Fin n → ℂ) (B L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hj : j<n) (hc : Coefficients n a eta s)
    (hB : 32≤B) (ha : a+2*n≤d) (hdB : d+L≤B) (hs : WordBound B s) :
    BoundedRuns program n x B (entered s) 7 (positiveResult s x eta a j hj) := by
  obtain ⟨hp,hn,hL,hbank,h1,h2,hindex,hadr⟩:=hd
  have hco:s.scalarHeap (a+j*2)=some (prepared (UniformChirp.chirp eta j)):=by
    simpa [Nat.mul_comm] using hc j hj
  have hent:WordBound B (entered s):=changePC_bound B s 4 hs (by omega)
  have hbr:WordBound B (positiveBranch s):=changePC_bound B s 5 hs (by omega)
  have hinput:=writeScalar_bound B (positiveBranch s) 0 ⟨x ⟨j,hj⟩,true⟩ hbr
    (by simp [positiveBranch];omega)
  have hdouble:=writeNat_bound B (readInput s x j hj) 6 (2*j) hinput
    (by simp [readInput,positiveBranch,writeScalar,next];omega) (by omega)
  have haddr:=writeNat_bound B (doubleIndex s x j hj) 6 (a+2*j) hdouble
    (by simp [doubleIndex,readInput,positiveBranch,writeNat,writeScalar,next];omega) (by omega)
  have hcoef:=writeScalar_bound B (coefficientAddress s x a j hj) 1 (prepared (UniformChirp.chirp eta j)) haddr
    (by simp [coefficientAddress,doubleIndex,readInput,positiveBranch,writeNat,writeScalar,next];omega)
  have hresult:=writeScalar_bound B (coefficientLoaded s x eta a j hj) 0 (paddedScalar eta x j) hcoef
    (by simp [coefficientLoaded,coefficientAddress,doubleIndex,readInput,positiveBranch,writeNat,writeScalar,next];omega)
  have hf:WordBound B (positiveResult s x eta a j hj):=changePC_bound B _ 13 hresult (by omega)
  refine .next hent (u:=positiveBranch s) ?_ (.next hbr (u:=readInput s x j hj) ?_
    (.next hinput (u:=doubleIndex s x j hj) ?_ (.next hdouble (u:=coefficientAddress s x a j hj) ?_
      (.next haddr (u:=coefficientLoaded s x eta a j hj) ?_
        (.next hcoef (u:=writeScalar (coefficientLoaded s x eta a j hj) 0 (paddedScalar eta x j)) ?_
          (.next hresult ?_ (.refl hf)))))))
  all_goals simp [step,program,positiveResult,coefficientLoaded,coefficientAddress,doubleIndex,
    readInput,positiveBranch,entered,writeNat,writeScalar,next,hp,hn,hL,hbank,h1,h2,hindex,hadr,
    hj,hco,hc j hj,evalNat,evalField,prepared,paddedScalar,Nat.mul_comm]

theorem zero_runs {n : ℕ} (x : Fin n → ℂ) (B L a d j : ℕ) (s : State)
    (hd : Data n L a d j s) (hj : n≤j) (hB : 32≤B) (hs : WordBound B s) :
    BoundedRuns program n x B (entered s) 2 (zeroResult s) := by
  have hent:WordBound B (entered s):=changePC_bound B s 4 hs (by omega)
  have hbr:WordBound B {s with pc:=12}:=changePC_bound B s 12 hs (by omega)
  have hf:=writeScalar_bound B {s with pc:=12} 0 (prepared 0) hbr (by change 12+1≤B;omega)
  refine .next hent (u:={s with pc:=12}) ?_ (.next hbr ?_ (.refl hf))
  all_goals simp [step,program,entered,zeroResult,hd.index,hd.count,show ¬j<n by omega,prepared]

structure TailReady (d j : ℕ) (value : Scalar) (s : State) : Prop where
  pc : s.pc=13
  one : s.natReg 3=1
  index : s.natReg 5=j
  address : s.natReg 9=d+j
  value : s.scalarReg 0=value

theorem tail_runs {n : ℕ} (x : Fin n → ℂ) (B d j L : ℕ) (value : Scalar) (s : State)
    (ht : TailReady d j value s) (hj : j<L) (hB : 32≤B) (hd : d+L≤B)
    (hs : WordBound B s) : BoundedRuns program n x B s 4 (rowEnd s j) := by
  obtain ⟨hp,h1,hi,ha,hv⟩:=ht
  have hst:=UniformInPlaceMachine.storeScalar_bound B s (s.natReg 9) (s.scalarReg 0) hs
    (by omega) (hs.2.1 9)
  have hadv:=writeNat_bound B (stored s) 9 (s.natReg 9+1) hst
    (by simp [stored,next,hp];omega) (by rw [ha];omega)
  have hidx:=writeNat_bound B (advanceAddress s) 5 (j+1) hadv
    (by simp [advanceAddress,stored,writeNat,next,hp];omega) (by omega)
  have hf:WordBound B (rowEnd s j):=changePC_bound B _ 3 hidx (by omega)
  refine .next hs (u:=stored s) ?_ (.next hst (u:=advanceAddress s) ?_
    (.next hadv (u:=writeNat (advanceAddress s) 5 (j+1)) ?_ (.next hidx ?_ (.refl hf))))
  all_goals simp [step,program,rowEnd,advanceAddress,stored,writeNat,next,hp,h1,hi,ha,hv,evalNat]

def result {n : ℕ} (s : State) (x : Fin n → ℂ) (eta : ℂ) (a j : ℕ) : State :=
  if hj:j<n then positiveResult s x eta a j hj else zeroResult s

theorem result_values {n : ℕ} (x : Fin n → ℂ) (L a d j : ℕ) (eta : ℂ) (s : State)
    (h : Data n L a d j s) :
    TailReady d j (paddedScalar eta x j) (result s x eta a j) ∧
    (result s x eta a j).natHeap=s.natHeap ∧ (result s x eta a j).scalarHeap=s.scalarHeap ∧
    (result s x eta a j).outputs=s.outputs ∧ (result s x eta a j).rootOrders=s.rootOrders ∧
    (∀ r,r≠6 → (result s x eta a j).natReg r=s.natReg r) := by
  obtain ⟨hp,hn,hL,ha,h1,h2,hj,hadr⟩:=h
  by_cases hpos:j<n
  · simp only [result,dif_pos hpos]
    refine ⟨?_,rfl,rfl,rfl,rfl,?_⟩
    · constructor <;> simp [positiveResult,coefficientLoaded,coefficientAddress,doubleIndex,
        readInput,positiveBranch,writeNat,writeScalar,next,h1,hj,hadr]
    · intro r hr
      simp [positiveResult,coefficientLoaded,coefficientAddress,doubleIndex,
        readInput,positiveBranch,writeNat,writeScalar,next,hr]
  · simp only [result,dif_neg hpos]
    refine ⟨?_,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
    constructor <;> simp [zeroResult,writeScalar,next,paddedScalar,hpos,h1,hj,hadr]

theorem row_execution {n : ℕ} (x : Fin n → ℂ) (B L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hj : j<L) (hc : Coefficients n a eta s)
    (hB : 32≤B) (ha : a+2*n≤d) (hdB : d+L≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s (if j<n then 12 else 7) (rowEnd (result s x eta a j) j) := by
  have hent:WordBound B (entered s):=changePC_bound B s 4 hs (by omega)
  have hentry:BoundedRuns program n x B s 1 (entered s):=by
    refine .next hs ?_ (.refl hent)
    simp [step,program,entered,hd.pc,hd.index,hd.width,hj]
  by_cases hp:j<n
  · have hr:=positive_runs x B L a d j eta s hd hp hc hB ha hdB hs
    have ht:=tail_runs x B d j L (paddedScalar eta x j) (positiveResult s x eta a j hp)
      (by simpa [result,hp] using (result_values x L a d j eta s hd).1) hj hB hdB hr.final_bound
    simpa [hp,result,Nat.add_assoc] using (hentry.trans hr).trans ht
  · have hr:=zero_runs x B L a d j s hd (by omega) hB hs
    have ht:=tail_runs x B d j L (paddedScalar eta x j) (zeroResult s)
      (by simpa [result,hp] using (result_values x L a d j eta s hd).1) hj hB hdB hr.final_bound
    simpa [hp,result,Nat.add_assoc] using (hentry.trans hr).trans ht

theorem row_data {n : ℕ} (x : Fin n → ℂ) (L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) : Data n L a d (j+1) (rowEnd (result s x eta a j) j) := by
  have hv:=result_values x L a d j eta s hd
  constructor
  · rfl
  · exact hv.2.2.2.2.2 0 (by omega) |>.trans hd.count
  · exact hv.2.2.2.2.2 1 (by omega) |>.trans hd.width
  · exact hv.2.2.2.2.2 2 (by omega) |>.trans hd.bank
  · exact hv.1.one
  · exact hv.2.2.2.2.2 4 (by omega) |>.trans hd.two
  · simp [rowEnd,writeNat,next]
  · simp [rowEnd,advanceAddress,stored,writeNat,next,hv.1.address,Nat.add_assoc]

theorem row_heap {n : ℕ} (x : Fin n → ℂ) (L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) :
    (rowEnd (result s x eta a j) j).scalarHeap=
      Function.update s.scalarHeap (d+j) (some (paddedScalar eta x j)) := by
  have hv:=result_values x L a d j eta s hd
  simp only [rowEnd,advanceAddress,stored,writeNat,next,hv.1.address,hv.1.value,hv.2.2.1]

def Partial {n : ℕ} (d j : ℕ) (eta : ℂ) (x : Fin n → ℂ) (s : State) : Prop :=
  ∀ k,k<j → s.scalarHeap (d+k)=some (paddedScalar eta x k)

def Frame (d L : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<d ∨ d+L≤b → u.scalarHeap b=s.scalarHeap b) ∧
  ∀ r,7≤r → r≠9 → u.natReg r=s.natReg r

theorem frame_refl (d L : ℕ) (s : State) : Frame d L s s:=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩

theorem frame_trans {d L : ℕ} {s u v : State} (hu : Frame d L s u) (hv : Frame d L u v) :
    Frame d L s v :=
  ⟨hv.1.trans hu.1,hv.2.1.trans hu.2.1,hv.2.2.1.trans hu.2.2.1,
    fun b hb=>(hv.2.2.2.1 b hb).trans (hu.2.2.2.1 b hb),
    fun r hr h9=>(hv.2.2.2.2 r hr h9).trans (hu.2.2.2.2 r hr h9)⟩

theorem row_frame {n : ℕ} (x : Fin n → ℂ) (L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hj : j<L) : Frame d L s (rowEnd (result s x eta a j) j) := by
  have hv:=result_values x L a d j eta s hd
  refine ⟨hv.2.1,hv.2.2.2.1,hv.2.2.2.2.1,?_,?_⟩
  · intro b hb
    rw [row_heap x L a d j eta s hd,Function.update_of_ne (by omega)]
  · intro r hr h9
    change (Function.update (Function.update (result s x eta a j).natReg 9
      ((result s x eta a j).natReg 9+1)) 5 (j+1)) r=s.natReg r
    rw [Function.update_of_ne (by omega),Function.update_of_ne h9]
    exact hv.2.2.2.2.2 r (by omega)

theorem row_partial {n : ℕ} (x : Fin n → ℂ) (L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hp : Partial d j eta x s) :
    Partial d (j+1) eta x (rowEnd (result s x eta a j) j) := by
  intro k hk
  rw [row_heap x L a d j eta s hd]
  by_cases h:k=j
  · subst k;exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by omega)]
    exact hp k (by omega)

theorem coefficients_frame {n : ℕ} {L a d : ℕ} {eta : ℂ} {s u : State}
    (hc : Coefficients n a eta s) (ha : a+2*n≤d) (hf : Frame d L s u) :
    Coefficients n a eta u := by
  intro j hj
  rw [hf.2.2.2.1 (a+2*j) (Or.inl (by omega))]
  exact hc j hj

def loopCost (n j : ℕ) : ℕ → ℕ
  | 0 => 2
  | t+1 => (if j<n then 12 else 7)+loopCost n (j+1) t

theorem loopCost_bound (n j t : ℕ) : loopCost n j t≤12*t+2 := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    have h:=ih (j+1)
    simp only [loopCost,Nat.mul_succ]
    split_ifs <;> omega

theorem loop_execution {n : ℕ} (x : Fin n → ℂ) (B L a d : ℕ) (eta : ℂ)
    (hB : 32≤B) (ha : a+2*n≤d) (hdB : d+L≤B) (t : ℕ) : ∀ j s,
    j+t=L → Data n L a d j s → Coefficients n a eta s → Partial d j eta x s →
    WordBound B s → ∃ u, BoundedExecution program n x B s (loopCost n j t) u ∧
    Partial d L eta x u ∧ Frame d L s u ∧ u.pc=17 := by
  induction t with
  | zero =>
    intro j s hj hd hc hp hs
    have he:j=L:=by omega
    let u:State:={s with pc:=17}
    have hu:WordBound B u:=changePC_bound B s 17 hs (by omega)
    refine ⟨u,?_,?_,frame_refl d L s,rfl⟩
    · refine .next hs (u:=u) ?_ (.halt hu ?_)
      · simp [step,program,u,hd.pc,hd.index,hd.width,he]
      · simp [step,program,u]
    · simpa [Partial,u,he] using hp
  | succ t ih =>
    intro j s hj hd hc hp hs
    have hjL:j<L:=by omega
    have he:=row_execution x B L a d j eta s hd hjL hc hB ha hdB hs
    have hf:=row_frame x L a d j eta s hd hjL
    obtain ⟨u,hu,hp',hf',hpc⟩:=ih (j+1) (rowEnd (result s x eta a j) j) (by omega)
      (row_data x L a d j eta s hd) (coefficients_frame hc ha hf)
      (row_partial x L a d j eta s hd hp) he.final_bound
    exact ⟨u,by simpa [loopCost] using he.executes hu,hp',frame_trans hf hf',hpc⟩

theorem initialized_frame (d L : ℕ) (s : State) : Frame d L s (initialized s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr h9
  simp [initialized,initTwo,initOne,writeNat,next,show r≠3 by omega,
    show r≠4 by omega,show r≠5 by omega]

/-- Actual input reads, prepared scaling and zero padding, including setup and
the final halt. The coefficient bank and every unrelated heap cell survive. -/
theorem input_execution {n : ℕ} (x : Fin n → ℂ) (B L a d : ℕ) (eta : ℂ) (s : State)
    (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d) (hc : Coefficients n a eta s)
    (hB : 32≤B) (hdisjoint : a+2*n≤d) (hspace : d+L≤B) (hs : WordBound B s) :
    ∃ u, BoundedExecution program n x B s (3+loopCost n 0 L) u ∧
    Partial d L eta x u ∧ Frame d L s u ∧ u.pc=17 := by
  have hstart:=startup_runs x B s hp hB hs
  obtain ⟨u,hu,ht,hf,hpc⟩:=loop_execution x B L a d eta hB hdisjoint hspace L 0
    (initialized s) (by omega) (initialized_data L a d s hp hn hL ha hd)
    hc (by intro k hk;omega) hstart.final_bound
  exact ⟨u,hstart.executes hu,ht,frame_trans (initialized_frame d L s) hf,hpc⟩

theorem input_cost_bound (n L : ℕ) : 3+loopCost n 0 L≤12*L+5 := by
  have h:=loopCost_bound n 0 L;omega

theorem coefficients_of_chirp_table {n : ℕ} {a : ℕ} {eta : ℂ} {s : State}
    (h : UniformChirpTableMachine.Partial a n eta s) : Coefficients n a eta s :=
  fun j hj => (h j hj).1

theorem paddedScalar_value {n : ℕ} (eta : ℂ) (x : Fin n → ℂ) (j : ℕ) :
    (paddedScalar eta x j).value=
      if hj:j<n then eta^((j:ℤ)^2)*x ⟨j,hj⟩ else 0 := by
  by_cases hj:j<n
  · simp [paddedScalar,hj,UniformChirp.chirp,←zpow_natCast]
  · simp [paddedScalar,hj,prepared]

theorem paddedScalar_cyclic {n L : ℕ} [NeZero L] (eta : ℂ) (x : Fin n → ℂ) (j : Fin L) :
    (paddedScalar eta x j.val).value=
      UniformCyclic.paddedChirp eta x (OAI.ExactFourier.FourierCRT.finZMod L j) := by
  rw [paddedScalar_value]
  simp [UniformCyclic.paddedChirp,UniformCyclic.pad,OAI.ExactFourier.FourierCRT.finZMod,
    Nat.mod_eq_of_lt j.isLt]

end
end ExactFourierCircuits.UniformPaddedInputMachine
