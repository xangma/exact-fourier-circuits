import UniformChirpTableMachine
import UniformCyclic

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3, signed fixed convolution operand after (5.7),
PDF p.22, and linear preparation, PDF p.23 (`eq:chirp`).

Writes positive support, negative support and literal zeros using the inverse
chirp bank. The 2n <= L condition proves the two signed supports do not overlap;
integer guards do not inspect complex input data.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformChirpKernelMachine
open UniformMachine UniformPairMachine
noncomputable section

/-- Nat0=n, Nat1=L, Nat2=inverse chirp bank base, Nat9=kernel base.
The entire signed kernel is written by one integer-controlled pass. -/
/- Paper stage: §5.3, signed fixed operand following (5.7), PDF p.22: integer-controlled support selection, inverse-chirp load, literal zero and store. -/
def program : Program :=
  [.natLiteral 3 1,.natLiteral 4 2,.natLiteral 5 0,
   .branchLT 5 1 4 19,.branchLT 5 0 5 7,.natBinary .mul 7 5 3,.jump 9,
   .natBinary .sub 7 1 5,.branchLT 7 0 9 14,
   .natBinary .mul 6 7 4,.natBinary .add 6 2 6,.natBinary .add 6 6 3,
   .loadScalar 0 6,.jump 15,.scalarLiteral 0 0,
   .storeScalar 9 0,.natBinary .add 9 9 3,.natBinary .add 5 5 3,.jump 3,.halt]

theorem program_length : program.length=20 := rfl

def kernelScalar (eta : ℂ) (n L j : ℕ) : Scalar :=
  if j<n then prepared (UniformChirp.chirp eta⁻¹ j)
  else if L-j<n then prepared (UniformChirp.chirp eta⁻¹ (L-j)) else prepared 0

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
  s.scalarHeap (a+2*j+1)=some (prepared (UniformChirp.chirp eta⁻¹ j))

def initOne (s : State) := writeNat s 3 1
def initTwo (s : State) := writeNat (initOne s) 4 2
def initialized (s : State) := writeNat (initTwo s) 5 0

theorem initialized_data (n L a d : ℕ) (s : State)
    (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d) : Data n L a d 0 (initialized s) := by
  constructor <;> simp [initialized,initTwo,initOne,writeNat,next,hp,hn,hL,ha,hd]

theorem startup_runs (N : ℕ) (x : Fin N → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=0) (hB : 20≤B) (hs : WordBound B s) :
    BoundedRuns program N x B s 3 (initialized s) := by
  have h1:=writeNat_bound B s 3 1 hs (by omega) (by omega)
  have h2:=writeNat_bound B (initOne s) 4 2 h1
    (by simp [initOne,writeNat,next,hp];omega) (by omega)
  have h3:=writeNat_bound B (initTwo s) 5 0 h2
    (by simp [initTwo,initOne,writeNat,next,hp];omega) (by omega)
  refine .next hs (u:=initOne s) ?_ (.next h1 (u:=initTwo s) ?_
    (.next h2 (u:=initialized s) ?_ (.refl h3)))
  all_goals simp [step,program,initialized,initTwo,initOne,writeNat,next,hp]

def entered (s : State) : State := {s with pc:=4}
def selecting (s : State) (p : ℕ) : State := {s with pc:=p}
def indexWritten (s : State) (p k : ℕ) := writeNat (selecting s p) 7 k
def selected (s : State) (p k q : ℕ) : State := {indexWritten s p k with pc:=q}
def doubleIndex (s : State) (k : ℕ) := writeNat s 6 (2*k)
def coefficientAddress (s : State) (a k : ℕ) := writeNat (doubleIndex s k) 6 (a+2*k)
def inverseAddress (s : State) (a k : ℕ) := writeNat (coefficientAddress s a k) 6 (a+2*k+1)
def coefficientLoaded (s : State) (eta : ℂ) (a k : ℕ) :=
  writeScalar (inverseAddress s a k) 0 (prepared (UniformChirp.chirp eta⁻¹ k))
def loaded (s : State) (eta : ℂ) (a k : ℕ) : State :=
  {coefficientLoaded s eta a k with pc:=15}
def zeroResult (s : State) := writeScalar s 0 (prepared 0)

theorem positive_selection (N : ℕ) (x : Fin N → ℂ) (B n L a d j : ℕ) (s : State)
    (hd : Data n L a d j s) (hj : j<n) (hB : 20≤B) (hs : WordBound B s) :
    BoundedRuns program N x B (entered s) 3 (selected s 5 j 9) := by
  have hent:=changePC_bound B s 4 hs (by omega)
  have hb:=changePC_bound B s 5 hs (by omega)
  have hw:=writeNat_bound B (selecting s 5) 7 j hb (by change 6≤B;omega)
    (by rw [←hd.index];exact hs.2.1 5)
  have hf:=changePC_bound B (indexWritten s 5 j) 9 hw (by omega)
  refine .next hent (u:=selecting s 5) ?_ (.next hb (u:=indexWritten s 5 j) ?_
    (.next hw ?_ (.refl hf)))
  all_goals simp [step,program,entered,selecting,indexWritten,selected,writeNat,next,
    hd.index,hd.count,hd.one,hj,evalNat]

theorem negative_selection (N : ℕ) (x : Fin N → ℂ) (B n L a d j : ℕ) (s : State)
    (hd : Data n L a d j s) (hj : n≤j) (hB : 20≤B) (hs : WordBound B s) :
    BoundedRuns program N x B (entered s) 3
      (selected s 7 (L-j) (if L-j<n then 9 else 14)) := by
  have hent:=changePC_bound B s 4 hs (by omega)
  have hb:=changePC_bound B s 7 hs (by omega)
  have hL:L≤B:=by rw [←hd.width];exact hs.2.1 1
  have hw:=writeNat_bound B (selecting s 7) 7 (L-j) hb (by change 8≤B;omega) (by omega)
  have hf:=changePC_bound B (indexWritten s 7 (L-j)) (if L-j<n then 9 else 14) hw
    (by split_ifs <;> omega)
  refine .next hent (u:=selecting s 7) ?_ (.next hb (u:=indexWritten s 7 (L-j)) ?_
    (.next hw ?_ (.refl hf)))
  all_goals simp [step,program,entered,selecting,indexWritten,selected,writeNat,next,
    hd.index,hd.count,hd.width,show ¬j<n by omega,evalNat]

theorem load_runs (N : ℕ) (x : Fin N → ℂ) (B n a k : ℕ) (eta : ℂ) (s : State)
    (hp : s.pc=9) (hk : s.natReg 7=k) (ha : s.natReg 2=a)
    (h1 : s.natReg 3=1) (h2 : s.natReg 4=2) (hc : Coefficients n a eta s)
    (hkn : k<n) (hB : 20≤B) (haB : a+2*n≤B) (hs : WordBound B s) :
    BoundedRuns program N x B s 5 (loaded s eta a k) := by
  have hco:s.scalarHeap (a+k*2+1)=some (prepared (UniformChirp.chirp eta⁻¹ k)):=by
    simpa [Nat.mul_comm] using hc k hkn
  have hd:=writeNat_bound B s 6 (2*k) hs (by omega) (by omega)
  have hb:=writeNat_bound B (doubleIndex s k) 6 (a+2*k) hd
    (by simp [doubleIndex,writeNat,next,hp];omega) (by omega)
  have hi:=writeNat_bound B (coefficientAddress s a k) 6 (a+2*k+1) hb
    (by simp [coefficientAddress,doubleIndex,writeNat,next,hp];omega) (by omega)
  have hl:=writeScalar_bound B (inverseAddress s a k) 0 (prepared (UniformChirp.chirp eta⁻¹ k)) hi
    (by simp [inverseAddress,coefficientAddress,doubleIndex,writeNat,next,hp];omega)
  have hf:=changePC_bound B (coefficientLoaded s eta a k) 15 hl (by omega)
  refine .next hs (u:=doubleIndex s k) ?_ (.next hd (u:=coefficientAddress s a k) ?_
    (.next hb (u:=inverseAddress s a k) ?_ (.next hi (u:=coefficientLoaded s eta a k) ?_
      (.next hl ?_ (.refl hf)))))
  all_goals simp [step,program,loaded,coefficientLoaded,inverseAddress,coefficientAddress,
    doubleIndex,writeNat,writeScalar,next,hp,hk,ha,h1,h2,hco,evalNat,Nat.mul_comm]

def result (s : State) (eta : ℂ) (n L a j : ℕ) : State :=
  if j<n then loaded (selected s 5 j 9) eta a j
  else if L-j<n then loaded (selected s 7 (L-j) 9) eta a (L-j)
  else zeroResult (selected s 7 (L-j) 14)

def stored (s : State) : State :=
  {next s with scalarHeap:=Function.update s.scalarHeap (s.natReg 9) (some (s.scalarReg 0))}
def advanceAddress (s : State) := writeNat (stored s) 9 (s.natReg 9+1)
def rowEnd (s : State) (j : ℕ) : State := {writeNat (advanceAddress s) 5 (j+1) with pc:=3}

structure TailReady (d j : ℕ) (value : Scalar) (s : State) : Prop where
  pc : s.pc=15
  one : s.natReg 3=1
  index : s.natReg 5=j
  address : s.natReg 9=d+j
  value : s.scalarReg 0=value

theorem result_values (n L a d j : ℕ) (eta : ℂ) (s : State) (hd : Data n L a d j s) :
    TailReady d j (kernelScalar eta n L j) (result s eta n L a j) ∧
    (result s eta n L a j).natHeap=s.natHeap ∧
    (result s eta n L a j).scalarHeap=s.scalarHeap ∧
    (result s eta n L a j).outputs=s.outputs ∧
    (result s eta n L a j).rootOrders=s.rootOrders ∧
    (∀ r,r≠6 → r≠7 → (result s eta n L a j).natReg r=s.natReg r) ∧
    ∀ r,r≠0 → (result s eta n L a j).scalarReg r=s.scalarReg r := by
  unfold result
  split_ifs with hpos hneg
  all_goals refine ⟨?_,rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals first
    | constructor <;> simp [loaded,coefficientLoaded,inverseAddress,coefficientAddress,doubleIndex,
        selected,indexWritten,selecting,zeroResult,writeScalar,writeNat,next,
        kernelScalar,hd.one,hd.index,hd.address] <;> simp_all <;>
        split_ifs <;> first | rfl | omega
    | intro r h6 h7; simp [loaded,coefficientLoaded,inverseAddress,coefficientAddress,doubleIndex,
        selected,indexWritten,selecting,zeroResult,writeScalar,writeNat,next,h6,h7]
    | intro r hr; simp [loaded,coefficientLoaded,inverseAddress,coefficientAddress,doubleIndex,
        selected,indexWritten,selecting,zeroResult,writeScalar,writeNat,next,hr]

theorem tail_runs (N : ℕ) (x : Fin N → ℂ) (B d j L : ℕ) (value : Scalar) (s : State)
    (ht : TailReady d j value s) (hj : j<L) (hB : 20≤B) (hd : d+L≤B)
    (hs : WordBound B s) : BoundedRuns program N x B s 4 (rowEnd s j) := by
  obtain ⟨hp,h1,hi,ha,hv⟩:=ht
  have hst:=UniformInPlaceMachine.storeScalar_bound B s (s.natReg 9) (s.scalarReg 0) hs
    (by omega) (hs.2.1 9)
  have hadv:=writeNat_bound B (stored s) 9 (s.natReg 9+1) hst
    (by simp [stored,next,hp];omega) (by rw [ha];omega)
  have hidx:=writeNat_bound B (advanceAddress s) 5 (j+1) hadv
    (by simp [advanceAddress,stored,writeNat,next,hp];omega) (by omega)
  have hf:=changePC_bound B (writeNat (advanceAddress s) 5 (j+1)) 3 hidx (by omega)
  refine .next hs (u:=stored s) ?_ (.next hst (u:=advanceAddress s) ?_
    (.next hadv (u:=writeNat (advanceAddress s) 5 (j+1)) ?_ (.next hidx ?_ (.refl hf))))
  all_goals simp [step,program,rowEnd,advanceAddress,stored,writeNat,next,hp,h1,hi,ha,hv,evalNat]

theorem result_runs (N : ℕ) (x : Fin N → ℂ) (B n L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hc : Coefficients n a eta s)
    (hB : 20≤B) (haB : a+2*n≤B) (hs : WordBound B s) :
    BoundedRuns program N x B (entered s) (if j<n ∨ L-j<n then 8 else 4)
      (result s eta n L a j) := by
  by_cases hpos:j<n
  · have hp:=positive_selection N x B n L a d j s hd hpos hB hs
    have hl:=load_runs N x B n a j eta (selected s 5 j 9) rfl
      (by simp [selected,indexWritten,writeNat,next])
      (by simp [selected,indexWritten,selecting,writeNat,next,hd.bank])
      (by simp [selected,indexWritten,selecting,writeNat,next,hd.one])
      (by simp [selected,indexWritten,selecting,writeNat,next,hd.two]) hc hpos hB haB hp.final_bound
    simpa [result,hpos] using hp.trans hl
  · have hp:=negative_selection N x B n L a d j s hd (by omega) hB hs
    by_cases hneg:L-j<n
    · have hp':BoundedRuns program N x B (entered s) 3 (selected s 7 (L-j) 9):=by
        simpa [hneg] using hp
      have hl:=load_runs N x B n a (L-j) eta (selected s 7 (L-j) 9) rfl
        (by simp [selected,indexWritten,writeNat,next])
        (by simp [selected,indexWritten,selecting,writeNat,next,hd.bank])
        (by simp [selected,indexWritten,selecting,writeNat,next,hd.one])
        (by simp [selected,indexWritten,selecting,writeNat,next,hd.two]) hc hneg hB haB hp'.final_bound
      simpa [result,hpos,hneg] using hp'.trans hl
    · have hp':BoundedRuns program N x B (entered s) 3 (selected s 7 (L-j) 14):=by
        simpa [hneg] using hp
      have hb:=writeScalar_bound B (selected s 7 (L-j) 14) 0 (prepared 0) hp'.final_bound
        (by change 15≤B;omega)
      have hz:BoundedRuns program N x B (selected s 7 (L-j) 14) 1
          (zeroResult (selected s 7 (L-j) 14)):=by
        refine .next hp'.final_bound ?_ (.refl hb)
        simp [step,program,zeroResult,selected,prepared]
      simpa [result,hpos,hneg] using hp'.trans hz

theorem row_runs (N : ℕ) (x : Fin N → ℂ) (B n L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hj : j<L) (hc : Coefficients n a eta s)
    (hB : 20≤B) (ha : a+2*n≤d) (hdB : d+L≤B) (hs : WordBound B s) :
    BoundedRuns program N x B s (if j<n ∨ L-j<n then 13 else 9)
      (rowEnd (result s eta n L a j) j) := by
  have hent:=changePC_bound B s 4 hs (by omega)
  have he:BoundedRuns program N x B s 1 (entered s):=by
    refine .next hs ?_ (.refl hent)
    simp [step,program,entered,hd.pc,hd.index,hd.width,hj]
  have hr:=result_runs N x B n L a d j eta s hd hc hB (by omega) hs
  have ht:=tail_runs N x B d j L (kernelScalar eta n L j) (result s eta n L a j)
    (result_values n L a d j eta s hd).1 hj hB hdB hr.final_bound
  convert (he.trans hr).trans ht using 1
  split_ifs <;> rfl

theorem row_data (n L a d j : ℕ) (eta : ℂ) (s : State) (hd : Data n L a d j s) :
    Data n L a d (j+1) (rowEnd (result s eta n L a j) j) := by
  have hv:=result_values n L a d j eta s hd
  constructor
  · rfl
  · exact (hv.2.2.2.2.2.1 0 (by omega) (by omega)).trans hd.count
  · exact (hv.2.2.2.2.2.1 1 (by omega) (by omega)).trans hd.width
  · exact (hv.2.2.2.2.2.1 2 (by omega) (by omega)).trans hd.bank
  · exact hv.1.one
  · exact (hv.2.2.2.2.2.1 4 (by omega) (by omega)).trans hd.two
  · simp [rowEnd,writeNat,next]
  · simp [rowEnd,advanceAddress,stored,writeNat,next,hv.1.address,Nat.add_assoc]

theorem row_heap (n L a d j : ℕ) (eta : ℂ) (s : State) (hd : Data n L a d j s) :
    (rowEnd (result s eta n L a j) j).scalarHeap=
      Function.update s.scalarHeap (d+j) (some (kernelScalar eta n L j)) := by
  have hv:=result_values n L a d j eta s hd
  simp only [rowEnd,advanceAddress,stored,writeNat,next,hv.1.address,hv.1.value,hv.2.2.1]

def Partial (d j n L : ℕ) (eta : ℂ) (s : State) : Prop :=
  ∀ k,k<j → s.scalarHeap (d+k)=some (kernelScalar eta n L k)

/-- Only scratch Nat3..7,Nat9 and Scalar0 may change. Headers, prepared
coefficients, arbitrary unrelated dirty cells and all roots/outputs survive. -/
def Frame (d L : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<d ∨ d+L≤b → u.scalarHeap b=s.scalarHeap b) ∧
  (∀ r,r<3 ∨ 8≤r → r≠9 → u.natReg r=s.natReg r) ∧
  ∀ r,r≠0 → u.scalarReg r=s.scalarReg r

theorem frame_refl (d L : ℕ) (s : State) : Frame d L s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _=>rfl⟩

theorem frame_trans {d L : ℕ} {s u v : State} (hu : Frame d L s u) (hv : Frame d L u v) :
    Frame d L s v :=
  ⟨hv.1.trans hu.1,hv.2.1.trans hu.2.1,hv.2.2.1.trans hu.2.2.1,
    fun b hb=>(hv.2.2.2.1 b hb).trans (hu.2.2.2.1 b hb),
    fun r hr h9=>(hv.2.2.2.2.1 r hr h9).trans (hu.2.2.2.2.1 r hr h9),
    fun r hr=>(hv.2.2.2.2.2 r hr).trans (hu.2.2.2.2.2 r hr)⟩

theorem row_frame (n L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hj : j<L) : Frame d L s (rowEnd (result s eta n L a j) j) := by
  have hv:=result_values n L a d j eta s hd
  refine ⟨hv.2.1,hv.2.2.2.1,hv.2.2.2.2.1,?_,?_,hv.2.2.2.2.2.2⟩
  · intro b hb
    rw [row_heap n L a d j eta s hd,Function.update_of_ne (by omega)]
  · intro r hr h9
    change (Function.update (Function.update (result s eta n L a j).natReg 9
      ((result s eta n L a j).natReg 9+1)) 5 (j+1)) r=s.natReg r
    rw [Function.update_of_ne (by omega),Function.update_of_ne h9]
    exact hv.2.2.2.2.2.1 r (by omega) (by omega)

theorem row_partial (n L a d j : ℕ) (eta : ℂ) (s : State)
    (hd : Data n L a d j s) (hp : Partial d j n L eta s) :
    Partial d (j+1) n L eta (rowEnd (result s eta n L a j) j) := by
  intro k hk
  rw [row_heap n L a d j eta s hd]
  by_cases h:k=j
  · subst k;exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by omega)]
    exact hp k (by omega)

theorem coefficients_frame {n L a d : ℕ} {eta : ℂ} {s u : State}
    (hc : Coefficients n a eta s) (ha : a+2*n≤d) (hf : Frame d L s u) :
    Coefficients n a eta u := by
  intro j hj
  rw [hf.2.2.2.1 (a+2*j+1) (Or.inl (by omega))]
  exact hc j hj

def loopCost (n L j : ℕ) : ℕ → ℕ
  | 0 => 2
  | t+1 => (if j<n ∨ L-j<n then 13 else 9)+loopCost n L (j+1) t

theorem loopCost_bound (n L j t : ℕ) : loopCost n L j t≤13*t+2 := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    have h:=ih (j+1)
    simp only [loopCost,Nat.mul_succ]
    split_ifs <;> omega

/- Paper stage: §5.3, linear operand preparation, PDF p.23: actual per-coordinate machine transitions and preserved source-bank reads. -/
theorem loop_execution (N : ℕ) (x : Fin N → ℂ) (B n L a d : ℕ) (eta : ℂ)
    (hB : 20≤B) (ha : a+2*n≤d) (hdB : d+L≤B) (t : ℕ) : ∀ j s,
    j+t=L → Data n L a d j s → Coefficients n a eta s → Partial d j n L eta s →
    WordBound B s → ∃ u, BoundedExecution program N x B s (loopCost n L j t) u ∧
    Partial d L n L eta u ∧ Frame d L s u ∧ u.pc=19 := by
  induction t with
  | zero =>
    intro j s hj hd hc hp hs
    have he:j=L:=by omega
    let u:State:={s with pc:=19}
    have hu:=changePC_bound B s 19 hs (by omega)
    refine ⟨u,?_,?_,frame_refl d L s,rfl⟩
    · refine .next hs (u:=u) ?_ (.halt hu ?_)
      · simp [step,program,u,hd.pc,hd.index,hd.width,he]
      · simp [step,program,u]
    · simpa [Partial,u,he] using hp
  | succ t ih =>
    intro j s hj hd hc hp hs
    have hjL:j<L:=by omega
    have he:=row_runs N x B n L a d j eta s hd hjL hc hB ha hdB hs
    have hf:=row_frame n L a d j eta s hd hjL
    obtain ⟨u,hu,hp',hf',hpc⟩:=ih (j+1) (rowEnd (result s eta n L a j) j) (by omega)
      (row_data n L a d j eta s hd) (coefficients_frame hc ha hf)
      (row_partial n L a d j eta s hd hp) he.final_bound
    exact ⟨u,by simpa [loopCost] using he.executes hu,hp',frame_trans hf hf',hpc⟩

theorem initialized_frame (d L : ℕ) (s : State) : Frame d L s (initialized s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_,fun _ _=>rfl⟩
  intro r hr h9
  simp [initialized,initTwo,initOne,writeNat,next,show r≠3 by omega,
    show r≠4 by omega,show r≠5 by omega]

/-- Actual charged preparation from the existing inverse-chirp table. No input
read, root request, scalar branch, division, or hidden table oracle occurs. -/
theorem kernel_execution (N : ℕ) (x : Fin N → ℂ) (B n L a d : ℕ) (eta : ℂ) (s : State)
    (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d) (hc : Coefficients n a eta s)
    (hB : 20≤B) (hdisjoint : a+2*n≤d) (hspace : d+L≤B) (hs : WordBound B s) :
    ∃ u, BoundedExecution program N x B s (3+loopCost n L 0 L) u ∧
      Partial d L n L eta u ∧ Frame d L s u ∧ u.pc=19 := by
  have hstart:=startup_runs N x B s hp hB hs
  obtain ⟨u,hu,ht,hf,hpc⟩:=loop_execution N x B n L a d eta hB hdisjoint hspace L 0
    (initialized s) (by omega) (initialized_data n L a d s hp hn hL ha hd)
    hc (by intro k hk;omega) hstart.final_bound
  exact ⟨u,hstart.executes hu,ht,frame_trans (initialized_frame d L s) hf,hpc⟩

theorem kernel_cost_bound (n L : ℕ) : 3+loopCost n L 0 L≤13*L+5 := by
  have h:=loopCost_bound n L 0 L;omega

theorem coefficients_of_chirp_table {n a : ℕ} {eta : ℂ} {s : State}
    (h : UniformChirpTableMachine.Partial a n eta s) : Coefficients n a eta s :=
  fun j hj => (h j hj).2

theorem kernelScalar_prepared (eta : ℂ) (n L j : ℕ) :
    (kernelScalar eta n L j).dependent=false := by
  unfold kernelScalar
  split_ifs <;> rfl

theorem inverse_chirp_zpow (eta : ℂ) (j : ℕ) :
    UniformChirp.chirp eta⁻¹ j=eta^(-((j:ℤ)^2)) := by
  simp [UniformChirp.chirp,zpow_neg,←zpow_natCast]

/- Paper stage: §5.3, signed support following (5.7), PDF p.22: identify the printed positive/end-of-array values with the cyclic signed kernel. -/
theorem kernelScalar_value (eta : ℂ) (n L : ℕ) [NeZero L] (_hL : 2*n≤L) (z : ZMod L) :
    (kernelScalar eta n L z.val).value=UniformCyclic.chirpKernel eta n z := by
  have hz:=ZMod.val_lt z
  by_cases hpos:z.val<n
  · simp [kernelScalar,UniformCyclic.chirpKernel,UniformCyclic.signedRepresentative,
      hpos,prepared,inverse_chirp_zpow]
  · by_cases hneg:L-z.val<n
    · have hs:(z.val:ℤ)-L = -((L-z.val:ℕ):ℤ):=by omega
      simp only [kernelScalar,ite_eq_right hpos,ite_eq_left hneg,prepared,
        UniformCyclic.chirpKernel,ite_eq_left (Or.inr hneg),
        UniformCyclic.signedRepresentative,hs,neg_sq,inverse_chirp_zpow]
    · simp [kernelScalar,UniformCyclic.chirpKernel,hpos,hneg,prepared]

/-- Fin addresses and cyclic Fourier coordinates use the same representative. -/
theorem kernelScalar_fin (eta : ℂ) (n L : ℕ) [NeZero L] (hL : 2*n≤L) (z : Fin L) :
    kernelScalar eta n L z.val=prepared
      (UniformCyclic.chirpKernel eta n (OAI.ExactFourier.FourierCRT.finZMod L z)) := by
  have hv : (kernelScalar eta n L z.val).value=
      UniformCyclic.chirpKernel eta n (OAI.ExactFourier.FourierCRT.finZMod L z) := by
    simpa [OAI.ExactFourier.FourierCRT.finZMod,Nat.mod_eq_of_lt z.isLt]
      using kernelScalar_value eta n L hL (OAI.ExactFourier.FourierCRT.finZMod L z)
  have hd:=kernelScalar_prepared eta n L z.val
  cases hk : kernelScalar eta n L z.val with
  | mk value dependent =>
    simp only [hk] at hv hd
    cases hv
    cases hd
    rfl

theorem signed_kernel_execution (N : ℕ) (x : Fin N → ℂ) (B n L a d : ℕ) [NeZero L]
    (eta : ℂ) (s : State) (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d)
    (hc : UniformChirpTableMachine.Partial a n eta s) (hB : 20≤B)
    (hpadding : 2*n≤L) (hdisjoint : a+2*n≤d) (hspace : d+L≤B) (hs : WordBound B s) :
    ∃ u, BoundedExecution program N x B s (3+loopCost n L 0 L) u ∧
      (∀ z : Fin L,u.scalarHeap (d+z.val)=some (prepared
        (UniformCyclic.chirpKernel eta n (OAI.ExactFourier.FourierCRT.finZMod L z)))) ∧
      Frame d L s u ∧ u.pc=19 := by
  obtain ⟨u,hu,ht,hf,hpc⟩:=kernel_execution N x B n L a d eta s hp hn hL ha hd
    (coefficients_of_chirp_table hc) hB hdisjoint hspace hs
  refine ⟨u,hu,?_,hf,hpc⟩
  intro z
  rw [ht z.val z.isLt,kernelScalar_fin eta n L hpadding z]

/- Paper stage: §5.3, operand preparation, PDF pp.22-23: the literal kernel producer supplies every scalar cell with a prepared tag. -/
theorem specified_kernel_execution (n : ℕ) (x : Fin n → ℂ) (B L a d : ℕ) [NeZero L]
    (s : State) (hp : s.pc=0) (hn : s.natReg 0=n) (hL : s.natReg 1=L)
    (ha : s.natReg 2=a) (hd : s.natReg 9=d)
    (hc : UniformChirpTableMachine.Partial a n (OAI.ExactFourier.zeta (2*n)) s)
    (hB : 20≤B) (hpadding : 2*n≤L) (hdisjoint : a+2*n≤d)
    (hspace : d+L≤B) (hs : WordBound B s) :
    ∃ u, BoundedExecution program n x B s (3+loopCost n L 0 L) u ∧
      (∀ z : Fin L,u.scalarHeap (d+z.val)=some (prepared
        (UniformCyclic.chirpKernel (OAI.ExactFourier.zeta (2*n)) n
          (OAI.ExactFourier.FourierCRT.finZMod L z)))) ∧
      Frame d L s u ∧ u.pc=19 :=
  signed_kernel_execution n x B n L a d _ s hp hn hL ha hd hc hB hpadding hdisjoint hspace hs

theorem contextFree : UniformContext.ContextFree program := by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program]

/-- The kernel follows the padded input region, with no extra permanent bank. -/
def kernelBase (ell n L : ℕ) : ℕ := ell+7+2*n+L
def wordBudget (ell n L : ℕ) : ℕ := ell+7+2*n+2*L+20

theorem layout_bounds (ell n L a : ℕ) (ha : a≤ell+7) :
    20≤wordBudget ell n L ∧ a+2*n≤kernelBase ell n L ∧
      kernelBase ell n L+L≤wordBudget ell n L := by
  unfold kernelBase wordBudget
  omega

theorem polynomial_word_budget (ell n L : ℕ) (hn : 0<n) (hell : ell≤n) (hL : L≤4*n) :
    wordBudget ell n L≤(n+2)^4 := by
  unfold wordBudget
  have h:ell+7+2*n+2*L+20≤11*n+27:=by omega
  calc
    ell+7+2*n+2*L+20≤11*n+27:=h
    _≤(n+2)^4:=by nlinarith [Nat.zero_le (n^4),Nat.zero_le (n^3),Nat.zero_le (n^2)]

theorem linear_cost (n L : ℕ) (hn : 0<n) (hL : L≤4*n) :
    3+loopCost n L 0 L≤57*n := by
  have h:=kernel_cost_bound n L
  omega

theorem inverse_bank_preserved {n L a d : ℕ} {eta : ℂ} {s u : State}
    (hc : UniformChirpTableMachine.Partial a n eta s) (ha : a+2*n≤d)
    (hf : Frame d L s u) : UniformChirpTableMachine.Partial a n eta u := by
  intro j hj
  rw [hf.2.2.2.1 (a+2*j) (Or.inl (by omega)),
    hf.2.2.2.1 (a+2*j+1) (Or.inl (by omega))]
  exact hc j hj

end
end ExactFourierCircuits.UniformChirpKernelMachine
