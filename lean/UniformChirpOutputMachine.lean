import UniformPaddedInputMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace ExactFourierCircuits.UniformChirpOutputMachine
open UniformMachine
open UniformPairMachine (prepared)
noncomputable section

/-- Nat8=n,17=L,25=chirp base,26=transform base,27=normalization
address. Reverse the cyclic frequency index, normalize, apply the chirp and emit. -/
def program : Program :=
  [.natLiteral 31 1,.natLiteral 32 2,.natLiteral 30 0,.loadScalar 1 27,
   .branchLT 30 8 5 17,.natBinary .sub 33 17 30,.natBinary .mod 33 33 17,
   .natBinary .add 34 26 33,.loadScalar 0 34,.fieldBinary .mul 0 1 0,
   .natBinary .mul 35 30 32,.natBinary .add 35 25 35,.loadScalar 2 35,
   .fieldBinary .mul 0 2 0,.output 30 0,.natBinary .add 30 30 31,.jump 4,.halt]

theorem program_length : program.length=18 := rfl

def negativeIndex (L j : ℕ) := (L-j)%L
def scaled (c : ℂ) (v : Scalar) : Scalar := ⟨c*v.value,v.dependent⟩
def value {L : ℕ} (hL : 0<L) (eta kappa : ℂ) (v : Fin L → Scalar) (j : ℕ) : Scalar :=
  scaled (UniformChirp.chirp eta j) (scaled kappa (v ⟨negativeIndex L j,Nat.mod_lt _ hL⟩))

def Coefficients (n a : ℕ) (eta : ℂ) (s : State) : Prop :=
  UniformPaddedInputMachine.Coefficients n a eta s
def Values (L d : ℕ) (v : Fin L → Scalar) (s : State) : Prop :=
  ∀ j,s.scalarHeap (d+j.val)=some (v j)

structure Data (n L a d j : ℕ) (kappa : ℂ) (s : State) : Prop where
  pc : s.pc=4
  count : s.natReg 8=n
  width : s.natReg 17=L
  bank : s.natReg 25=a
  transform : s.natReg 26=d
  one : s.natReg 31=1
  two : s.natReg 32=2
  index : s.natReg 30=j
  normalization : s.scalarReg 1=prepared kappa

def entered (s : State) : State := {s with pc:=5}
def difference (s : State) (L j : ℕ) := writeNat (entered s) 33 (L-j)
def residue (s : State) (L j : ℕ) := writeNat (difference s L j) 33 (negativeIndex L j)
def address (s : State) (L d j : ℕ) := writeNat (residue s L j) 34 (d+negativeIndex L j)
def loaded {L : ℕ} (hL : 0<L) (s : State) (d j : ℕ) (v : Fin L → Scalar) :=
  writeScalar (address s L d j) 0 (v ⟨negativeIndex L j,Nat.mod_lt _ hL⟩)
def normalized {L : ℕ} (hL : 0<L) (s : State) (d j : ℕ) (kappa : ℂ) (v : Fin L → Scalar) :=
  writeScalar (loaded hL s d j v) 0 (scaled kappa (v ⟨negativeIndex L j,Nat.mod_lt _ hL⟩))
def doubleIndex {L : ℕ} (hL : 0<L) (s : State) (d j : ℕ) (kappa : ℂ) (v : Fin L → Scalar) :=
  writeNat (normalized hL s d j kappa v) 35 (2*j)
def coefficientAddress {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (kappa : ℂ) (v : Fin L → Scalar) :=
  writeNat (doubleIndex hL s d j kappa v) 35 (a+2*j)
def coefficientLoaded {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ) (v : Fin L → Scalar) :=
  writeScalar (coefficientAddress hL s a d j kappa v) 2 (prepared (UniformChirp.chirp eta j))
def completed {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ) (v : Fin L → Scalar) :=
  writeScalar (coefficientLoaded hL s a d j eta kappa v) 0 (value hL eta kappa v j)
def emitted (s : State) (j : ℕ) (v : Scalar) : State :=
  {next s with outputs:=Function.update s.outputs j (some v.value)}
def rowEnd {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ) (v : Fin L → Scalar) : State :=
  {writeNat (emitted (completed hL s a d j eta kappa v) j (value hL eta kappa v j))
    30 (j+1) with pc:=4}

theorem row_runs {n L : ℕ} (x : Fin n → ℂ) (hL : 0<L) (B a d j : ℕ)
    (eta kappa : ℂ) (v : Fin L → Scalar) (s : State)
    (hd : Data n L a d j kappa s) (hj : j<n) (hc : Coefficients n a eta s)
    (hv : Values L d v s) (hB : 64≤B) (ha : a+2*n≤B) (hdB : d+L≤B)
    (hnB : n≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 13 (rowEnd hL s a d j eta kappa v) := by
  obtain ⟨hp,hn,hw,hbank,ht,h1,h2,hi,hk⟩:=hd
  have hLB:L≤B:=by simpa [hw] using hs.2.1 17
  have hidx:negativeIndex L j<L:=Nat.mod_lt _ hL
  have hco:s.scalarHeap (a+j*2)=some (prepared (UniformChirp.chirp eta j)):=by
    simpa [Nat.mul_comm] using hc j hj
  have hread:s.scalarHeap (d+(L-j)%L)=some (v ⟨negativeIndex L j,hidx⟩):=
    hv ⟨negativeIndex L j,hidx⟩
  have hent:=changePC_bound B s 5 hs (by omega)
  have hdiff:=writeNat_bound B (entered s) 33 (L-j) hent
    (by change 5+1≤B;omega) (by omega)
  have hres:=writeNat_bound B (difference s L j) 33 (negativeIndex L j) hdiff
    (by simp [difference,entered,writeNat,next];omega) (by omega)
  have hadr:=writeNat_bound B (residue s L j) 34 (d+negativeIndex L j) hres
    (by simp [residue,difference,entered,writeNat,next];omega) (by omega)
  have hload:=writeScalar_bound B (address s L d j) 0 (v ⟨negativeIndex L j,hidx⟩) hadr
    (by simp [address,residue,difference,entered,writeNat,next];omega)
  have hnorm:=writeScalar_bound B (loaded hL s d j v) 0
    (scaled kappa (v ⟨negativeIndex L j,hidx⟩)) hload
    (by simp [loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega)
  have hdouble:=writeNat_bound B (normalized hL s d j kappa v) 35 (2*j) hnorm
    (by simp [normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega) (by omega)
  have hcadr:=writeNat_bound B (doubleIndex hL s d j kappa v) 35 (a+2*j) hdouble
    (by simp [doubleIndex,normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega) (by omega)
  have hcoef:=writeScalar_bound B (coefficientAddress hL s a d j kappa v) 2
    (prepared (UniformChirp.chirp eta j)) hcadr
    (by simp [coefficientAddress,doubleIndex,normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega)
  have hcomplete:=writeScalar_bound B (coefficientLoaded hL s a d j eta kappa v) 0
    (value hL eta kappa v j) hcoef
    (by simp [coefficientLoaded,coefficientAddress,doubleIndex,normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega)
  have hemit:WordBound B (emitted (completed hL s a d j eta kappa v) j (value hL eta kappa v j)):=
    emit_bound B (completed hL s a d j eta kappa v) j (value hL eta kappa v j).value
      ((completed hL s a d j eta kappa v).pc+1) hcomplete (by omega)
      (by simp [completed,coefficientLoaded,coefficientAddress,doubleIndex,normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega)
  have hinc:=writeNat_bound B (emitted (completed hL s a d j eta kappa v) j (value hL eta kappa v j))
    30 (j+1) hemit (by simp [emitted,completed,coefficientLoaded,coefficientAddress,doubleIndex,normalized,
      loaded,address,residue,difference,entered,writeNat,writeScalar,next];omega) (by omega)
  have hfinal:WordBound B (rowEnd hL s a d j eta kappa v):=changePC_bound B _ 4 hinc (by omega)
  refine .next hs (u:=entered s) ?_ (.next hent (u:=difference s L j) ?_
    (.next hdiff (u:=residue s L j) ?_ (.next hres (u:=address s L d j) ?_
      (.next hadr (u:=loaded hL s d j v) ?_ (.next hload (u:=normalized hL s d j kappa v) ?_
        (.next hnorm (u:=doubleIndex hL s d j kappa v) ?_ (.next hdouble (u:=coefficientAddress hL s a d j kappa v) ?_
          (.next hcadr (u:=coefficientLoaded hL s a d j eta kappa v) ?_ (.next hcoef (u:=completed hL s a d j eta kappa v) ?_
            (.next hcomplete (u:=emitted (completed hL s a d j eta kappa v) j (value hL eta kappa v j)) ?_
              (.next hemit (u:=writeNat (emitted (completed hL s a d j eta kappa v) j (value hL eta kappa v j)) 30 (j+1)) ?_
                (.next hinc ?_ (.refl hfinal)))))))))))))
  all_goals simp [step,program,rowEnd,emitted,completed,coefficientLoaded,coefficientAddress,doubleIndex,
    normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next,hp,hn,hw,hbank,ht,
    h1,h2,hi,hk,hj,hread,hco,evalNat,evalField,scaled,value,prepared,negativeIndex,
    Nat.mul_comm,show L≠0 by omega]

theorem row_data {n L : ℕ} (hL : 0<L) (a d j : ℕ) (eta kappa : ℂ)
    (v : Fin L → Scalar) (s : State) (h : Data n L a d j kappa s) :
    Data n L a d (j+1) kappa (rowEnd hL s a d j eta kappa v) := by
  obtain ⟨hp,hn,hw,ha,hd,h1,h2,hj,hk⟩:=h
  constructor <;> simp [rowEnd,emitted,completed,coefficientLoaded,coefficientAddress,doubleIndex,
    normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next,
    hp,hn,hw,ha,hd,h1,h2,hj,hk]

theorem row_outputs {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ)
    (v : Fin L → Scalar) : (rowEnd hL s a d j eta kappa v).outputs=
      Function.update s.outputs j (some (value hL eta kappa v j).value) := rfl

def Frame (n : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,n≤b → u.outputs b=s.outputs b) ∧
  ∀ r,r<30 ∨ 35<r → u.natReg r=s.natReg r

theorem frame_refl (n : ℕ) (s : State) : Frame n s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩

theorem frame_trans {n : ℕ} {s u v : State} (hu : Frame n s u) (hv : Frame n u v) :
    Frame n s v := ⟨hv.1.trans hu.1,hv.2.1.trans hu.2.1,hv.2.2.1.trans hu.2.2.1,
    fun b hb=>(hv.2.2.2.1 b hb).trans (hu.2.2.2.1 b hb),
    fun r hr=>(hv.2.2.2.2 r hr).trans (hu.2.2.2.2 r hr)⟩

theorem row_frame {n L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ)
    (v : Fin L → Scalar) (hj : j<n) : Frame n s (rowEnd hL s a d j eta kappa v) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro b hb
    rw [row_outputs,Function.update_of_ne (by omega)]
  · intro r hr
    simp [rowEnd,emitted,completed,coefficientLoaded,coefficientAddress,doubleIndex,
      normalized,loaded,address,residue,difference,entered,writeNat,writeScalar,next,
      show r≠30 by omega,show r≠33 by omega,show r≠34 by omega,show r≠35 by omega]

def Partial {L : ℕ} (hL : 0<L) (eta kappa : ℂ) (v : Fin L → Scalar) (j : ℕ) (s : State) : Prop :=
  ∀ k,k<j → s.outputs k=some (value hL eta kappa v k).value

theorem row_partial {L : ℕ} (hL : 0<L) (s : State) (a d j : ℕ) (eta kappa : ℂ)
    (v : Fin L → Scalar) (hp : Partial hL eta kappa v j s) :
    Partial hL eta kappa v (j+1) (rowEnd hL s a d j eta kappa v) := by
  intro k hk
  rw [row_outputs]
  by_cases he:k=j
  · subst k;exact Function.update_self _ _ _
  · rw [Function.update_of_ne he]
    exact hp k (by omega)

theorem loop_execution {n L : ℕ} (x : Fin n → ℂ) (hL : 0<L) (B a d : ℕ)
    (eta kappa : ℂ) (v : Fin L → Scalar) (hB : 64≤B) (ha : a+2*n≤B)
    (hdB : d+L≤B) (hnB : n≤B) (t : ℕ) : ∀ j s,
    j+t=n → Data n L a d j kappa s → Coefficients n a eta s → Values L d v s →
    Partial hL eta kappa v j s → WordBound B s → ∃ u,
    BoundedExecution program n x B s (13*t+2) u ∧ Partial hL eta kappa v n u ∧
    Frame n s u ∧ u.pc=17 := by
  induction t with
  | zero =>
    intro j s hj hd hc hv hp hs
    have he:j=n:=by omega
    let u:State:={s with pc:=17}
    have hu:WordBound B u:=changePC_bound B s 17 hs (by omega)
    refine ⟨u,?_,?_,frame_refl n s,rfl⟩
    · refine .next hs (u:=u) ?_ (.halt hu ?_)
      · simp [step,program,u,hd.pc,hd.index,hd.count,he]
      · simp [step,program,u]
    · simpa [Partial,u,he] using hp
  | succ t ih =>
    intro j s hj hd hc hv hp hs
    have hjn:j<n:=by omega
    have hr:=row_runs x hL B a d j eta kappa v s hd hjn hc hv hB ha hdB hnB hs
    have hf:=row_frame hL s a d j eta kappa v hjn
    obtain ⟨u,hu,hp',hf',hpc⟩:=ih (j+1) (rowEnd hL s a d j eta kappa v) (by omega)
      (row_data hL a d j eta kappa v s hd) hc hv (row_partial hL s a d j eta kappa v hp)
      hr.final_bound
    refine ⟨u,?_,hp',frame_trans hf hf',hpc⟩
    convert hr.executes hu using 1 <;> omega

def initOne (s : State) := writeNat s 31 1
def initTwo (s : State) := writeNat (initOne s) 32 2
def initIndex (s : State) := writeNat (initTwo s) 30 0
def initialized (s : State) (kappa : ℂ) := writeScalar (initIndex s) 1 (prepared kappa)

theorem startup_runs {n : ℕ} (x : Fin n → ℂ) (B c : ℕ) (kappa : ℂ) (s : State)
    (hp : s.pc=0) (hc : s.natReg 27=c) (hnorm : s.scalarHeap c=some (prepared kappa))
    (hB : 64≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 4 (initialized s kappa) := by
  have h1:=writeNat_bound B s 31 1 hs (by omega) (by omega)
  have h2:=writeNat_bound B (initOne s) 32 2 h1
    (by simp [initOne,writeNat,next,hp];omega) (by omega)
  have h3:=writeNat_bound B (initTwo s) 30 0 h2
    (by simp [initTwo,initOne,writeNat,next,hp];omega) (by omega)
  have h4:=writeScalar_bound B (initIndex s) 1 (prepared kappa) h3
    (by simp [initIndex,initTwo,initOne,writeNat,next,hp];omega)
  refine .next hs (u:=initOne s) ?_ (.next h1 (u:=initTwo s) ?_
    (.next h2 (u:=initIndex s) ?_ (.next h3 (u:=initialized s kappa) ?_ (.refl h4))))
  all_goals simp [step,program,initialized,initIndex,initTwo,initOne,writeNat,writeScalar,next,hp,hc,hnorm]

theorem initialized_data {n : ℕ} (L a d : ℕ) (kappa : ℂ) (s : State)
    (hp : s.pc=0) (hn : s.natReg 8=n) (hL : s.natReg 17=L)
    (ha : s.natReg 25=a) (hd : s.natReg 26=d) : Data n L a d 0 kappa (initialized s kappa) := by
  constructor <;> simp [initialized,initIndex,initTwo,initOne,writeNat,writeScalar,next,hp,hn,hL,ha,hd]

theorem initialized_frame (n : ℕ) (kappa : ℂ) (s : State) : Frame n s (initialized s kappa) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr
  simp [initialized,initIndex,initTwo,initOne,writeNat,writeScalar,next,
    show r≠30 by omega,show r≠31 by omega,show r≠32 by omega]

/-- One literal program normalizes and emits every original output coordinate.
The transform and all coefficient heaps are read only. -/
theorem output_execution {n L : ℕ} (x : Fin n → ℂ) (hL : 0<L) (B a d c : ℕ)
    (eta kappa : ℂ) (v : Fin L → Scalar) (s : State)
    (hp : s.pc=0) (hn : s.natReg 8=n) (hwidth : s.natReg 17=L)
    (ha : s.natReg 25=a) (hd : s.natReg 26=d) (hc : s.natReg 27=c)
    (hnorm : s.scalarHeap c=some (prepared kappa)) (hcoeff : Coefficients n a eta s)
    (hvalues : Values L d v s) (hB : 64≤B) (hab : a+2*n≤B) (hdb : d+L≤B)
    (hs : WordBound B s) : ∃ u, BoundedExecution program n x B s (13*n+6) u ∧
    Partial hL eta kappa v n u ∧ Frame n s u ∧ u.pc=17 := by
  have hstart:=startup_runs x B c kappa s hp hc hnorm hB hs
  have hnB:n≤B:=by simpa [hn] using hs.2.1 8
  obtain ⟨u,hu,ht,hf,hpc⟩:=loop_execution x hL B a d eta kappa v hB hab hdb hnB n 0
    (initialized s kappa) (by omega) (initialized_data L a d kappa s hp hn hwidth ha hd)
    hcoeff hvalues (by intro k hk;omega) hstart.final_bound
  refine ⟨u,?_,ht,frame_trans (initialized_frame n kappa s) hf,hpc⟩
  convert hstart.executes hu using 1 <;> omega

theorem output_cost_linear {n : ℕ} (hn : 0<n) : 13*n+6≤19*n := by omega

theorem negativeIndex_ZMod {L : ℕ} (j : ℕ) (hj : j≤L) :
    (negativeIndex L j:ZMod L)= -(j:ZMod L) := by
  rw [negativeIndex,ZMod.natCast_mod,Nat.cast_sub hj]
  simp

def FinalSpectrum {n L : ℕ} [NeZero L] (x : Fin n → ℂ) (v : Fin L → Scalar) : Prop :=
  ∀ j,(v j).value=UniformCyclic.positiveDFT (fun t=>
    UniformCyclic.positiveDFT (UniformCyclic.paddedChirp (OAI.ExactFourier.zeta (2*n)) x) t *
    UniformCyclic.positiveDFT (UniformCyclic.chirpKernel (OAI.ExactFourier.zeta (2*n)) n) t)
    (OAI.ExactFourier.FourierCRT.finZMod L j)

theorem value_fourier {n L : ℕ} [NeZero L] (hn : 0<n) (hL : 0<L) (hnL : 2*n≤L)
    (x : Fin n → ℂ) (v : Fin L → Scalar) (hv : FinalSpectrum x v) (k : Fin n) :
    (value hL (OAI.ExactFourier.zeta (2*n)) (L:ℂ)⁻¹ v k.val).value=
      (OAI.ExactFourier.fourierMatrix n).mulVec x k := by
  have hi:OAI.ExactFourier.FourierCRT.finZMod L ⟨negativeIndex L k.val,Nat.mod_lt _ hL⟩=
      -(k.val:ZMod L):=negativeIndex_ZMod k.val (by have hk:=k.isLt;omega)
  have hc:UniformChirp.chirp (OAI.ExactFourier.zeta (2*n)) k.val=
      OAI.ExactFourier.zeta (2*n)^((k.val:ℤ)^2):=by simp [UniformChirp.chirp,←zpow_natCast]
  simp only [value,scaled]
  rw [hv ⟨negativeIndex L k.val,Nat.mod_lt _ hL⟩,hi,hc]
  simpa only [mul_assoc] using (UniformCyclic.bluestein_positive_transforms hn hnL x k).symm

/-- The final loop closes the standard DFT output contract from the actual last
transform's value postcondition. Preparation and transform executions remain
separate obligations of the caller. -/
theorem output_execution_dft {n L : ℕ} [NeZero L] (hn : 0<n) (hL : 0<L)
    (hnL : 2*n≤L) (x : Fin n → ℂ) (B a d c : ℕ) (v : Fin L → Scalar) (s : State)
    (hp : s.pc=0) (hcount : s.natReg 8=n) (hwidth : s.natReg 17=L)
    (ha : s.natReg 25=a) (hd : s.natReg 26=d) (hc : s.natReg 27=c)
    (hnorm : s.scalarHeap c=some (prepared (L:ℂ)⁻¹))
    (hcoeff : Coefficients n a (OAI.ExactFourier.zeta (2*n)) s)
    (hvalues : Values L d v s) (hspectrum : FinalSpectrum x v)
    (hB : 64≤B) (hab : a+2*n≤B) (hdb : d+L≤B) (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (13*n+6) u ∧ ComputesDFT n x u ∧ Frame n s u ∧ u.pc=17 := by
  obtain ⟨u,hu,ht,hf,hpc⟩:=output_execution x hL B a d c (OAI.ExactFourier.zeta (2*n))
    (L:ℂ)⁻¹ v s hp hcount hwidth ha hd hc hnorm hcoeff hvalues hB hab hdb hs
  refine ⟨u,hu,?_,hf,hpc⟩
  intro k
  rw [ht k.val k.isLt,value_fourier hn hL hnL x v hspectrum k]

end
end ExactFourierCircuits.UniformChirpOutputMachine
