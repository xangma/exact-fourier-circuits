import UniformChirpTableMachine
import UniformCRTHeaderMachine
import UniformBoundedAssembly
import UniformRootTableMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 (5.7)-(5.9), PDF pp.22-23
(`eq:chirp`, `eq:master-root`, `eq:root-size`).

Extracts eta from the already supplied master root by charged binary powering,
then executes the linear chirp-table producer. Header restoration and heap
frames are implementation details of the paper's charged preparation.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ExactFourierCircuits.UniformChirpPreparation
open UniformMachine UniformAssembly UniformPairMachine
noncomputable section

/-- Save the header, extract the canonical half-angle root from the existing
master root, generate the chirp table above the axis-root slots, and restore it. -/
/- Paper stage: §5.3 (5.8)-(5.9), PDF p.23: load the existing master root and use charged binary powering before generating chirps. -/
def program : Program :=
  [.natLiteral 34 0,.natBinary .add 44 0 34,.natLiteral 32 2,
   .natBinary .mul 31 8 32,.natBinary .div 0 24 31,.natLiteral 33 0,.loadScalar 1 33] ++
  UniformPowerMachine.program.map (relocate 7 19) ++
  [.natBinary .add 0 8 34,.natLiteral 35 7,.natBinary .add 9 10 35] ++
  UniformChirpTableMachine.program.map (relocate 22 42) ++
  [.natBinary .add 0 44 34,.halt]

theorem program_length : program.length=44 := rfl

theorem power_code : CodeAt UniformPowerMachine.program program 7 19 := by
  intro i hi;change i<12 at hi;interval_cases i <;> rfl

theorem chirp_code : CodeAt UniformChirpTableMachine.program program 22 42 := by
  intro i hi;change i<20 at hi;interval_cases i <;> rfl

def zeroed (s : State) := writeNat s 34 0
def saved (s : State) := writeNat (zeroed s) 44 (s.natReg 0)
def two (s : State) := writeNat (saved s) 32 2
def divisor (s : State) (n : ℕ) := writeNat (two s) 31 (2*n)
def exponent (s : State) (n D : ℕ) := writeNat (divisor s n) 0 (D/(2*n))
def address (s : State) (n D : ℕ) := writeNat (exponent s n D) 33 0
def rootLoaded (s : State) (n D : ℕ) := writeScalar (address s n D) 1 (prepared (OAI.ExactFourier.zeta D))

/-- Literal setup neither obtains a new root nor writes a table. -/
theorem startup_runs {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) (B D : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (hD : s.natReg 24=D)
    (hroot : s.scalarHeap 0=some (prepared (OAI.ExactFourier.zeta D)))
    (hB : 128≤B) (hnB : 2*n≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 7 (rootLoaded s n D) := by
  have hDB:D≤B:=by simpa [hD] using hs.2.1 24
  have h1:=writeNat_bound B (s) 34 0 hs (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (by omega)
  have h2:=writeNat_bound B (zeroed s) 44 (s.natReg 0) h1 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (hs.2.1 0)
  have h3:=writeNat_bound B (saved s) 32 2 h2 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (by omega)
  have h4:=writeNat_bound B (two s) 31 (2*n) h3 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (by omega)
  have h5:=writeNat_bound B (divisor s n) 0 (D/(2*n)) h4 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (by exact (Nat.div_le_self D (2*n)).trans hDB)
  have h6:=writeNat_bound B (exponent s n D) 33 0 h5 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega) (by omega)
  have h7:=writeScalar_bound B (address s n D) 1 (prepared (OAI.ExactFourier.zeta D)) h6 (by simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp];omega)
  refine .next hs (u:=zeroed s) ?_ (.next h1 (u:=saved s) ?_ (.next h2 (u:=two s) ?_ (.next h3 (u:=divisor s n) ?_ (.next h4 (u:=exponent s n D) ?_ (.next h5 (u:=address s n D) ?_ (.next h6 (u:=rootLoaded s n D) ?_ (.refl h7)))))))
  all_goals simp [step,program,UniformPowerMachine.program,UniformChirpTableMachine.program,rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp,h8,hD,hroot,evalNat,show 2*n≠0 by omega,show n≠0 by omega,Nat.mul_comm]

theorem setup_values (s : State) (n D : ℕ) :
    (rootLoaded s n D).natReg 0=D/(2*n) ∧
    (rootLoaded s n D).scalarReg 1=prepared (OAI.ExactFourier.zeta D) ∧
    (rootLoaded s n D).natReg 34=0 ∧ (rootLoaded s n D).natReg 44=s.natReg 0 := by
  simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next]

def SetupFrame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧
  ∀ r,5≤r → r≠0 → r≠31 → r≠32 → r≠33 → r≠34 → r≠44 → u.natReg r=s.natReg r

theorem setup_frame (s : State) (n D : ℕ) : SetupFrame s (rootLoaded s n D) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r h5 h0 h31 h32 h33 h34 h44
  simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,
    h0,h31,h32,h33,h34,h44]

/-- The only supplied root is the already requested master root. -/
/- Paper stage: §5.3, root extraction after (5.9), PDF p.23: D_*/(2n) powers recover the specified half-angle root without another request. -/
theorem halfAngle_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) (B D : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (hDreg : s.natReg 24=D)
    (hroot : s.scalarHeap 0=some (prepared (OAI.ExactFourier.zeta D)))
    (hD : 0<D) (hdiv : 2*n∣D) (hB : 128≤B) (hnB : 2*n≤B) (hs : WordBound B s) : ∃ u,
    BoundedRuns program n x B s (11+UniformPowerMachine.loopCost (D/(2*n))) u ∧
    u.scalarReg 0=prepared (OAI.ExactFourier.zeta (2*n)) ∧ SetupFrame s u ∧
    u.natReg 34=0 ∧ u.natReg 44=s.natReg 0 ∧ u.pc=19 := by
  have hstart:=startup_runs hn x B D s hp h8 hDreg hroot hB hnB hs
  let entry:State:={rootLoaded s n D with pc:=0}
  have hb:WordBound B entry:=changePC_bound B _ 0 hstart.final_bound (by omega)
  have he:(entry.scalarReg 1).dependent=false:=by
    rw [show entry.scalarReg 1=prepared (OAI.ExactFourier.zeta D) from (setup_values s n D).2.1]
    rfl
  obtain ⟨v,hv,hvalue,hdep,hframe⟩:=UniformPowerMachine.bounded_power_correct B (by omega)
    entry hb rfl he n x
  have hloadedpc:(rootLoaded s n D).pc=7 := by
    simp [rootLoaded,address,exponent,divisor,two,saved,zeroed,writeNat,writeScalar,next,hp]
  have hloaded : {rootLoaded s n D with pc:=7}=rootLoaded s n D := by
    cases hh:rootLoaded s n D;simp_all
  have hpower:BoundedRuns program n x B (rootLoaded s n D)
      (4+UniformPowerMachine.loopCost (D/(2*n))) {v with pc:=19} := by
    simpa [entry,placed,(setup_values s n D).1,hloaded] using
      UniformBoundedAssembly.boundedExecution_placed power_code (by change 7+12≤B;omega) (by omega) hv
  have hval:v.scalarReg 0=prepared (OAI.ExactFourier.zeta (2*n)) := by
    have h : (v.scalarReg 0).value=OAI.ExactFourier.zeta (2*n) := by
      calc
        _ = OAI.ExactFourier.zeta D^(D/(2*n)) := by
          simpa [entry,(setup_values s n D).1,(setup_values s n D).2.1,prepared] using hvalue
        _ = _:=UniformRoots.specifiedRoot_divisor_power D (2*n) hD (by omega) hdiv
    cases hh:v.scalarReg 0 with
    | mk value dependent =>
      simp only [hh] at h hdep
      simp [hh,h,hdep,prepared]
  have hf:=setup_frame s n D
  have hfr:SetupFrame s {v with pc:=19} := by
    refine ⟨hframe.1.trans hf.1,hframe.2.1.trans hf.2.1,hframe.2.2.1.trans hf.2.2.1,
      hframe.2.2.2.1.trans hf.2.2.2.1,?_⟩
    intro r h5 h0 h31 h32 h33 h34 h44
    exact (hframe.2.2.2.2.1 r h5).trans (hf.2.2.2.2 r h5 h0 h31 h32 h33 h34 h44)
  refine ⟨{v with pc:=19},?_,hval,hfr,?_,?_,rfl⟩
  · convert hstart.trans hpower using 1 <;> omega
  · exact (hframe.2.2.2.2.1 34 (by omega)).trans (setup_values s n D).2.2.1
  · exact (hframe.2.2.2.2.1 44 (by omega)).trans (setup_values s n D).2.2.2

def countState (s : State) (n : ℕ) := writeNat s 0 n
def sevenState (s : State) (n : ℕ) := writeNat (countState s n) 35 7
def tableEntry (s : State) (n ell : ℕ) := writeNat (sevenState s n) 9 (ell+7)

theorem table_setup (n : ℕ) (x : Fin n → ℂ) (B ell : ℕ) (s : State)
    (hp : s.pc=19) (h8 : s.natReg 8=n) (hell : s.natReg 10=ell)
    (hz : s.natReg 34=0) (hB : 128≤B) (ha : ell+7≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 3 (tableEntry s n ell) := by
  have hn:n≤B:=by simpa [h8] using hs.2.1 8
  have h1:=writeNat_bound B s 0 n hs (by omega) hn
  have h2:=writeNat_bound B (countState s n) 35 7 h1
    (by simp [countState,writeNat,next,hp];omega) (by omega)
  have h3:=writeNat_bound B (sevenState s n) 9 (ell+7) h2
    (by simp [sevenState,countState,writeNat,next,hp];omega) ha
  refine .next hs (u:=countState s n) ?_ (.next h1 (u:=sevenState s n) ?_
    (.next h2 (u:=tableEntry s n ell) ?_ (.refl h3)))
  all_goals simp [step,program,UniformPowerMachine.program,UniformChirpTableMachine.program,tableEntry,sevenState,countState,writeNat,next,hp,h8,hell,hz,evalNat]

def ResultFrame (n ell : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<ell+7 ∨ ell+7+2*n≤b → u.scalarHeap b=s.scalarHeap b) ∧
  u.natReg 0=s.natReg 0 ∧
  ∀ r,5≤r → r≠9 → r≠31 → r≠32 → r≠33 → r≠34 → r≠35 → r≠44 →
    u.natReg r=s.natReg r

/-- Complete charged root-extraction/table helper, including header restoration. -/
theorem post_header_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) (B D ell : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (h10 : s.natReg 10=ell) (hDreg : s.natReg 24=D)
    (hroot : s.scalarHeap 0=some (prepared (OAI.ExactFourier.zeta D)))
    (hD : 0<D) (hdiv : 2*n∣D) (hB : 128≤B) (hspace : ell+2*n+128≤B)
    (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (11*n+26+UniformPowerMachine.loopCost (D/(2*n))) u ∧
    UniformChirpTableMachine.Partial (ell+7) n (OAI.ExactFourier.zeta (2*n)) u ∧
    ResultFrame n ell s u ∧ u.pc=43 := by
  obtain ⟨v,hv,hval,hframe,hzero,hsave,hpc⟩:=halfAngle_execution hn x B D s hp h8 hDreg
    hroot hD hdiv hB (by omega) hs
  have h8v:v.natReg 8=n:=(hframe.2.2.2.2 8 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).trans h8
  have h10v:v.natReg 10=ell:=(hframe.2.2.2.2 10 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).trans h10
  have hsetup:=table_setup n x B ell v hpc h8v h10v hzero hB (by omega) hv.final_bound
  let entry:State:={tableEntry v n ell with pc:=0}
  have hb:WordBound B entry:=changePC_bound B _ 0 hsetup.final_bound (by omega)
  obtain ⟨w,hw,ht,hf,_hwpc⟩:=UniformChirpTableMachine.table_execution n x B n (ell+7)
    (OAI.ExactFourier.zeta (2*n)) entry (UniformRoots.specifiedRoot_ne_zero _) rfl
    (by simp [entry,tableEntry,sevenState,countState,writeNat,next])
    (by simp [entry,tableEntry,sevenState,countState,writeNat,next])
    hval (by omega) (by omega) hb
  have hentrypc:(tableEntry v n ell).pc=22:=by
    simp [tableEntry,sevenState,countState,writeNat,next,hpc]
  have hentryeq:{tableEntry v n ell with pc:=22}=tableEntry v n ell:=by
    cases hh:tableEntry v n ell;simp_all
  have htable:BoundedRuns program n x B (tableEntry v n ell) (11*n+10) {w with pc:=42} := by
    simpa [entry,placed,hentryeq] using UniformBoundedAssembly.boundedExecution_placed
      chirp_code (by change 22+20≤B;omega) (by omega) hw
  have h34:w.natReg 34=0:=by
    have hh:=hf.2.2.2.2.2.1 34 (by omega) (by omega)
    simpa [entry,tableEntry,sevenState,countState,writeNat,next,hzero] using hh
  have h44:w.natReg 44=s.natReg 0:=by
    have hh:=hf.2.2.2.2.2.1 44 (by omega) (by omega)
    simpa [entry,tableEntry,sevenState,countState,writeNat,next,hsave] using hh
  let u:State:=writeNat {w with pc:=42} 0 (s.natReg 0)
  have hub:WordBound B u:=writeNat_bound B {w with pc:=42} 0 (s.natReg 0)
    htable.final_bound (by change 42+1≤B;omega) (hs.2.1 0)
  have hfinish:BoundedExecution program n x B {w with pc:=42} 2 u:=by
    refine .next htable.final_bound ?_ (.halt hub ?_)
    · simp [step,program,UniformPowerMachine.program,UniformChirpTableMachine.program,u,h34,h44,evalNat]
    · simp [step,program,UniformPowerMachine.program,UniformChirpTableMachine.program,u,writeNat,next]
  refine ⟨u,?_,ht,?_,rfl⟩
  · convert ((hv.trans hsetup).trans htable).executes hfinish using 1 <;> omega
  · refine ⟨hf.1.trans hframe.1,hf.2.1.trans hframe.2.2.1,
      hf.2.2.1.trans hframe.2.2.2.1,?_,?_,?_⟩
    · intro b hb
      exact (hf.2.2.2.1 b hb).trans (congrFun hframe.2.1 b)
    · simp [u,writeNat,next]
    · intro r h5 h9 h31 h32 h33 h34 h35 h44
      have hh:=hf.2.2.2.2.2.1 r (by omega) h9
      have hh':u.natReg r=v.natReg r:=by
        simpa [u,entry,tableEntry,sevenState,countState,writeNat,next,h35,h9,show r≠0 by omega] using hh
      exact hh'.trans (hframe.2.2.2.2 r h5 (by omega) h31 h32 h33 h34 h44)

theorem ResultFrame.header {n ell : ℕ} {s u : State} (hf : ResultFrame n ell s u)
    (h : UniformCRTHeaderMachine.Header n s) : UniformCRTHeaderMachine.Header n u := by
  obtain ⟨h0,h10,h11,h16,h17,h18,hprimes⟩:=h
  refine ⟨hf.2.2.2.2.1.trans h0,?_,?_,?_,?_,?_,?_⟩
  · exact (hf.2.2.2.2.2 10 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h10
  · exact (hf.2.2.2.2.2 11 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h11
  · exact (hf.2.2.2.2.2 16 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h16
  · exact (hf.2.2.2.2.2 17 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h17
  · exact (hf.2.2.2.2.2 18 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h18
  · simpa [UniformWorkingMachine.PrimeTable,hf.1] using hprimes

theorem ResultFrame.crt {n ell : ℕ} {s u : State} (hf : ResultFrame n ell s u)
    (h : UniformCRTHeaderMachine.CRTTable n s) : UniformCRTHeaderMachine.CRTTable n u := by
  simpa [UniformCRTHeaderMachine.CRTTable,hf.1] using h

/-- The initial-state preparation includes the real CRT and radix-root bank. -/
def fullProgram : Program := UniformAssembly.embed
  (UniformRootTableMachine.fullProgram.map (relocate 0 185)) program [.halt] 229

theorem rootTable_code : CodeAt UniformRootTableMachine.fullProgram fullProgram 0 185 := by
  intro i hi
  simp only [fullProgram,UniformAssembly.embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem preparation_code : CodeAt program fullProgram 185 229 := UniformAssembly.embed_code _ _ _ _

theorem fullProgram_length : fullProgram.length=230 := by
  rw [fullProgram,UniformAssembly.embed_length,List.length_map,
    UniformRootTableMachine.fullProgram_length,program_length]
  rfl

theorem full_finish_code : fullProgram[229]?=some .halt := by
  simp only [fullProgram,UniformAssembly.embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformRootTableMachine.fullProgram_length,program_length];omega)]
  simp only [List.length_append,List.length_map,UniformRootTableMachine.fullProgram_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def extractionBudget (n : ℕ) : ℕ :=
  26+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/(2*n))
def overheadBudget (n : ℕ) : ℕ :=
  UniformRootTableMachine.fullPreparationBudget n+extractionBudget n+1
def fullPreparationBudget (n : ℕ) : ℕ := 11*n+overheadBudget n

theorem full_wordBound_setup {n : ℕ} (hn : 0<n) :
    185+(n+2)^16≤(n+2)^17 ∧ 230≤(n+2)^17 ∧
    UniformWorkingLength.axisCount n+2*n+128≤(n+2)^16 := by
  have h16:230≤(n+2)^16:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 16
    norm_num at h;omega
  have hell:UniformWorkingLength.axisCount n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount;omega
  have h15:128≤(n+2)^15:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 15
    norm_num at h;omega
  have hspace:UniformWorkingLength.axisCount n+2*n+128≤(n+2)^16:=by
    rw [show (n+2)^16=(n+2)*(n+2)^15 by ring]
    nlinarith
  rw [show (n+2)^17=(n+2)^16*(n+2) by ring]
  exact ⟨by nlinarith,by nlinarith,hspace⟩

/-- Closed actual initial-state preparation of all selected roots and the chirp
coefficients; no initialized table, value, inverse or action premise is supplied. -/
/- Paper stage: §5.3, charged preparation, PDF p.23: join actual CRT/root and chirp-table runs from the initial state. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^17) initial t u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
    (∀ j : Fin 6,u.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀ j : Fin (UniformWorkingLength.axisCount n+1),u.scalarHeap (6+j.val)=
      some (prepared (OAI.ExactFourier.zeta (UniformSelectedCRT.radices n j)))) ∧
    UniformChirpTableMachine.Partial (UniformWorkingLength.axisCount n+7) n
      (OAI.ExactFourier.zeta (2*n)) u ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=229 ∧ t≤fullPreparationBudget n := by
  obtain ⟨hBC,hfinishB,hspace⟩:=full_wordBound_setup hn
  obtain ⟨tc,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hrootOrders,hout,_hpc,hcost⟩:=
    UniformRootTableMachine.preparation_execution hn x
  let entry:State:={v with pc:=0}
  have heB:WordBound ((n+2)^16) entry:=changePC_bound _ v 0 hv.final_bound (by omega)
  have hroot:entry.scalarHeap 0=some (prepared (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))):=by
    simpa [entry,UniformCConstantsMachine.bank] using hbank 0
  have h128:128≤(n+2)^16:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 16
    norm_num at h;omega
  obtain ⟨u,hu,htable,hframe,_hup⟩:=post_header_execution hn x ((n+2)^16)
    (UniformMasterRootMachine.order n) (UniformWorkingLength.axisCount n) entry rfl h8 hheader.2.1
    horder hroot (UniformMasterRootMachine.order_bounds hn).1
    (UniformMasterRootMachine.divisor_orders n).1 h128 hspace heB
  have hprefix:BoundedRuns fullProgram n x ((n+2)^17) initial tc {v with pc:=185}:=by
    have h:=UniformAssembly.BoundedExecution.placed rootTable_code
      (by omega : 0+(n+2)^16≤(n+2)^17) (by omega : 185≤(n+2)^17) hv
    simpa [placed,initial] using h
  have htail:BoundedRuns fullProgram n x ((n+2)^17) {v with pc:=185}
      (11*n+26+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/(2*n)))
      {u with pc:=229}:=by
    have h:=UniformAssembly.BoundedExecution.placed preparation_code hBC (by omega : 229≤(n+2)^17) hu
    simpa [placed,entry] using h
  let final:State:={u with pc:=229}
  have hh:BoundedExecution fullProgram n x ((n+2)^17) final 1 final:=
    .halt htail.final_bound (by simp [step,final,full_finish_code])
  refine ⟨tc+(11*n+26+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/(2*n)))+1,
    final,(hprefix.trans htail).executes hh,hframe.header hheader,hframe.crt hcrt,?_,?_,?_,?_,htable,?_,?_,rfl,?_⟩
  · exact (hframe.2.2.2.2.2 24 (by decide) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans horder
  · exact (hframe.2.2.2.2.2 8 (by decide) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans h8
  · intro j
    exact (hframe.2.2.2.1 j.val (Or.inl (by have hj:=j.isLt;omega))).trans (hbank j)
  · intro j
    exact (hframe.2.2.2.1 (6+j.val) (Or.inl (by have hj:=j.isLt;omega))).trans (hroots j)
  · exact hframe.2.2.1.trans hrootOrders
  · exact hframe.2.1.trans hout
  · dsimp [fullPreparationBudget,overheadBudget,extractionBudget];omega

theorem extractionBudget_bound (n : ℕ) :
    extractionBudget n≤2*UniformRootTableMachine.rowBudget n := by
  have he:UniformMasterRootMachine.order n/(2*n)≤UniformMasterRootMachine.order n:=Nat.div_le_self _ _
  have hp:2^Nat.log2 (UniformMasterRootMachine.order n/(2*n)+1)≤
      UniformMasterRootMachine.order n/(2*n)+1:=Nat.log2_self_le (Nat.succ_ne_zero _)
  have hm:Nat.log2 (UniformMasterRootMachine.order n/(2*n)+1)≤
      Nat.log2 (UniformMasterRootMachine.order n+1):=
    (Nat.le_log2 (Nat.succ_ne_zero _)).2 (hp.trans (Nat.add_le_add_right he 1))
  have hc:=UniformPowerMachine.totalCost_log_bound (UniformMasterRootMachine.order n/(2*n))
  dsimp [extractionBudget,UniformRootTableMachine.rowBudget]
  omega

theorem extractionBudget_isBigO_log :
    (fun n : ℕ => (extractionBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => Real.log (n:ℝ)) := by
  have h:(fun n : ℕ => (extractionBudget n:ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (UniformRootTableMachine.rowBudget n:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [] with n
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),Nat.cast_mul,Nat.cast_ofNat]
      using (show (extractionBudget n:ℝ)≤2*(UniformRootTableMachine.rowBudget n:ℝ) by
        exact_mod_cast extractionBudget_bound n)
  exact h.trans UniformRootTableMachine.rowBudget_isBigO_log

theorem overheadBudget_isLittleO_input :
    (fun n : ℕ => (overheadBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hlog:(fun n : ℕ => Real.log (n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hc:(fun _n : ℕ => (1:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isLittleO_const_id_atTop (1:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  have h:=(UniformRootTableMachine.fullPreparationBudget_isLittleO_input.add
    (extractionBudget_isBigO_log.trans_isLittleO hlog)).add hc
  simpa [overheadBudget,Nat.cast_add] using h

theorem fullPreparationBudget_isBigO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have h:(fun n : ℕ => ((11*n:ℕ):ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 11
    filter_upwards [] with n
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg n)]
  simpa [fullPreparationBudget,Nat.cast_add] using h.add overheadBudget_isLittleO_input.isBigO

end
end ExactFourierCircuits.UniformChirpPreparation
