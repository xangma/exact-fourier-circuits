import UniformBoundedAssembly
import UniformCConstantsMachine
import UniformSelectedCRT
import UniformCRTHeaderMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRootTableMachine
open UniformMachine UniformAssembly UniformPairMachine OAI.ExactFourier
noncomputable section

/-- Nat31 is the axis index, Nat10 the odd-axis count, Nat18 the binary factor,
Nat24 the master order, and Nat34 zero. Only the prime table and master-root bank
are read; an order-one binary factor is retained. -/
def selector : Program :=
  [.branchLT 31 10 1 3,.loadNat 35 31,.jump 4,
   .natBinary .add 35 18 34,.natBinary .div 0 24 35,
   .natLiteral 36 0,.loadScalar 1 36,.halt]

structure Ready (ell j D q : ℕ) (s : State) : Prop where
  pc : s.pc=0
  axes : s.natReg 10=ell
  index : s.natReg 31=j
  order : s.natReg 24=D
  zero : s.natReg 34=0
  factor : if j<ell then s.natHeap j=some q else s.natReg 18=q
  root : s.scalarHeap 0=some (prepared (zeta D))

def selected (s : State) (q : ℕ) : State :=
  {s with pc:=4,natReg:=Function.update s.natReg 35 q}
def exponentState (s : State) (D q : ℕ) : State := writeNat (selected s q) 0 (D/q)
def addressState (s : State) (D q : ℕ) : State := writeNat (exponentState s D q) 36 0
def selectorState (s : State) (D q : ℕ) : State :=
  writeScalar (addressState s D q) 1 (prepared (zeta D))

theorem selector_length : selector.length=8 := rfl

theorem selector_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (ell j D q : ℕ) (hr : Ready ell j D q s) (hq : 0<q)
    (hB : 8≤B) (hs : WordBound B s) :
    BoundedExecution selector n x B s (if j<ell then 7 else 6) (selectorState s D q) := by
  obtain ⟨hp,ha,hj,hD,hz,hqtable,hroot⟩:=hr
  have hbq : q≤B := by
    by_cases hjl:j<ell
    · rw [ite_eq_left hjl] at hqtable;exact (hs.2.2.1 j q hqtable).2
    · rw [ite_eq_right hjl] at hqtable;simpa [hqtable] using hs.2.1 18
  have hbD : D≤B := by simpa [hD] using hs.2.1 24
  have hsel : WordBound B (selected s q) := by
    refine ⟨by simp [selected];omega,?_,hs.2.2⟩
    intro r;by_cases he:r=35 <;> simp [selected,he,hs.2.1,hbq]
  have h1:=writeNat_bound B (selected s q) 0 (D/q) hsel (by simp [selected];omega)
    ((Nat.div_le_self D q).trans hbD)
  have h2:=writeNat_bound B (exponentState s D q) 36 0 h1
    (by simp [exponentState,selected,writeNat,next];omega) (by omega)
  have h3:=writeScalar_bound B (addressState s D q) 1 (prepared (zeta D)) h2
    (by simp [addressState,exponentState,selected,writeNat,next];omega)
  have tail : BoundedExecution selector n x B (selected s q) 4 (selectorState s D q) := by
    refine .next hsel (u:=exponentState s D q) ?_
      (.next h1 (u:=addressState s D q) ?_
        (.next h2 (u:=selectorState s D q) ?_ (.halt h3 ?_)))
    all_goals simp [step,selector,selectorState,addressState,exponentState,selected,
      writeScalar,writeNat,next,hD,hroot,evalNat,show q≠0 by omega]
  by_cases h:j<ell
  · have ht:s.natHeap j=some q := by simpa [h] using hqtable
    let branch:State:={s with pc:=1}
    let loaded:State:=writeNat branch 35 q
    have hbr:WordBound B branch:=changePC_bound B s 1 hs (by omega)
    have hld:WordBound B loaded:=writeNat_bound B branch 35 q hbr (by simp [branch];omega) hbq
    have hh:BoundedExecution selector n x B s 7 (selectorState s D q) := by
      refine .next hs (u:=branch) ?_ (.next hbr (u:=loaded) ?_ (.next hld (u:=selected s q) ?_ tail))
      all_goals simp [step,selector,branch,loaded,selected,writeNat,next,hp,ha,hj,h,ht]
    simpa [h] using hh
  · have hb:s.natReg 18=q := by simpa [h] using hqtable
    let branch:State:={s with pc:=3}
    have hbr:WordBound B branch:=changePC_bound B s 3 hs (by omega)
    have hh:BoundedExecution selector n x B s 6 (selectorState s D q) := by
      refine .next hs (u:=branch) ?_ (.next hbr (u:=selected s q) ?_ tail)
      all_goals simp [step,selector,branch,selected,writeNat,next,hp,ha,hj,h,hb,hz,evalNat]
    simpa [h] using hh

theorem selector_values (s : State) (D q : ℕ) :
    (selectorState s D q).natReg 0=D/q ∧
    (selectorState s D q).scalarReg 1=prepared (zeta D) := by
  simp [selectorState,addressState,exponentState,selected,writeNat,writeScalar,next]

theorem selector_frame (s : State) (D q : ℕ) :
    (selectorState s D q).natHeap=s.natHeap ∧
    (selectorState s D q).scalarHeap=s.scalarHeap ∧
    (selectorState s D q).outputs=s.outputs ∧
    (selectorState s D q).rootOrders=s.rootOrders ∧
    (∀ r,r≠0 → r≠35 → r≠36 → (selectorState s D q).natReg r=s.natReg r) ∧
    ∀ r,r≠1 → (selectorState s D q).scalarReg r=s.scalarReg r := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · intro r h0 h35 h36
    simp [selectorState,addressState,exponentState,selected,writeNat,writeScalar,next,h0,h35,h36]
  · intro r h1
    simp [selectorState,addressState,exponentState,selected,writeNat,writeScalar,next,h1]

/-- Literal loop: select an actual factor, execute the fixed power helper,
store its specified root, and advance the index. Nat37 saves nextPrime. -/
def program : Program :=
  [.natLiteral 34 0,.natBinary .add 37 0 34,.natLiteral 30 6,.natLiteral 31 0,
   .natLiteral 32 1,.natBinary .add 33 10 32,.branchLT 31 33 7 16] ++
  selector.map (relocate 7 18) ++
  [.jump 6,.natBinary .add 0 37 34,.halt] ++
  UniformPowerMachine.program.map (relocate 18 30) ++
  [.natBinary .add 38 30 31,.storeScalar 38 0,.natBinary .add 31 31 32,.jump 6]

theorem program_length : program.length=34 := rfl

theorem selector_code : CodeAt selector program 7 18 := by
  intro i hi;change i<8 at hi;interval_cases i <;> rfl

theorem power_code : CodeAt UniformPowerMachine.program program 18 30 := by
  intro i hi;change i<12 at hi;interval_cases i <;> rfl


def Frame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧
  (∀ r,5≤r → r≠35 → r≠36 → u.natReg r=s.natReg r) ∧
  ∀ r,2≤r → u.scalarReg r=s.scalarReg r

/-- A literal selected-factor read and a literal placed power execution produce
its specified root without a new root request or integer-bound inflation. -/
theorem selector_power (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (ell j D q : ℕ) (hr : Ready ell j D q s) (hD : 0<D) (hq : 0<q) (hdiv:q∣D)
    (hB : 128≤B) (hs : WordBound B s) : ∃ u : State,
    BoundedRuns program n x B (placed 7 s)
      ((if j<ell then 7 else 6)+4+UniformPowerMachine.loopCost (D/q)) u ∧
      u.scalarReg 0=prepared (zeta q) ∧ Frame s u ∧ u.pc=30 := by
  have he:=selector_execution n x B s ell j D q hr hq (by omega) hs
  let entry:State:={selectorState s D q with pc:=0}
  have hentry:WordBound B entry:=changePC_bound B _ 0 he.final_bound (by omega)
  have hentryBase:(entry.scalarReg 1).dependent=false := by
    rw [show entry.scalarReg 1=prepared (zeta D) from (selector_values s D q).2]
    rfl
  obtain ⟨v,hpow,hval,hdep,hframe⟩:=UniformPowerMachine.bounded_power_correct B (by omega)
    entry hentry rfl hentryBase n x
  have hvalue:v.scalarReg 0=prepared (zeta q) := by
    have h : (v.scalarReg 0).value=zeta q := by
      calc
        (v.scalarReg 0).value=(zeta D)^(D/q) := by
          simpa [entry,(selector_values s D q).1,(selector_values s D q).2,prepared] using hval
        _ = zeta q:=UniformRoots.specifiedRoot_divisor_power D q hD hq hdiv
    cases hh:v.scalarReg 0 with
    | mk value dependent =>
      simp only [hh] at h hdep
      simp [h,hdep,prepared]
  have hsel:BoundedRuns program n x B (placed 7 s) (if j<ell then 7 else 6)
      {selectorState s D q with pc:=18} :=
    UniformBoundedAssembly.boundedExecution_placed selector_code
      (by rw [selector_length];omega) (by omega) he
  have hpower:BoundedRuns program n x B {selectorState s D q with pc:=18}
      (4+UniformPowerMachine.loopCost (D/q)) {v with pc:=30} := by
    simpa [entry,placed,(selector_values s D q).1] using
      UniformBoundedAssembly.boundedExecution_placed power_code (by change 18+12≤B;omega)
        (by omega) hpow
  have hf:=selector_frame s D q
  have hfr:Frame s {v with pc:=30} := by
    refine ⟨hframe.1.trans hf.1,hframe.2.1.trans hf.2.1,hframe.2.2.1.trans hf.2.2.1,
      hframe.2.2.2.1.trans hf.2.2.2.1,?_,?_⟩
    · intro r h5 h35 h36
      exact (hframe.2.2.2.2.1 r h5).trans (hf.2.2.2.2.1 r (by omega) h35 h36)
    · intro r h2
      exact (hframe.2.2.2.2.2 r (by omega) (by omega)).trans (hf.2.2.2.2.2 r (by omega))
  refine ⟨{v with pc:=30},?_,hvalue,hfr,rfl⟩
  simpa [Nat.add_assoc] using hsel.trans hpower

def radixAt (n j : ℕ) : ℕ :=
  if j<UniformWorkingLength.axisCount n then UniformWorkingLength.oddPrime j
    else UniformWorkingLength.binaryFactor n

theorem radixAt_eq (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n+1)) :
    radixAt n i.val=UniformSelectedCRT.radices n i := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [radixAt,UniformSelectedCRT.radices]
  · simp [radixAt,UniformSelectedCRT.radices,j.isLt]

theorem radixAt_pos (n j : ℕ) : 0<radixAt n j := by
  unfold radixAt;split_ifs
  · exact (UniformWorkingLength.oddPrime_prime j).pos
  · exact Nat.two_pow_pos _

theorem radixAt_divides (n j : ℕ) : radixAt n j∣UniformMasterRootMachine.order n := by
  unfold radixAt;split_ifs with h
  · exact (UniformMasterRootMachine.divisor_orders n).2.2.2 j h
  · exact (UniformMasterRootMachine.divisor_orders n).2.2.1

structure Header (n : ℕ) (s : State) : Prop where
  pc : s.pc=0
  nextPrime : s.natReg 0=UniformWorkingLength.nextPrime n
  axes : s.natReg 10=UniformWorkingLength.axisCount n
  binary : s.natReg 18=UniformWorkingLength.binaryFactor n
  order : s.natReg 24=UniformMasterRootMachine.order n
  primes : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s
  root : s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n)))

def initialized (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 34 0)
    37 (s.natReg 0)) 30 6) 31 0) 32 1) 33 (s.natReg 10+1)

structure LoopData (n saved j : ℕ) (s : State) : Prop where
  pc : s.pc=6
  axes : s.natReg 10=UniformWorkingLength.axisCount n
  binary : s.natReg 18=UniformWorkingLength.binaryFactor n
  order : s.natReg 24=UniformMasterRootMachine.order n
  base : s.natReg 30=6
  index : s.natReg 31=j
  one : s.natReg 32=1
  total : s.natReg 33=UniformWorkingLength.axisCount n+1
  zero : s.natReg 34=0
  savedPrime : s.natReg 37=saved
  primes : UniformWorkingMachine.PrimeTable (UniformWorkingLength.axisCount n) s
  root : s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n)))

/-- Only the root-table interval is overwritten; the populated Nat heap is
retained in full, including the existing CRT tail. -/
def TableFrame (n : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ a,a<6 ∨ 6+UniformWorkingLength.axisCount n+1≤a → u.scalarHeap a=s.scalarHeap a) ∧
  (∀ r,5≤r → r<30 ∨ 38<r → u.natReg r=s.natReg r) ∧
  ∀ r,2≤r → u.scalarReg r=s.scalarReg r

theorem tableFrame_refl (n : ℕ) (s : State) : TableFrame n s s :=
  ⟨rfl,rfl,rfl,fun _ _ => rfl,fun _ _ _ => rfl,fun _ _ => rfl⟩

theorem TableFrame.trans {n : ℕ} {s u v : State} (h : TableFrame n s u)
    (h' : TableFrame n u v) : TableFrame n s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun a ha => (h'.2.2.2.1 a ha).trans (h.2.2.2.1 a ha),
    fun r hr hs => (h'.2.2.2.2.1 r hr hs).trans (h.2.2.2.2.1 r hr hs),
    fun r hr => (h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩

theorem initialized_data {n : ℕ} (s : State) (h : Header n s) :
    LoopData n (s.natReg 0) 0 (initialized s) := by
  constructor <;> simp [initialized,writeNat,next,h.pc,h.axes,h.binary,h.order,h.root]
  exact h.primes

theorem initialized_frame (n : ℕ) (s : State) : TableFrame n s (initialized s) := by
  refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,?_⟩
  · intro r hr ht
    have h30:r≠30:=by omega
    have h31:r≠31:=by omega
    have h32:r≠32:=by omega
    have h33:r≠33:=by omega
    have h34:r≠34:=by omega
    have h37:r≠37:=by omega
    simp [initialized,writeNat,next,h30,h31,h32,h33,h34,h37]
  · intro r hr; rfl

theorem startup_runs (n B : ℕ) (x : Fin n → ℂ) (s : State) (h : Header n s)
    (hB : 128≤B) (hs : WordBound B s) (hell : UniformWorkingLength.axisCount n+1≤B) :
    BoundedRuns program n x B s 6 (initialized s) := by
  let s1 := writeNat s 34 0
  let s2 := writeNat s1 37 (s.natReg 0)
  let s3 := writeNat s2 30 6
  let s4 := writeNat s3 31 0
  let s5 := writeNat s4 32 1
  have h1:=writeNat_bound B s 34 0 hs (by rw [h.pc];omega) (by omega)
  have h2:=writeNat_bound B s1 37 (s.natReg 0) h1
    (by simp [s1,writeNat,next,h.pc];omega) (hs.2.1 _)
  have h3:=writeNat_bound B s2 30 6 h2
    (by simp [s2,s1,writeNat,next,h.pc];omega) (by omega)
  have h4:=writeNat_bound B s3 31 0 h3
    (by simp [s3,s2,s1,writeNat,next,h.pc];omega) (by omega)
  have h5:=writeNat_bound B s4 32 1 h4
    (by simp [s4,s3,s2,s1,writeNat,next,h.pc];omega) (by omega)
  have h6:=writeNat_bound B s5 33 (s.natReg 10+1) h5
    (by simp [s5,s4,s3,s2,s1,writeNat,next,h.pc];omega) (by rw [h.axes];exact hell)
  refine .next hs (u:=s1) ?_ (.next h1 (u:=s2) ?_ (.next h2 (u:=s3) ?_
    (.next h3 (u:=s4) ?_ (.next h4 (u:=s5) ?_ (.next h5 (u:=initialized s) ?_ (.refl h6))))))
  all_goals simp [step,program,initialized,s1,s2,s3,s4,s5,writeNat,next,h.pc,evalNat]

def storedRoot (s : State) (address : ℕ) (value : Scalar) : State :=
  {next s with scalarHeap:=Function.update s.scalarHeap address (some value)}

def rowResult (s : State) (j : ℕ) (value : Scalar) : State :=
  {writeNat (storedRoot (writeNat s 38 (6+j)) (6+j) value) 31 (j+1) with pc:=6}

def rowCost (n j : ℕ) : ℕ :=
  (if j<UniformWorkingLength.axisCount n then 16 else 15)+
    UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/radixAt n j)

theorem row_result_data {n saved j : ℕ} (s u : State) (hd : LoopData n saved j s)
    (hf : Frame s u) (_hp : u.pc=30) (_hj : j<UniformWorkingLength.axisCount n+1)
    (value : Scalar) : LoopData n saved (j+1) (rowResult u j value) := by
  have high (r : ℕ) (hr:5≤r) (h35:r≠35) (h36:r≠36) : u.natReg r=s.natReg r :=
    hf.2.2.2.2.1 r hr h35 h36
  constructor
  · rfl
  · simp [rowResult,storedRoot,writeNat,next,high,hd.axes]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.binary]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.order]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.base]
  · simp [rowResult,writeNat]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.one]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.total]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.zero]
  · simp [rowResult,storedRoot,writeNat,next,high,hd.savedPrime]
  · simpa only [UniformWorkingMachine.PrimeTable,rowResult,storedRoot,writeNat,next,hf.1] using hd.primes
  · have hh : u.scalarHeap 0=s.scalarHeap 0 := congrFun hf.2.1 0
    simpa [rowResult,storedRoot,writeNat,next,hh,show (0:ℕ)≠6+j by omega] using hd.root

theorem row_result_frame {n j : ℕ} (s u : State) (hf : Frame s u)
    (hj : j<UniformWorkingLength.axisCount n+1) (value : Scalar) :
    TableFrame n s (rowResult u j value) := by
  refine ⟨hf.1,hf.2.2.1,hf.2.2.2.1,?_,?_,?_⟩
  · intro a ha
    have hne:a≠6+j:=by omega
    simpa [rowResult,storedRoot,writeNat,next,hne] using congrFun hf.2.1 a
  · intro r hr ht
    have h31:r≠31:=by omega
    have h38:r≠38:=by omega
    simpa [rowResult,storedRoot,writeNat,next,h31,h38] using
      hf.2.2.2.2.1 r hr (by omega) (by omega)
  · intro r hr
    exact hf.2.2.2.2.2 r hr

theorem row_result_heap (s u : State) (hf : Frame s u) (j : ℕ) (value : Scalar) :
    (rowResult u j value).scalarHeap=Function.update s.scalarHeap (6+j) (some value) := by
  simp [rowResult,storedRoot,writeNat,next,hf.2.1]

theorem row_runs {n : ℕ} (hn : 0<n) (B saved j : ℕ) (x : Fin n → ℂ) (s : State)
    (hd : LoopData n saved j s) (hj : j<UniformWorkingLength.axisCount n+1)
    (hB : UniformMasterRootMachine.order n+UniformWorkingLength.axisCount n+128≤B)
    (hs : WordBound B s) : ∃ u,
    BoundedRuns program n x B s (rowCost n j) u ∧ LoopData n saved (j+1) u ∧
    TableFrame n s u ∧ u.scalarHeap=Function.update s.scalarHeap (6+j)
      (some (prepared (zeta (radixAt n j)))) := by
  let entry:State:={s with pc:=0}
  have heB:WordBound B entry:=changePC_bound B s 0 hs (by omega)
  have ready:Ready (UniformWorkingLength.axisCount n) j (UniformMasterRootMachine.order n)
      (radixAt n j) entry := by
    refine ⟨rfl,hd.axes,hd.index,hd.order,hd.zero,?_,hd.root⟩
    unfold radixAt;split_ifs with h
    · exact hd.primes j h
    · exact hd.binary
  obtain ⟨u,hu,hroot,hf,hpc⟩:=selector_power n x B entry _ _ _ _ ready
    (UniformMasterRootMachine.order_bounds hn).1 (radixAt_pos n j) (radixAt_divides n j)
    (by omega) heB
  have hbranch:BoundedRuns program n x B s 1 (placed 7 entry) := by
    refine .next hs ?_ (.refl (changePC_bound B s 7 hs (by omega)))
    simp [step,program,placed,entry,hd.pc,hd.index,hd.total,hj]
  have hfu:Frame s u:=hf
  have hhigh(r:ℕ)(hr:5≤r)(h35:r≠35)(h36:r≠36):u.natReg r=s.natReg r:=
    hfu.2.2.2.2.1 r hr h35 h36
  let a:=writeNat u 38 (6+j)
  let b:=storedRoot a (6+j) (prepared (zeta (radixAt n j)))
  let c:=writeNat b 31 (j+1)
  have h1:=writeNat_bound B u 38 (6+j) hu.final_bound (by omega) (by omega)
  have h2:=UniformInPlaceMachine.storeScalar_bound B a (6+j)
    (prepared (zeta (radixAt n j))) h1 (by simp [a,writeNat,next,hpc];omega) (by omega)
  have h3:=writeNat_bound B b 31 (j+1) h2 (by simp [b,a,storedRoot,writeNat,next,hpc];omega) (by omega)
  have h4:=changePC_bound B c 6 h3 (by omega)
  have hpost:BoundedRuns program n x B u 4 (rowResult u j (prepared (zeta (radixAt n j)))) := by
    refine .next hu.final_bound (u:=a) ?_ (.next h1 (u:=b) ?_ (.next h2 (u:=c) ?_ (.next h3 ?_ (.refl h4))))
    all_goals simp [step,program,selector,UniformPowerMachine.program,relocate,a,b,c,rowResult,storedRoot,writeNat,next,hpc,
      hhigh,hd.base,hd.index,hd.one,hroot,evalNat]
  refine ⟨rowResult u j (prepared (zeta (radixAt n j))),?_,
    row_result_data s u hd hfu hpc hj _,row_result_frame s u hfu hj _,row_result_heap s u hfu j _⟩
  have he:1+((if j<UniformWorkingLength.axisCount n then 7 else 6)+4+
      UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/radixAt n j))+4=rowCost n j := by
    unfold rowCost;split_ifs <;> omega
  simpa only [he] using (hbranch.trans hu).trans hpost

def Table (n count : ℕ) (s : State) : Prop :=
  ∀ j,j<count → s.scalarHeap (6+j)=some (prepared (zeta (radixAt n j)))

def finished (s : State) (saved : ℕ) : State := writeNat {s with pc:=16} 0 saved

theorem terminal_execution (n B saved : ℕ) (x : Fin n → ℂ) (s : State)
    (hd : LoopData n saved (UniformWorkingLength.axisCount n+1) s)
    (hB : 128≤B) (hs : WordBound B s) :
    BoundedExecution program n x B s 3 (finished s saved) := by
  have h1:=changePC_bound B s 16 hs (by omega)
  have h2:=writeNat_bound B {s with pc:=16} 0 saved h1 (by change 16+1≤B;omega)
    (by simpa [hd.savedPrime] using hs.2.1 37)
  refine .next hs (u:={s with pc:=16}) ?_ (.next h1 (u:=finished s saved) ?_ (.halt h2 ?_))
  all_goals simp [step,program,selector,UniformPowerMachine.program,relocate,
    finished,writeNat,next,hd.pc,hd.index,hd.total,hd.savedPrime,hd.zero,evalNat]

theorem terminal_frame (n saved : ℕ) (s : State) : TableFrame n s (finished s saved) := by
  refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,fun _ _ => rfl⟩
  intro r hr _ht
  simp [finished,writeNat,next,show r≠0 by omega]

theorem table_step {n j : ℕ} (s u : State) (h : Table n j s)
    (hu : u.scalarHeap=Function.update s.scalarHeap (6+j)
      (some (prepared (zeta (radixAt n j))))) : Table n (j+1) u := by
  intro i hi
  rw [hu]
  by_cases he:i=j
  · subst i; simp
  · have hne:6+i≠6+j:=by omega
    rw [Function.update_of_ne hne]
    exact h i (by omega)

def loopCost (n j : ℕ) : ℕ → ℕ
  | 0 => 3
  | fuel+1 => rowCost n j+loopCost n (j+1) fuel

/-- Every retained axis is visited once, including a binary factor of one. -/
theorem loop_execution {n : ℕ} (hn : 0<n) (B saved : ℕ) (x : Fin n → ℂ)
    (fuel j : ℕ) (s : State) (hd : LoopData n saved j s)
    (hj : j+fuel=UniformWorkingLength.axisCount n+1) (ht : Table n j s)
    (hB : UniformMasterRootMachine.order n+UniformWorkingLength.axisCount n+128≤B)
    (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (loopCost n j fuel) u ∧
    Table n (UniformWorkingLength.axisCount n+1) u ∧ TableFrame n s u ∧
    u.natReg 0=saved ∧ u.pc=17 := by
  induction fuel generalizing j s with
  | zero =>
      have he:j=UniformWorkingLength.axisCount n+1:=by omega
      subst j
      refine ⟨finished s saved,terminal_execution n B saved x s hd (by omega) hs,?_,
        terminal_frame n saved s,?_,?_⟩
      · exact ht
      · simp [finished,writeNat]
      · simp [finished,writeNat,next]
  | succ fuel ih =>
      have hjlt:j<UniformWorkingLength.axisCount n+1:=by omega
      obtain ⟨v,hv,hdata,hframe,hheap⟩:=row_runs hn B saved j x s hd hjlt hB hs
      obtain ⟨u,hu,htable,hf,hzero,hpc⟩:=ih (j+1) v hdata (by omega)
        (table_step s v ht hheap) hv.final_bound
      exact ⟨u,hv.executes hu,htable,hframe.trans hf,hzero,hpc⟩

def rowBudget (n : ℕ) : ℕ :=
  7*(Nat.log2 (UniformMasterRootMachine.order n+1)+1)+18

theorem rowCost_bound (n j : ℕ) : rowCost n j≤rowBudget n := by
  have he:UniformMasterRootMachine.order n/radixAt n j≤UniformMasterRootMachine.order n:=
    Nat.div_le_self _ _
  have hE:UniformMasterRootMachine.order n/radixAt n j+1≠0:=Nat.succ_ne_zero _
  have hD:UniformMasterRootMachine.order n+1≠0:=Nat.succ_ne_zero _
  have hp:2^Nat.log2 (UniformMasterRootMachine.order n/radixAt n j+1)≤
      UniformMasterRootMachine.order n/radixAt n j+1:=Nat.log2_self_le hE
  have hm:Nat.log2 (UniformMasterRootMachine.order n/radixAt n j+1)≤
      Nat.log2 (UniformMasterRootMachine.order n+1) :=
    (Nat.le_log2 hD).2 (hp.trans (Nat.add_le_add_right he 1))
  have h:=UniformPowerMachine.totalCost_log_bound (UniformMasterRootMachine.order n/radixAt n j)
  unfold rowCost rowBudget
  split_ifs <;> omega

theorem loopCost_bound (n j fuel : ℕ) : loopCost n j fuel≤fuel*rowBudget n+3 := by
  induction fuel generalizing j with
  | zero => simp [loopCost]
  | succ fuel ih =>
      have h:=rowCost_bound n j
      rw [loopCost,Nat.succ_mul]
      have hb:=ih (j+1)
      omega

def preparationBudget (n : ℕ) : ℕ :=
  (UniformWorkingLength.axisCount n+1)*rowBudget n+9

/-- A real selected header suffices; no empty Nat-heap tail is assumed. -/
theorem post_header_execution {n : ℕ} (hn : 0<n) (B : ℕ) (x : Fin n → ℂ)
    (s : State) (h : Header n s) (hs : WordBound B s)
    (hB : UniformMasterRootMachine.order n+UniformWorkingLength.axisCount n+128≤B) : ∃ t u,
    BoundedExecution program n x B s t u ∧
    Table n (UniformWorkingLength.axisCount n+1) u ∧ TableFrame n s u ∧
    u.natReg 0=UniformWorkingLength.nextPrime n ∧ u.pc=17 ∧ t≤preparationBudget n := by
  have hstart:=startup_runs n B x s h (by omega) hs (by omega)
  obtain ⟨u,hu,htable,hframe,hzero,hpc⟩:=loop_execution hn B (s.natReg 0) x
    (UniformWorkingLength.axisCount n+1) 0 (initialized s) (initialized_data s h)
    (by omega) (by intro j hj;omega) hB hstart.final_bound
  refine ⟨6+loopCost n 0 (UniformWorkingLength.axisCount n+1),u,hstart.executes hu,
    htable,(initialized_frame n s).trans hframe,hzero.trans h.nextPrime,hpc,?_⟩
  have hc:=loopCost_bound n 0 (UniformWorkingLength.axisCount n+1)
  unfold preparationBudget
  omega

theorem TableFrame.header {n : ℕ} {s u : State} (hf : TableFrame n s u)
    (hh : UniformCRTHeaderMachine.Header n s)
    (h0 : u.natReg 0=UniformWorkingLength.nextPrime n) : UniformCRTHeaderMachine.Header n u := by
  obtain ⟨_h0,h10,h11,h16,h17,h18,hprime⟩:=hh
  refine ⟨h0,?_,?_,?_,?_,?_,?_⟩
  · exact (hf.2.2.2.2.1 10 (by decide) (by omega)).trans h10
  · exact (hf.2.2.2.2.1 11 (by decide) (by omega)).trans h11
  · exact (hf.2.2.2.2.1 16 (by decide) (by omega)).trans h16
  · exact (hf.2.2.2.2.1 17 (by decide) (by omega)).trans h17
  · exact (hf.2.2.2.2.1 18 (by decide) (by omega)).trans h18
  · simpa only [UniformWorkingMachine.PrimeTable,hf.1] using hprime

theorem TableFrame.crt {n : ℕ} {s u : State} (hf : TableFrame n s u)
    (h : UniformCRTHeaderMachine.CRTTable n s) : UniformCRTHeaderMachine.CRTTable n u := by
  simpa only [UniformCRTHeaderMachine.CRTTable,hf.1] using h

/-- The first helper halts into the literal table program; the second halt
becomes one charged jump to the final halt. -/
def fullProgram : Program := UniformAssembly.embed
  (UniformCRTHeaderMachine.fullProgram.map (relocate 0 150)) program [.halt] 184

theorem header_code : CodeAt UniformCRTHeaderMachine.fullProgram fullProgram 0 150 := by
  intro i hi
  simp only [fullProgram,UniformAssembly.embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem table_code : CodeAt program fullProgram 150 184 := UniformAssembly.embed_code _ _ _ _

theorem fullProgram_length : fullProgram.length=185 := by
  rw [fullProgram,UniformAssembly.embed_length,List.length_map,
    UniformCRTHeaderMachine.fullProgram_length,program_length]
  rfl

theorem full_finish_code : fullProgram[184]?=some .halt := by
  simp only [fullProgram,UniformAssembly.embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformCRTHeaderMachine.fullProgram_length,program_length];omega)]
  simp only [List.length_append,List.length_map,UniformCRTHeaderMachine.fullProgram_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def fullPreparationBudget (n : ℕ) : ℕ :=
  UniformCRTHeaderMachine.fullPreparationBudget n+preparationBudget n+1

theorem full_wordBound_setup {n : ℕ} (hn : 0<n) :
    (n+2)^15≤(n+2)^16 ∧ 185≤(n+2)^16 ∧
    UniformMasterRootMachine.order n+UniformWorkingLength.axisCount n+128≤(n+2)^16 := by
  have horder:UniformMasterRootMachine.order n<1024*n^3:=(UniformMasterRootMachine.order_bounds hn).2
  have hell:UniformWorkingLength.axisCount n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have h13:2048≤(n+2)^13:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 13
    norm_num at h
    omega
  have h185:185≤(n+2)^16:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 16
    norm_num at h
    omega
  refine ⟨?_,h185,?_⟩
  · rw [show (n+2)^16=(n+2)^15*(n+2) from pow_succ _ 15]
    nlinarith
  · have hbase:UniformMasterRootMachine.order n+UniformWorkingLength.axisCount n+128≤2048*(n+2)^3:=by
      nlinarith
    have hm:=Nat.mul_le_mul_left ((n+2)^3) h13
    rw [show (n+2)^16=(n+2)^3*(n+2)^13 by ring]
    nlinarith

/-- One fixed finite program prepares the real selected CRT header and all
specified radix roots from the initial state, making only the master root request. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^16) initial t u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
    (∀ j : Fin 6,u.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀ j : Fin (UniformWorkingLength.axisCount n+1),u.scalarHeap (6+j.val)=
      some (prepared (zeta (UniformSelectedCRT.radices n j)))) ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=184 ∧ t≤fullPreparationBudget n := by
  obtain ⟨hBC,h185,hpostB⟩:=full_wordBound_setup hn
  obtain ⟨tc,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hout,_hpc,hcost⟩:=
    UniformCRTHeaderMachine.preparation_execution hn x
  let entry:State:={v with pc:=0}
  have heB:WordBound ((n+2)^16) entry:=changePC_bound _ v 0
    (UniformAssembly.wordBound_mono hBC hv.final_bound) (by omega)
  have hroot:entry.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n))):=by
    simpa [entry,UniformCConstantsMachine.bank] using hbank 0
  have he:Header n entry:=⟨rfl,hheader.1,hheader.2.1,hheader.2.2.2.2.2.1,horder,hheader.2.2.2.2.2.2,hroot⟩
  obtain ⟨tt,u,hu,htable,hframe,hzero,_hup,htcost⟩:=post_header_execution hn ((n+2)^16) x entry he heB hpostB
  have hprefix:BoundedRuns fullProgram n x ((n+2)^16) initial tc {v with pc:=150}:=by
    have h:=UniformAssembly.BoundedExecution.placed header_code
      (by omega : 0+(n+2)^15≤(n+2)^16) (by omega : 150≤(n+2)^16) hv
    simpa [placed,initial] using h
  have htail:BoundedRuns fullProgram n x ((n+2)^16) {v with pc:=150} tt {u with pc:=184}:=by
    have h:=UniformBoundedAssembly.boundedExecution_placed table_code
      (by rw [program_length];omega) (by omega) hu
    simpa [placed,entry] using h
  let final:State:={u with pc:=184}
  have hhalt:BoundedExecution fullProgram n x ((n+2)^16) final 1 final:=
    .halt htail.final_bound (by simp [step,final,full_finish_code])
  refine ⟨tc+tt+1,final,(hprefix.trans htail).executes hhalt,
    hframe.header hheader hzero,hframe.crt hcrt,?_,?_,?_,?_,?_,?_,rfl,?_⟩
  · exact (hframe.2.2.2.2.1 24 (by decide) (by omega)).trans horder
  · exact (hframe.2.2.2.2.1 8 (by decide) (by omega)).trans h8
  · intro j
    exact (hframe.2.2.2.1 j.val (Or.inl j.isLt)).trans (hbank j)
  · intro j
    simpa only [radixAt_eq n j] using htable j.val j.isLt
  · exact hframe.2.2.1.trans hroots
  · exact hframe.2.1.trans hout
  · unfold fullPreparationBudget;omega

theorem rowBudget_isBigO_log :
    (fun n : ℕ => (rowBudget n : ℝ)) =O[Filter.atTop] (fun n : ℕ => Real.log (n:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 137
  have htlog:Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ)) Filter.atTop Filter.atTop:=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ),
    htlog.eventually (Filter.eventually_ge_atTop (1:ℝ))] with n hn hlog
  have hnpos:0<n:=by omega
  have hnReal:0<(n:ℝ):=by exact_mod_cast hnpos
  have hbound:UniformMasterRootMachine.order n+1≤1024*n^3:=by
    have h:=(UniformMasterRootMachine.order_bounds hnpos).2
    omega
  have hcast:((UniformMasterRootMachine.order n+1:ℕ):ℝ)≤1024*(n:ℝ)^3:=by exact_mod_cast hbound
  have hlogOrder:=Real.log_le_log (by positivity : 0<((UniformMasterRootMachine.order n+1:ℕ):ℝ)) hcast
  have hlog1024:Real.log (1024:ℝ)=10*Real.log 2:=by
    rw [show (1024:ℝ)=(2:ℝ)^10 by norm_num,Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (1024:ℝ)≠0) (pow_ne_zero 3 hnReal.ne'),
    Real.log_pow,hlog1024] at hlogOrder
  have hnonneg:0≤Real.logb 2 ((UniformMasterRootMachine.order n+1:ℕ):ℝ):=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤UniformMasterRootMachine.order n+1 by omega))
  have hfloor:(Nat.log2 (UniformMasterRootMachine.order n+1):ℝ)≤
      Real.logb 2 ((UniformMasterRootMachine.order n+1:ℕ):ℝ):=by
    rw [Nat.log2_eq_log_two,←Real.natFloor_logb_natCast]
    exact Nat.floor_le hnonneg
  have h2:0<Real.log 2:=Real.log_pos (by norm_num)
  have h2low:=UniformWorkingLength.log_two_lower
  have hfrac:(10*Real.log 2+3*Real.log (n:ℝ))/Real.log 2≤10+6*Real.log (n:ℝ):=by
    apply (div_le_iff₀ h2).2
    have hm:=mul_nonneg (by linarith : 0≤Real.log (n:ℝ)) (by linarith : 0≤2*Real.log 2-1)
    nlinarith
  have hb:(Nat.log2 (UniformMasterRootMachine.order n+1):ℝ)≤10+6*Real.log (n:ℝ):=
    hfloor.trans ((div_le_div_of_nonneg_right hlogOrder h2.le).trans hfrac)
  have hr:(rowBudget n:ℝ)≤137*Real.log (n:ℝ):=by
    dsimp [rowBudget]
    push_cast
    linarith
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by linarith : 0≤Real.log (n:ℝ))] using hr

theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have haxes:(fun n : ℕ => ((UniformWorkingLength.axisCount n+1:ℕ):ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n+2:ℕ):ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul]
    exact_mod_cast (show UniformWorkingLength.axisCount n+1≤UniformWorkingLength.axisCount n+2 by omega)
  have hprod:(fun n : ℕ => ((UniformWorkingLength.axisCount n+1:ℕ):ℝ)*(rowBudget n:ℝ))
      =O[Filter.atTop] (fun n : ℕ => Real.log (n:ℝ)^2):=by
    simpa only [pow_two] using (haxes.trans UniformWorkingPreparation.axisCount_plus_two_isBigO_log).mul
      rowBudget_isBigO_log
  have hl:(fun n : ℕ => Real.log (n:ℝ)^2) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hc:(fun _n : ℕ => (9:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isLittleO_const_id_atTop (9:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  have h:=(hprod.trans_isLittleO hl).add hc
  simpa [preparationBudget,Nat.cast_add,Nat.cast_mul] using h

theorem fullPreparationBudget_isLittleO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hc:(fun _n : ℕ => (1:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    (Asymptotics.isLittleO_const_id_atTop (1:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  have h:=(UniformCRTHeaderMachine.fullPreparationBudget_isLittleO_input.add
    preparationBudget_isLittleO_input).add hc
  simpa [fullPreparationBudget,Nat.cast_add] using h

end
end ExactFourierCircuits.UniformRootTableMachine
