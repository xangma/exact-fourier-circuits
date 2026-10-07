import UniformPairMachine
import UniformPowerMachine
import UniformMasterRootMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformCKernelPreparation
open UniformMachine OAI.ExactFourier
noncomputable section

theorem zeta_four : zeta 4=Complex.I := by
  unfold zeta
  have he : 2*(Real.pi:ℂ)*Complex.I/(4:ℂ)=(Real.pi:ℂ)/2*Complex.I := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he,Complex.exp_pi_div_two_mul_I]

theorem four_dvd_order {n : ℕ} (hn : 0<n) : 4∣UniformMasterRootMachine.order n := by
  have hL := UniformWorkingLength.workingLength_pos hn
  simpa using UniformMasterRootMachine.localPowerOrder_dvd
    (r:=UniformWorkingLength.workingLength n) (e:=2) (le_refl _) (by omega)

/-- The original master root is saved at scalar heap address 0. Nat31 saves
nextPrime across the exponent helper; Nat30 is zero. All setup is printed. -/
def setup : Program :=
  [.natLiteral 30 0,.natBinary .add 31 0 30,.storeScalar 30 0,
   .scalarLiteral 1 0,.fieldBinary .add 1 1 0,
   .natLiteral 1 4,.natBinary .div 0 24 1]

def program : Program :=
  UniformMasterRootMachine.program.map (UniformAssembly.relocate 0 61) ++ setup ++
  UniformPowerMachine.program.map (UniformAssembly.relocate 68 80) ++
  [.natBinary .add 0 31 30] ++
  UniformPairMachine.coefficientProgram.map (UniformAssembly.relocate 81 88) ++ [.halt]

theorem program_length : program.length=89 := by decide

theorem master_code : UniformAssembly.CodeAt UniformMasterRootMachine.program program 0 61 := by
  intro i hi
  simp only [program,List.append_assoc,Nat.zero_add]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem power_code : UniformAssembly.CodeAt UniformPowerMachine.program program 68 80 := by
  intro i hi
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map,UniformMasterRootMachine.program_length];omega)]
  simp only [List.length_map,UniformMasterRootMachine.program_length]
  rw [show 68+i-61=7+i by omega,List.getElem?_append_right (by simp [setup])]
  simp only [show setup.length=7 from rfl]
  rw [show 7+i-7=i by omega,List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem coefficient_code : UniformAssembly.CodeAt UniformPairMachine.coefficientProgram program 81 88 := by
  intro i hi
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map,UniformMasterRootMachine.program_length];omega)]
  simp only [List.length_map,UniformMasterRootMachine.program_length]
  rw [show 81+i-61=7+(13+i) by omega,List.getElem?_append_right (by simp [setup])]
  simp only [show setup.length=7 from rfl]
  rw [show 7+(13+i)-7=12+(1+i) by omega,List.getElem?_append_right (by simp [UniformPowerMachine.program])]
  simp only [List.length_map,show UniformPowerMachine.program.length=12 from rfl]
  rw [show 12+(1+i)-12=1+i by omega,List.getElem?_append_right (by simp)]
  simp only [List.length_singleton,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

def zeroState (s : State) : State := writeNat s 30 0
def headerState (s : State) : State := writeNat (zeroState s) 31 (s.natReg 0)
def savedState (s : State) : State :=
  {next (headerState s) with scalarHeap:=Function.update s.scalarHeap 0 (some (s.scalarReg 0))}
def copyZeroState (s : State) : State := writeScalar (savedState s) 1 Scalar.zero
def copyState (s : State) : State := writeScalar (copyZeroState s) 1 (s.scalarReg 0)
def divisorState (s : State) : State := writeNat (copyState s) 1 4
def setupState (s : State) : State := writeNat (divisorState s) 0 (s.natReg 24/4)

theorem setup_code (i : ℕ) (hi : i<7) : program[61+i]?=setup[i]? := by
  simp only [program,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map,UniformMasterRootMachine.program_length];omega)]
  simp only [List.length_map,UniformMasterRootMachine.program_length,Nat.add_sub_cancel_left]
  exact List.getElem?_append_left (by simpa [setup] using hi)

theorem setup_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=61) (hdep : (s.scalarReg 0).dependent=false)
    (hB : 89≤B) (hs : WordBound B s) :
    BoundedRuns program n x B s 7 (setupState s) := by
  have hc : Scalar.mk (s.scalarReg 0).value false=s.scalarReg 0 := by
    cases h:(s.scalarReg 0) with
    | mk value dependent =>
      have hd : dependent=false := by simpa [h] using hdep
      subst dependent
      rfl
  have h1 := writeNat_bound B s 30 0 hs (by omega) (by omega)
  have h2 := writeNat_bound B (zeroState s) 31 (s.natReg 0) h1
    (by simp [zeroState,writeNat,next,hp];omega) (hs.2.1 0)
  have h3 := UniformInPlaceMachine.storeScalar_bound B (headerState s) 0 (s.scalarReg 0) h2
    (by simp [headerState,zeroState,writeNat,next,hp];omega) (by omega)
  have h4 := writeScalar_bound B (savedState s) 1 Scalar.zero h3
    (by simp [savedState,headerState,zeroState,writeNat,next,hp];omega)
  have h5 := writeScalar_bound B (copyZeroState s) 1 (s.scalarReg 0) h4
    (by simp [copyZeroState,savedState,headerState,zeroState,writeNat,writeScalar,next,hp];omega)
  have h6 := writeNat_bound B (copyState s) 1 4 h5
    (by simp [copyState,copyZeroState,savedState,headerState,zeroState,writeNat,writeScalar,next,hp];omega) (by omega)
  have h7 := writeNat_bound B (divisorState s) 0 (s.natReg 24/4) h6
    (by simp [divisorState,copyState,copyZeroState,savedState,headerState,zeroState,writeNat,writeScalar,next,hp];omega)
    ((Nat.div_le_self _ _).trans (hs.2.1 24))
  have c0 := setup_code 0 (by decide)
  have c1 := setup_code 1 (by decide)
  have c2 := setup_code 2 (by decide)
  have c3 := setup_code 3 (by decide)
  have c4 := setup_code 4 (by decide)
  have c5 := setup_code 5 (by decide)
  have c6 := setup_code 6 (by decide)
  refine .next hs (u:=zeroState s) ?_ (.next h1 (u:=headerState s) ?_
    (.next h2 (u:=savedState s) ?_ (.next h3 (u:=copyZeroState s) ?_
      (.next h4 (u:=copyState s) ?_ (.next h5 (u:=divisorState s) ?_
        (.next h6 (u:=setupState s) ?_ (.refl h7)))))))
  all_goals simp [step,setup,c0,c1,c2,c3,c4,c5,c6,setupState,divisorState,copyState,
    copyZeroState,savedState,headerState,zeroState,writeNat,writeScalar,next,hp,
    Scalar.zero,evalField,evalNat,hdep,hc]

theorem setup_properties (s : State) :
    (setupState s).pc=s.pc+7 ∧ (setupState s).natReg 0=s.natReg 24/4 ∧
      (setupState s).natReg 30=0 ∧ (setupState s).natReg 31=s.natReg 0 ∧
      (setupState s).scalarReg 1=s.scalarReg 0 ∧
      (setupState s).scalarHeap=Function.update s.scalarHeap 0 (some (s.scalarReg 0)) ∧
      (setupState s).natHeap=s.natHeap ∧ (setupState s).outputs=s.outputs ∧
      (setupState s).rootOrders=s.rootOrders := by
  simp [setupState,divisorState,copyState,copyZeroState,savedState,headerState,zeroState,
    writeNat,writeScalar,next,Nat.add_assoc]

theorem setup_registers (s : State) (r : ℕ) (h0 : r≠0) (h1 : r≠1)
    (h30 : r≠30) (h31 : r≠31) : (setupState s).natReg r=s.natReg r := by
  simp [setupState,divisorState,copyState,copyZeroState,savedState,headerState,zeroState,
    writeNat,writeScalar,next,h0,h1,h30,h31]

def restoreState (s : State) : State := writeNat {s with pc:=80} 0 (s.natReg 31)

theorem restore_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hB : 89≤B) (hs : WordBound B s) (hzero : s.natReg 30=0) :
    BoundedRuns program n x B {s with pc:=80} 1 (restoreState s) := by
  have h := changePC_bound B s 80 hs (by omega)
  have hb := writeNat_bound B {s with pc:=80} 0 (s.natReg 31) h (by simp;omega) (hs.2.1 31)
  have hc : program[80]?=some (.natBinary .add 0 31 30) := by decide
  refine .next h (u:=restoreState s) ?_ (.refl hb)
  simp [step,hc,restoreState,writeNat,next,evalNat,hzero]


def HeaderFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧
  ∀ r, r=0 ∨ (5≤r ∧ r≠30 ∧ r≠31) → u.natReg r=s.natReg r

theorem HeaderFrame.prepared {n : ℕ} {s u : State} (hf : HeaderFrame s u)
    (hs : UniformWorkingCompletion.PreparedState n s) : UniformWorkingCompletion.PreparedState n u := by
  obtain ⟨⟨h0,h10,h11,ht,hh⟩,h16,h18,h17⟩ := hs
  refine ⟨⟨(hf.2 0 (by simp)).trans h0,(hf.2 10 (by simp)).trans h10,
    (hf.2 11 (by simp)).trans h11,?_,?_⟩,
    (hf.2 16 (by simp)).trans h16,(hf.2 18 (by simp)).trans h18,
    (hf.2 17 (by simp)).trans h17⟩
  · simpa [UniformWorkingMachine.PrimeTable,hf.1] using ht
  · simpa [hf.1] using hh

theorem scalar_eq (v : Scalar) (c : ℂ) (hv : v.value=c) (hd : v.dependent=false) :
    v=UniformPairMachine.prepared c := by
  cases v
  simp_all [UniformPairMachine.prepared]

/-- Charged extraction and C coefficient arithmetic from an actual master-root
poststate. The saved root and complete integer working header survive. -/
theorem tail_execution (D n B Cb : ℕ) (x : Fin n → ℂ) (s : State)
    (hD : 0<D) (hdiv : 4∣D) (hp : s.pc=61) (horder : s.natReg 24=D)
    (hroot : s.scalarReg 0=UniformPairMachine.prepared (zeta D))
    (hB : 89≤B) (hBC : 81+B≤Cb) (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x Cb s (20+UniformPowerMachine.loopCost (D/4)) u ∧
      u.pc=88 ∧ u.scalarReg 0=UniformPairMachine.prepared a ∧
      u.scalarReg 1=UniformPairMachine.prepared b ∧
      u.scalarHeap=Function.update s.scalarHeap 0 (some (s.scalarReg 0)) ∧
      u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧ HeaderFrame s u := by
  have hdep : (s.scalarReg 0).dependent=false := by rw [hroot];rfl
  have hsetup := setup_bounded n x B s hp hdep hB hs
  have hprops := setup_properties s
  let entry := {setupState s with pc:=0}
  have hb : WordBound B entry := changePC_bound B _ 0 hsetup.final_bound (by omega)
  have hbase : entry.scalarReg 1=UniformPairMachine.prepared (zeta D) := hprops.2.2.2.2.1.trans hroot
  have he : entry.natReg 0=D/4 := hprops.2.1.trans (congrArg (·/4) horder)
  obtain ⟨w,hw,hval,hdepw,hframe⟩ := UniformPowerMachine.bounded_power_correct B (by omega)
    entry hb rfl (by rw [hbase];rfl) n x
  have hi : w.scalarReg 0=UniformPairMachine.prepared Complex.I := by
    apply scalar_eq _ _ _ hdepw
    rw [hval,hbase,he]
    exact (UniformRoots.specifiedRoot_divisor_power D 4 hD (by decide) hdiv).trans zeta_four
  have hpower : BoundedRuns program n x Cb (setupState s)
      (4+UniformPowerMachine.loopCost (D/4)) {w with pc:=80} := by
    have h := UniformAssembly.BoundedExecution.placed power_code (by omega : 68+B≤Cb)
      (by omega : 80≤Cb) hw
    have hpc : (setupState s).pc=68 := by rw [hprops.1,hp]
    have hplaced : UniformAssembly.placed 68 entry=setupState s := by
      change {setupState s with pc:=68}=setupState s
      rw [←hpc]
    rw [hplaced,he] at h
    exact h
  have hzero : w.natReg 30=0 := (hframe.2.2.2.2.1 30 (by decide)).trans hprops.2.2.1
  have hrestore := restore_bounded n x B w hB hw.final_bound hzero
  let ce := {restoreState w with pc:=0}
  have hcB : WordBound B ce := changePC_bound B _ 0 hrestore.final_bound (by omega)
  have hci : ce.scalarReg 0=UniformPairMachine.prepared Complex.I := hi
  have hc := UniformPairMachine.coefficient_execution n x B ce rfl hci (by omega) hcB
  have hcoefficient : BoundedRuns program n x Cb (restoreState w) 7
      {UniformPairMachine.coefficientState ce with pc:=88} := by
    have h := UniformAssembly.BoundedExecution.placed coefficient_code hBC (by omega : 88≤Cb) hc
    simpa [UniformAssembly.placed,ce,restoreState,writeNat,next] using h
  let u := {UniformPairMachine.coefficientState ce with pc:=88}
  have huB : WordBound Cb u := hcoefficient.final_bound
  have hc88 : program[88]?=some .halt := by decide
  have hhalt : BoundedExecution program n x Cb u 1 u := .halt huB (by simp [step,u,hc88])
  have hcoef := UniformPairMachine.coefficient_values ce
  have hcf := UniformPairMachine.coefficient_frame ce
  have hsetupC := UniformWorkingMachine.boundedRuns_mono (by omega : B≤Cb) hsetup
  have hrC := UniformWorkingMachine.boundedRuns_mono (by omega : B≤Cb) hrestore
  refine ⟨u,?_,rfl,hcoef.1,hcoef.2,?_,?_,?_,?_,?_⟩
  · convert (((hsetupC.trans hpower).trans hrC).trans hcoefficient).executes hhalt using 1; omega
  · exact hcf.2.2.1.trans (hframe.2.1.trans hprops.2.2.2.2.2.1)
  · exact hcf.2.2.2.2.trans (hframe.2.2.2.1.trans hprops.2.2.2.2.2.2.2.2)
  · exact hcf.2.2.2.1.trans (hframe.2.2.1.trans hprops.2.2.2.2.2.2.2.1)
  · exact hcf.2.1.trans (hframe.1.trans hprops.2.2.2.2.2.2.1)
  · intro r hr
    rw [show u.natReg=(restoreState w).natReg from hcf.1]
    rcases hr with rfl | ⟨hr5,hr30,hr31⟩
    · change w.natReg 31=s.natReg 0
      exact (hframe.2.2.2.2.1 31 (by decide)).trans hprops.2.2.2.1
    · have hr0 : r≠0 := by omega
      have hr1 : r≠1 := by omega
      simp only [restoreState,writeNat,next,Function.update_of_ne hr0]
      exact (hframe.2.2.2.2.1 r hr5).trans (setup_registers s r hr0 hr1 hr30 hr31)

def preparationBudget (n : ℕ) : ℕ := UniformMasterRootMachine.preparationBudget n+
  20+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/4)

theorem wordBound_setup {n : ℕ} (hn : 0<n) :
    89≤(n+2)^12 ∧ 81+(n+2)^12≤(n+2)^13 := by
  have h : 531441≤(n+2)^12 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 12
    norm_num at h
    exact h
  refine ⟨by omega,?_⟩
  rw [show (n+2)^13=(n+2)^12*(n+2) from pow_succ (n+2) 12]
  nlinarith

/-- One literal 89-instruction program, from initial for every positive n,
prepares the actual working header, its one master root, and both C coefficients.
Root provision, storage, argument setup, extraction, restoration, arithmetic
and continuation transfers are all charged. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x ((n+2)^13) initial t u ∧
      UniformWorkingCompletion.PreparedState n u ∧
      u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
      u.scalarReg 0=UniformPairMachine.prepared a ∧
      u.scalarReg 1=UniformPairMachine.prepared b ∧
      u.scalarHeap=Function.update initial.scalarHeap 0
        (some (UniformPairMachine.prepared (zeta (UniformMasterRootMachine.order n)))) ∧
      u.rootOrders=[UniformMasterRootMachine.order n] ∧
      u.outputs=initial.outputs ∧ u.pc=88 ∧ t≤preparationBudget n := by
  obtain ⟨hB,hBC⟩ := wordBound_setup hn
  obtain ⟨t,v,hv,hm,hpc,h8,hheap,hout,hreg,hcost⟩ := UniformMasterRootMachine.master_execution hn x
  let entry := {v with pc:=61}
  have hentryB : WordBound ((n+2)^12) entry :=
    changePC_bound _ v 61 hv.final_bound (by omega)
  obtain ⟨u,hu,upc,ua,ub,uh,uroot,uout,uf⟩ := tail_execution (UniformMasterRootMachine.order n)
    n ((n+2)^12) ((n+2)^13) x entry (UniformMasterRootMachine.order_bounds hn).1
    (four_dvd_order hn) rfl hm.2.1 hm.2.2.2.2.1 hB hBC hentryB
  have hprefix : BoundedRuns program n x ((n+2)^13) initial t entry := by
    have h := UniformAssembly.BoundedExecution.placed master_code
      (by omega : 0+(n+2)^12≤(n+2)^13) (by omega : 61≤(n+2)^13) hv
    simpa [UniformAssembly.placed,entry,initial] using h
  refine ⟨t+(20+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/4)),u,
    hprefix.executes hu,uf.prepared hm.1,?_,?_,ua,ub,?_,?_,?_,upc,?_⟩
  · exact (uf.2 24 (by simp)).trans hm.2.1
  · exact (uf.2 8 (by simp)).trans h8
  · rw [uh]
    change Function.update v.scalarHeap 0 (some (v.scalarReg 0))=_
    rw [hheap,hm.2.2.2.2.1]
    rfl
  · exact uroot.trans hm.2.2.2.2.2
  · exact uout.trans hout
  · dsimp [preparationBudget]
    omega

def extractionBudget (n : ℕ) : ℕ := 20+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/4)

theorem extractionBudget_bound {n : ℕ} (hn : 0<n) :
    extractionBudget n≤84*Nat.clog 2 (n+2)+29 := by
  have horder := (UniformMasterRootMachine.order_bounds hn).2
  have hpoly := (UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have he : UniformMasterRootMachine.order n/4+1≤(n+2)^12 := by
    have h := Nat.div_le_self (UniformMasterRootMachine.order n) 4
    omega
  have hpow : (n+2)^12≤2^(12*Nat.clog 2 (n+2)) := by
    calc
      (n+2)^12≤(2^Nat.clog 2 (n+2))^12 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 12
      _ = _ := by rw [←pow_mul,Nat.mul_comm]
  have hclog : Nat.clog 2 (UniformMasterRootMachine.order n/4+1)≤12*Nat.clog 2 (n+2) :=
    Nat.clog_le_of_le_pow (he.trans hpow)
  have hlog : Nat.log2 (UniformMasterRootMachine.order n/4+1)≤12*Nat.clog 2 (n+2) := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_clog _ _).trans hclog
  have hcost := UniformPowerMachine.totalCost_log_bound (UniformMasterRootMachine.order n/4)
  dsimp [extractionBudget]
  omega

theorem extractionBudget_isBigO_log :
    (fun n : ℕ => (extractionBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => Real.log (n:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 640
  have htlog : Filter.Tendsto (fun n : ℕ => Real.log (n:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ),
    htlog.eventually (Filter.eventually_ge_atTop (1:ℝ))] with n hn hlog
  have hnpos : 0<n := by omega
  have hnonneg : 0≤Real.log ((n+2:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n+2 by omega))
  have hclog : (Nat.clog 2 (n+2):ℝ)≤Real.logb 2 ((n+2:ℕ):ℝ)+1 := by
    have hnlog : 0≤Real.logb 2 ((n+2:ℕ):ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤n+2 by omega))
    rw [←Real.natCeil_logb_natCast 2 (n+2)]
    exact (Nat.ceil_lt_add_one hnlog).le
  have hshift : Real.log ((n+2:ℕ):ℝ)≤2+Real.log (n:ℝ) := by
    have hp : 0<(n:ℝ) := by exact_mod_cast hnpos
    have hle : ((n+2:ℕ):ℝ)≤3*(n:ℝ) := by exact_mod_cast (show n+2≤3*n by omega)
    have h := Real.log_le_log (by positivity : 0<((n+2:ℕ):ℝ)) hle
    rw [Real.log_mul (by norm_num) hp.ne'] at h
    have h3 : Real.log (3:ℝ)≤2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
      norm_num at h
      exact h
    linarith
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h2low := UniformWorkingLength.log_two_lower
  have hfrac : Real.log ((n+2:ℕ):ℝ)/Real.log 2≤2*Real.log ((n+2:ℕ):ℝ) := by
    apply (div_le_iff₀ h2).2
    have h := mul_nonneg hnonneg (by linarith : 0≤2*Real.log 2-1)
    nlinarith
  rw [Real.logb] at hclog
  have hnat := extractionBudget_bound hnpos
  have hreal : (extractionBudget n:ℝ)≤84*(Nat.clog 2 (n+2):ℝ)+29 := by exact_mod_cast hnat
  have hbound : (extractionBudget n:ℝ)≤640*Real.log (n:ℝ) := by linarith
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by linarith : 0≤Real.log (n:ℝ))] using hbound

theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hlog : (fun n : ℕ => Real.log (n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hsum := UniformMasterRootMachine.preparationBudget_isLittleO_input.add
    (extractionBudget_isBigO_log.trans_isLittleO hlog)
  simpa [preparationBudget,extractionBudget,Nat.cast_add,add_assoc] using hsum

end
end ExactFourierCircuits.UniformCKernelPreparation
