import UniformPermutationInversePreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRootExtractionMachine
open UniformMachine UniformAssembly OAI.ExactFourier
noncomputable section

/-- Nat104=master order, Nat141=positive divisor, Nat140=destination.
The root is actually loaded from heap0, and its exponent is actually divided. -/
def head : Program := [.natLiteral 146 0,.natBinary .div 0 104 141,.loadScalar 1 146]
def program : Program := embed head UniformPowerMachine.program [.storeScalar 140 0,.halt] 15
theorem program_length : program.length=17 := rfl
theorem prefix_code (i : ℕ) (hi:i<3) : program[i]?=head[i]? := by
  unfold program embed
  rw [List.getElem?_append_left (by simp only [List.length_append,head,List.length_cons,List.length_nil];omega)]
  exact List.getElem?_append_left hi
theorem power_code : CodeAt UniformPowerMachine.program program 3 15 :=
  embed_code head UniformPowerMachine.program [.storeScalar 140 0,.halt] 15
theorem store_at : program[15]?=some (.storeScalar 140 0) := rfl
theorem halt_at : program[16]?=some .halt := rfl

def zero (s : State) := writeNat s 146 0
def ratio (s : State) := writeNat (zero s) 0 (s.natReg 104/s.natReg 141)
def loaded (s : State) (D : ℕ) := writeScalar (ratio s) 1 ⟨zeta D,false⟩
def store (s : State) : State :=
  {next s with scalarHeap:=Function.update s.scalarHeap (s.natReg 140) (some (s.scalarReg 0))}

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,r≠0 → r≠1 → u.scalarReg r=s.scalarReg r) ∧
  ∀r,5≤r → r≠146 → u.natReg r=s.natReg r

theorem loaded_frame (s : State) (D : ℕ) : Frame s (loaded s D) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r h0 h1;simp [loaded,ratio,zero,writeNat,writeScalar,next,h1]
  · intro r hr h146
    simp [loaded,ratio,zero,writeNat,writeScalar,next,h146,show r≠0 by omega]

theorem startup (n D d B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (_hD:s.natReg 104=D) (hd:s.natReg 141=d) (hdpos:0<d)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hcode:17≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 3 (loaded s D) := by
  have b0:=writeNat_bound B s 146 0 hs (by omega) (by omega)
  have br:=writeNat_bound B (zero s) 0 (s.natReg 104/s.natReg 141) b0
    (by change s.pc+2≤B;omega) ((Nat.div_le_self _ _).trans (hs.2.1 104))
  have bl:=writeScalar_bound B (ratio s) 1 ⟨zeta D,false⟩ br (by change s.pc+3≤B;omega)
  have t0:step program n x s=.running (zero s):=by
    simp only [step,hp,prefix_code 0 (by decide)];rfl
  have t1:step program n x (zero s)=.running (ratio s):=by
    simp [step,program,embed,head,zero,ratio,writeNat,next,hp,hd,hdpos.ne',evalNat]
  have t2:step program n x (ratio s)=.running (loaded s D):=by
    simp [step,program,embed,head,zero,ratio,loaded,writeNat,next,hp,hroot]
  exact .next hs t0 (.next b0 t1 (.next br t2 (.refl bl)))

/-- No root request: a canonical divisor root is produced from the existing
master bank with all division, power, heap and control instructions charged. -/
theorem execution (n D d a B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hD:s.natReg 104=D) (hd:s.natReg 141=d) (ha:s.natReg 140=a)
    (hDpos:0<D) (hdpos:0<d) (hdiv:d∣D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hcode:17≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9+UniformPowerMachine.loopCost (D/d)) u ∧
    u.scalarHeap a=some ⟨zeta d,false⟩ ∧
    (∀b,b≠a → u.scalarHeap b=s.scalarHeap b) ∧ Frame s u ∧ u.pc=16 := by
  have hstart:=startup n D d B x s hp hD hd hdpos hroot hcode hs
  let e:State:={loaded s D with pc:=0}
  have he:WordBound B e:=changePC_bound B _ 0 hstart.final_bound (by omega)
  obtain ⟨v,hv,hval,hdep,hframe⟩:=UniformPowerMachine.bounded_power_correct B (by omega)
    e he rfl (by simp [e,loaded,writeScalar]) n x
  have hratio:e.natReg 0=D/d:=by simp [e,loaded,ratio,zero,writeNat,writeScalar,next,hD,hd]
  have hbase:(e.scalarReg 1).value=zeta D:=by simp [e,loaded,writeScalar]
  have hscalar:v.scalarReg 0=⟨zeta d,false⟩:=by
    have hz:(v.scalarReg 0).value=zeta d:=by
      rw [hval,hbase,hratio,UniformRoots.specifiedRoot_divisor_power D d hDpos hdpos hdiv]
    cases hr0:v.scalarReg 0 with
    | mk value dep =>
      have hv':value=zeta d:=by simpa only [hr0] using hz
      have hd':dep=false:=by simpa only [hr0] using hdep
      simp only [hv',hd']
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed power_code
    (by change 3+12≤B;omega) (by omega) hv
  have hentry:placed 3 e=loaded s D:=by
    simp [placed,e,loaded,ratio,zero,writeScalar,writeNat,next,hp]
  rw [hentry] at hplaced
  let w:State:={v with pc:=15}
  let u:State:=store w
  have ha':w.natReg 140=a:=by
    calc w.natReg 140=v.natReg 140:=rfl
         _=e.natReg 140:=hframe.2.2.2.2.1 _ (by omega)
         _=s.natReg 140:=by simp [e,loaded,ratio,zero,writeNat,writeScalar,next]
         _=a:=ha
  have hstore:WordBound B u:=UniformPermutationMachine.store_bound B w (w.natReg 140)
    (w.scalarReg 0) hplaced.final_bound (by change 16≤B;omega) (hplaced.final_bound.2.1 140)
  have ht:step program n x w=.running u:=by
    simp only [step,w,store_at]
    rfl
  have hhalt:step program n x u=.halted u:=by
    have hpc:u.pc=16:=rfl
    simp only [step,hpc,halt_at]
  have htail:BoundedExecution program n x B w 2 u:=.next hplaced.final_bound ht (.halt hstore hhalt)
  have hl:=loaded_frame s D
  refine ⟨u,?_,?_,?_,?_,rfl⟩
  · have all:=hstart.executes (hplaced.executes htail)
    rw [hratio] at all
    convert all using 1; omega
  · change Function.update v.scalarHeap (w.natReg 140) (some (v.scalarReg 0)) a=_
    rw [ha',hscalar]
    simp
  · intro b hb
    change Function.update v.scalarHeap (w.natReg 140) (some (v.scalarReg 0)) b=s.scalarHeap b
    rw [ha',Function.update_of_ne hb,hframe.2.1]
    rfl
  · refine ⟨hframe.1,hframe.2.2.1,hframe.2.2.2.1,?_,?_⟩
    · intro r h0 h1
      exact (hframe.2.2.2.2.2 r h0 h1).trans (hl.2.2.2.1 r h0 h1)
    · intro r hr h146
      exact (hframe.2.2.2.2.1 r hr).trans (hl.2.2.2.2 r hr h146)

theorem runtime_log_bound (D d : ℕ) :
    9+UniformPowerMachine.loopCost (D/d)≤7*(Nat.log2 (D+1)+1)+11 := by
  have h:=UniformPowerMachine.totalCost_log_bound (D/d)
  have hl:UniformPowerMachine.loopCost (D/d)≤7*(Nat.log2 (D/d+1)+1)+2:=by omega
  have hdle:D/d+1≤D+1:=Nat.add_le_add_right (Nat.div_le_self D d) 1
  have hp:2^(Nat.log2 (D/d+1))≤D/d+1:=Nat.log2_self_le (n:=D/d+1) (Nat.succ_ne_zero _)
  have hm:Nat.log2 (D/d+1)≤Nat.log2 (D+1):=
    (Nat.le_log2 (n:=D+1) (k:=Nat.log2 (D/d+1)) (Nat.succ_ne_zero _)).2 (hp.trans hdle)
  calc
    9+UniformPowerMachine.loopCost (D/d)≤7*(Nat.log2 (D/d+1)+1)+11:=by omega
    _≤7*(Nat.log2 (D+1)+1)+11:=by omega

theorem Frame.saved {s u : State} {p n ell L D : ℕ} (h:Frame s u)
    (hs:UniformGlobalNatPreparation.SavedHeaders p n ell L D s) :
    UniformGlobalNatPreparation.SavedHeaders p n ell L D u := by
  refine ⟨(h.2.2.2.2 100 (by decide) (by decide)).trans hs.nextPrime,
    (h.2.2.2.2 101 (by decide) (by decide)).trans hs.inputLength,
    (h.2.2.2.2 102 (by decide) (by decide)).trans hs.count,
    (h.2.2.2.2 103 (by decide) (by decide)).trans hs.workingLength,
    (h.2.2.2.2 104 (by decide) (by decide)).trans hs.masterRoot,
    (h.2.2.2.2 105 (by decide) (by decide)).trans hs.copyAddress,
    (h.2.2.2.2 106 (by decide) (by decide)).trans hs.copyLength⟩

theorem Frame.metadata {n : ℕ} {s u : State} (h:Frame s u)
    (hm:UniformPermutationInversePreparation.Metadata n s) :
    UniformPermutationInversePreparation.Metadata n u :=
  hm.transport_saved (h.saved hm.saved) (fun _ _=>congrFun h.1 _)

/-- The supplied value is obtained from the actual startup bank, rather than
an arbitrary primitive-root premise. All local dyadic convolution sizes fit
the same master order. Register141 must contain the producer's actual size. -/
theorem selected_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (r k a : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s)
    (hr:r≤UniformWorkingLength.workingLength n) (hk:2^k≤8*r)
    (hp:s.pc=0) (hd:s.natReg 141=2^k) (ha:s.natReg 140=a)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s
      (9+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/2^k)) u ∧
    u.scalarHeap a=some ⟨zeta (2^k),false⟩ ∧
    (∀b,b≠a → u.scalarHeap b=s.scalarHeap b) ∧
    UniformPermutationInversePreparation.Metadata n u ∧ Frame s u ∧ u.pc=16 := by
  have hroot:s.scalarHeap 0=some ⟨zeta (UniformMasterRootMachine.order n),false⟩:=by
    simpa [UniformCConstantsMachine.bank,UniformPairMachine.prepared] using ho.constants 0
  have hcode:17≤(n+2)^19:=by have h:=UniformInitialPreparation.word_setup hn;omega
  obtain ⟨u,hu,hbank,houtside,hframe,hpc⟩:=execution n (UniformMasterRootMachine.order n)
    (2^k) a ((n+2)^19) x s hp hm.saved.masterRoot hd ha
    (UniformMasterRootMachine.order_bounds hn).1 (by positivity)
    (UniformMasterRootMachine.localPowerOrder_dvd hr hk) hroot hcode hs
  exact ⟨u,hu,hbank,houtside,hframe.metadata hm,hframe,hpc⟩

end
end ExactFourierCircuits.UniformRootExtractionMachine
