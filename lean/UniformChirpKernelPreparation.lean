import UniformPaddedInputPreparation
import UniformChirpKernelMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3, operand preparation and three-transform argument,
PDF pp.22-23 (`eq:chirp`).

Composes actual root/chirp, padded-input and fixed-kernel preparation.
This prepares operands only; the fixed operand's Fourier transform remains a
separately charged stage of the final program.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace ExactFourierCircuits.UniformChirpKernelPreparation
open UniformMachine UniformPairMachine UniformAssembly
noncomputable section

def head : Program :=
  [.natLiteral 34 0,.natBinary .add 40 0 34,.natBinary .add 0 8 34,
   .natBinary .add 1 17 34,.natLiteral 35 7,.natBinary .add 2 10 35,
   .natLiteral 36 2,.natBinary .mul 37 8 36,.natBinary .add 9 2 37,.natBinary .add 9 9 17]

/-- The literal signed-kernel producer consumes the inverse chirp bank and restores the header. -/
/- Paper stage: §5.3, operand construction, PDF p.22: actual header restoration and signed-kernel producer; addresses are implementation details. -/
def program : Program := embed head UniformChirpKernelMachine.program
  [.natBinary .add 0 40 34,.halt] 30

theorem program_length : program.length=32 := rfl
theorem kernel_code : CodeAt UniformChirpKernelMachine.program program 10 30 :=
  embed_code _ _ _ _

def zeroed (s : State) := writeNat s 34 0
def saved (s : State) := writeNat (zeroed s) 40 (s.natReg 0)
def count (s : State) (n : ℕ) := writeNat (saved s) 0 n
def width (s : State) (n L : ℕ) := writeNat (count s n) 1 L
def seven (s : State) (n L : ℕ) := writeNat (width s n L) 35 7
def bank (s : State) (n L ell : ℕ) := writeNat (seven s n L) 2 (ell+7)
def two (s : State) (n L ell : ℕ) := writeNat (bank s n L ell) 36 2
def double (s : State) (n L ell : ℕ) := writeNat (two s n L ell) 37 (2*n)
def dataEntry (s : State) (n L ell : ℕ) := writeNat (double s n L ell) 9 (ell+7+2*n)
def kernelEntry (s : State) (n L ell : ℕ) := writeNat (dataEntry s n L ell) 9 (ell+7+2*n+L)

theorem startup_runs {n : ℕ} (x : Fin n → ℂ) (B L ell : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (h17 : s.natReg 17=L)
    (h10 : s.natReg 10=ell) (hB : 128≤B) (hspace : ell+7+2*n+2*L≤B)
    (hs : WordBound B s) : BoundedRuns program n x B s 10 (kernelEntry s n L ell) := by
  have h1:=writeNat_bound B s 34 0 hs (by omega) (by omega)
  have h2:=writeNat_bound B (zeroed s) 40 (s.natReg 0) h1
    (by simp [zeroed,writeNat,next,hp];omega) (hs.2.1 0)
  have h3:=writeNat_bound B (saved s) 0 n h2
    (by simp [saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h4:=writeNat_bound B (count s n) 1 L h3
    (by simp [count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h5:=writeNat_bound B (width s n L) 35 7 h4
    (by simp [width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h6:=writeNat_bound B (seven s n L) 2 (ell+7) h5
    (by simp [seven,width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h7:=writeNat_bound B (bank s n L ell) 36 2 h6
    (by simp [bank,seven,width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h8b:=writeNat_bound B (two s n L ell) 37 (2*n) h7
    (by simp [two,bank,seven,width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h9:=writeNat_bound B (double s n L ell) 9 (ell+7+2*n) h8b
    (by simp [double,two,bank,seven,width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h10b:=writeNat_bound B (dataEntry s n L ell) 9 (ell+7+2*n+L) h9
    (by simp [dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next,hp];omega) (by omega)
  refine .next hs (u:=zeroed s) ?_ (.next h1 (u:=saved s) ?_ (.next h2 (u:=count s n) ?_
    (.next h3 (u:=width s n L) ?_ (.next h4 (u:=seven s n L) ?_ (.next h5 (u:=bank s n L ell) ?_
      (.next h6 (u:=two s n L ell) ?_ (.next h7 (u:=double s n L ell) ?_
        (.next h8b (u:=dataEntry s n L ell) ?_ (.next h9 (u:=kernelEntry s n L ell) ?_ (.refl h10b))))))))))
  all_goals simp [step,program,embed,head,UniformChirpKernelMachine.program,kernelEntry,dataEntry,double,
    two,bank,seven,width,count,saved,zeroed,writeNat,next,hp,h8,h17,h10,evalNat,Nat.mul_comm]

def SetupFrame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧
  ∀ r,8≤r → r≠9 → r≠34 → r≠35 → r≠36 → r≠37 → r≠40 → u.natReg r=s.natReg r

theorem setup_frame (s : State) (n L ell : ℕ) : SetupFrame s (kernelEntry s n L ell) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr h9 h34 h35 h36 h37 h40
  simp [kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next,
    h9,h34,h35,h36,h37,h40,show r≠0 by omega,show r≠1 by omega,show r≠2 by omega]

def ResultFrame (n L ell : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<ell+7+2*n+L ∨ ell+7+2*n+2*L≤b → u.scalarHeap b=s.scalarHeap b) ∧
  u.natReg 0=s.natReg 0 ∧
  ∀ r,8≤r → r≠9 → r≠34 → r≠35 → r≠36 → r≠37 → r≠40 → u.natReg r=s.natReg r

theorem post_header_execution {n : ℕ} (x : Fin n → ℂ) (B L ell : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (h17 : s.natReg 17=L)
    (h10 : s.natReg 10=ell)
    (hc : UniformChirpTableMachine.Partial (ell+7) n (OAI.ExactFourier.zeta (2*n)) s)
    (hB : 128≤B) (hspace : ell+7+2*n+2*L≤B) (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (15+UniformChirpKernelMachine.loopCost n L 0 L) u ∧
    UniformChirpKernelMachine.Partial (ell+7+2*n+L) L n L (OAI.ExactFourier.zeta (2*n)) u ∧
    ResultFrame n L ell s u ∧ u.pc=31 := by
  have hstart:=startup_runs x B L ell s hp h8 h17 h10 hB hspace hs
  let entry:State:={kernelEntry s n L ell with pc:=0}
  have he:WordBound B entry:=changePC_bound B _ 0 hstart.final_bound (by omega)
  obtain ⟨w,hw,ht,hf,_hpc⟩:=UniformChirpKernelMachine.kernel_execution n x B n L (ell+7)
    (ell+7+2*n+L) (OAI.ExactFourier.zeta (2*n)) entry rfl
    (by simp [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (UniformChirpKernelMachine.coefficients_of_chirp_table hc) (by omega) (by omega) (by omega) he
  have hepc:(kernelEntry s n L ell).pc=10:=by
    simp [kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next,hp]
  have htable:BoundedRuns program n x B (kernelEntry s n L ell)
      (3+UniformChirpKernelMachine.loopCost n L 0 L) {w with pc:=30}:=by
    have heq:{kernelEntry s n L ell with pc:=10}=kernelEntry s n L ell:=by
      cases h:kernelEntry s n L ell;simp_all
    simpa [placed,entry,heq] using UniformBoundedAssembly.boundedExecution_placed kernel_code
      (by change 10+20≤B;omega) (by omega) hw
  have hz:w.natReg 34=0:=by
    have h:=hf.2.2.2.2.1 34 (Or.inr (by omega)) (by omega)
    simpa [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next] using h
  have hsave:w.natReg 40=s.natReg 0:=by
    have h:=hf.2.2.2.2.1 40 (Or.inr (by omega)) (by omega)
    simpa [entry,kernelEntry,dataEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next] using h
  let u:State:=writeNat {w with pc:=30} 0 (s.natReg 0)
  have hub:WordBound B u:=writeNat_bound B {w with pc:=30} 0 (s.natReg 0)
    htable.final_bound (by change 30+1≤B;omega) (hs.2.1 0)
  have hfinish:BoundedExecution program n x B {w with pc:=30} 2 u:=by
    refine .next htable.final_bound ?_ (.halt hub ?_)
    · simp [step,program,embed,head,UniformChirpKernelMachine.program,u,hz,hsave,evalNat]
    · simp [step,program,embed,head,UniformChirpKernelMachine.program,u,writeNat,next]
  refine ⟨u,?_,ht,?_,rfl⟩
  · convert (hstart.trans htable).executes hfinish using 1 <;> omega
  · refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,?_,?_⟩
    · intro b hb
      exact hf.2.2.2.1 b (by omega)
    · simp [u,writeNat,next]
    · intro r hr h9 h34 h35 h36 h37 h40
      have h:=hf.2.2.2.2.1 r (Or.inr hr) h9
      have hs':SetupFrame s (kernelEntry s n L ell):=setup_frame s n L ell
      have h':u.natReg r=(kernelEntry s n L ell).natReg r:=by
        simpa [u,entry,writeNat,next,show r≠0 by omega] using h
      exact h'.trans (hs'.2.2.2.2 r hr h9 h34 h35 h36 h37 h40)

theorem ResultFrame.header {n L ell : ℕ} {s u : State} (hf : ResultFrame n L ell s u)
    (h : UniformCRTHeaderMachine.Header n s) : UniformCRTHeaderMachine.Header n u := by
  obtain ⟨h0,h10,h11,h16,h17,h18,hprimes⟩:=h
  refine ⟨hf.2.2.2.2.1.trans h0,?_,?_,?_,?_,?_,?_⟩
  · exact (hf.2.2.2.2.2 10 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h10
  · exact (hf.2.2.2.2.2 11 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h11
  · exact (hf.2.2.2.2.2 16 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h16
  · exact (hf.2.2.2.2.2 17 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h17
  · exact (hf.2.2.2.2.2 18 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h18
  · simpa [UniformWorkingMachine.PrimeTable,hf.1] using hprimes

theorem ResultFrame.crt {n L ell : ℕ} {s u : State} (hf : ResultFrame n L ell s u)
    (h : UniformCRTHeaderMachine.CRTTable n s) : UniformCRTHeaderMachine.CRTTable n u := by
  simpa [UniformCRTHeaderMachine.CRTTable,hf.1] using h

def fullProgram : Program := embed
  (UniformPaddedInputPreparation.fullProgram.map (relocate 0 260)) program [.halt] 292

theorem paddedInput_code : CodeAt UniformPaddedInputPreparation.fullProgram fullProgram 0 260 := by
  intro i hi
  simp only [fullProgram,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem preparation_code : CodeAt program fullProgram 260 292 := by
  simpa only [fullProgram,List.length_map,UniformPaddedInputPreparation.fullProgram_length] using
    embed_code (UniformPaddedInputPreparation.fullProgram.map (relocate 0 260)) program [.halt] 292

theorem fullProgram_length : fullProgram.length=293 := by
  rw [fullProgram,embed_length,List.length_map,UniformPaddedInputPreparation.fullProgram_length,
    program_length]
  rfl

theorem full_finish_code : fullProgram[292]?=some .halt := by
  simp only [fullProgram,embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformPaddedInputPreparation.fullProgram_length,program_length];omega)]
  simp only [List.length_append,List.length_map,UniformPaddedInputPreparation.fullProgram_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def kernelBase (n : ℕ) : ℕ := UniformPaddedInputPreparation.dataBase n+UniformWorkingLength.workingLength n
def fullPreparationBudget (n : ℕ) : ℕ := UniformPaddedInputPreparation.fullPreparationBudget n+52*n+18

theorem full_wordBound_setup {n : ℕ} (hn : 0<n) :
    260+(n+2)^18≤(n+2)^19 ∧ 293≤(n+2)^19 ∧
    128≤(n+2)^18 ∧ kernelBase n+UniformWorkingLength.workingLength n≤(n+2)^18 := by
  have h17:300≤(n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 17
    norm_num at h;omega
  have hell:UniformWorkingLength.axisCount n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount;omega
  have hL:UniformWorkingLength.workingLength n<4*n:=UniformWorkingLength.workingLength_upper hn
  have he18:(n+2)^18=(n+2)*(n+2)^17:=by ring
  have he19:(n+2)^19=(n+2)*(n+2)^18:=by ring
  have h18:300≤(n+2)^18:=by rw [he18];nlinarith
  refine ⟨?_,?_,by omega,?_⟩
  · rw [he19];nlinarith
  · rw [he19];nlinarith
  · dsimp [kernelBase,UniformPaddedInputPreparation.dataBase];rw [he18];nlinarith

/-- Initial-state execution prepares both actual convolution operands, all root
and CRT banks, with every input read, store, branch and halt charged. Transforms
and the final output phase remain separate. -/
/- Paper stage: §5.3, preparation and three-transform discussion, PDF p.23: actual operand production is charged; this theorem does not include their transforms. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^19) initial t u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
    (∀ j : Fin 6,u.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀ j : Fin (UniformWorkingLength.axisCount n+1),u.scalarHeap (6+j.val)=
      some (prepared (OAI.ExactFourier.zeta (UniformSelectedCRT.radices n j)))) ∧
    UniformChirpTableMachine.Partial (UniformWorkingLength.axisCount n+7) n
      (OAI.ExactFourier.zeta (2*n)) u ∧
    UniformPaddedInputMachine.Partial (UniformPaddedInputPreparation.dataBase n) (UniformWorkingLength.workingLength n)
      (OAI.ExactFourier.zeta (2*n)) x u ∧
    UniformChirpKernelMachine.Partial (kernelBase n) (UniformWorkingLength.workingLength n)
      n (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) u ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=292 ∧ t≤fullPreparationBudget n := by
  obtain ⟨hBC,hfinishB,h128,hspace⟩:=full_wordBound_setup hn
  obtain ⟨tc,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hchirp,hdata,hrootOrders,hout,_hpc,hcost⟩:=
    UniformPaddedInputPreparation.preparation_execution hn x
  let entry:State:={v with pc:=0}
  have heB:WordBound ((n+2)^18) entry:=changePC_bound _ v 0 hv.final_bound (by omega)
  obtain ⟨u,hu,htable,hframe,_hup⟩:=post_header_execution x ((n+2)^18)
    (UniformWorkingLength.workingLength n) (UniformWorkingLength.axisCount n) entry rfl
    h8 hheader.2.2.2.2.1 hheader.2.1 hchirp h128
    (by simpa [kernelBase,UniformPaddedInputPreparation.dataBase,two_mul,Nat.add_assoc] using hspace) heB
  have hprefix:BoundedRuns fullProgram n x ((n+2)^19) initial tc {v with pc:=260}:=by
    have h:=UniformAssembly.BoundedExecution.placed paddedInput_code
      (by omega : 0+(n+2)^18≤(n+2)^19) (by omega : 260≤(n+2)^19) hv
    simpa [placed,initial] using h
  have htail:BoundedRuns fullProgram n x ((n+2)^19) {v with pc:=260}
      (15+UniformChirpKernelMachine.loopCost n (UniformWorkingLength.workingLength n) 0 (UniformWorkingLength.workingLength n))
      {u with pc:=292}:=by
    have h:=UniformAssembly.BoundedExecution.placed preparation_code hBC (by omega : 292≤(n+2)^19) hu
    simpa [placed,entry] using h
  let final:State:={u with pc:=292}
  have hh:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=
    .halt htail.final_bound (by simp [step,final,full_finish_code])
  refine ⟨tc+(15+UniformChirpKernelMachine.loopCost n (UniformWorkingLength.workingLength n) 0 (UniformWorkingLength.workingLength n))+1,
    final,(hprefix.trans htail).executes hh,hframe.header hheader,hframe.crt hcrt,?_,?_,?_,?_,?_,?_,htable,
    hframe.2.2.1.trans hrootOrders,hframe.2.1.trans hout,rfl,?_⟩
  · exact (hframe.2.2.2.2.2 24 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans horder
  · exact (hframe.2.2.2.2.2 8 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans h8
  · intro j
    exact (hframe.2.2.2.1 j.val (Or.inl (by have hj:=j.isLt;omega))).trans (hbank j)
  · intro j
    exact (hframe.2.2.2.1 (6+j.val) (Or.inl (by have hj:=j.isLt;omega))).trans (hroots j)
  · intro j hj
    have hc:=hchirp j hj
    constructor
    · exact (hframe.2.2.2.1 (UniformWorkingLength.axisCount n+7+2*j)
        (Or.inl (by omega))).trans hc.1
    · exact (hframe.2.2.2.1 (UniformWorkingLength.axisCount n+7+2*j+1)
        (Or.inl (by omega))).trans hc.2
  · intro k hk
    exact (hframe.2.2.2.1 (UniformPaddedInputPreparation.dataBase n+k)
      (Or.inl (by dsimp [UniformPaddedInputPreparation.dataBase];omega))).trans (hdata k hk)
  · have hc:=UniformChirpKernelMachine.loopCost_bound n (UniformWorkingLength.workingLength n) 0 (UniformWorkingLength.workingLength n)
    have hL:UniformWorkingLength.workingLength n<4*n:=UniformWorkingLength.workingLength_upper hn
    dsimp [fullPreparationBudget];omega

theorem fullPreparationBudget_isBigO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hl:(fun n : ℕ => ((52*n:ℕ):ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 52
    filter_upwards [] with n
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hc:(fun _n : ℕ => (18:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (18:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa [fullPreparationBudget,Nat.cast_add,Nat.cast_mul] using
    (UniformPaddedInputPreparation.fullPreparationBudget_isBigO_input.add hl).add hc

theorem paddedOperand {n : ℕ} {x : Fin n → ℂ} {u : State}
    (h : UniformPaddedInputMachine.Partial (UniformPaddedInputPreparation.dataBase n)
      (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) x u)
    (j : Fin (UniformWorkingLength.workingLength n)) [NeZero (UniformWorkingLength.workingLength n)] :
    ∃ v,u.scalarHeap (UniformPaddedInputPreparation.dataBase n+j.val)=some v ∧
      v.value=UniformCyclic.paddedChirp (OAI.ExactFourier.zeta (2*n)) x
        (OAI.ExactFourier.FourierCRT.finZMod (UniformWorkingLength.workingLength n) j) :=
  ⟨_,h j.val j.isLt,UniformPaddedInputMachine.paddedScalar_cyclic _ x j⟩

theorem kernelOperand {n : ℕ} {u : State}
    (h : UniformChirpKernelMachine.Partial (kernelBase n) (UniformWorkingLength.workingLength n)
      n (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) u)
    (j : Fin (UniformWorkingLength.workingLength n)) [NeZero (UniformWorkingLength.workingLength n)] :
    u.scalarHeap (kernelBase n+j.val)=some (prepared
      (UniformCyclic.chirpKernel (OAI.ExactFourier.zeta (2*n)) n
        (OAI.ExactFourier.FourierCRT.finZMod (UniformWorkingLength.workingLength n) j))) := by
  rw [h j.val j.isLt,UniformChirpKernelMachine.kernelScalar_fin _ n _
    (UniformWorkingLength.workingLength_lower n) j]

end
end ExactFourierCircuits.UniformChirpKernelPreparation
