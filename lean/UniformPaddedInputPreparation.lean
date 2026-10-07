import UniformPaddedInputMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace ExactFourierCircuits.UniformPaddedInputPreparation
open UniformMachine UniformPairMachine UniformAssembly
noncomputable section

def head : Program :=
  [.natLiteral 34 0,.natBinary .add 40 0 34,.natBinary .add 0 8 34,
   .natBinary .add 1 17 34,.natLiteral 35 7,.natBinary .add 2 10 35,
   .natLiteral 36 2,.natBinary .mul 37 8 36,.natBinary .add 9 2 37]

/-- The literal loader consumes the prepared chirp bank and restores the header. -/
def program : Program := embed head UniformPaddedInputMachine.program
  [.natBinary .add 0 40 34,.halt] 27

theorem program_length : program.length=29 := rfl
theorem input_code : CodeAt UniformPaddedInputMachine.program program 9 27 :=
  embed_code _ _ _ _

def zeroed (s : State) := writeNat s 34 0
def saved (s : State) := writeNat (zeroed s) 40 (s.natReg 0)
def count (s : State) (n : ℕ) := writeNat (saved s) 0 n
def width (s : State) (n L : ℕ) := writeNat (count s n) 1 L
def seven (s : State) (n L : ℕ) := writeNat (width s n L) 35 7
def bank (s : State) (n L ell : ℕ) := writeNat (seven s n L) 2 (ell+7)
def two (s : State) (n L ell : ℕ) := writeNat (bank s n L ell) 36 2
def double (s : State) (n L ell : ℕ) := writeNat (two s n L ell) 37 (2*n)
def inputEntry (s : State) (n L ell : ℕ) := writeNat (double s n L ell) 9 (ell+7+2*n)

theorem startup_runs {n : ℕ} (x : Fin n → ℂ) (B L ell : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (h17 : s.natReg 17=L)
    (h10 : s.natReg 10=ell) (hB : 128≤B) (hspace : ell+7+2*n+L≤B)
    (hs : WordBound B s) : BoundedRuns program n x B s 9 (inputEntry s n L ell) := by
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
  refine .next hs (u:=zeroed s) ?_ (.next h1 (u:=saved s) ?_ (.next h2 (u:=count s n) ?_
    (.next h3 (u:=width s n L) ?_ (.next h4 (u:=seven s n L) ?_ (.next h5 (u:=bank s n L ell) ?_
      (.next h6 (u:=two s n L ell) ?_ (.next h7 (u:=double s n L ell) ?_
        (.next h8b (u:=inputEntry s n L ell) ?_ (.refl h9)))))))))
  all_goals simp [step,program,embed,head,UniformPaddedInputMachine.program,inputEntry,double,
    two,bank,seven,width,count,saved,zeroed,writeNat,next,hp,h8,h17,h10,evalNat,Nat.mul_comm]

def SetupFrame (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧
  ∀ r,7≤r → r≠9 → r≠34 → r≠35 → r≠36 → r≠37 → r≠40 → u.natReg r=s.natReg r

theorem setup_frame (s : State) (n L ell : ℕ) : SetupFrame s (inputEntry s n L ell) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr h9 h34 h35 h36 h37 h40
  simp [inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next,
    h9,h34,h35,h36,h37,h40,show r≠0 by omega,show r≠1 by omega,show r≠2 by omega]

def ResultFrame (n L ell : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀ b,b<ell+7+2*n ∨ ell+7+2*n+L≤b → u.scalarHeap b=s.scalarHeap b) ∧
  u.natReg 0=s.natReg 0 ∧
  ∀ r,7≤r → r≠9 → r≠34 → r≠35 → r≠36 → r≠37 → r≠40 → u.natReg r=s.natReg r

theorem post_header_execution {n : ℕ} (x : Fin n → ℂ) (B L ell : ℕ) (s : State)
    (hp : s.pc=0) (h8 : s.natReg 8=n) (h17 : s.natReg 17=L)
    (h10 : s.natReg 10=ell)
    (hc : UniformChirpTableMachine.Partial (ell+7) n (OAI.ExactFourier.zeta (2*n)) s)
    (hB : 128≤B) (hspace : ell+7+2*n+L≤B) (hs : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (14+UniformPaddedInputMachine.loopCost n 0 L) u ∧
    UniformPaddedInputMachine.Partial (ell+7+2*n) L (OAI.ExactFourier.zeta (2*n)) x u ∧
    ResultFrame n L ell s u ∧ u.pc=28 := by
  have hstart:=startup_runs x B L ell s hp h8 h17 h10 hB hspace hs
  let entry:State:={inputEntry s n L ell with pc:=0}
  have he:WordBound B entry:=changePC_bound B _ 0 hstart.final_bound (by omega)
  obtain ⟨w,hw,ht,hf,_hpc⟩:=UniformPaddedInputMachine.input_execution x B L (ell+7)
    (ell+7+2*n) (OAI.ExactFourier.zeta (2*n)) entry rfl
    (by simp [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (by simp [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next])
    (UniformPaddedInputMachine.coefficients_of_chirp_table hc) (by omega) (by omega) hspace he
  have hepc:(inputEntry s n L ell).pc=9:=by
    simp [inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next,hp]
  have htable:BoundedRuns program n x B (inputEntry s n L ell)
      (3+UniformPaddedInputMachine.loopCost n 0 L) {w with pc:=27}:=by
    have heq:{inputEntry s n L ell with pc:=9}=inputEntry s n L ell:=by
      cases h:inputEntry s n L ell;simp_all
    simpa [placed,entry,heq] using UniformBoundedAssembly.boundedExecution_placed input_code
      (by change 9+18≤B;omega) (by omega) hw
  have hz:w.natReg 34=0:=by
    have h:=hf.2.2.2.2 34 (by omega) (by omega)
    simpa [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next] using h
  have hsave:w.natReg 40=s.natReg 0:=by
    have h:=hf.2.2.2.2 40 (by omega) (by omega)
    simpa [entry,inputEntry,double,two,bank,seven,width,count,saved,zeroed,writeNat,next] using h
  let u:State:=writeNat {w with pc:=27} 0 (s.natReg 0)
  have hub:WordBound B u:=writeNat_bound B {w with pc:=27} 0 (s.natReg 0)
    htable.final_bound (by change 27+1≤B;omega) (hs.2.1 0)
  have hfinish:BoundedExecution program n x B {w with pc:=27} 2 u:=by
    refine .next htable.final_bound ?_ (.halt hub ?_)
    · simp [step,program,embed,head,UniformPaddedInputMachine.program,u,hz,hsave,evalNat]
    · simp [step,program,embed,head,UniformPaddedInputMachine.program,u,writeNat,next]
  refine ⟨u,?_,ht,?_,rfl⟩
  · convert (hstart.trans htable).executes hfinish using 1 <;> omega
  · refine ⟨hf.1,hf.2.1,hf.2.2.1,?_,?_,?_⟩
    · exact hf.2.2.2.1
    · simp [u,writeNat,next]
    · intro r hr h9 h34 h35 h36 h37 h40
      have h:=hf.2.2.2.2 r hr h9
      have hs':SetupFrame s (inputEntry s n L ell):=setup_frame s n L ell
      have h':u.natReg r=(inputEntry s n L ell).natReg r:=by
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
  (UniformChirpPreparation.fullProgram.map (relocate 0 230)) program [.halt] 259

theorem chirp_code : CodeAt UniformChirpPreparation.fullProgram fullProgram 0 230 := by
  intro i hi
  simp only [fullProgram,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem preparation_code : CodeAt program fullProgram 230 259 := embed_code _ _ _ _

theorem fullProgram_length : fullProgram.length=260 := by
  rw [fullProgram,embed_length,List.length_map,UniformChirpPreparation.fullProgram_length,
    program_length]
  rfl

theorem full_finish_code : fullProgram[259]?=some .halt := by
  simp only [fullProgram,embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformChirpPreparation.fullProgram_length,program_length];omega)]
  simp only [List.length_append,List.length_map,UniformChirpPreparation.fullProgram_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def dataBase (n : ℕ) : ℕ := UniformWorkingLength.axisCount n+7+2*n
def fullPreparationBudget (n : ℕ) : ℕ := UniformChirpPreparation.fullPreparationBudget n+48*n+17

theorem full_wordBound_setup {n : ℕ} (hn : 0<n) :
    230+(n+2)^17≤(n+2)^18 ∧ 260≤(n+2)^18 ∧
    128≤(n+2)^17 ∧ dataBase n+UniformWorkingLength.workingLength n≤(n+2)^17 := by
  have h16:260≤(n+2)^16:=by
    have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 16
    norm_num at h;omega
  have hell:UniformWorkingLength.axisCount n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount;omega
  have hL:UniformWorkingLength.workingLength n<4*n:=
    UniformWorkingLength.workingLength_upper hn
  have h17:(n+2)^17=(n+2)*(n+2)^16:=by ring
  have h18:(n+2)^18=(n+2)*(n+2)^17:=by ring
  have h17lower:260≤(n+2)^17:=by rw [h17];nlinarith
  refine ⟨?_,?_,by omega,?_⟩
  · rw [h18];nlinarith
  · rw [h18];nlinarith
  · dsimp [dataBase];rw [h17];nlinarith

/-- Initial-state execution now constructs the real padded input as well as the
root, CRT and chirp banks. All input reads, stores, branches and halts are charged. -/
theorem preparation_execution {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^18) initial t u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
    (∀ j : Fin 6,u.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀ j : Fin (UniformWorkingLength.axisCount n+1),u.scalarHeap (6+j.val)=
      some (prepared (OAI.ExactFourier.zeta (UniformSelectedCRT.radices n j)))) ∧
    UniformChirpTableMachine.Partial (UniformWorkingLength.axisCount n+7) n
      (OAI.ExactFourier.zeta (2*n)) u ∧
    UniformPaddedInputMachine.Partial (dataBase n) (UniformWorkingLength.workingLength n)
      (OAI.ExactFourier.zeta (2*n)) x u ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=259 ∧ t≤fullPreparationBudget n := by
  obtain ⟨hBC,hfinishB,h128,hspace⟩:=full_wordBound_setup hn
  obtain ⟨tc,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hchirp,hrootOrders,hout,_hpc,hcost⟩:=
    UniformChirpPreparation.preparation_execution hn x
  let entry:State:={v with pc:=0}
  have heB:WordBound ((n+2)^17) entry:=changePC_bound _ v 0 hv.final_bound (by omega)
  obtain ⟨u,hu,htable,hframe,_hup⟩:=post_header_execution x ((n+2)^17)
    (UniformWorkingLength.workingLength n) (UniformWorkingLength.axisCount n) entry rfl
    h8 hheader.2.2.2.2.1 hheader.2.1 hchirp h128 hspace heB
  have hprefix:BoundedRuns fullProgram n x ((n+2)^18) initial tc {v with pc:=230}:=by
    have h:=UniformAssembly.BoundedExecution.placed chirp_code
      (by omega : 0+(n+2)^17≤(n+2)^18) (by omega : 230≤(n+2)^18) hv
    simpa [placed,initial] using h
  have htail:BoundedRuns fullProgram n x ((n+2)^18) {v with pc:=230}
      (14+UniformPaddedInputMachine.loopCost n 0 (UniformWorkingLength.workingLength n))
      {u with pc:=259}:=by
    have h:=UniformAssembly.BoundedExecution.placed preparation_code hBC (by omega : 259≤(n+2)^18) hu
    simpa [placed,entry] using h
  let final:State:={u with pc:=259}
  have hh:BoundedExecution fullProgram n x ((n+2)^18) final 1 final:=
    .halt htail.final_bound (by simp [step,final,full_finish_code])
  refine ⟨tc+(14+UniformPaddedInputMachine.loopCost n 0 (UniformWorkingLength.workingLength n))+1,
    final,(hprefix.trans htail).executes hh,hframe.header hheader,hframe.crt hcrt,?_,?_,?_,?_,?_,htable,
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
  · have hc:=UniformPaddedInputMachine.loopCost_bound n 0 (UniformWorkingLength.workingLength n)
    have hL:UniformWorkingLength.workingLength n<4*n:=UniformWorkingLength.workingLength_upper hn
    dsimp [fullPreparationBudget];omega

theorem fullPreparationBudget_isBigO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hl:(fun n : ℕ => ((48*n:ℕ):ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 48
    filter_upwards [] with n
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hc:(fun _n : ℕ => (17:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (17:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa [fullPreparationBudget,Nat.cast_add,Nat.cast_mul] using
    (UniformChirpPreparation.fullPreparationBudget_isBigO_input.add hl).add hc

end
end ExactFourierCircuits.UniformPaddedInputPreparation
