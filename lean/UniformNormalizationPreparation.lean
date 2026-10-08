import UniformNormalizationMachine
import UniformChirpKernelPreparation
import UniformReciprocalMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformNormalizationPreparation
open UniformMachine UniformAssembly UniformPairMachine
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)
noncomputable section

def layout : List Op := [.literal 43 7,.add 27 10 43,.literal 44 2,
  .mul 44 8 44,.add 27 27 44,.add 27 27 17,.add 27 27 17]
theorem layout_length : layout.length=7 := rfl
def normBase (n : ℕ) : ℕ :=
  UniformChirpKernelPreparation.kernelBase n+UniformWorkingLength.workingLength n
def fullProgram : Program := embed
  (UniformChirpKernelPreparation.fullProgram.map (relocate 0 293)++layout.map Op.code)
  UniformNormalizationMachine.program [.halt] 336

theorem fullProgram_length : fullProgram.length=337 := by
  rw [fullProgram,embed_length,List.length_append,List.length_map,List.length_map,
    UniformChirpKernelPreparation.fullProgram_length,layout_length,
    UniformNormalizationMachine.program_length]
  rfl

theorem kernel_code : CodeAt UniformChirpKernelPreparation.fullProgram fullProgram 0 293 := by
  intro i hi
  simp only [fullProgram,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem layout_code : BlockAt layout fullProgram 293 := by
  intro i hi
  have hi7:i<7:=hi
  unfold fullProgram embed
  rw [List.getElem?_append_left (by
    simp only [List.length_append,List.length_map,UniformChirpKernelPreparation.fullProgram_length,
      UniformNormalizationMachine.program_length,layout_length];omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append,List.length_map,UniformChirpKernelPreparation.fullProgram_length,
      layout_length];omega)]
  rw [List.getElem?_append_right (by simp [UniformChirpKernelPreparation.fullProgram_length])]
  simp only [List.length_map,UniformChirpKernelPreparation.fullProgram_length,Nat.add_sub_cancel_left,
    List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]

theorem normalization_code : CodeAt UniformNormalizationMachine.program fullProgram 300 336 := by
  simpa only [fullProgram,List.length_append,List.length_map,
    UniformChirpKernelPreparation.fullProgram_length,layout_length] using
    embed_code (UniformChirpKernelPreparation.fullProgram.map (relocate 0 293)++layout.map Op.code)
      UniformNormalizationMachine.program [.halt] 336

theorem finish_code : fullProgram[336]?=some .halt := by
  simp only [fullProgram,embed]
  rw [List.getElem?_append_right (by simp [UniformChirpKernelPreparation.fullProgram_length,
    layout_length,UniformNormalizationMachine.program_length])]
  simp [UniformChirpKernelPreparation.fullProgram_length,layout_length,
    UniformNormalizationMachine.program_length]

theorem layout_peak (n ell L B : ℕ) (s : State) (h8:s.natReg 8=n)
    (h10:s.natReg 10=ell) (h17:s.natReg 17=L) (hB:ell+7+2*n+2*L≤B) :
    peak layout s≤B := by
  simp [layout,peak,Op.peak,Op.apply,writeNat,next,h8,h10,h17]
  omega

theorem layout_base (n ell L : ℕ) (s : State) (h8:s.natReg 8=n)
    (h10:s.natReg 10=ell) (h17:s.natReg 17=L) :
    (applyBlock layout s).natReg 27=ell+7+2*n+2*L := by
  simp [applyBlock,layout,Op.apply,writeNat,next,h8,h10,h17]
  omega

theorem layout_nat (s : State) (r : ℕ) (h27:r≠27) (h43:r≠43) (h44:r≠44) :
    (applyBlock layout s).natReg r=s.natReg r := by
  simp [applyBlock,layout,Op.apply,writeNat,next,h27,h43,h44]

theorem layout_heap (s : State) : (applyBlock layout s).scalarHeap=s.scalarHeap := rfl
theorem layout_natHeap (s : State) : (applyBlock layout s).natHeap=s.natHeap := rfl
theorem layout_outputs (s : State) : (applyBlock layout s).outputs=s.outputs := rfl
theorem layout_roots (s : State) : (applyBlock layout s).rootOrders=s.rootOrders := rfl

theorem word_setup {n : ℕ} (hn:0<n) :
    337≤(n+2)^19 ∧ normBase n≤(n+2)^19 := by
  have h:=UniformChirpKernelPreparation.full_wordBound_setup hn
  have hp:337≤(n+2)^19:=by
    have hp:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
    norm_num at hp;omega
  have hb:(n+2)^18≤(n+2)^19:=by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hp,le_trans h.2.2.2 hb⟩

def fullPreparationBudget (n : ℕ) : ℕ :=
  UniformChirpKernelPreparation.fullPreparationBudget n+
    UniformNormalizationMachine.runtime (UniformWorkingLength.workingLength n)+8

/-- Actual initial-state preparation of both convolution operands and their
normalization. Fast Fourier execution and final output remain separate. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃ t u,
    BoundedExecution fullProgram n x ((n+2)^19) initial t u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.natReg 24=UniformMasterRootMachine.order n ∧ u.natReg 8=n ∧
    (∀j : Fin 6,u.scalarHeap j.val=some (prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀j : Fin (UniformWorkingLength.axisCount n+1),u.scalarHeap (6+j.val)=some
      (prepared (OAI.ExactFourier.zeta (UniformSelectedCRT.radices n j)))) ∧
    UniformChirpTableMachine.Partial (UniformWorkingLength.axisCount n+7) n
      (OAI.ExactFourier.zeta (2*n)) u ∧
    UniformPaddedInputMachine.Partial (UniformPaddedInputPreparation.dataBase n)
      (UniformWorkingLength.workingLength n) (OAI.ExactFourier.zeta (2*n)) x u ∧
    UniformChirpKernelMachine.Partial (UniformChirpKernelPreparation.kernelBase n)
      (UniformWorkingLength.workingLength n) n (UniformWorkingLength.workingLength n)
      (OAI.ExactFourier.zeta (2*n)) u ∧
    u.scalarHeap (normBase n)=some (prepared (UniformWorkingLength.workingLength n:ℂ)⁻¹) ∧
    u.natReg 27=normBase n ∧ u.rootOrders=[UniformMasterRootMachine.order n] ∧
    u.outputs=initial.outputs ∧ u.pc=336 ∧ t≤fullPreparationBudget n := by
  obtain ⟨t,v,hv,hheader,hcrt,horder,h8,hbank,hroots,hchirp,hdata,hkernel,hroot,hout,hpc,hcost⟩:=
    UniformChirpKernelPreparation.preparation_execution hn x
  obtain ⟨h337,hspace⟩:=word_setup hn
  have hprefix:=UniformBoundedAssembly.boundedExecution_placed kernel_code
    (by rw [UniformChirpKernelPreparation.fullProgram_length];omega :
      0+UniformChirpKernelPreparation.fullProgram.length≤(n+2)^19) (by omega : 293≤(n+2)^19) hv
  have hp0:placed 0 initial=initial:=rfl
  rw [hp0] at hprefix
  let w:State:={v with pc:=293}
  have hlayout:=block_runs layout fullProgram 293 n ((n+2)^19) x w layout_code rfl
    hprefix.final_bound (by rw [layout_length];omega)
    (by simp [readable,layout,Op.readable])
    (layout_peak n (UniformWorkingLength.axisCount n) (UniformWorkingLength.workingLength n)
      ((n+2)^19) w h8 hheader.2.1 hheader.2.2.2.2.1
      (by simpa [normBase,UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,
        two_mul,Nat.add_assoc] using hspace))
  let z:=applyBlock layout w
  let e:State:={z with pc:=0}
  have heB:WordBound ((n+2)^19) e:=changePC_bound _ z 0 hlayout.final_bound (by omega)
  have hbase:z.natReg 27=normBase n:=by
    simpa [z,normBase,UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,
      two_mul,Nat.add_assoc] using layout_base n (UniformWorkingLength.axisCount n)
      (UniformWorkingLength.workingLength n) w h8 hheader.2.1 hheader.2.2.2.2.1
  have hL:e.natReg 17=UniformWorkingLength.workingLength n:=
    (layout_nat w 17 (by decide) (by decide) (by decide)).trans hheader.2.2.2.2.1
  obtain ⟨u,hu,hnorm,hf,hup⟩:=UniformNormalizationMachine.normalization_execution x ((n+2)^19)
    (UniformWorkingLength.workingLength n) (normBase n) e rfl hL hbase
    (UniformWorkingLength.workingLength_pos hn) (by omega) heB
  have htail:=UniformBoundedAssembly.boundedExecution_placed normalization_code
    (by rw [UniformNormalizationMachine.program_length];omega :
      300+UniformNormalizationMachine.program.length≤(n+2)^19) (by omega : 336≤(n+2)^19) hu
  have hpz:z.pc=300:=by rw [UniformReciprocalMachine.applyBlock_pc,layout_length]
  have heq:placed 300 e=z:=by change {z with pc:=300}=z;rw [←hpz]
  rw [heq] at htail
  let final:State:={u with pc:=336}
  have hh:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=
    .halt htail.final_bound (by simp [step,final,finish_code])
  have hnats:∀r,7≤r → r≠27 → r≠41 → r≠42 → r≠43 → r≠44 → u.natReg r=v.natReg r:=by
    intro r hr h27 h41 h42 h43 h44
    exact (hf.2.2.2.2.2.1 r hr h41 h42).trans (layout_nat w r h27 h43 h44)
  have hheap:∀a,a<normBase n → u.scalarHeap a=v.scalarHeap a:=by
    intro a ha
    exact hf.2.2.2.1 a (by omega)
  have hNatHeap:u.natHeap=v.natHeap:=by
    simpa [e,z,w,layout_natHeap] using hf.1
  have hhead:UniformCRTHeaderMachine.Header n u:=by
    obtain ⟨hh0,hh10,hh11,hh16,hh17,hh18,hhp⟩:=hheader
    refine ⟨hf.2.2.2.2.1.trans ((layout_nat w 0 (by decide) (by decide) (by decide)).trans hh0),
      ?_,?_,?_,?_,?_,?_⟩
    · exact (hnats 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh10
    · exact (hnats 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh11
    · exact (hnats 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh16
    · exact (hnats 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh17
    · exact (hnats 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh18
    · simpa [UniformWorkingMachine.PrimeTable,hNatHeap] using hhp
  refine ⟨t+7+UniformNormalizationMachine.runtime (UniformWorkingLength.workingLength n)+1,final,
    (hprefix.trans hlayout).executes (htail.executes hh),hhead,?_,?_,?_,?_,?_,?_,?_,?_,hnorm,?_,
    hf.2.2.1.trans hroot,hf.2.1.trans hout,rfl,?_⟩
  · simpa [UniformCRTHeaderMachine.CRTTable,final,hNatHeap] using hcrt
  · exact (hnats 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans horder
  · exact (hnats 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  · intro j
    exact (hheap j.val (by have hj:=j.isLt;dsimp [normBase,UniformChirpKernelPreparation.kernelBase,
      UniformPaddedInputPreparation.dataBase];omega)).trans (hbank j)
  · intro j
    exact (hheap (6+j.val) (by have hj:=j.isLt;dsimp [normBase,UniformChirpKernelPreparation.kernelBase,
      UniformPaddedInputPreparation.dataBase];omega)).trans (hroots j)
  · intro j hj
    refine ⟨?_,?_⟩
    · exact (hheap _ (by dsimp [normBase,UniformChirpKernelPreparation.kernelBase,
        UniformPaddedInputPreparation.dataBase];omega)).trans (hchirp j hj).1
    · exact (hheap _ (by dsimp [normBase,UniformChirpKernelPreparation.kernelBase,
        UniformPaddedInputPreparation.dataBase];omega)).trans (hchirp j hj).2
  · intro j hj
    exact (hheap _ (by dsimp [normBase,UniformChirpKernelPreparation.kernelBase,
      UniformPaddedInputPreparation.dataBase];omega)).trans (hdata j hj)
  · intro j hj
    exact (hheap _ (by unfold normBase;omega)).trans (hkernel j hj)
  · exact (hf.2.2.2.2.2.1 27 (by decide) (by decide) (by decide)).trans hbase
  · unfold fullPreparationBudget;omega

theorem normalizationBudget_bound {n : ℕ} (hn:0<n) :
    UniformNormalizationMachine.runtime (UniformWorkingLength.workingLength n)≤82*n := by
  have h:=UniformNormalizationMachine.runtime_log_bound (UniformWorkingLength.workingLength n)
  have hl:=Nat.log2_le_self (UniformWorkingLength.workingLength n+1)
  have hL:=UniformWorkingLength.workingLength_upper hn
  omega

theorem fullPreparationBudget_isBigO_input :
    (fun n : ℕ => (fullPreparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)) := by
  have hr:(fun n : ℕ => (UniformNormalizationMachine.runtime (UniformWorkingLength.workingLength n):ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 82
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hb:=normalizationBudget_bound (show 0<n by omega)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact_mod_cast hb
  have hc:(fun _n : ℕ => (8:ℝ)) =O[Filter.atTop] (fun n : ℕ => (n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (8:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa [fullPreparationBudget,Nat.cast_add] using
    (UniformChirpKernelPreparation.fullPreparationBudget_isBigO_input.add hr).add hc

end
end ExactFourierCircuits.UniformNormalizationPreparation
