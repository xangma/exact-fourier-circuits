import DFTModelChirpTablesCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirpTables
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem output_value (n L j : ℕ) (z : ℂ) (hj : j<n) :
    (values n L (DFTModelChirp.bank n z)).2.1.look j 0 = UniformChirp.chirp z j := by
  simp only [values,Tape.look,Tape.tab,hj,↓reduceDIte,forward]
  exact DFTModelChirp.bank_even n j z hj

theorem input_value (n L j : ℕ) (z : ℂ) (hj : j<L) :
    (values n L (DFTModelChirp.bank n z)).2.2.1.look j 0 =
      if j<n then UniformChirp.chirp z j else 0 := by
  simp only [values,Tape.look,Tape.tab,hj,↓reduceDIte,inputValue,forward]
  by_cases hn : j<n
  · simp only [hn,↓reduceIte]
    exact DFTModelChirp.bank_even n j z hn
  · simp [hn]

theorem kernel_value (n L j : ℕ) (z : ℂ) (hj : j<L) :
    (values n L (DFTModelChirp.bank n z)).2.2.2.1.look j 0 =
      (UniformChirpKernelMachine.kernelScalar z n L j).value := by
  simp only [values,Tape.look,Tape.tab,hj,↓reduceDIte,kernelValue,
    UniformChirpKernelMachine.kernelScalar]
  by_cases hn : j<n
  · simp only [hn,↓reduceIte,UniformPairMachine.prepared]
    exact DFTModelChirp.bank_odd n j z hn
  · by_cases hd : L-j<n
    · simp only [hn,hd,↓reduceIte,UniformPairMachine.prepared]
      exact DFTModelChirp.bank_odd n (L-j) z hd
    · simp [hn,hd,UniformPairMachine.prepared]

/-- Multiplying the generated input coefficient gives the actual source operand,
including the literal zero padding. No coefficient action is assumed. -/
theorem padded_input_value {n : ℕ} (x : Fin n → ℂ) (L j : ℕ) (z : ℂ) (hj : j<L) :
    (values n L (DFTModelChirp.bank n z)).2.2.1.look j 0 *
      (Tape.mk n x).look j 0 = (UniformPaddedInputMachine.paddedScalar z x j).value := by
  rw [input_value n L j z hj]
  by_cases hn : j<n
  · simp [UniformPaddedInputMachine.paddedScalar,Tape.look,hn]
  · simp [UniformPaddedInputMachine.paddedScalar,Tape.look,hn,UniformPairMachine.prepared]

/-- The physical source bank addresses are retained in this correspondence. -/
structure SourceMatch {n : ℕ} (x : Fin n → ℂ) (o : Output.T) (s : UniformMachine.State) : Prop where
  chirp : ∀j,j<n → s.scalarHeap (UniformWorkingLength.axisCount n+7+2*j)=
    some (UniformPairMachine.prepared (o.1.look (2*j) 0))
  inverseChirp : ∀j,j<n → s.scalarHeap (UniformWorkingLength.axisCount n+7+2*j+1)=
    some (UniformPairMachine.prepared (o.1.look (2*j+1) 0))
  outputCoefficient : ∀j,j<n → s.scalarHeap (UniformWorkingLength.axisCount n+7+2*j)=
    some (UniformPairMachine.prepared (o.2.1.look j 0))
  input : ∀j,j<UniformWorkingLength.workingLength n →
    (s.scalarHeap (UniformPaddedInputPreparation.dataBase n+j)).map UniformMachine.Scalar.value =
      some (o.2.2.1.look j 0*(Tape.mk n x).look j 0)
  kernel : ∀j,j<UniformWorkingLength.workingLength n →
    s.scalarHeap (UniformChirpKernelPreparation.kernelBase n+j)=
      some (UniformPairMachine.prepared (o.2.2.2.1.look j 0))
  normalization : s.scalarHeap (UniformNormalizationPreparation.normBase n)=
    some (UniformPairMachine.prepared o.2.2.2.2)

/-- Exact relation to the genuinely executed source preparation from `initial`.
The source execution, generated tables and scalar identities are all discharged. -/
theorem source_preparation {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃t u, UniformMachine.BoundedExecution UniformNormalizationPreparation.fullProgram n x
      ((n+2)^19) UniformMachine.initial t u ∧
      SourceMatch x (run program ((n,UniformWorkingLength.workingLength n),
        OAI.ExactFourier.zeta (2*n))).val u ∧
      t≤UniformNormalizationPreparation.fullPreparationBudget n := by
  obtain ⟨t,u,he,_header,_crt,_order,_n,_constants,_roots,hc,hi,hk,hnorm,
    _normBase,_rootOrders,_out,_pc,hcost⟩ := UniformNormalizationPreparation.preparation_execution hn x
  refine ⟨t,u,he,?_,hcost⟩
  rw [program_value n _ _ hn (DFTModelChirp.specified_period n hn)]
  constructor
  · intro j hj
    simpa only [values,DFTModelChirp.bank_even n j _ hj] using (hc j hj).1
  · intro j hj
    simpa only [values,DFTModelChirp.bank_odd n j _ hj] using (hc j hj).2
  · intro j hj
    rw [output_value n _ j _ hj]
    exact (hc j hj).1
  · intro j hj
    rw [hi j hj,padded_input_value x _ j _ hj]
    rfl
  · intro j hj
    rw [kernel_value n _ j _ hj,hk j hj]
    congr 1
    unfold UniformChirpKernelMachine.kernelScalar
    split <;> simp [UniformPairMachine.prepared]
    split <;> simp
  · exact hnorm

end
end ExactFourierCircuits.DFTModelChirpTables
