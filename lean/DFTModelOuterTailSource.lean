import DFTModelOuterTailProgram
import UniformSequentialExecution
import UniformFinalOuterHeaders

set_option autoImplicit false

/-! Actual original outer stages 18–20. Stage 17's physical source spectrum,
AP/BI tables and retained prepared coefficients remain genuine entry contracts.
Every BI/AP gather, original output header and output instruction is charged. -/
namespace ExactFourierCircuits.DFTModelOuterTail
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformNatBlockMachine UniformSequentialAssembly UniformSequentialExecution
noncomputable section
attribute [local irreducible] applyBlock UniformFinalOuterHeaders.output
  UniformPhysicalCRTConsumerMachine.program UniformChirpOutputMachine.program

def stages : List Program := [UniformPhysicalCRTConsumerMachine.program,
  natProgram UniformFinalOuterHeaders.output,UniformChirpOutputMachine.program]

structure Entry (n V S T AP BI a c B : ℕ) (eta kappa : ℂ)
    (f : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (s : State) : Prop where
  positive : 0<V
  count : s.natReg 101=n
  width : s.natReg 103=V
  sourceBase : s.natReg 6026=S
  targetBase : s.natReg 6025=T
  alphaBase : s.natReg 7310=AP
  betaBase : s.natReg 7311=BI
  chirpAddress : a=s.natReg 102+7
  normalizationAddress : c=a+2*n+2*V
  source : ∀j : Fin V, s.scalarHeap (S+j.val)=some (f j)
  alphaTable : UniformGlobalNatPreparation.PermutationBank V AP s.natHeap alpha
  betaTable : UniformGlobalNatPreparation.PermutationBank V BI s.natHeap betaInverse
  coefficients : UniformChirpOutputMachine.Coefficients n a eta s
  normalization : s.scalarHeap c=some (UniformPairMachine.prepared kappa)
  disjoint : UniformPermutationMachine.Disjoint S T V
  coefficientsBeforeSource : a+2*n≤S
  coefficientsBeforeTarget : a+2*n≤T
  normalizationBeforeSource : c<S
  normalizationBeforeTarget : c<T
  sourceFit : S+V≤B
  targetFit : T+V≤B
  alphaFit : AP+V≤B
  betaFit : BI+V≤B
  code : 64≤B
  wordBound : WordBound B s

/-- The original eleven header operations, specialized only by the three
saved geometry registers. No replacement literals are substituted. -/
theorem output_headers (n V a c : ℕ) (s : State)
    (count : s.natReg 101=n) (width : s.natReg 103=V)
    (chirp : a=s.natReg 102+7) (norm : c=a+2*n+2*V) :
    (applyBlock UniformFinalOuterHeaders.output s).natReg 8=n ∧
    (applyBlock UniformFinalOuterHeaders.output s).natReg 17=V ∧
    (applyBlock UniformFinalOuterHeaders.output s).natReg 25=a ∧
    (applyBlock UniformFinalOuterHeaders.output s).natReg 26=s.natReg 6025 ∧
    (applyBlock UniformFinalOuterHeaders.output s).natReg 27=c := by
  simp only [UniformFinalOuterHeaders.output,applyBlock,
    UniformFinalOuterHeaders.literal_reg,UniformFinalOuterHeaders.binary_reg]
  simp [evalNat,count,width,chirp,norm,Nat.mul_comm,Nat.add_assoc,Nat.mul_two]

structure Result (n V S T : ℕ) (hV : 0<V) (eta kappa : ℂ)
    (f : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (u : State) : Prop where
  source : ∀j : Fin V, u.scalarHeap (S+j.val)=some (f (betaInverse (alpha j)))
  target : ∀j : Fin V, u.scalarHeap (T+j.val)=some (f (betaInverse j))
  outputs : ∀j,j<n → u.outputs j=some
    (UniformChirpOutputMachine.value hV eta kappa (fun j => f (betaInverse j)) j).value
  pc : u.pc=17

theorem execution {n V S T AP BI a c B : ℕ} (x : Fin n → ℂ) (eta kappa : ℂ)
    (f : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (s : State)
    (entry : Entry n V S T AP BI a c B eta kappa f alpha betaInverse s) :
    ∃u, LocalStages n B x stages s (18*V+13*n+36) u ∧
      Result n V S T entry.positive eta kappa f alpha betaInverse u := by
  let e : State := {s with pc:=0}
  have ewb : WordBound B e := changePC_bound _ s 0 entry.wordBound (by omega)
  obtain ⟨t,crt,tpc,source,target,outside,frame⟩ := UniformPhysicalCRTConsumerMachine.execution
    n B V S T AP BI x f alpha betaInverse e rfl entry.width entry.sourceBase
    entry.targetBase entry.alphaBase entry.betaBase entry.source entry.alphaTable entry.betaTable
    entry.disjoint entry.sourceFit entry.targetFit entry.alphaFit entry.betaFit
    (by have h:=entry.code;omega) ewb
  have reg (q : ℕ) (hq : UniformPhysicalCRTConsumerMachine.Protected q) :
      t.natReg q=s.natReg q := frame.natReg q hq
  have tn : t.natReg 101=n := (reg _ (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans entry.count
  have tv : t.natReg 103=V := (reg _ (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans entry.width
  have tt : t.natReg 6025=T := (reg _ (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)).trans entry.targetBase
  have t102 : t.natReg 102=s.natReg 102 := reg _ (by unfold UniformPhysicalCRTConsumerMachine.Protected;omega)
  have co : UniformChirpOutputMachine.Coefficients n a eta t := by
    intro j hj
    exact (outside _ (Or.inl (by have h:=entry.coefficientsBeforeSource;omega))
      (Or.inl (by have h:=entry.coefficientsBeforeTarget;omega))).trans (entry.coefficients j hj)
  have norm : t.scalarHeap c=some (UniformPairMachine.prepared kappa) :=
    (outside _ (Or.inl entry.normalizationBeforeSource) (Or.inl entry.normalizationBeforeTarget)).trans entry.normalization
  let d : State := {t with pc:=0}
  have dwb : WordBound B d := changePC_bound _ t 0 crt.final_bound (by omega)
  have normFit : c≤B := entry.wordBound.2.2.2.1 _ _ entry.normalization
  have safe := UniformFinalOuterHeaders.output_safe d B
    (by change t.natReg 6025≤B;exact crt.final_bound.2.1 _)
    (by change t.natReg 102+2*t.natReg 101+2*t.natReg 103+7≤B
        rw [t102,tn,tv]
        have aeq:=entry.chirpAddress;have ceq:=entry.normalizationAddress;omega)
  have header := nat_execution UniformFinalOuterHeaders.output x d rfl dwb
    (by rw [UniformFinalOuterHeaders.output_length];have h:=entry.code;omega) safe.1 safe.2
  let h := applyBlock UniformFinalOuterHeaders.output d
  have headerFrame := UniformFinalOuterHeaders.output_frame d
  have heap : h.scalarHeap=t.scalarHeap := headerFrame.2.1
  have headers := output_headers n V a c d tn tv
    (by change a=t.natReg 102+7;rw [t102];exact entry.chirpAddress) entry.normalizationAddress
  have hco : UniformChirpOutputMachine.Coefficients n a eta {h with pc:=0} := by
    intro j hj
    change h.scalarHeap (a+2*j)=some (UniformPairMachine.prepared (UniformChirp.chirp eta j))
    rw [heap]
    exact co j hj
  have hv : UniformChirpOutputMachine.Values V T (fun j => f (betaInverse j)) {h with pc:=0} := by
    intro j
    change h.scalarHeap (T+j.val)=some (f (betaInverse j))
    rw [heap]
    exact target j
  obtain ⟨u,output,values,outputFrame,upc⟩ := UniformChirpOutputMachine.output_execution x
    entry.positive B a T c eta kappa (fun j => f (betaInverse j)) {h with pc:=0}
    rfl headers.1 headers.2.1 headers.2.2.1 (headers.2.2.2.1.trans tt) headers.2.2.2.2
    (by change h.scalarHeap c=some (UniformPairMachine.prepared kappa);rw [heap];exact norm)
    hco hv entry.code (by have h:=entry.coefficientsBeforeSource;have h':=entry.sourceFit;omega)
    entry.targetFit (changePC_bound _ h 0 header.final_bound (by omega))
  have native : LocalStages n B x stages s (18*V+13*n+36) u := by
    have head : BoundedExecution (natProgram UniformFinalOuterHeaders.output) n x B
        {t with pc:=0} 12 h := by simpa only [UniformFinalOuterHeaders.output_length] using header
    have tail : LocalStages n B x [UniformChirpOutputMachine.program] h (13*n+6) u := by
      simpa only [Nat.add_zero] using LocalStages.cons output (LocalStages.nil u output.final_bound)
    have joined : LocalStages n B x
        [UniformPhysicalCRTConsumerMachine.program,natProgram UniformFinalOuterHeaders.output,
         UniformChirpOutputMachine.program] s ((18*V+18)+(12+(13*n+6))) u :=
      LocalStages.cons crt (LocalStages.cons head tail)
    change LocalStages n B x
      [UniformPhysicalCRTConsumerMachine.program,natProgram UniformFinalOuterHeaders.output,
       UniformChirpOutputMachine.program] s (18*V+13*n+36) u
    have time : (18*V+18)+(12+(13*n+6))=18*V+13*n+36 := by omega
    rw [time] at joined
    exact joined
  refine ⟨u,native,⟨?_,?_,values,upc⟩⟩
  · intro j
    exact (congrFun outputFrame.2.1 _).trans ((congrFun heap _).trans (source j))
  · intro j
    exact (congrFun outputFrame.2.1 _).trans ((congrFun heap _).trans (target j))

/-- Optional terminated assembly adds its one final halt to the same charged
three-helper run. The surrounding outer program uses the local continuation. -/
theorem assembled_execution {n V S T AP BI a c B : ℕ} (x : Fin n → ℂ) (eta kappa : ℂ)
    (f : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (s : State)
    (entry : Entry n V S T AP BI a c B eta kappa f alpha betaInverse s) :
    ∃u, BoundedExecution (UniformSequentialAssembly.program stages) n x B
      {s with pc:=0} (18*V+13*n+37) {u with pc:=64} ∧
      Result n V S T entry.positive eta kappa f alpha betaInverse u := by
  obtain ⟨u,h,result⟩ := execution x eta kappa f alpha betaInverse s entry
  have size : UniformSequentialAssembly.size stages=64 := by
    simp only [stages,UniformSequentialAssembly.size,UniformPhysicalCRTConsumerMachine.program_length,
      UniformChirpOutputMachine.program_length,natProgram_length,UniformFinalOuterHeaders.output_length]
  have assembled := h.execution (by rw [size];exact entry.code)
  refine ⟨u,?_,result⟩
  simpa only [size,Nat.add_assoc] using assembled

/-- The real final loop supplies the standard DFT contract once the actual
third transform's BI-reindexed spectrum is identified by the clock caller. -/
theorem execution_dft {n V S T AP BI a c B : ℕ} [NeZero V]
    (hn : 0<n) (hnV : 2*n≤V) (x : Fin n → ℂ)
    (f : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (s : State)
    (entry : Entry n V S T AP BI a c B (OAI.ExactFourier.zeta (2*n)) (V:ℂ)⁻¹
      f alpha betaInverse s)
    (spectrum : UniformChirpOutputMachine.FinalSpectrum x (fun j => f (betaInverse j))) :
    ∃u, LocalStages n B x stages s (18*V+13*n+36) u ∧ ComputesDFT n x u := by
  obtain ⟨u,h,result⟩ := execution x _ _ f alpha betaInverse s entry
  refine ⟨u,h,?_⟩
  intro j
  rw [result.outputs j.val j.isLt,
    UniformChirpOutputMachine.value_fourier hn entry.positive hnV x _ spectrum j]

end
end ExactFourierCircuits.DFTModelOuterTail
