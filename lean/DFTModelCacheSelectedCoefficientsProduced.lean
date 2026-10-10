import DFTModelCacheSelectedCoefficientsSource
import DFTModelCacheSpectrumConjugateBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] program constants DFTModelCacheSpectrumConjugate.program

abbrev ProducedInput := p (p w Bases) (p DFTModelCacheSpectrum.Input (Ty.a Row))
abbrev ProducedOutput := p ProducedInput Output

def producerArgument : Prog false ProducedInput Input :=
  .fork (.atom .fst) (.fork
    (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelCacheSpectrumConjugate.program)
    (.comp (.atom .snd) (.atom .snd)))
/-- Proper rectangle7N production, real constants, signed address decoding,
and row-order tabulation all occur in this one closed typed program. -/
def produced : Prog false ProducedInput ProducedOutput :=
  .fork (.atom .id) (.comp producerArgument program)

def producedArgs (K C T P : ℕ) (raw : DFTModelCacheSpectrum.Input.T)
    (rs : Tape Row.T) : ProducedInput.T := ((K,(C,(T,P))),(raw,rs))

theorem producerArgument_run (K C T P : ℕ) (raw : DFTModelCacheSpectrum.Input.T)
    (rs : Tape Row.T) :
    run producerArgument (producedArgs K C T P raw rs)=
      ((run DFTModelCacheSpectrumConjugate.program raw).pass
        (fun b=>Bill.one (args K C T P b rs))).pay 9 0 := by
  simp [producerArgument,producedArgs,args,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem produced_run (K C T P : ℕ) (raw : DFTModelCacheSpectrum.Input.T)
    (rs : Tape Row.T) :
    run produced (producedArgs K C T P raw rs)=
      ((run DFTModelCacheSpectrumConjugate.program raw).pass (fun b=>
        (run program (args K C T P b rs)).pass
          (fun z=>Bill.one (producedArgs K C T P raw rs,z)))).pay 12 0 := by
  rw [produced,fork_run,comp_run,producerArgument_run]
  simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem produced_retained (K C T P : ℕ) (raw : DFTModelCacheSpectrum.Input.T)
    (rs : Tape Row.T) :
    (run produced (producedArgs K C T P raw rs)).val.1=producedArgs K C T P raw rs ∧
    (run produced (producedArgs K C T P raw rs)).val.2.1=
      args K C T P (run DFTModelCacheSpectrumConjugate.program raw).val rs := by
  rw [produced_run]
  simp only [Bill.pass,Bill.pay,Bill.one,program_value]
  exact ⟨trivial,trivial⟩

/-- Canonical root and actual metadata determine the shared7N values.
Selected physical row production is the sole remaining row-input boundary. -/
theorem produced_specification {M : ℕ} (r D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape:DFTModelCacheDisplacement.Shape p r) (K C T P : ℕ)
    (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
    (radixDiv:r∣D) (fftDiv:UniformRadixTwoDAG.width K∣D)
    (rs : Tape Row.T)
    (labels:Fin M→UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize K))
    (rows:RowSource C T P rs labels)
    (positive:C+UniformToeplitzCrossDAG.bankSize K≤T)
    (negative:T+UniformToeplitzCrossDAG.bankSize K≤P) :
    let raw:= (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))
    let bank:=UniformToeplitzCrossDAG.sharedBank K
      (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r))
    DFTModelCacheMatchingFactors.CoefficientSource
      (run produced (producedArgs K C T P raw rs)).val.2.2.2
      (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i)) ∧
    (run produced (producedArgs K C T P raw rs)).valid ∧
    (run produced (producedArgs K C T P raw rs)).work≤
      DFTModelCacheSpectrumConjugate.workBudget r D p+40*(Nat.log2 (K+1)+1)+99*M+534 ∧
    (run produced (producedArgs K C T P raw rs)).peak≤
      max (max (D+2) (r+7*p.N+7)) (max (K+6) (max M (max (UniformToeplitzCrossDAG.bankSize K) 6))) := by
  dsimp only
  let raw:DFTModelCacheSpectrum.Input.T:=
    (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))
  let bank:=UniformToeplitzCrossDAG.sharedBank K
    (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r))
  let b:PairBank.T:=(run DFTModelCacheSpectrumConjugate.program raw).val
  have spec:=DFTModelCacheSpectrumConjugate.specification r D p shape K width hD radixDiv fftDiv
  have source:PairSource b bank:=⟨spec.1,spec.2.1⟩
  have coeff:=program_coefficients K C T P b bank rs labels source rows positive negative
  have bound:=program_bounds K C T P b bank rs labels source rows positive negative
  rw [produced_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,and_true]
  refine ⟨coeff,⟨spec.2.2.1,bound.1⟩,?_,?_⟩
  · have h:=spec.2.2.2.1
    change (run DFTModelCacheSpectrumConjugate.program raw).work≤_ at h
    have h':=bound.2.1
    change (run DFTModelCacheSpectrumConjugate.program raw).work+
      (run program (args K C T P b rs)).work+1+12≤_
    omega
  · exact max_le (spec.2.2.2.2.trans (le_max_left _ _)) (bound.2.2.trans (le_max_right _ _))

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
