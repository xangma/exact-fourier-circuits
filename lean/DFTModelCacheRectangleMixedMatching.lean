import DFTModelCacheSelectedPhysicalRowsCallerPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section
attribute [local irreducible] program DFTModelCacheSelectedCoefficients.produced
 DFTModelCacheMatchingNat.program DFTModelCConstants.program DFTModelCacheMatchingFactors.program

theorem mixed_factorArgs_canonical (r seedRadix D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (K C T P : ℕ) (rs : Tape DFTModelCacheSelectedCoefficients.Row.T)
    (hD : 0<D) (h4 : 4∣D) :
    factorArgs (readyValue (args r K C T P
      (DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D)) rs))=
    DFTModelCacheMatchingFactors.args r
      (run DFTModelCacheMatchingNat.program (r,rs)).val.2
      (run DFTModelCacheSelectedCoefficients.produced
        (DFTModelCacheSelectedCoefficients.producedArgs K C T P
          (DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D)) rs)).val.2.2.2
      Complex.I ExactFourierCircuits.a⁻¹ := by
  simp only [factorArgs,readyValue,matchedValue,seedValue,args,
    DFTModelCacheSelectedCoefficients.producedArgs]
  rw [DFTModelCConstants.program_value D hD h4]
  have i : DFTModelCConstants.bank.look 3 0=Complex.I := by
    simpa using (DFTModelCConstants.bank_cell (3:Fin 5))
  have ai : DFTModelCConstants.bank.look 2 0=ExactFourierCircuits.a⁻¹ := by
    simpa using (DFTModelCConstants.bank_cell (2:Fin 5))
  rw [i,ai]


def mixedWorkBudget (r seedRadix D : ℕ) (p : UniformRankKernelMachine.Parameters) (K M : ℕ) : ℕ :=
  DFTModelCacheSpectrumConjugate.workBudget seedRadix D p+40*(Nat.log2 (K+1)+1)+99*M+
    3000000*(r+1)^2+400*(UniformPowerMachine.loopCost (D/4)+1)+2781*r+620

def mixedPeakBudget (r seedRadix D : ℕ) (p : UniformRankKernelMachine.Parameters) (K M : ℕ) : ℕ :=
  max (max (D+2) (seedRadix+7*p.N+7))
    (max (max (K+6) (max M (max (UniformToeplitzCrossDAG.bankSize K) 6)))
      (max (4000*(r+1)) (9*r)))

private theorem add_work {a b c d A B C D : ℕ}
    (ha:a≤A)(hb:b≤B)(hc:c≤C)(hd:d≤D) :
    a+b+c+d+73≤A+B+C+D+73 := by omega

private theorem max_peak {a b c d A B r : ℕ} (radix:2≤r)
    (ha:a≤ max A B)(hb:b≤4000*(r+1))(hc:c≤A)(hd:d≤9*r) :
    max a (max b (max c (max d 3)))≤ max A (max B (max (4000*(r+1)) (9*r))) := by omega

/-- The SAME closed program independently uses the outer physical radix for
Matching55/factors and the raw spectrum radix for the original axis root.
Nested rectangle widths need not equal their retained Newton seed order. -/
theorem mixed_specification {M : ℕ} (r seedRadix D : ℕ) (p : UniformRankKernelMachine.Parameters)
    (shape : DFTModelCacheDisplacement.Shape p seedRadix) (K C T P : ℕ)
    (width : p.N=UniformRadixTwoDAG.width K) (hD : 0<D)
    (radixDiv : seedRadix∣D) (fftDiv : UniformRadixTwoDAG.width K∣D) (h4 : 4∣D)
    (rs : Tape DFTModelCacheSelectedCoefficients.Row.T) (E : Fin M→Edge)
    (rowEndpoints : DFTModelCacheMatchingNat.Rows E rs)
    (hm : Matching E) (hr : InRange r E) (radix : 2≤r)
    (labels : Fin M→UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize K))
    (rowLabels : DFTModelCacheSelectedCoefficients.RowSource C T P rs labels)
    (positive : C+UniformToeplitzCrossDAG.bankSize K≤T)
    (negative : T+UniformToeplitzCrossDAG.bankSize K≤P) :
    let raw := (DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D))
    let x := args r K C T P raw rs
    let bank := UniformToeplitzCrossDAG.sharedBank K
      (DFTModelCacheSpectrum.rankKernels seedRadix p K (OAI.ExactFourier.zeta seedRadix))
    (run program x).val.1=readyValue x ∧
    (run program x).valid ∧
    (run program x).work≤ mixedWorkBudget r seedRadix D p K M ∧
    (run program x).peak≤ mixedPeakBudget r seedRadix D p K M ∧
    (run program x).val.2.len=9*r ∧
    ∀lane:Fin 9,∀d:Fin r,
      (run program x).val.2.look (lane.val*r+d.val) 0=
        UniformGlobalMatchingScaleBankBridge.nativeFactor E
          (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i)) lane d.val := by
  dsimp only
  have coef:=DFTModelCacheSelectedCoefficients.produced_specification seedRadix D p shape K C T P
    width hD radixDiv fftDiv rs labels rowLabels positive negative
  have matched:=matching_specification r rs E rowEndpoints hm hr
  have cst:=DFTModelCConstants.specification D hD h4
  have factors:=DFTModelCacheMatchingFactors.produces_native r E hm hr radix
    (run DFTModelCacheMatchingNat.program (r,rs)).val.2
    (run DFTModelCacheSelectedCoefficients.produced
      (DFTModelCacheSelectedCoefficients.producedArgs K C T P
        (DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D)) rs)).val.2.2.2
    _ matched.1 coef.1
  rw [program_run,mixed_factorArgs_canonical r seedRadix D p K C T P rs hD h4]
  simp only [args,DFTModelCacheSelectedCoefficients.producedArgs] at coef factors ⊢
  refine ⟨by trivial,⟨coef.2.1,matched.2.1,cst.2.1,factors.1⟩,?_,?_,factors.2.2.2.1,factors.2.2.2.2⟩
  · have sum:=add_work coef.2.2.1 matched.2.2.1 cst.2.2.1 factors.2.1
    dsimp only [mixedWorkBudget]
    convert sum using 1; omega
  · exact max_peak radix coef.2.2.2 matched.2.2.2
      (cst.2.2.2.trans (le_max_left _ _)) factors.2.2.1

end
end ExactFourierCircuits.DFTModelCacheMatchingProduced
