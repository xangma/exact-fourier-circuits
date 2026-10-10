import DFTModelGlobalCompactPools
import DFTModelCacheMatchingProducedCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalCompactPoolsProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section

/-- One actual factor producer, followed by charged projections into the
compact (radix,9r factors) ABI. Its raw row/master input is retained internally
by the original producer; no factor table is supplied. -/
def record : Prog false DFTModelCacheMatchingProduced.Input DFTModelGlobalCompactPools.Pool :=
  .fork (.atom .fst) (.comp DFTModelCacheMatchingProduced.program (.atom .snd))

attribute [local irreducible] DFTModelCacheMatchingProduced.program

theorem record_run (x:DFTModelCacheMatchingProduced.Input.T) : run record x=
    ⟨(x.1,(run DFTModelCacheMatchingProduced.program x).val.2),
      (run DFTModelCacheMatchingProduced.program x).work+4,
      (run DFTModelCacheMatchingProduced.program x).peak,
      (run DFTModelCacheMatchingProduced.program x).valid⟩ := by
  simp [record,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

def entry {M:ℕ} (r:ℕ) (positive:0<r) (pool:ℕ) (E:Fin M→Edge) (mu:Fin M→ℂ) :
    UniformGlobalDiagonalRowsMachine.Entry where
  radix:=r
  positive:=positive
  pool:=pool
  value:=fun lane d=>UniformGlobalMatchingScaleBankBridge.nativeFactor E mu lane d.val

/-- All inputs here are original metadata/root/Row3 plus ordinary matching
and label geometry. The nine-lane values follow from the genuine producer. -/
theorem record_specification {M:ℕ} (r D:ℕ) (p:UniformRankKernelMachine.Parameters)
    (shape:DFTModelCacheDisplacement.Shape p r) (K C T P pool:ℕ)
    (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
    (radixDiv:r∣D) (fftDiv:UniformRadixTwoDAG.width K∣D) (h4:4∣D)
    (rs:Tape DFTModelCacheSelectedCoefficients.Row.T) (E:Fin M→Edge)
    (rowEndpoints:DFTModelCacheMatchingNat.Rows E rs)
    (hm:Matching E) (hr:InRange r E) (radix:2≤r)
    (labels:Fin M→UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize K))
    (rowLabels:DFTModelCacheSelectedCoefficients.RowSource C T P rs labels)
    (positive:C+UniformToeplitzCrossDAG.bankSize K≤T)
    (negative:T+UniformToeplitzCrossDAG.bankSize K≤P) :
    let raw:=(DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))
    let x:=DFTModelCacheMatchingProduced.args r K C T P raw rs
    let bank:=UniformToeplitzCrossDAG.sharedBank K
      (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r))
    let a:=entry r (by omega) pool E
      (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i))
    (run record x).val.1=a.radix ∧ (run record x).val.2.len=9*a.radix ∧
    (∀lane:Fin 9,∀d:Fin a.radix,(run record x).val.2.look (lane.val*a.radix+d.val) 0=a.value lane d) ∧
    (run record x).valid ∧
    (run record x).work≤DFTModelCacheMatchingProduced.workBudget r D p K M+4 ∧
    (run record x).peak≤DFTModelCacheMatchingProduced.peakBudget r D p K M := by
  dsimp only
  have h:=DFTModelCacheMatchingProduced.specification r D p shape K C T P width hD
    radixDiv fftDiv h4 rs E rowEndpoints hm hr radix labels rowLabels positive negative
  rw [record_run]
  exact ⟨rfl,h.2.2.2.2.1,h.2.2.2.2.2,h.2.1,Nat.add_le_add_right h.2.2.1 4,h.2.2.2.1⟩

end
end ExactFourierCircuits.DFTModelGlobalCompactPoolsProduced
