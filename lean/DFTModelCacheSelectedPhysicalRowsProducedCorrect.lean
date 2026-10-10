import DFTModelCacheSelectedPhysicalRowsProduced

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsProduced
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section
attribute [local irreducible] program DFTModelCacheSelectedPhysicalRows.program
 DFTModelCacheMatchingProduced.program

def nativeInput (p:UniformChunkMatchingPreparation.Parameters)
 (W:List (UniformReplayPrint.ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (C T P:ℕ) (raw:DFTModelCacheSpectrum.Input.T) : Input.T :=
 (((p.height.K,(C,(T,P))),raw),
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p,
   DFTModelCacheSelectedPhysicalRows.rowTape (UniformChunkMatchingPreparation.selectedRows p W
    (UniformCrossShearTableMachine.locations _ C T P))))

theorem nativeArgument (p:UniformChunkMatchingPreparation.Parameters)
 (W:List (UniformReplayPrint.ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (C T P:ℕ) (raw:DFTModelCacheSpectrum.Input.T) :
 argumentValue (nativeInput p W C T P raw)
  (run DFTModelCacheSelectedPhysicalRows.program (nativeInput p W C T P raw).2).val=
 DFTModelCacheMatchingProduced.args p.radix p.height.K C T P raw
  (run DFTModelCacheSelectedPhysicalRows.program (nativeInput p W C T P raw).2).val := rfl

def workBudget (p:UniformChunkMatchingPreparation.Parameters) (D:ℕ)
 (kernel:UniformRankKernelMachine.Parameters) (M:ℕ) : ℕ :=
 DFTModelCacheSelectedPhysicalRows.workBudget p.radix M+
 DFTModelCacheMatchingProduced.workBudget p.radix D kernel p.height.K M+27

/-- Actual physical row generation discharges every row/matching/range/label
premise of MatchingProduced. Rectangle/root/address geometry remains ordinary
caller data. The selected native occurrence list is the explicit boundary. -/
theorem specification {B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (domain:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (D:ℕ) (kernel:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape kernel p.radix)
 (width:kernel.N=UniformRadixTwoDAG.width p.height.K) (hD:0<D)
 (radixDiv:p.radix∣D) (fftDiv:UniformRadixTwoDAG.width p.height.K∣D) (h4:4∣D)
 (C T P:ℕ) (positive:C+UniformToeplitzCrossDAG.bankSize p.height.K≤T)
 (negative:T+UniformToeplitzCrossDAG.bankSize p.height.K≤P) :
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 let input:=nativeInput p W C T P raw
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W domain
 let bank:=UniformToeplitzCrossDAG.sharedBank p.height.K
  (DFTModelCacheSpectrum.rankKernels p.radix kernel p.height.K (OAI.ExactFourier.zeta p.radix))
 (run program input).valid ∧
 (run program input).work≤workBudget p D kernel (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program input).val.2.len=9*p.radix ∧
 ∀lane:Fin 9,∀d:Fin p.radix,
  (run program input).val.2.look (lane.val*p.radix+d.val) 0=
  UniformGlobalMatchingScaleBankBridge.nativeFactor E
   (fun i=>UniformMatchingConjugateLoadMachine.value p.height.K bank
    (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 dsimp only
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 let input:=nativeInput p W C T P raw
 let rs:=(run DFTModelCacheSelectedPhysicalRows.program input.2).val
 have rows:=DFTModelCacheSelectedPhysicalRows.native_matching p layout W C T P domain degree
 have labels:=DFTModelCacheSelectedPhysicalRows.native_source p layout.capacity W C T P domain
 have spec:=DFTModelCacheMatchingProduced.specification p.radix D kernel shape p.height.K C T P
  width hD radixDiv fftDiv h4 rs (UniformChunkMatchingPreparation.physicalEdges layout W domain)
  rows.1 rows.2.1 rows.2.2 layout.radixPositive
  (fun i=>UniformPackedMatchingShearMachine.selectedLabels p W i.val) labels positive negative
 obtain ⟨_retained,valid,work,_peak,length,factors⟩:=spec
 have mapValid:=DFTModelCacheSelectedPhysicalRows.program_valid input.2
 have mapWork:=DFTModelCacheSelectedPhysicalRows.program_work input.2
 have count:input.2.2.len=(UniformChunkMatchingPreparation.indices p W).length:=by
  simp only [input,nativeInput,DFTModelCacheSelectedPhysicalRows.rowTape,
   DFTModelCacheSelectedCoefficients.physicalRows,Tape.tab,
   UniformChunkMatchingPreparation.selectedRows,List.length_map]
 change (run program input).valid ∧ _
 rw [program_run,nativeArgument]
 refine ⟨⟨mapValid,valid⟩,?_,length,factors⟩
 change (run DFTModelCacheSelectedPhysicalRows.program input.2).work+
  (run DFTModelCacheMatchingProduced.program
   (DFTModelCacheMatchingProduced.args p.radix p.height.K C T P raw rs)).work+27≤_
 change (run DFTModelCacheSelectedPhysicalRows.program input.2).work≤
  DFTModelCacheSelectedPhysicalRows.workBudget p.radix input.2.2.len at mapWork
 rw [count] at mapWork
 unfold workBudget
 exact Nat.add_le_add_right (Nat.add_le_add mapWork work) 27

theorem peak {B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (domain:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:DegreeBound (UniformChunkMatchingPreparation.edges W) 6)
 (D:ℕ) (kernel:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape kernel p.radix)
 (width:kernel.N=UniformRadixTwoDAG.width p.height.K) (hD:0<D)
 (radixDiv:p.radix∣D) (fftDiv:UniformRadixTwoDAG.width p.height.K∣D) (h4:4∣D)
 (C T P:ℕ) (positive:C+UniformToeplitzCrossDAG.bankSize p.height.K≤T)
 (negative:T+UniformToeplitzCrossDAG.bankSize p.height.K≤P)
 (WB:ℕ) (hWB:5≤WB)
 (words:DFTModelCacheHeight.Words DFTModelCacheSelectedPhysicalRows.Input WB
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p,
   DFTModelCacheSelectedPhysicalRows.rowTape (UniformChunkMatchingPreparation.selectedRows p W
    (UniformCrossShearTableMachine.locations _ C T P)))) :
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 (run program (nativeInput p W C T P raw)).peak≤
 max (WB^DFTModelCacheSelectedPhysicalRows.wordDegree)
  (DFTModelCacheMatchingProduced.peakBudget p.radix D kernel p.height.K
   (UniformChunkMatchingPreparation.indices p W).length) := by
 dsimp only
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 let input:=nativeInput p W C T P raw
 let rs:=(run DFTModelCacheSelectedPhysicalRows.program input.2).val
 have rows:=DFTModelCacheSelectedPhysicalRows.native_matching p layout W C T P domain degree
 have labels:=DFTModelCacheSelectedPhysicalRows.native_source p layout.capacity W C T P domain
 have spec:=DFTModelCacheMatchingProduced.specification p.radix D kernel shape p.height.K C T P
  width hD radixDiv fftDiv h4 rs (UniformChunkMatchingPreparation.physicalEdges layout W domain)
  rows.1 rows.2.1 rows.2.2 layout.radixPositive
  (fun i=>UniformPackedMatchingShearMachine.selectedLabels p W i.val) labels positive negative
 have mapped:=DFTModelCacheSelectedPhysicalRows.program_peak input.2 WB hWB words
 rw [program_run,nativeArgument]
 exact max_le_max mapped spec.2.2.2.1

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsProduced
