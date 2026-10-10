import DFTModelCacheSelectedPhysicalRowsCallerNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheHeightColorCaller.program
 DFTModelCacheSelectedPhysicalRowsProduced.program

def workBudget (p:UniformChunkMatchingPreparation.Parameters) (D:ℕ)
 (kernel:UniformRankKernelMachine.Parameters) (M:ℕ) : ℕ :=
 DFTModelCacheHeightColorCaller.workBudget p.height.a p.height.e+
 DFTModelCacheSelectedPhysicalRowsProduced.workBudget p D kernel M+25

/-- Genuine raw dimensions generate every selected row and color internally.
The native borrowed injection then derives physical matching/range and exact
coefficient-label provenance. No selected tape, colors, degree, permutation or
decoded coefficient bank is an input or hypothesis. Arbitrary-K native callers
remain separate; the actual SeedChunk caller discharges `computed` by rfl. -/
theorem specification {B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (computed:p.height.K=DFTModelCacheTopology.exponent p.height.a p.height.e)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (height:p.depth≤8*p.height.K+6)
 (D:ℕ) (kernel:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape kernel p.radix)
 (width:kernel.N=UniformRadixTwoDAG.width p.height.K) (hD:0<D)
 (radixDiv:p.radix∣D) (fftDiv:UniformRadixTwoDAG.width p.height.K∣D) (h4:4∣D)
 (C T P:ℕ) (positive:C+UniformToeplitzCrossDAG.bankSize p.height.K≤T)
 (negative:T+UniformToeplitzCrossDAG.bankSize p.height.K≤P) :
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 let domain:=UniformChunkMatchingPreparation.cross_domain p ha he
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 let input:=nativeInput p C T P raw
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W domain
 let bank:=UniformToeplitzCrossDAG.sharedBank p.height.K
  (DFTModelCacheSpectrum.rankKernels p.radix kernel p.height.K (OAI.ExactFourier.zeta p.radix))
 ∃u ticks,DFTModelCacheTopology.Result p.height.a p.height.e u ticks ∧
 (run program input).valid ∧
 (run program input).work≤workBudget p D kernel (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program input).val.1=
  (run DFTModelCacheHeightColorCaller.program input.2.2).val ∧
 (run program input).val.2.2.len=9*p.radix ∧
 ∀lane:Fin 9,∀d:Fin p.radix,
  (run program input).val.2.2.look (lane.val*p.radix+d.val) 0=
  UniformGlobalMatchingScaleBankBridge.nativeFactor E
   (fun i=>UniformMatchingConjugateLoadMachine.value p.height.K bank
    (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 dsimp only
 have hd:p.depth≤8*DFTModelCacheTopology.exponent p.height.a p.height.e+6:=by simpa only [computed] using height
 obtain ⟨u,ticks,source,valid,work,_,_,_,_,_⟩:=DFTModelCacheHeightColorCaller.specification
  p.color p.height.a p.height.e 0 C P p.depth
  (DFTModelCacheHeightColorCaller.localBound p.height.a p.height.e) p.height.enabled hd (by omega)
 have next:=DFTModelCacheSelectedPhysicalRowsProduced.specification p layout
  (UniformChunkMatchingPreparation.crossWord p ha he)
  (UniformChunkMatchingPreparation.cross_domain p ha he)
  (UniformChunkMatchingPreparation.cross_degree p ha he)
  D kernel shape width hD radixDiv fftDiv h4 C T P positive negative
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 change ∃u ticks,DFTModelCacheTopology.Result p.height.a p.height.e u ticks ∧ _
 rw [program_run,native_argument p computed ha he height C T P raw]
 refine ⟨u,ticks,source,⟨valid,next.1⟩,?_,rfl,next.2.2.1,next.2.2.2⟩
 change (run DFTModelCacheHeightColorCaller.program
  (DFTModelCacheHeightColorCaller.input p.color p.height.a p.height.e 0 C P p.depth p.height.enabled)).work+_+25≤_
 unfold workBudget
 exact Nat.add_le_add_right (Nat.add_le_add work next.2.1) 25

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
