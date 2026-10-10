import DFTModelGlobalKernelSourceBounds
import DFTModelGlobalKernelAssemblyPeak
import DFTModelGlobalSectorBillingSelected
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open UniformMachine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
namespace KS
export DFTModelGlobalKernelSource (Context W states)
end KS
namespace GA
export DFTModelGlobalKernelAssembly (nativeInput packed prepared savingWork)
end GA

abbrev axes {F : ℕ} (c : KS.Context F) := UniformSectorPackingMachine.physicalAxes c.physical

def input {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T) : DFTModelGlobalKernelAssembly.Input.T :=
 GA.nativeInput (axes c) Complex.I KS.W bank

/-- Actual original-address input cells, before any packing or child work. -/
def Entry {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T)
 (v v0 : ℕ→Fin c.packing.volume→Scalar) : Prop :=
 ∀r,r<KS.W→∀j : Fin c.packing.volume,
 bank.look (r*c.packing.volume+j.val) Tagged.blank=encodePaired (v r j) (v0 r j)

lemma packed_at {F : ℕ} (c : KS.Context F) (v : ℕ→Fin c.packing.volume→Scalar)
 (r : ℕ) (j : Fin c.packing.volume) :
 UniformConditionalKernelLayout.packed c v r j.val=
 v r (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume j) := by
 unfold UniformConditionalKernelLayout.packed UniformGlobalPackingChildPreparation.packedValues
 simp only[dite_eq_left j.isLt]

/-- The typed packed input is derived from actual entry cells and the SAME
physical permutations; no packed-bank certificate is supplied. -/
theorem packed_encoded {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T)
 (v v0 : ℕ→Fin c.packing.volume→Scalar) (entry : Entry c bank v v0) :
 DFTModelGlobalSectorLoop.Encoded c.loop.volume (GA.packed (input c bank))
 (UniformConditionalKernelLayout.packed c v) (UniformConditionalKernelLayout.packed c v0) := by
 intro r hr j hj
 have volume:c.loop.volume=c.packing.volume:=c.loopVolume.trans c.inverseVolume.symm
 rw[volume] at hj
 let p : Fin c.packing.volume:=⟨j,hj⟩
 let k:Fin (UniformSectorPacking.radices (axes c)).prod:=(finCongr c.physicalVolume).symm p
 have kval:k.val=j:=rfl
 have cell:=DFTModelGlobalKernelAssembly.packed_cell (axes c) Complex.I KS.W r bank hr k
 have original:=entry r hr
  (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume p)
 have same : (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume p).val=
  (UniformSectorPacking.unpackingPermutation (axes c) k).val := rfl
 rw[same] at original
 have val : (GA.packed (input c bank)).look (r*c.packing.volume+j) Tagged.blank=
  encodePaired
   (v r (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume p))
   (v0 r (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume p)) := by
  have get : (GA.packed (input c bank)).look (r*c.packing.volume+j) Tagged.blank=
   bank.look (r*c.packing.volume+(UniformSectorPacking.unpackingPermutation (axes c) k).val) Tagged.blank := by
   simpa only[input,c.physicalVolume,kval] using cell
  exact get.trans original
 rw[volume]
 simpa only[←packed_at,p] using val

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin
