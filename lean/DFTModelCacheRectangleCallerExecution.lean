import DFTModelCacheRectangleCallerBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run program argument DFTModelCacheSelectedPhysicalRowsCaller.program
 DFTModelCacheTopology.prepare

def nativeArgument (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) : DFTModelCacheSelectedPhysicalRowsCaller.Input.T :=
 DFTModelCacheSelectedPhysicalRowsCaller.nativeInput
  (DFTModelCacheRectangleMetadata.chunk q original c slot)
  original.C original.negative original.constants
  (DFTModelCacheDisplacement.metadata (radix n j)
    (DFTModelCacheRectangleMetadata.kernel n j q original),
   (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))

theorem genuine_value (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) :
 (run program (genuineInput n j q original slot)).val=
 ((genuineInput n j q original slot,preparedConfig q),
  (run DFTModelCacheSelectedPhysicalRowsCaller.program (nativeArgument n j q original c slot)).val) := by
 have hp:=DFTModelCacheTopology.prepare_spec q.a q.e
 have hpv:(run DFTModelCacheTopology.prepare (q.a,q.e)).val=preparedConfig q:=hp.1
 rw [program_value,genuine_dimensions]
 dsimp only
 rw [hpv,argument_native]
 rfl

theorem genuine_work (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) :
 (run program (genuineInput n j q original slot)).work=
 28*DFTModelCacheRectanglePreparation.height q+35+
 (run DFTModelCacheSelectedPhysicalRowsCaller.program (nativeArgument n j q original c slot)).work+291 := by
 have hp:=DFTModelCacheTopology.prepare_spec q.a q.e
 have hpv:(run DFTModelCacheTopology.prepare (q.a,q.e)).val=preparedConfig q:=hp.1
 rw [program_work,genuine_dimensions]
 dsimp only
 rw [hpv,hp.2.2.1,argument_native]
 rfl

theorem genuine_valid (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) :
 (run program (genuineInput n j q original slot)).valid ↔
 (run DFTModelCacheSelectedPhysicalRowsCaller.program (nativeArgument n j q original c slot)).valid := by
 have hp:=DFTModelCacheTopology.prepare_spec q.a q.e
 have hpv:(run DFTModelCacheTopology.prepare (q.a,q.e)).val=preparedConfig q:=hp.1
 rw [program_valid,genuine_dimensions]
 simp only [hpv,hp.2.1,true_and]
 rw [argument_native]
 rfl

theorem genuine_peak (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) :
 (run program (genuineInput n j q original slot)).peak≤
 max (max 3 (4*(q.a+q.e)+2)) (max (argumentPeak (preparedConfig q))
  (run DFTModelCacheSelectedPhysicalRowsCaller.program (nativeArgument n j q original c slot)).peak) := by
 have hp:=DFTModelCacheTopology.prepare_spec q.a q.e
 have hpv:(run DFTModelCacheTopology.prepare (q.a,q.e)).val=preparedConfig q:=hp.1
 rw [program_peak,genuine_dimensions]
 dsimp only
 rw [hpv]
 have ha:=argument_peak (genuineInput n j q original slot) (preparedConfig q)
 rw [argument_native]
 exact max_le_max (max_le_max (Nat.le_refl 3) hp.2.2.2) (max_le_max ha (Nat.le_refl _))

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller
