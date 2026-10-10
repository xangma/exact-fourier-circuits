import DFTModelSavingCostRecords
import DFTModelSavingCostSuffix
import DFTModelSavingShape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.large DFTModelSavingProgram.body
  DFTModelCacheRecords.seed DFTModelSavingRecords.stream DFTModelSavingBinarySuffix.program

/-- The concrete large branch produces its own seed and then runs the actual
chronological stream and spectator suffix. Billing needs only the invariant
bank length; the tags may be any pattern produced by the recursive body. -/
theorem large_work_bound (h : Handler ChildPort) (k : ℕ) (I : ℂ)
    (v : Tape Tagged.T) (even : 2*(v.len/2)=v.len) :
    (Code.run DFTModelSavingProgram.large h ((k,I),v)).work≤
      seedAllowance+73+8*(k/UniformFixedNetwork.m*UniformFixedNetwork.m)+
        (k-k/UniformFixedNetwork.m*UniformFixedNetwork.m)*(420*(v.len/2)+123)+
        (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
          (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed
            (k/UniformFixedNetwork.m)).val,((k,I),v)))).work := by
  have cost:=large_work h k I v
  dsimp only at cost
  rw [DFTModelSavingProgram.setup_run] at cost
  dsimp only [Bill.val,Bill.work] at cost
  rw [seedArgs_run] at cost
  dsimp only [Bill.val,Bill.work] at cost
  rw [suffixArgs_run] at cost
  dsimp only [Bill.val,Bill.work] at cost
  let rs:=(run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val
  let u:=(Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
    (k%UniformFixedNetwork.m,(rs,((k,I),v)))).val
  have shape:=DFTModelSavingShape.stream_preserves UniformBatching.width
    (k%UniformFixedNetwork.m) rs ((k,I),v) h
  have same : u=((k,I),u.2) := Prod.ext shape.1 rfl
  change (Code.run DFTModelSavingProgram.large h ((k,I),v)).work=
    17+((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).work+10)+
    (Code.run (DFTModelSavingRecords.stream UniformBatching.width) h
      (k%UniformFixedNetwork.m,(rs,((k,I),v)))).work+9+
    (run DFTModelSavingBinarySuffix.program
      (k/UniformFixedNetwork.m*UniformFixedNetwork.m,u)).work+12 at cost
  rw [same] at cost
  have len : u.2.len=v.len := shape.2
  have parity : 2*(u.2.len/2)=u.2.len := by rw [len];exact even
  rw [suffix_work _ k I u.2 parity,len] at cost
  have seed:=DFTModelCacheRecords.seed_work (k/UniformFixedNetwork.m)
  change _≤ seedAllowance at seed
  dsimp only [rs] at cost
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
