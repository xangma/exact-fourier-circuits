import DFTModelGlobalSectorPreparationProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] prepareAxis expand base finalize

theorem base_value (i : ℕ) (axes : Tape Axis.T) :
 (run base (i,axes)).val=baseValue := by
 simp only [base,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.word,Bill.one]
 rw [ModelEquivalenceInterpreter.tab_value,ModelEquivalenceInterpreter.tab_value]
 rfl

theorem body_value (h : Handler (some (Node,Tables))) (i : ℕ) (axes : Tape Axis.T) :
 (body.run h (i,axes)).val=
   expandedValue (preparedAxisValue (axes.look i Axis.blank)) (h (i+1,axes)).val := by
 simp only [body,current,next,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 have hp:=prepareAxis_value (axes.look i Axis.blank)
 dsimp only [run] at hp
 rw [hp]
 have he:=expand_value (preparedAxisValue (axes.look i Axis.blank)) (h (i+1,axes)).val
 dsimp only [run] at he
 rw [he]

attribute [local irreducible] body

theorem depth_value (k i : ℕ) (axes : Tape Axis.T) :
 (depthRun (run base) body.run k (i,axes)).val=tableValue k i axes := by
 induction k generalizing i with
 | zero => exact base_value i axes
 | succ k ih =>
   rw [depthRun]
   simp only [Bill.pay]
   rw [body_value]
   simp only [tableValue]
   rw [ih]

theorem tables_value (axes : Tape Axis.T) :
 (run tables axes).val=tableValue axes.len 0 axes := by
 simp only [tables,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 exact depth_value axes.len 0 axes

theorem finalize_value (t : Tables.T) :
 (run finalize t).val=finalizedValue t := by
 simp only [finalize,packing,unpacking,outputVolume,outputCount,run,Code.run,
   Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [DFTModelCRT.sow_value,DFTModelCRT.sow_value]
 have hp:(fun j=>(Code.run (.fork originalAddress packedAddress) () (t,j)).val)=
     fun j=>(addressPair t j).swap := by
  funext j
  simp [originalAddress,packedAddress,emitAddress,nat,Code.run,Atom.run,
    NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,addressPair,Ty.blank]
 have hu:(fun j=>(Code.run (.fork packedAddress originalAddress) () (t,j)).val)=addressPair t := by
  funext j
  simp [originalAddress,packedAddress,emitAddress,nat,Code.run,Atom.run,
    NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,addressPair,Ty.blank]
 simp only [Code.run,Bill.pass,Bill.one] at hp hu
 simp only [Bill.word]
 rw [hp,hu]
 rfl

theorem program_value (axes : Tape Axis.T) :
 (run program axes).val=finalizedValue (tableValue axes.len 0 axes) := by
 change (run finalize (run tables axes).val).val=_
 rw [tables_value,finalize_value]

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
