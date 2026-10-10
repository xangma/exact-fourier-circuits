import DFTModelGlobalSectorPreparationRun
import DFTModelGlobalSectorPreparationAxisBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] sectorCell addressCell prepareAxis expand

theorem expand_work_exact (x : PreparedAxis.T) (t : Tables.T) :
 (run expand (x,t)).work=
 (Bill.tab (x.2.1.len*t.2.1.len) Sector.blank (fun j=>run sectorCell ((x,t),j))).work+
 (Bill.tab (x.1*t.2.2.len) Address.blank (fun j=>run addressCell ((x,t),j))).work+43 := by
 simp only [expand,sectorLength,addressLength,firstRadix,firstBlocks,tailSectors,
   tailAddresses,tailVolume,nat,run,Code.run,Atom.run,NOp.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
 norm_num
 omega

theorem expand_work (x : PreparedAxis.T) (t : Tables.T) :
 (run expand (x,t)).work≤1004*(x.2.1.len*t.2.1.len+x.1*t.2.2.len)+47 := by
 rw [expand_work_exact,ModelEquivalenceInterpreter.tab_work,ModelEquivalenceInterpreter.tab_work]
 have hs:(∑j∈Finset.range (x.2.1.len*t.2.1.len),(run sectorCell ((x,t),j)).work)≤
     1000*(x.2.1.len*t.2.1.len) := by
  calc
   _≤∑_j∈Finset.range (x.2.1.len*t.2.1.len),1000 :=
    Finset.sum_le_sum (fun j _=>sectorCell_work x t j)
   _=_ := by simp [Nat.mul_comm]
 have ha:(∑j∈Finset.range (x.1*t.2.2.len),(run addressCell ((x,t),j)).work)≤
     1000*(x.1*t.2.2.len) := by
  calc
   _≤∑_j∈Finset.range (x.1*t.2.2.len),1000 :=
    Finset.sum_le_sum (fun j _=>addressCell_work x t j)
   _=_ := by simp [Nat.mul_comm]
 omega

theorem expand_valid (x : PreparedAxis.T) (t : Tables.T) : (run expand (x,t)).valid := by
 have hs:(Bill.tab (x.2.1.len*t.2.1.len) Sector.blank (fun j=>run sectorCell ((x,t),j))).valid :=
  (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>sectorCell_valid x t j)
 have ha:(Bill.tab (x.1*t.2.2.len) Address.blank (fun j=>run addressCell ((x,t),j))).valid :=
  (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>addressCell_valid x t j)
 simpa [expand,sectorLength,addressLength,firstRadix,firstBlocks,tailSectors,
   tailAddresses,tailVolume,nat,run,Code.run,Atom.run,NOp.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word] using And.intro hs ha

theorem emitPacking_run (t : Tables.T) (j : ℕ) :
 Code.run (.fork originalAddress packedAddress) () (t,j)=
   ⟨(addressPair t j).swap,47,(addressPair t j).1,True⟩ := by
 simp [originalAddress,packedAddress,emitAddress,nat,Code.run,Atom.run,
   NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,addressPair,Ty.blank]

theorem emitUnpacking_run (t : Tables.T) (j : ℕ) :
 Code.run (.fork packedAddress originalAddress) () (t,j)=
   ⟨addressPair t j,47,(addressPair t j).1,True⟩ := by
 simp [originalAddress,packedAddress,emitAddress,nat,Code.run,Atom.run,
   NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,addressPair,Ty.blank]

theorem packing_work (t : Tables.T) : (run packing t).work=t.1+49*t.2.2.len+9 := by
 simp only [packing,outputVolume,outputCount,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [DFTModelCRT.sow_work]
 have hh:(fun j=>(Code.run (.fork originalAddress packedAddress) () (t,j)).work)=fun _=>47 :=
  funext (fun j=>congrArg Bill.work (emitPacking_run t j))
 simp only [Code.run,Bill.pass,Bill.one] at hh
 rw [hh]
 simp [Bill.word]
 omega

theorem unpacking_work (t : Tables.T) : (run unpacking t).work=t.1+49*t.2.2.len+9 := by
 simp only [unpacking,outputVolume,outputCount,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 rw [DFTModelCRT.sow_work]
 have hh:(fun j=>(Code.run (.fork packedAddress originalAddress) () (t,j)).work)=fun _=>47 :=
  funext (fun j=>congrArg Bill.work (emitUnpacking_run t j))
 simp only [Code.run,Bill.pass,Bill.one] at hh
 rw [hh]
 simp [Bill.word]
 omega


theorem packing_valid (t : Tables.T) : (run packing t).valid := by
 simp only [packing,outputVolume,outputCount,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,true_and]
 apply (DFTModelCRT.sow_valid _ _ _ _).2
 intro j _
 have h:=congrArg Bill.valid (emitPacking_run t j)
 simpa only [Code.run,Bill.pass,Bill.one] using of_eq_true h

theorem unpacking_valid (t : Tables.T) : (run unpacking t).valid := by
 simp only [unpacking,outputVolume,outputCount,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,true_and]
 apply (DFTModelCRT.sow_valid _ _ _ _).2
 intro j _
 have h:=congrArg Bill.valid (emitUnpacking_run t j)
 simpa only [Code.run,Bill.pass,Bill.one] using of_eq_true h

theorem base_work (i : ℕ) (axes : Tape Axis.T) : (run base (i,axes)).work=31 := by
 simp [base,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay,
   ModelEquivalenceInterpreter.tab_work]

theorem base_valid (i : ℕ) (axes : Tape Axis.T) : (run base (i,axes)).valid := by
 simp [base,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay,
   ModelEquivalenceInterpreter.tab_valid]

theorem body_work (h : Handler (some (Node,Tables))) (i : ℕ) (axes : Tape Axis.T) :
 (body.run h (i,axes)).work=(run prepareAxis (axes.look i Axis.blank)).work+
   (h (i+1,axes)).work+
   (run expand ((run prepareAxis (axes.look i Axis.blank)).val,(h (i+1,axes)).val)).work+20 := by
 simp only [body,current,next,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 norm_num
 omega

theorem body_valid (h : Handler (some (Node,Tables))) (i : ℕ) (axes : Tape Axis.T)
 (valid:(h (i+1,axes)).valid) : (body.run h (i,axes)).valid := by
 have hp:=prepareAxis_valid (axes.look i Axis.blank)
 have he:=expand_valid (run prepareAxis (axes.look i Axis.blank)).val (h (i+1,axes)).val
 dsimp only [run] at hp he
 simpa [body,current,next,nat,Code.run,Atom.run,NOp.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word] using And.intro (And.intro hp valid) he

attribute [local irreducible] body base

theorem depth_valid (k i : ℕ) (axes : Tape Axis.T) :
 (depthRun (run base) body.run k (i,axes)).valid := by
 induction k generalizing i with
 | zero=>exact base_valid i axes
 | succ k ih=>exact body_valid _ i axes (ih (i+1))

theorem tables_valid (axes : Tape Axis.T) : (run tables axes).valid := by
 simpa [tables,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
   using depth_valid axes.len 0 axes

theorem finalize_work (t : Tables.T) :
 (run finalize t).work=2*t.1+98*t.2.2.len+25 := by
 change 1+((run packing t).work+((run unpacking t).work+3+1)+1)+1=_
 rw [packing_work,unpacking_work]
 omega

theorem finalize_valid (t : Tables.T) : (run finalize t).valid := by
 have hp:=packing_valid t
 have hu:=unpacking_valid t
 dsimp only [run] at hp hu
 simpa [finalize,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
   using And.intro hp hu

theorem program_valid (axes : Tape Axis.T) : (run program axes).valid :=
 And.intro (tables_valid axes) (finalize_valid _)

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
