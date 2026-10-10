import DFTModelGlobalSectorPreparationSource
import DFTModelGlobalSectorPreparationWork

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

abbrev Directory := p w (Ty.a (p w w))
def outputSectors : Prog false Output (Ty.a Sector) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def directoryCell : Prog false (p Output w) (p w w) :=
 .comp (.fork (.comp (.atom .fst) outputSectors) (.atom .snd))
   (.comp (.atom .look) (.fork (.comp (.atom .snd) (.atom .snd))
     (.comp (.atom .snd) (.atom .fst))))
def directory : Prog false Output Directory :=
 .fork (.atom .fst) (.tab (.comp outputSectors (.atom .len)) directoryCell)
/-- Run the global producer once, retaining its tables and its charged map directory. -/
def withDirectory : Prog false Axes (p Output Directory) :=
 .comp program (.fork (.atom .id) directory)

theorem directoryCell_run (t : Output.T) (j : ℕ) :
 run directoryCell (t,j)=
   ⟨let s:=t.2.2.2.look j (0,(0,0));(s.2.2,s.2.1),19,0,True⟩ := by
 simp [directoryCell,outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Ty.blank]

theorem directory_value (t : Output.T) :
 (run directory t).val=(t.1,Tape.tab t.2.2.2.len
   (fun j=>let s:=t.2.2.2.look j (0,(0,0));(s.2.2,s.2.1))) := by
 simp only [directory,outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [ModelEquivalenceInterpreter.tab_value]
 have hh:(fun j=>(Code.run directoryCell () (t,j)).val)=
   fun j=>let s:=t.2.2.2.look j (0,(0,0));(s.2.2,s.2.1) := by
   funext j;exact congrArg Bill.val (directoryCell_run t j)
 rw [hh]

theorem directory_valid (t : Output.T) : (run directory t).valid := by
 simp only [directory,outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,true_and,and_true]
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro j _
 exact of_eq_true (congrArg Bill.valid (directoryCell_run t j))

theorem directory_work (t : Output.T) : (run directory t).work=23*t.2.2.2.len+12 := by
 simp only [directory,outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [ModelEquivalenceInterpreter.tab_work]
 have hh:(fun j=>(Code.run directoryCell () (t,j)).work)=fun _=>19 := by
   funext j;exact congrArg Bill.work (directoryCell_run t j)
 rw [hh]
 simp
 omega

theorem directory_peak (t : Output.T) : (run directory t).peak=t.2.2.2.len := by
 simp only [directory,outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [ModelEquivalenceInterpreter.tab_peak]
 have hh:(fun j=>(Code.run directoryCell () (t,j)).peak)=fun _=>0 := by
   funext j;exact congrArg Bill.peak (directoryCell_run t j)
 rw [hh]
 simp

theorem directory_list (V : ℕ) (xs : List UniformSectorPacking.BlockState)
 (packing unpacking : Tape ℕ) :
 (run directory (V,(packing,(unpacking,ofList (xs.map encodeSector))))).val=
   (V,ofList (xs.map (fun s=>(s.start,s.width)))) := by
 rw [directory_value]
 apply Prod.ext
 · rfl
 apply tape_ext _ _ (0,0) (by simp [Tape.tab,ofList])
 intro j hj
 have h:j<xs.length:=by simpa [Tape.tab,ofList] using hj
 simp [Tape.look,Tape.tab,ofList,h,encodeSector]

theorem withDirectory_value (as : List UniformSectorPacking.Axis) :
 let u:=(run withDirectory (ofList (as.map encodeAxis))).val
 u.1=(run program (ofList (as.map encodeAxis))).val ∧
 u.2=((UniformSectorPacking.radices as).prod,
   ofList ((UniformSectorPacking.sectorStates as).map (fun s=>(s.start,s.width)))) := by
 have h:=program_native as
 dsimp only at h
 change _=_ ∧ (run directory (run program (ofList (as.map encodeAxis))).val).val=_
 refine ⟨rfl,?_⟩
 have hu:(run program (ofList (as.map encodeAxis))).val=
   ((UniformSectorPacking.radices as).prod,
     ((run program (ofList (as.map encodeAxis))).val.2.1,
       ((run program (ofList (as.map encodeAxis))).val.2.2.1,
         ofList ((UniformSectorPacking.sectorStates as).map encodeSector)))) := by
   exact Prod.ext h.1 (Prod.ext rfl (Prod.ext rfl h.2.2.2.2.2))
 rw [hu]
 exact directory_list _ _ _ _

theorem withDirectory_valid (axes : Tape Axis.T) : (run withDirectory axes).valid :=
 ⟨program_valid axes,⟨trivial,directory_valid _,trivial⟩⟩

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
