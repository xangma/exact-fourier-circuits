import DFTModelGlobalKernelAssemblyMove

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean
open scoped BigOperators
noncomputable section
namespace GP
export DFTModelGlobalSectorPreparation (Sector)
end GP
abbrev SectorInput := p sc (p w (p w (p (Ty.a GP.Sector) (Ty.a Tagged))))
abbrev SectorCell := p SectorInput w

def sectorTape : Prog false SectorInput (Ty.a GP.Sector) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def sectorAt : Prog false SectorCell GP.Sector :=
 .comp (.fork (.comp (.atom .fst) sectorTape) (.atom .snd)) (.atom .look)
def childArgument : Prog false SectorCell (DFTModelSectorTranspose.RawInput Tagged) :=
 .fork (.fork (.comp sectorAt (.atom .fst)) (.comp (.atom .fst) (.atom .fst)))
  (.fork
   (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
    (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
      (.comp sectorAt (.comp (.atom .snd) (.atom .snd)))))
   (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))))
/-- One invocation of the actual closed saving program for this generated sector. -/
def sectorCell : Prog false SectorCell (Ty.a Tagged) :=
 .comp childArgument (.comp DFTModelSectorTranspose.saving (.atom .snd))
def sectors : Prog false SectorInput (Ty.a (Ty.a Tagged)) :=
 .tab (.comp sectorTape (.atom .len)) sectorCell

def sectorArgs (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) (j:ℕ) :
 (DFTModelSectorTranspose.RawInput Tagged).T :=
 let s:=ss.look j GP.Sector.blank
 ((s.1,I),((W,(V,s.2.2)),v))
def patches (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) : Tape (Tape Tagged.T) :=
 Tape.tab ss.len (fun j=>(run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).val.2)

theorem childArgument_run (I:ℂ) (W V j:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 run childArgument ((I,(W,(V,(ss,v)))),j)=⟨sectorArgs I W V ss v j,61,0,True⟩ := by
 simp [childArgument,sectorAt,sectorTape,sectorArgs,run,Code.run,Atom.run,
  Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] DFTModelSectorTranspose.saving childArgument

theorem sectorCell_run (I:ℂ) (W V j:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 run sectorCell ((I,(W,(V,(ss,v)))),j)=
 ((run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).pass
  (fun z=>Bill.one z.2)).pay 63 0 := by
 rw [sectorCell,DFTModelSectorMaterialization.comp_run,childArgument_run]
 simp [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Nat.add_comm,Nat.add_left_comm]
 omega

theorem sectors_run (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 run sectors (I,(W,(V,(ss,v))))=
 (Bill.tab ss.len (Ty.a Tagged).blank (fun j=>run sectorCell ((I,(W,(V,(ss,v)))),j))).pay 10 ss.len := by
 rw [sectors,DFTModelSectorMap.tab_run]
 simp [sectorTape,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
  max_comm,Nat.add_comm]
 omega

attribute [local irreducible] sectorCell sectors

theorem sectors_value (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 (run sectors (I,(W,(V,(ss,v))))).val=patches I W V ss v := by
 rw [sectors_run]
 change (Bill.tab _ _ _).val=_
 rw [ModelEquivalenceInterpreter.tab_value]
 exact congrArg (Tape.tab ss.len) (funext (fun j=>congrArg Bill.val (sectorCell_run I W V j ss v)))

theorem sectors_work (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 (run sectors (I,(W,(V,(ss,v))))).work=12+68*ss.len+
   ∑j∈Finset.range ss.len,(run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).work := by
 rw [sectors_run]
 change (Bill.tab _ _ _).work+10=_
 rw [ModelEquivalenceInterpreter.tab_work]
 have h:(fun j=>(run sectorCell ((I,(W,(V,(ss,v)))),j)).work)=
   fun j=>(run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).work+64 := by
  funext j;rw [sectorCell_run];rfl
 rw [h,Finset.sum_add_distrib]
 simp
 omega

theorem sectors_valid (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 (run sectors (I,(W,(V,(ss,v))))).valid := by
 rw [sectors_run]
 apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
 intro j _
 rw [sectorCell_run]
 exact ⟨DFTModelSectorTranspose.saving_valid _ _ _ _ _ _,trivial⟩

theorem patches_boolean (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T)
 (before:Boolean v) (j:ℕ) : Boolean ((patches I W V ss v).look j (Tape.empty Tagged.T)) := by
 by_cases h:j<ss.len
 · rw [patches]
   simp only [Tape.look,Tape.tab,h,↓reduceDIte]
   dsimp only [sectorArgs]
   rw [DFTModelSectorTranspose.saving_value]
   exact DFTModelSavingClosedBoolean.program_boolean _ _ _
    (DFTModelSectorTranspose.gathered_boolean _ _ _ _ _ before)
 · simp [patches,Tape.look,Tape.tab,h]
   intro i hi
   change i<0 at hi
   omega

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly
