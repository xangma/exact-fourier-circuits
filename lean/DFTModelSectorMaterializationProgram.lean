import DFTModelSectorMapPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMaterialization
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSectorMap.program DFTModelSectorMap.reader

abbrev Input (t : Ty) := p w (DFTModelSectorMap.ReadContext t)
def count (t : Ty) : Prog false (Input t) w :=
 binary .mul (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def cell (t : Ty) : Prog false (p (Input t) w) t :=
 .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (DFTModelSectorMap.reader t)
/-- The only whole-bank allocation: one tab of all W*V complete elements. -/
def program (t : Ty) : Prog false (Input t) (Ty.a t) := .tab (count t) (cell t)

theorem count_run (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (count t) (W,(V,(m,(patches,old))))=⟨W*V,7,W*V,True⟩ := by
 simp [count,binary,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem cell_run (t : Ty) (W V j : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (cell t) ((W,(V,(m,(patches,old)))),j)=
 (run (DFTModelSectorMap.reader t) ((V,(m,(patches,old))),j)).pay 6 0 := by
 simp [cell,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
 omega

attribute [local irreducible] cell

theorem program_run (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (program t) (W,(V,(m,(patches,old))))=
 (Bill.tab (W*V) t.blank (fun j=>run (cell t) ((W,(V,(m,(patches,old)))),j))).pay 8 (W*V) := by
 rw [program,DFTModelSectorMap.tab_run,count_run]
 simp only [Bill.pass,Bill.pay,true_and]
 congr 1 <;> omega

attribute [local irreducible] program

theorem program_value (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (program t) (W,(V,(m,(patches,old))))).val=
 Tape.tab (W*V) (fun j=>DFTModelSectorMap.overlay V j m patches old t.blank) := by
 rw [program_run]
 change (Bill.tab _ _ _).val=_
 rw [ModelEquivalenceInterpreter.tab_value]
 congr 1;funext j
 rw [cell_run]
 exact DFTModelSectorMap.reader_value t V j m patches old

theorem program_length (t : Ty) (W V : ℕ) (m : Tape DFTModelSectorMap.Cell.T)
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 (run (program t) (W,(V,(m,(patches,old))))).val.len=W*V := by
 rw [program_value];rfl

/-- The original raw directory and child patches are retained explicitly. -/
abbrev JoinedInput (t : Ty) := p w (p DFTModelSectorMap.Input (p (Ty.a (Ty.a t)) (Ty.a t)))
def prepareMap (t : Ty) : Prog false (JoinedInput t) (Ty.a DFTModelSectorMap.Cell) :=
 .comp (.atom .snd) (.comp (.atom .fst) DFTModelSectorMap.program)
def shape (t : Ty) : Prog false (p (JoinedInput t) (Ty.a DFTModelSectorMap.Cell)) (Input t) :=
 .fork (.comp (.atom .fst) (.atom .fst))
  (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))))
   (.fork (.atom .snd) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))))
def joinedTape (t : Ty) : Prog false (JoinedInput t) (Ty.a t) :=
 .comp (.fork (.atom .id) (prepareMap t)) (.comp (shape t) (program t))
def joined (t : Ty) : Prog false (JoinedInput t) (p (JoinedInput t) (Ty.a t)) :=
 .fork (.atom .id) (joinedTape t)

theorem prepareMap_run (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (prepareMap t) (W,((V,d),(patches,old)))=(run DFTModelSectorMap.program (V,d)).pay 4 0 := by
 simp only [prepareMap,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1;omega

theorem shape_run (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) (m : Tape DFTModelSectorMap.Cell.T) :
 run (shape t) ((W,((V,d),(patches,old))),m)=⟨(W,(V,(m,(patches,old)))),19,0,True⟩ := by
 simp [shape,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem bind_run {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) (x : a.T) :
 run (.comp (.fork (.atom .id) f) g) x=
 ((run f x).pass (fun y=>run g (x,y))).pay 3 0 := by
 simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,and_true,max_zero,zero_max]
 congr 1;omega

theorem comp_run {a b c : Ty} (f : Prog false a b) (g : Prog false b c) (x : a.T) :
 run (.comp f g) x=((run f x).pass (fun y=>run g y)).pay 1 0 :=rfl

attribute [local irreducible] prepareMap shape

theorem joinedTape_run (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (joinedTape t) (W,((V,d),(patches,old)))=
 ((run DFTModelSectorMap.program (V,d)).pass (fun m=>run (program t) (W,(V,(m,(patches,old)))))).pay 27 0 := by
 rw [joinedTape,bind_run,prepareMap_run]
 dsimp only [Bill.pay,Bill.pass]
 rw [comp_run,shape_run]
 simp only [Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1;omega

attribute [local irreducible] joinedTape

theorem joined_run (t : Ty) (W V : ℕ) (d : Tape (ℕ×ℕ))
 (patches : Tape (Tape t.T)) (old : Tape t.T) :
 run (joined t) (W,((V,d),(patches,old)))=
 ((run (joinedTape t) (W,((V,d),(patches,old)))).pass
  (fun bank=>Bill.one ((W,((V,d),(patches,old))),bank))).pay 1 0 := by
 simp only [joined,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,and_true,max_zero,zero_max]
 congr 1;omega

end
end ExactFourierCircuits.DFTModelSectorMaterialization
