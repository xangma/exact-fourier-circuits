import DFTModelSectorMapFinalBounds
import DFTModelSectorMapFinalSource
import DFTModelSectorMapCarry
import DFTModelSectorMapParameters

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] power sparse DFTModelSectorMapBits.pack DFTModelSectorMapBits.highTable
 DFTModelSectorMapParameters.program DFTModelSectorMapCarry.program finalMap


abbrev S1 := p Input w
abbrev S2 := p S1 (Ty.a w)
abbrev S3 := p S2 (Ty.a w)
abbrev S4 := p S3 (Ty.a w)
abbrev S5 := p S4 (Ty.a w)
abbrev S6 := p S5 (Ty.a w)

def bind {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) : Prog false a c :=
 .comp (.fork (.atom .id) f) g

def powers : Prog false w (Ty.a w) := .tab (binary .add (.atom .id) (.atom (.lit 1)))
 (.comp (.atom .snd) power)
def startBits : Prog false Input w := .comp volume DFTModelSectorMapParameters.program
def startMarks : Prog false S1 (Ty.a w) := .comp (.atom .fst) sparse
def startPack : Prog false S2 (Ty.a w) := .comp
 (.fork (.comp (.atom .fst) (.atom .snd))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) volume)) (.atom .snd))) DFTModelSectorMapBits.pack
def startHighs : Prog false S3 (Ty.a w) := .comp (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))) DFTModelSectorMapBits.highTable
def startPowers : Prog false S4 (Ty.a w) := .comp
 (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))) powers
def startCarry : Prog false S5 (Ty.a w) := .comp
 (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))))
  (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))))))
 DFTModelSectorMapCarry.program

def shapeRaw : Prog false S6 Input := .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst)))))
def shapeBits : Prog false S6 w := .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))))
def shapeMarks : Prog false S6 (Ty.a w) := .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))))
def shapePacked : Prog false S6 (Ty.a w) := .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .snd)))
def shapeHighs : Prog false S6 (Ty.a w) := .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def shapePowers : Prog false S6 (Ty.a w) := .comp (.atom .fst) (.atom .snd)
def shape : Prog false S6 Tables := .fork shapeRaw
 (.fork shapeBits (.fork shapeMarks (.fork shapePacked (.fork shapeHighs (.fork shapePowers (.atom .snd))))))
def finish : Prog false S6 (Ty.a Cell) := .comp shape finalMap

def program : Prog false Input (Ty.a Cell) :=
 bind startBits (bind startMarks (bind startPack (bind startHighs (bind startPowers (bind startCarry finish)))))

def marks (V : ℕ) (d : Tape (ℕ×ℕ)) := (run sparse (V,d)).val
def packedTable (V : ℕ) (d : Tape (ℕ×ℕ)) :=
 (run DFTModelSectorMapBits.pack (DFTModelSectorMapParameters.blockBits V,(V,marks V d))).val
def highTable (V : ℕ) := (run DFTModelSectorMapBits.highTable (DFTModelSectorMapParameters.blockBits V)).val
def powerTable (V : ℕ) := (run powers (DFTModelSectorMapParameters.blockBits V)).val
def carryTable (V : ℕ) (d : Tape (ℕ×ℕ)) :=
 (run DFTModelSectorMapCarry.program (DFTModelSectorMapParameters.blockBits V,(V,d))).val


theorem tab_value {a b : Ty} (n : Prog false a w) (f : Prog false (p a w) b) (x : a.T) :
 (run (.tab n f) x).val=Tape.tab (run n x).val (fun i=>(run f (x,i)).val) :=
 ModelEquivalenceInterpreter.tab_value _ _ _

theorem powers_value (b : ℕ) : (run powers b).val=Tape.tab (b+1) (fun i=>2^i) := by
 rw [powers,tab_value]
 have count:(run (binary .add (.atom .id) (.atom (.lit 1))) b).val=b+1:=rfl
 rw [count]
 congr 1;funext i
 change (run power i).val=2^i
 exact power_value i

theorem powers_lookup (b k : ℕ) (hk:k≤b) : (run powers b).val.look k 0=2^k := by
 rw [powers_value]
 simp [Tape.look,Tape.tab,show k<b+1 by omega]

theorem startBits_run (V : ℕ) (d : Tape (ℕ×ℕ)) :
 run startBits (V,d)=(run DFTModelSectorMapParameters.program V).pay 2 0 := by
 simp only [startBits,volume,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem startMarks_run (V b : ℕ) (d : Tape (ℕ×ℕ)) :
 run startMarks ((V,d),b)=(run sparse (V,d)).pay 2 0 := by
 simp only [startMarks,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem startPack_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m : Tape ℕ) :
 run startPack (((V,d),b),m)=(run DFTModelSectorMapBits.pack (b,(V,m))).pay 12 0 := by
 simp only [startPack,volume,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem startHighs_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk : Tape ℕ) :
 run startHighs ((((V,d),b),m),pk)=(run DFTModelSectorMapBits.highTable b).pay 6 0 := by
 simp only [startHighs,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem startPowers_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi : Tape ℕ) :
 run startPowers (((((V,d),b),m),pk),hi)=(run powers b).pay 8 0 := by
 simp only [startPowers,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem startCarry_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw : Tape ℕ) :
 run startCarry ((((((V,d),b),m),pk),hi),pw)=(run DFTModelSectorMapCarry.program (b,(V,d))).pay 20 0 := by
 simp only [startCarry,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
 congr 1; omega

theorem shape_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 run shape (((((((V,d),b),m),pk),hi),pw),ca)=⟨tables V d b m pk hi pw ca,53,0,True⟩ := by
 simp [shape,shapeRaw,shapeBits,shapeMarks,shapePacked,shapeHighs,shapePowers,tables,
 run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] startBits startMarks startPack startHighs startPowers startCarry shape

theorem finish_run (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 run finish (((((((V,d),b),m),pk),hi),pw),ca)=
 (run finalMap (tables V d b m pk hi pw ca)).pay 54 0 := by
 rw [finish,run,Code.run,←run,shape_run]
 simp only [Bill.pass,Bill.pay,run,true_and,max_zero,zero_max]
 congr 1; omega

attribute [local irreducible] finish

theorem program_value (V : ℕ) (d : Tape (ℕ×ℕ)) :
 (run program (V,d)).val=
 Tape.tab V (fun j=>mapped d j (chosen (DFTModelSectorMapParameters.blockBits V) j
  (marks V d) (packedTable V d) (highTable V) (powerTable V) (carryTable V d))) := by
 unfold program
 repeat rw [bind,bind_value]
 rw [startBits_run]
 dsimp only [Bill.pay]
 rw [DFTModelSectorMapParameters.program_value]
 rw [startMarks_run]
 dsimp only [Bill.pay]
 rw [startPack_run]
 dsimp only [Bill.pay]
 rw [startHighs_run]
 dsimp only [Bill.pay]
 rw [startPowers_run]
 dsimp only [Bill.pay]
 rw [startCarry_run]
 dsimp only [Bill.pay]
 rw [finish_run]
 dsimp only [Bill.pay]
 exact finalMap_value _ _ _ _ _ _ _ _

end
end ExactFourierCircuits.DFTModelSectorMap
