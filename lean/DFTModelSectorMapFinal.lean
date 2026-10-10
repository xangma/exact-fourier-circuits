import DFTModelSectorMapSparseSource
import DFTModelSectorMapBitsSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSectorMap
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

/-- Actual prepared tables, retained with the original raw directory. -/
abbrev Tables := p Input (p w (p (Ty.a w) (p (Ty.a w) (p (Ty.a w) (p (Ty.a w) (Ty.a w))))))
abbrev FinalInput := p Tables w

def finalV : Prog false FinalInput w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def finalDirectory : Prog false FinalInput (Ty.a Row) := .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def finalB : Prog false FinalInput w := .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def finalMarkers : Prog false FinalInput (Ty.a w) := .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def finalPacked : Prog false FinalInput (Ty.a w) := .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def finalHighs : Prog false FinalInput (Ty.a w) := .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))))
def finalPowers : Prog false FinalInput (Ty.a w) := .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))))
def finalCarry : Prog false FinalInput (Ty.a w) := .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))))
def chunk : Prog false FinalInput w := binary .div (.atom .snd) finalB
def withinChunk : Prog false FinalInput w := binary .mod (.atom .snd) finalB
def chunkStart : Prog false FinalInput w := binary .mul chunk finalB
def prefixPower : Prog false FinalInput w := .comp (.fork finalPowers (binary .add withinChunk (.atom (.lit 1)))) (.atom .look)
def prefixBits : Prog false FinalInput w := binary .mod (.comp (.fork finalPacked chunk) (.atom .look)) prefixPower
def nearest : Prog false FinalInput w := .comp (.fork finalHighs prefixBits) (.atom .look)
def candidate : Prog false FinalInput w := .ifz nearest
 (.comp (.fork finalCarry chunk) (.atom .look))
 (.comp (.fork finalMarkers (binary .add chunkStart (binary .sub nearest (.atom (.lit 1))))) (.atom .look))
abbrev BoundFinal := p FinalInput w
def selectedRow : Prog false BoundFinal Row := .comp (.fork (.comp (.atom .fst) finalDirectory)
 (binary .sub (.atom .snd) (.atom (.lit 1)))) (.atom .look)
def selectedStart : Prog false BoundFinal w := .comp selectedRow (.atom .fst)
def selectedWidth : Prog false BoundFinal w := .comp selectedRow (.atom .snd)
def selectedJ : Prog false BoundFinal w := .comp (.atom .fst) (.atom .snd)
def selectedCell : Prog false BoundFinal Cell := .fork (.atom .snd)
 (.fork selectedWidth (binary .sub selectedJ selectedStart))
def blankCell : Prog false BoundFinal Cell := .fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.atom (.lit 0)))
def checkEnd : Prog false BoundFinal Cell := .ifz
 (binary .lt selectedJ (binary .add selectedStart selectedWidth)) blankCell selectedCell
def checkStart : Prog false BoundFinal Cell := .ifz (binary .lt selectedJ selectedStart) checkEnd blankCell
def checkCandidate : Prog false BoundFinal Cell := .ifz (.atom .snd) blankCell checkStart
def finalCell : Prog false FinalInput Cell := .comp (.fork (.atom .id) candidate) checkCandidate
def finalMap : Prog false Tables (Ty.a Cell) := .tab (.comp (.atom .fst) (.atom .fst)) finalCell

def chosen (b j : ℕ) (m pk hi pw ca : Tape ℕ) : ℕ :=
 let h:=hi.look (pk.look (j/b) 0 % pw.look (j%b+1) 0) 0
 if h=0 then ca.look (j/b) 0 else m.look ((j/b)*b+(h-1)) 0

def mapped (d : Tape (ℕ×ℕ)) (j c : ℕ) : Cell.T :=
 let st:=d.look (c-1) (0,0)
 if c=0 then (0,(0,0)) else if j<st.1 then (0,(0,0)) else
 if j<st.1+st.2 then (c,(st.2,j-st.1)) else (0,(0,0))

def tables (V : ℕ) (d : Tape (ℕ×ℕ)) (b : ℕ) (m pk hi pw ca : Tape ℕ) : Tables.T :=
 ((V,d),(b,(m,(pk,(hi,(pw,ca))))))

theorem candidate_value (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run candidate (tables V d b m pk hi pw ca,j)).val=chosen b j m pk hi pw ca := by
 simp only [candidate,nearest,prefixBits,prefixPower,chunk,withinChunk,chunkStart,
 finalMarkers,finalPacked,finalHighs,finalPowers,finalCarry,finalB,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases h:hi.look (pk.look (j/b) 0 % pw.look (j%b+1) 0) 0=0 <;> simp [chosen,Ty.blank,h]

theorem checkCandidate_value (V j b c : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run checkCandidate ((tables V d b m pk hi pw ca,j),c)).val=mapped d j c := by
 simp only [checkCandidate,checkStart,checkEnd,selectedCell,selectedJ,
 blankCell,selectedStart,selectedWidth,selectedRow,finalDirectory,tables,
 binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 by_cases hc:c=0 <;> by_cases hs:j<(d.look (c-1) (0,0)).1 <;>
 by_cases he:j<(d.look (c-1) (0,0)).1+(d.look (c-1) (0,0)).2 <;>
 simp [mapped,Ty.blank,Row,Cell,hc,hs,he]

theorem bind_value {a b c : Ty} (f : Prog false a b) (g : Prog false (p a b) c) (x : a.T) :
 (run (.comp (.fork (.atom .id) f) g) x).val=(run g (x,(run f x).val)).val := rfl

attribute [local irreducible] candidate checkCandidate

theorem finalCell_value (V j b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalCell (tables V d b m pk hi pw ca,j)).val=
 mapped d j (chosen b j m pk hi pw ca) := by
 rw [finalCell,bind_value,candidate_value,checkCandidate_value]

attribute [local irreducible] finalCell

theorem finalMap_value (V b : ℕ) (d : Tape (ℕ×ℕ)) (m pk hi pw ca : Tape ℕ) :
 (run finalMap (tables V d b m pk hi pw ca)).val=
 Tape.tab V (fun j=>mapped d j (chosen b j m pk hi pw ca)) := by
 change (Bill.tab V Cell.blank (fun j=>run finalCell (tables V d b m pk hi pw ca,j))).val=_
 rw [ModelEquivalenceInterpreter.tab_value]
 congr 1;funext j;exact finalCell_value _ _ _ _ _ _ _ _ _

end
end ExactFourierCircuits.DFTModelSectorMap
