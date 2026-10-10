import DFTModelGlobalSectorPreparationAxis
import DFTModelCRTInverse

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Axes := Ty.a Axis
abbrev Node := p w Axes
abbrev Sector := Block
abbrev Address := Digit
abbrev Tables := PreparedAxis
abbrev Expansion := p PreparedAxis Tables
abbrev ExpansionCell := p Expansion w
abbrev Output := p w (p (Ty.a w) (p (Ty.a w) (Ty.a Sector)))

def tailVolume : Prog false Expansion w := .comp (.atom .snd) (.atom .fst)
def firstRadix : Prog false Expansion w := .comp (.atom .fst) (.atom .fst)
def tailSectors : Prog false Expansion (Ty.a Sector) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def tailAddresses : Prog false Expansion (Ty.a Address) :=
 .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def firstBlocks : Prog false Expansion (Ty.a Block) :=
 .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def firstDigits : Prog false Expansion (Ty.a Digit) :=
 .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def sectorTailLength : Prog false ExpansionCell w := .comp (.atom .fst) (.comp tailSectors (.atom .len))
def addressTailLength : Prog false ExpansionCell w := .comp (.atom .fst) (.comp tailAddresses (.atom .len))
def firstBlock : Prog false ExpansionCell Block :=
 .comp (.fork (.comp (.atom .fst) firstBlocks)
   (nat .div (.atom .snd) sectorTailLength)) (.atom .look)
def lastSector : Prog false ExpansionCell Sector :=
 .comp (.fork (.comp (.atom .fst) tailSectors)
   (nat .mod (.atom .snd) sectorTailLength)) (.atom .look)
def firstDigit : Prog false ExpansionCell Digit :=
 .comp (.fork (.comp (.atom .fst) firstDigits)
   (nat .div (.atom .snd) addressTailLength)) (.atom .look)
def lastAddress : Prog false ExpansionCell Address :=
 .comp (.fork (.comp (.atom .fst) tailAddresses)
   (nat .mod (.atom .snd) addressTailLength)) (.atom .look)
def sectorCell : Prog false ExpansionCell Sector :=
 .fork (nat .add (.comp firstBlock (.atom .fst)) (.comp lastSector (.atom .fst)))
   (.fork
     (nat .mul (.comp firstBlock (.comp (.atom .snd) (.atom .fst)))
       (.comp lastSector (.comp (.atom .snd) (.atom .fst))))
     (nat .add
       (nat .mul (.comp firstBlock (.comp (.atom .snd) (.atom .snd)))
         (.comp (.atom .fst) tailVolume))
       (nat .mul (.comp firstBlock (.comp (.atom .snd) (.atom .fst)))
         (.comp lastSector (.comp (.atom .snd) (.atom .snd))))))
def addressCell : Prog false ExpansionCell Address :=
 .fork
   (nat .mul (.comp firstDigit (.atom .fst)) (.comp lastAddress (.atom .fst)))
   (.fork
     (nat .add
       (nat .mul (.comp firstDigit (.comp (.atom .snd) (.atom .fst)))
         (.comp (.atom .fst) tailVolume))
       (nat .mul (.comp firstDigit (.atom .fst))
         (.comp lastAddress (.comp (.atom .snd) (.atom .fst)))))
     (.fork
       (nat .add
         (nat .mul (.comp firstDigit (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
           (.comp lastAddress (.atom .fst)))
         (.comp lastAddress (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))))
       (nat .add
         (nat .mul (.comp firstDigit (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
           (.comp (.atom .fst) tailVolume))
         (.comp lastAddress (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))))
def sectorLength : Prog false Expansion w :=
 nat .mul (.comp firstBlocks (.atom .len)) (.comp tailSectors (.atom .len))
def addressLength : Prog false Expansion w :=
 nat .mul firstRadix (.comp tailAddresses (.atom .len))
def expand : Prog false Expansion Tables :=
 .fork (nat .mul firstRadix tailVolume)
   (.fork (.tab sectorLength sectorCell) (.tab addressLength addressCell))

def current : Prog false Node Axis := .comp (.fork (.atom .snd) (.atom .fst)) (.atom .look)
def next : Prog false Node Node :=
 .fork (nat .add (.atom .fst) (.atom (.lit 1))) (.atom .snd)
def base : Prog false Node Tables :=
 .fork (.atom (.lit 1))
  (.fork
    (.tab (.atom (.lit 1)) (.fork (.atom (.lit 0)) (.fork (.atom (.lit 1)) (.atom (.lit 0)))))
    (.tab (.atom (.lit 1)) (.fork (.atom (.lit 1)) (.fork (.atom (.lit 0))
      (.fork (.atom (.lit 0)) (.atom (.lit 0)))))))
def body : Code false (some (Node,Tables)) Node Tables :=
 .comp (.fork (.importClosed (.comp current prepareAxis))
   (.comp (.importClosed next) .call)) (.importClosed expand)
def tables : Prog false Axes Tables :=
 .comp (.fork (.atom .len) (.fork (.atom (.lit 0)) (.atom .id))) (.descend base body)

abbrev EmitCell := p Tables w

def emitAddress : Prog false EmitCell Address :=
 .comp (.fork (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))) (.atom .snd)) (.atom .look)
def packedAddress : Prog false EmitCell w :=
 nat .add (.comp emitAddress (.comp (.atom .snd) (.atom .fst)))
   (.comp emitAddress (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def originalAddress : Prog false EmitCell w :=
 .comp emitAddress (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def outputVolume : Prog false Tables w := .atom .fst
def outputCount : Prog false Tables w := .comp (.comp (.atom .snd) (.atom .snd)) (.atom .len)
def packing : Prog false Tables (Ty.a w) :=
 .sow outputVolume outputCount (.fork originalAddress packedAddress)
def unpacking : Prog false Tables (Ty.a w) :=
 .sow outputVolume outputCount (.fork packedAddress originalAddress)
def finalize : Prog false Tables Output :=
 .fork (.atom .fst) (.fork packing (.fork unpacking (.comp (.atom .snd) (.atom .fst))))
/-- One fixed closed program, using one suffix call per physical axis. -/
def program : Prog false Axes Output := .comp tables finalize

abbrev SectorValue := ℕ × (ℕ × ℕ)
abbrev AddressValue := ℕ × (ℕ × (ℕ × ℕ))
abbrev TablesValue := ℕ × (Tape SectorValue × Tape AddressValue)

def sectorCellValue (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) : SectorValue :=
 let l:=x.2.1.look (j/t.2.1.len) (0,(0,0))
 let u:=t.2.1.look (j%t.2.1.len) (0,(0,0))
 (l.1+u.1,(l.2.1*u.2.1,l.2.2*t.1+l.2.1*u.2.2))
def addressCellValue (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) : AddressValue :=
 let l:=x.2.2.look (j/t.2.2.len) (0,(0,(0,0)))
 let u:=t.2.2.look (j%t.2.2.len) (0,(0,(0,0)))
 (l.1*u.1,(l.2.1*t.1+l.1*u.2.1,
   (l.2.2.1*u.1+u.2.2.1,l.2.2.2*t.1+u.2.2.2)))
def expandedValue (x : PreparedAxis.T) (t : Tables.T) : Tables.T :=
 (x.1*t.1,(Tape.tab (x.2.1.len*t.2.1.len) (sectorCellValue x t),
   Tape.tab (x.1*t.2.2.len) (addressCellValue x t)))
def baseValue : Tables.T :=
 (1,(Tape.tab 1 (fun _=>(0,(1,0))),Tape.tab 1 (fun _=>(1,(0,(0,0))))))
def tableValue : ℕ → ℕ → Tape Axis.T → Tables.T
 | 0,_,_ => baseValue
 | k+1,i,axes => expandedValue (preparedAxisValue (axes.look i Axis.blank))
    (tableValue k (i+1) axes)
def addressPair (t : Tables.T) (j : ℕ) : ℕ × ℕ :=
 let u:=t.2.2.look j (0,(0,(0,0)))
 (u.2.1+u.2.2.1,u.2.2.2)
def finalizedValue (t : Tables.T) : Output.T :=
 (t.1,(Tape.sow t.1 t.2.2.len 0 (fun j=>(addressPair t j).swap),
   (Tape.sow t.1 t.2.2.len 0 (addressPair t),t.2.1)))

theorem sectorCell_value (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run sectorCell ((x,t),j)).val=sectorCellValue x t j := by
 simp [sectorCell,firstBlock,lastSector,firstBlocks,tailSectors,sectorTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank,sectorCellValue]

theorem sectorCell_valid (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run sectorCell ((x,t),j)).valid := by
 simp [sectorCell,firstBlock,lastSector,firstBlocks,tailSectors,sectorTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank]

theorem sectorCell_work (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run sectorCell ((x,t),j)).work≤1000 := by
 simp [sectorCell,firstBlock,lastSector,firstBlocks,tailSectors,sectorTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem addressCell_value (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run addressCell ((x,t),j)).val=addressCellValue x t j := by
 simp [addressCell,firstDigit,lastAddress,firstDigits,tailAddresses,addressTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank,addressCellValue]

theorem addressCell_valid (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run addressCell ((x,t),j)).valid := by
 simp [addressCell,firstDigit,lastAddress,firstDigits,tailAddresses,addressTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,
   Bill.word,Ty.blank]

theorem addressCell_work (x : PreparedAxis.T) (t : Tables.T) (j : ℕ) :
 (run addressCell ((x,t),j)).work≤1000 := by
 simp [addressCell,firstDigit,lastAddress,firstDigits,tailAddresses,addressTailLength,
   tailVolume,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] sectorCell addressCell

theorem expand_value (x : PreparedAxis.T) (t : Tables.T) :
 (run expand (x,t)).val=expandedValue x t := by
 simp only [expand,run,Code.run,Bill.pass,Bill.pay,Bill.one]
 simp only [sectorLength,addressLength,firstRadix,tailVolume,firstBlocks,tailSectors,
   tailAddresses,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [ModelEquivalenceInterpreter.tab_value,ModelEquivalenceInterpreter.tab_value]
 have hs:(fun j=>(sectorCell.run () ((x,t),j)).val)=sectorCellValue x t :=
  funext (sectorCell_value x t)
 have ha:(fun j=>(addressCell.run () ((x,t),j)).val)=addressCellValue x t :=
  funext (addressCell_value x t)
 rw [hs,ha]
 rfl

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
