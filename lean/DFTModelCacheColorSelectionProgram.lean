import DFTModelCacheColorPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorSelection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row nat)
noncomputable section
abbrev Input := p w (p (Ty.a Row) (Ty.a w))
abbrev Cell := p Input w
abbrev State := p w Row
abbrev Request := p Input w
abbrev Cursor := p Request (p w State)
def rows : Prog false Input (Ty.a Row) := .comp (.atom .snd) (.atom .fst)
def colors : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def count : Prog false Input w := .comp rows (.atom .len)
def row : Prog false Cell Row := .comp (.fork (.comp (.atom .fst) rows) (.atom .snd)) (.atom .look)
def color : Prog false Cell w := .comp (.fork (.comp (.atom .fst) colors) (.atom .snd)) (.atom .look)
def equal {a : Ty} (u v : Prog false a w) : Prog false a w :=
 nat .add (nat .sub u v) (nat .sub v u)
def root : Prog false Cursor Input := .comp (.atom .fst) (.atom .fst)
def query : Prog false Cursor w := .comp (.atom .fst) (.atom .snd)
def index : Prog false Cursor w := .comp (.atom .snd) (.atom .fst)
def old : Prog false Cursor State := .comp (.atom .snd) (.atom .snd)
def ordinal : Prog false Cursor w := .comp old (.atom .fst)
def step : Prog false Cursor State :=
 .ifz (equal (.comp (.fork root index) color) (.comp root (.atom .fst)))
  (.fork (nat .add ordinal (.atom (.lit 1)))
    (.ifz (equal ordinal query) (.comp (.fork root index) row) (.comp old (.atom .snd)))) old

def selector : Prog false Request State := .loop (.comp (.atom .fst) count)
 (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.atom (.lit 0))))) step
def length : Prog false Input w := .comp (.comp (.fork (.atom .id) (.atom (.lit 0))) selector) (.atom .fst)
def rowCell : Prog false Cell Row := .comp selector (.atom .snd)
def program : Prog false Input (Ty.a Row) := .tab length rowCell

def rowValue (x : Input.T) (j : ℕ) : Row.T := x.2.1.look j Row.blank
def accepts (x : Input.T) (j : ℕ) : Prop := x.2.2.look j 0=x.1
instance accepts_decidable (x : Input.T) (j : ℕ) : Decidable (accepts x j) := by
 unfold accepts;infer_instance
def rowsPrefix (x : Input.T) (l : ℕ) : List Row.T := (List.range l).filterMap
 (fun j=>if accepts x j then some (rowValue x j) else none)
end
end ExactFourierCircuits.DFTModelCacheColorSelection
