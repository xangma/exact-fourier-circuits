import DFTModelCacheBucketSource
import UniformCrossDepthReplayPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeight
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDAGDepth (nat)
noncomputable section
abbrev Row := p w (p w w)
abbrev Params := p w (p w (p w (p w (p w w))))
abbrev Input := p Params (p (Ty.a w) (p (Ty.a w) (Ty.a w)))
abbrev Cell := p Input w
abbrev State := p w Row
abbrev Request := p Input w
abbrev Cursor := p Request (p w State)
def param : Prog false Input Params := .atom .fst
def inputs : Prog false Input w := .comp param (.atom .fst)
def dataBase : Prog false Input w := .comp param (.comp (.atom .snd) (.atom .fst))
def coefficients : Prog false Input w := .comp param (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def constants : Prog false Input w := .comp param (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def height : Prog false Input w := .comp param (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))))
def enabled : Prog false Input w := .comp param (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
def topology : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def order : Prog false Input (Ty.a w) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def directory : Prog false Input (Ty.a w) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def start : Prog false Input w := .comp (.fork directory height) (.atom .look)
def finish : Prog false Input w := .comp (.fork directory (nat .add height (.atom (.lit 1)))) (.atom .look)
def count : Prog false Input w := nat .sub finish start
def slots : Prog false Input w := nat .mul (.atom (.lit 2)) count
def gate : Prog false Cell w := .comp (.fork (.comp (.atom .fst) order)
 (nat .add (.comp (.atom .fst) start) (nat .div (.atom .snd) (.atom (.lit 2))))) (.atom .look)
def side : Prog false Cell w := nat .mod (.atom .snd) (.atom (.lit 2))
def field (j:ℕ) : Prog false Cell w := .comp (.fork (.comp (.atom .fst) topology)
 (nat .add (nat .mul (.atom (.lit 5)) gate) (.atom (.lit j)))) (.atom .look)
def source : Prog false Cell w := .ifz side (field 1) (field 2)
def accept : Prog false Cell w :=
 .ifz (nat .lt source (.comp (.atom .fst) inputs))
  (nat .lt (.comp (.atom .fst) inputs) source)
  (.ifz (.comp (.atom .fst) enabled) (.atom (.lit 0)) (.atom (.lit 1)))
def active : Prog false Cell w := .ifz side accept
 (.ifz (nat .lt (field 0) (.atom (.lit 2))) (.atom (.lit 0)) accept)
def coefficient : Prog false Cell w := .ifz side
 (.ifz (nat .lt (field 0) (.atom (.lit 2)))
  (.ifz (nat .lt (field 3) (.atom (.lit 1)))
   (nat .add (.comp (.atom .fst) coefficients) (field 4))
   (.ifz (nat .lt (field 4) (.atom (.lit 2)))
    (nat .add (.comp (.atom .fst) constants) (.atom (.lit 2)))
    (.comp (.atom .fst) constants)))
  (.comp (.atom .fst) constants))
 (nat .add (.comp (.atom .fst) constants) (field 0))
def row : Prog false Cell Row := .fork
 (nat .add (.comp (.atom .fst) dataBase)
  (nat .add (nat .add (.comp (.atom .fst) inputs) (.atom (.lit 1))) gate))
 (.fork (nat .add (.comp (.atom .fst) dataBase) source) coefficient)
def root : Prog false Cursor Input := .comp (.atom .fst) (.atom .fst)
def query : Prog false Cursor w := .comp (.atom .fst) (.atom .snd)
def index : Prog false Cursor w := .comp (.atom .snd) (.atom .fst)
def old : Prog false Cursor State := .comp (.atom .snd) (.atom .snd)
def ordinal : Prog false Cursor w := .comp old (.atom .fst)
def equal := DFTModelCacheBucket.equal
def step : Prog false Cursor State := .ifz (.comp (.fork root index) active) old
 (.fork (nat .add ordinal (.atom (.lit 1)))
  (.ifz (.comp (.fork ordinal query) equal) (.comp old (.atom .snd)) (.comp (.fork root index) row)))
def selector : Prog false Request State := .loop (.comp (.atom .fst) slots)
 (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.atom (.lit 0))))) step
def length : Prog false Input w := .comp (.comp (.fork (.atom .id) (.atom (.lit 0))) selector) (.atom .fst)
def rowCell : Prog false Cell Row := .comp selector (.atom .snd)
def program : Prog false Input (Ty.a Row) := .tab length rowCell

def gateValue (x:Input.T) (j:ℕ) : ℕ :=
 x.2.2.1.look (x.2.2.2.look x.1.2.2.2.2.1 0+j/2) 0
def fieldValue (x:Input.T) (j k:ℕ) : ℕ := x.2.1.look (5*gateValue x j+k) 0
def rowValue (x:Input.T) (j:ℕ) : Row.T :=
 let n:=x.1.1;let A:=x.1.2.1;let C:=x.1.2.2.1;let P:=x.1.2.2.2.1
 let f:=fieldValue x j
 (A+(n+1+gateValue x j),(A+(if j%2=0 then f 1 else f 2),
 if j%2=0 then (if f 0<2 then P else if f 3<1 then (if f 4<2 then P else P+2) else C+f 4) else P+f 0))
def accepts (x:Input.T) (j:ℕ) : Prop :=
 let f:=fieldValue x j
 let s:=if j%2=0 then f 1 else f 2
 (j%2=0 ∨ f 0<2) ∧ (if s<x.1.1 then x.1.2.2.2.2.2≠0 else x.1.1<s)
def slotCount (x:Input.T) : ℕ := 2*(x.2.2.2.look (x.1.2.2.2.2.1+1) 0-x.2.2.2.look x.1.2.2.2.2.1 0)
instance accepts_decidable (x:Input.T) (j:ℕ) : Decidable (accepts x j) := by
 unfold accepts
 infer_instance
def rowsPrefix (x:Input.T) (l:ℕ) : List Row.T := (List.range l).filterMap
 (fun j=>if accepts x j then some (rowValue x j) else none)

end
end ExactFourierCircuits.DFTModelCacheHeight
