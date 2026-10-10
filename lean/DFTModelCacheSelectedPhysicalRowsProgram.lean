import DFTModelCacheColorRebaseSelected
import DFTModelCacheSelectedCoefficientsPhysicalRows

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row nat)
noncomputable section
/-- Radix, source offset/width, target offset/width, gate count. These are
coordinate geometry; coefficient addresses never determine a table length. -/
abbrev Geometry := p w (p w (p w (p w (p w w))))
abbrev Input := p Geometry (Ty.a Row)
abbrev Ready := p Input (Ty.a Row)
abbrev Cell := p Ready w
abbrev Candidate := p Geometry w
def radix : Prog false Geometry w := .atom .fst
def source : Prog false Geometry w := .comp (.atom .snd) (.atom .fst)
def inputs : Prog false Geometry w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def target : Prog false Geometry w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def targets : Prog false Geometry w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def gates : Prog false Geometry w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
def outside {s:Ty} (q start width:Prog false s w) : Prog false s w :=
 .ifz (nat .sub start q) (.ifz (nat .sub (nat .add start width) q)
  (.atom (.lit 1)) (.atom (.lit 0))) (.atom (.lit 1))
def candidate : Prog false Candidate Row :=
 .fork (.atom .snd) (.fork (.atom (.lit 0)) (.atom (.lit 0)))
def eligible : Prog false Candidate w := nat .mul
 (outside (.atom .snd) (.comp (.atom .fst) source) (.comp (.atom .fst) inputs))
 (outside (.atom .snd) (.comp (.atom .fst) target) (.comp (.atom .fst) targets))
def borrowedArgs : Prog false Geometry DFTModelCacheColorSelection.Input :=
 .fork (.atom (.lit 1)) (.fork (.tab radix candidate) (.tab radix eligible))
/-- Generate the ascending eligible coordinates. Only the first g are read;
the fit theorem identifies them with the native Borrowed17 table. -/
def borrowed : Prog false Geometry (Ty.a Row) :=
 .comp borrowedArgs DFTModelCacheColorSelection.program
def geometry : Prog false Ready Geometry := .comp (.atom .fst) (.atom .fst)
def borrowedAt : Prog false Cell w := .comp
 (.comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)) (.atom .fst)
def coordinate : Prog false Cell w :=
 .ifz (nat .sub (.comp (.atom .fst) (.comp geometry inputs)) (.atom .snd))
  (.ifz (nat .sub
   (nat .add (nat .add (.comp (.atom .fst) (.comp geometry inputs)) (.atom (.lit 1)))
    (.comp (.atom .fst) (.comp geometry gates))) (.atom .snd))
   (nat .add (.comp (.atom .fst) (.comp geometry target))
    (nat .sub (.atom .snd)
     (nat .add (nat .add (.comp (.atom .fst) (.comp geometry inputs)) (.atom (.lit 1)))
      (.comp (.atom .fst) (.comp geometry gates)))))
   (.comp (.fork (.atom .fst) (nat .sub (.atom .snd)
    (nat .add (.comp (.atom .fst) (.comp geometry inputs)) (.atom (.lit 1))))) borrowedAt))
  (nat .add (.comp (.atom .fst) (.comp geometry source)) (.atom .snd))
def rows : Prog false Ready (Ty.a Row) := .comp (.atom .fst) (.atom .snd)
def row : Prog false Cell Row := .comp
 (.fork (.comp (.atom .fst) rows) (.atom .snd)) (.atom .look)
def mapRow : Prog false Cell Row := .fork
 (.comp (.fork (.atom .fst) (.comp row (.atom .fst))) coordinate)
 (.fork (.comp (.fork (.atom .fst) (.comp row (.comp (.atom .snd) (.atom .fst)))) coordinate)
  (.comp row (.comp (.atom .snd) (.atom .snd))))
def mapper : Prog false Ready (Ty.a Row) := .tab (.comp rows (.atom .len)) mapRow
def prepare : Prog false Input Ready :=
 .fork (.atom .id) (.comp (.atom .fst) borrowed)
/-- Closed finite code: generate borrowed cells, then map the supplied selected
occurrences in order. No borrowed table or coefficient decoding is supplied. -/
def program : Prog false Input (Ty.a Row) := .comp prepare mapper

def geom (v s e t a g:ℕ) : Geometry.T := (v,(s,(e,(t,(a,g)))))
def encode (q:UniformInPlaceMachine.Row) : Row.T := (q.dst,(q.src,q.coefficient))
def rowTape (qs:List UniformInPlaceMachine.Row) : Tape Row.T :=
 DFTModelCacheSelectedCoefficients.physicalRows qs
def availableRows (v s e t a:ℕ) : List Row.T :=
 (UniformBorrowedCoordinateMachine.available v s e t a).map (fun j=>(j,(0,0)))
end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
