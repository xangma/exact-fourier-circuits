import DFTModelCacheRectangleMixedCaller

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Root := p w (p w sc)
abbrev Bases := p w (p w w)
abbrev Slot := p w (p w w)
/-- Original axis seed order/master, ordinary coefficient addresses, actual
depth/color/enabled slot, and the literal seven-word rectangle descriptor. -/
abbrev Input := p Root (p Bases (p Slot (Ty.a w)))
abbrev Context := p Input DFTModelCacheTopology.Config
abbrev Output := p Context DFTModelCacheSelectedPhysicalRowsCaller.Output

def root : Prog false Input Root := .atom .fst
def bases : Prog false Input Bases := .comp (.atom .snd) (.atom .fst)
def slot : Prog false Input Slot := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def rows : Prog false Input (Ty.a w) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def row (j:ℕ) : Prog false Input w := .comp (.fork rows (.atom (.lit j))) (.atom .look)
def dimensions : Prog false Input DFTModelCacheTopology.Input := .fork (row 2) (row 3)
def prepare : Prog false Input Context := .fork (.atom .id)
 (.comp dimensions DFTModelCacheTopology.prepare)

def original {s:Ty} (f:Prog false Input s) : Prog false Context s := .comp (.atom .fst) f
def configuration {s:Ty} (f:Prog false DFTModelCacheTopology.Config s) : Prog false Context s :=
 .comp (.atom .snd) f
def seedRadix : Prog false Context w := .comp (original root) (.atom .fst)
def master : Prog false Context (p w sc) := .comp (original root) (.atom .snd)
def C : Prog false Context w := .comp (original bases) (.atom .fst)
def P : Prog false Context w := .comp (original bases) (.comp (.atom .snd) (.atom .snd))
def depth : Prog false Context w := .comp (original slot) (.atom .fst)
def color : Prog false Context w := .comp (original slot) (.comp (.atom .snd) (.atom .fst))
def enabled : Prog false Context w := .comp (original slot) (.comp (.atom .snd) (.atom .snd))

def metadata : Prog false Context DFTModelCacheDisplacement.Metadata :=
 .fork seedRadix (.fork (.fork (original (row 2)) (original (row 3)))
  (.fork (.fork (original (row 5)) (original (row 6)))
   (.fork (original (row 4)) (configuration DFTModelCacheTopology.n))))
def control : Prog false Context DFTModelCacheSelectedPhysicalRowsProduced.Control :=
 .fork (.fork (configuration DFTModelCacheTopology.k) (original bases)) (.fork metadata master)
def geometry : Prog false Context DFTModelCacheSelectedPhysicalRows.Geometry :=
 .fork (original (row 0)) (.fork (original (row 6)) (.fork (original (row 3))
  (.fork (original (row 5)) (.fork (original (row 2))
   (configuration DFTModelCacheTopology.crossCount)))))
def heightInput : Prog false Context DFTModelCacheHeightColorCaller.Input :=
 .fork color (.fork (.fork (.atom (.lit 0)) (.fork C (.fork P (.fork depth enabled))))
  (original dimensions))
def argument : Prog false Context DFTModelCacheSelectedPhysicalRowsCaller.Input :=
 .fork control (.fork geometry heightInput)
def finish : Prog false Context Output := .fork (.atom .id)
 (.comp argument DFTModelCacheSelectedPhysicalRowsCaller.program)
/-- The descriptor is read by charged look/projection operations. One charged
logarithm derives K/N; the unchanged raw height/color/mapper/factor circuit runs
once. Original offset and the whole descriptor stay in the retained context. -/
def program : Prog false Input Output := .comp prepare finish

def input (seedRadix D C T P:ℕ) (z:ℂ) (depth color:ℕ) (enabled:Bool)
 (q:UniformLocalRectangleDescriptors.Row) : Input.T :=
 ((seedRadix,(D,z)),((C,(T,P)),((depth,(color,if enabled then 1 else 0)),
  Tape.tab 7 (fun j=>q.words[j]?.getD 0))))

def rowValue (x:Input.T) (j:ℕ) : ℕ := x.2.2.2.look j 0
def gateValue (v:DFTModelCacheTopology.Config.T) : ℕ :=
 6*(3*v.2.1*v.2.2+2*v.2.2)+2*v.1.1
def metadataValue (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 DFTModelCacheDisplacement.Metadata.T :=
 (x.1.1,((rowValue x 2,rowValue x 3),
  ((rowValue x 5,rowValue x 6),(rowValue x 4,v.2.2))))
def controlValue (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 DFTModelCacheSelectedPhysicalRowsProduced.Control.T :=
 ((v.2.1,x.2.1),(metadataValue x v,x.1.2))
def geometryValue (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 DFTModelCacheSelectedPhysicalRows.Geometry.T :=
 (rowValue x 0,(rowValue x 6,(rowValue x 3,(rowValue x 5,(rowValue x 2,gateValue v)))))
def heightValue (x:Input.T) : DFTModelCacheHeightColorCaller.Input.T :=
 (x.2.2.1.2.1,((0,(x.2.1.1,(x.2.1.2.2,(x.2.2.1.1,x.2.2.1.2.2)))),
  (rowValue x 2,rowValue x 3)))
def argumentValue (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 DFTModelCacheSelectedPhysicalRowsCaller.Input.T :=
 (controlValue x v,(geometryValue x v,heightValue x))

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller
