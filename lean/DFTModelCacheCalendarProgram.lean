import DFTModelCacheCalendarSequence
import DFTModelCacheDescriptorNodeBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine
open DFTModelCacheTraversal (ofList rectangleEncode append appendValue singleton)
noncomputable section

abbrev Input : Ty := p w (p w w)
abbrev NodeFrame : Ty := p Input (p w (Ty.a Row7))
abbrev Joined : Ty := p NodeFrame (p Output Output)
abbrev Finished : Ty := p Joined Output
abbrev RecPort : Port := some (Input,Output)

def width : Prog false Input w := .atom .fst
def offset : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def start : Prog false Input w := .comp (.atom .snd) (.atom .snd)
def directCount : Prog false Input w := nat .add width
  (nat .mul (nat .mul (.atom (.lit 14)) width) (nat .sub width (.atom (.lit 1))))
def directEvent : Prog false Input Event9 := .fork start (.fork (.atom (.lit 0))
  (.fork width (.fork offset (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0))
    (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.atom (.lit 0)))))))))
def direct : Prog false Input Output := .fork directCount (.comp directEvent (singleton Event9))
def prepare : Prog false Input NodeFrame :=
  .fork (.atom .id) (.comp (.fork width offset) DFTModelCacheDescriptor.node)

def nodeWidth : Prog false NodeFrame w := .comp (.atom .fst) width
def nodeOffset : Prog false NodeFrame w := .comp (.atom .fst) offset
def nodeStart : Prog false NodeFrame w := .comp (.atom .fst) start
def nodeRows : Prog false NodeFrame (Ty.a Row7) := .comp (.atom .snd) (.atom .snd)
def nodeSmall : Prog false NodeFrame w := nat .lt nodeWidth (.atom (.lit 2))
def half : Prog false NodeFrame w := nat .div nodeWidth (.atom (.lit 2))
def leftInput : Prog false NodeFrame Input := .fork half (.fork nodeOffset nodeStart)
def rightInput : Prog false NodeFrame Input := .fork (nat .sub nodeWidth half)
  (.fork (nat .add nodeOffset half) nodeStart)

def maximum {s : Ty} (f g : Prog false s w) : Prog false s w :=
  .ifz (nat .lt f g) f g

def left : Prog false Joined Output := .comp (.atom .snd) (.atom .fst)
def right : Prog false Joined Output := .comp (.atom .snd) (.atom .snd)
def childDuration : Prog false Joined w :=
  maximum (.comp left (.atom .fst)) (.comp right (.atom .fst))
def correctionStart : Prog false Joined w := nat .add (.comp (.atom .fst) nodeStart) childDuration
def correction : Prog false Joined Output :=
  .comp (.fork correctionStart (.comp (.atom .fst) nodeRows)) sequence

def finishedDuration : Prog false Finished w :=
  nat .add (.comp (.atom .fst) childDuration) (.comp (.atom .snd) (.atom .fst))
def firstEvents : Prog false Finished (Ty.a Event9) :=
  .comp (.atom .fst) (.comp left (.atom .snd))
def secondEvents : Prog false Finished (Ty.a Event9) :=
  .comp (.atom .fst) (.comp right (.atom .snd))
def parentEvents : Prog false Finished (Ty.a Event9) := .comp (.atom .snd) (.atom .snd)
def finishedEvents : Prog false Finished (Ty.a Event9) :=
  .comp (.fork (.comp (.fork firstEvents secondEvents) (append Event9)) parentEvents) (append Event9)
def finish : Prog false Joined Output :=
  .comp (.fork (.atom .id) correction) (.fork finishedDuration finishedEvents)

def splitCode : Code false RecPort NodeFrame Output :=
  .comp (.fork (.atom .id) (.fork (.comp (.importClosed leftInput) .call)
    (.comp (.importClosed rightInput) .call))) (.importClosed finish)
def directCode : Code false RecPort NodeFrame Output :=
  .comp (.atom .fst) (.importClosed direct)
def branch : Code false RecPort NodeFrame Output :=
  .ifz (.importClosed nodeSmall) (.ifz (.comp (.atom .snd) (.atom .fst)) directCode splitCode) directCode
def body : Code false RecPort Input Output := .comp (.importClosed prepare) branch

def result (fuel v o t : ℕ) : Bill Output.T :=
  depthRun (run direct) body.run fuel (v,(o,t))
def header : Prog false Input (p w Input) :=
  .fork (nat .add width (.atom (.lit 1))) (.atom .id)
def program : Prog false Input Output := .comp header (.descend direct body)

/-- Exact source tree; no tree value occurs in the program's input. -/
def sourceTree (v o : ℕ) : Tree := ofPlan (UniformBalancedToeplitz.plan v) o
def expected (v o t : ℕ) : Output.T :=
  (treeDuration (sourceTree v o),ofList ((treeTimed t (sourceTree v o)).map eventEncode))

end
end ExactFourierCircuits.DFTModelCacheCalendar
