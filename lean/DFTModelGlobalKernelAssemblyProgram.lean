import DFTModelGlobalKernelAssemblySectors

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine
noncomputable section
abbrev Preparation := p DFTModelGlobalSectorPreparation.Output DFTModelGlobalSectorPreparation.Directory
abbrev Input := p DFTModelGlobalSectorPreparation.Axes (p sc (p w (Ty.a Tagged)))
abbrev Prepared := p Input Preparation
abbrev Packed := p Prepared (Ty.a Tagged)
abbrev Solved := p Packed (Ty.a (Ty.a Tagged))
abbrev Merged := p Solved (p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged))
abbrev Output := p Merged (Ty.a Tagged)

def inputI : Prog false Input sc := .comp (.atom .snd) (.atom .fst)
def inputW : Prog false Input w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def inputBank : Prog false Input (Ty.a Tagged) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def preparation : Prog false Input Preparation :=
 .comp (.atom .fst) DFTModelGlobalSectorPreparation.withDirectory

def volume : Prog false Prepared w := .comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))
def packing : Prog false Prepared (Ty.a w) :=
 .comp (.atom .snd) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
def unpacking : Prog false Prepared (Ty.a w) :=
 .comp (.atom .snd) (.comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def generatedSectors : Prog false Prepared (Ty.a DFTModelGlobalSectorPreparation.Sector) :=
 .comp (.atom .snd) (.comp (.atom .fst) DFTModelGlobalSectorPreparation.outputSectors)
def directory : Prog false Prepared DFTModelGlobalSectorPreparation.Directory := .comp (.atom .snd) (.atom .snd)

def gatherArgument : Prog false Prepared MoveInput :=
 .fork (.comp (.atom .fst) inputW)
  (.fork volume (.fork unpacking (.comp (.atom .fst) inputBank)))
def gather : Prog false Prepared (Ty.a Tagged) := .comp gatherArgument move

def sectorArgument : Prog false Packed SectorInput :=
 .fork (.comp (.atom .fst) (.comp (.atom .fst) inputI))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) inputW))
   (.fork (.comp (.atom .fst) volume)
    (.fork (.comp (.atom .fst) generatedSectors) (.atom .snd))))
def solve : Prog false Packed (Ty.a (Ty.a Tagged)) := .comp sectorArgument sectors

def mergeArgument : Prog false Solved (DFTModelSectorMaterialization.JoinedInput Tagged) :=
 .fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) inputW)))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) directory))
   (.fork (.atom .snd) (.comp (.atom .fst) (.atom .snd))))
def merge : Prog false Solved (p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged)) :=
 .comp mergeArgument (DFTModelSectorMaterialization.joined Tagged)

def scatterArgument : Prog false Merged MoveInput :=
 .fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) inputW))))
  (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) volume)))
   (.fork (.comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) packing)))
    (.comp (.atom .snd) (.atom .snd))))
def scatter : Prog false Merged (Ty.a Tagged) := .comp scatterArgument move

/-- One generated packing/directory, two linear whole-bank movements,
one compact closed-saving call per generated sector, and one materializer. -/
def program : Prog false Input Output :=
 .comp (.fork (.atom .id) preparation)
  (.comp (.fork (.atom .id) gather)
   (.comp (.fork (.atom .id) solve)
    (.comp (.fork (.atom .id) merge) (.fork (.atom .id) scatter))))

attribute [local irreducible] move sectors DFTModelGlobalSectorPreparation.withDirectory
 DFTModelSectorMaterialization.joined

theorem gatherArgument_run (x:Input.T) (p:Preparation.T) :
 run gatherArgument (x,p)=⟨(x.2.2.1,(p.1.1,(p.1.2.2.1,x.2.2.2))),31,0,True⟩ := by
 simp [gatherArgument,inputW,inputBank,volume,unpacking,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem sectorArgument_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) :
 run sectorArgument ((x,p),v)=⟨(x.2.1,(x.2.2.1,(p.1.1,(p.1.2.2.2,v)))),39,0,True⟩ := by
 simp [sectorArgument,inputI,inputW,volume,generatedSectors,
  DFTModelGlobalSectorPreparation.outputSectors,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem mergeArgument_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) (ps:Tape (Tape Tagged.T)) :
 run mergeArgument (((x,p),v),ps)=⟨(x.2.2.1,(p.2,(ps,v))),25,0,True⟩ := by
 simp [mergeArgument,inputW,directory,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem scatterArgument_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T)
 (ps:Tape (Tape Tagged.T)) (m:(Ty.p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged)).T) :
 run scatterArgument ((((x,p),v),ps),m)=⟨(x.2.2.1,(p.1.1,(p.1.2.1,m.2))),43,0,True⟩ := by
 simp [scatterArgument,inputW,volume,packing,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly
