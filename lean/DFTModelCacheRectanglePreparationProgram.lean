import DFTModelCacheRectanglePreparationGeometry
import DFTModelCacheDescriptorLog

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDescriptor (Row7 rowEncode nat)
noncomputable section
attribute [local irreducible] DFTModelCacheSpectrum.program DFTModelCacheDescriptor.logarithm

abbrev Input := p (p w Row7) (p w sc)
abbrev Seed := p Input DFTModelCacheDescriptor.LogResult
abbrev Output := p Row7 (p w (Ty.a sc))

def rowA : Prog false Row7 w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def rowE : Prog false Row7 w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def rowSplit : Prog false Row7 w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))))
def rowI0 : Prog false Row7 w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd)
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))))
def rowJ0 : Prog false Row7 w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd)
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
def inputRow : Prog false Input Row7 := .comp (.atom .fst) (.atom .snd)
def threshold : Prog false Input w :=
  nat .mul (.atom (.lit 2)) (nat .add (.comp inputRow rowA) (.comp inputRow rowE))
def seed : Prog false Input Seed :=
  .fork (.atom .id) (.comp threshold DFTModelCacheDescriptor.logarithm)

def savedRow : Prog false Seed Row7 := .comp (.atom .fst) inputRow
def savedRadix : Prog false Seed w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def computedHeight : Prog false Seed w := .comp (.atom .snd) (.atom .fst)
def computedWidth : Prog false Seed w := .comp (.atom .snd) (.atom .snd)
def metadata : Prog false Seed DFTModelCacheDisplacement.Metadata :=
  .fork savedRadix (.fork (.fork (.comp savedRow rowA) (.comp savedRow rowE))
    (.fork (.fork (.comp savedRow rowI0) (.comp savedRow rowJ0))
      (.fork (.comp savedRow rowSplit) computedWidth)))
def argument : Prog false Seed DFTModelCacheSpectrum.Input :=
  .fork metadata (.comp (.atom .fst) (.atom .snd))
def body : Prog false Seed Output :=
  .fork savedRow (.fork computedHeight (.comp argument DFTModelCacheSpectrum.program))
def program : Prog false Input Output := .comp seed body

theorem threshold_run (r D : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    run threshold ((r,rowEncode q),(D,z))=⟨2*(q.a+q.e),27,
      max 2 (2*(q.a+q.e)),True⟩ := by
  simp [threshold,nat,inputRow,rowA,rowE,rowEncode,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem seed_run (r D : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    run seed ((r,rowEncode q),(D,z))=
      ((run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).pass
        (fun kw=>Bill.one (((r,rowEncode q),(D,z)),kw))).pay 29
          (max 2 (2*(q.a+q.e))) := by
  simp [seed,threshold,nat,inputRow,rowA,rowE,rowEncode,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem metadata_run (r D K N : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    run metadata (((r,rowEncode q),(D,z)),(K,N))=
      ⟨(r,((q.a,q.e),((q.i0,q.j0),(q.split,N)))),87,0,True⟩ := by
  simp [metadata,savedRadix,savedRow,inputRow,rowA,rowE,rowI0,rowJ0,rowSplit,
    computedWidth,rowEncode,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] seed metadata

theorem body_run (r D K N : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    run body (((r,rowEncode q),(D,z)),(K,N))=
      ((run DFTModelCacheSpectrum.program
        ((r,((q.a,q.e),((q.i0,q.j0),(q.split,N)))),(D,z))).pass
          (fun bank=>Bill.one (rowEncode q,(K,bank)))).pay 101 0 := by
  simp [body,savedRow,inputRow,computedHeight,argument,run,Code.run,Atom.run,
    metadata,savedRadix,rowA,rowE,rowI0,rowJ0,rowSplit,computedWidth,rowEncode,
    Bill.one,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] body

theorem program_run (r D : ℕ) (q : UniformLocalRectangleDescriptors.Row) (z : ℂ) :
    run program ((r,rowEncode q),(D,z))=
      ((run DFTModelCacheDescriptor.logarithm (2*(q.a+q.e))).pass (fun kw=>
        (run DFTModelCacheSpectrum.program
          ((r,((q.a,q.e),((q.i0,q.j0),(q.split,kw.2)))),(D,z))).pass
            (fun bank=>Bill.one (rowEncode q,(kw.1,bank))))).pay 132
              (max 2 (2*(q.a+q.e))) := by
  change ((run seed ((r,rowEncode q),(D,z))).pass (run body)).pay 1 0=_
  rw [seed_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [body_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  congr 1 <;> first | omega | ac_rfl

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
