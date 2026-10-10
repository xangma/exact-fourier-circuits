import DFTModelRecursiveYActual
import DFTModelRecursiveScalarSource

set_option autoImplicit false

/-! A real opcode3 caller: headers and each inline direction are read from the
original record tape. The loop carries one paired affine bank. -/
namespace ExactFourierCircuits.DFTModelSavingY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelResidualCore
noncomputable section

abbrev Input := p w (p (Ty.a w) Node)
abbrev Body := p Input (p w Node)
def rest : Prog false Input w := .atom .fst
def raw : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def initial : Prog false Input Node := .comp (.atom .snd) (.atom .snd)
def field (i : ℕ) : Prog false Input w :=
  .comp (.fork raw (.atom (.lit i))) (.atom .look)
def original : Prog false Body Input := .atom .fst
def index : Prog false Body w := .comp (.atom .snd) (.atom .fst)
def old : Prog false Body Node := .comp (.atom .snd) (.atom .snd)
def rowBase : Prog false Body w := binary .add (.atom (.lit 8))
  (binary .mul (binary .add (.comp original (field 2)) (.atom (.lit 1))) index)
def arguments : Prog false Body DFTModelRecursiveYDirection.Input :=
  .fork (.fork (.comp original (field 1))
    (.fork (.comp original (field 2)) (.fork rowBase (.comp original raw))))
    (.fork (.comp original rest) old)
def body (R : ℕ) : Prog false Body Node :=
  .comp arguments (DFTModelRecursiveYDirection.program R)
def program (R : ℕ) : Prog false Input Node := .loop (field 6) initial (body R)

def input (r k : ℕ) (I : ℂ) (record : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) : Input.T := (r,(record,((k,I),v)))
def rowInput (r k i : ℕ) (I : ℂ) (record : Tape ℕ)
    (originalBank v : Tape DFTModelAffine.Tagged.T) : Body.T :=
  (input r k I record originalBank,(i,((k,I),v)))

attribute [local irreducible] DFTModelRecursiveYDirection.program

theorem field_run (i : ℕ) (x : Input.T) :
    run (field i) x=⟨x.2.1.look i 0,7,i,True⟩ := by
  simp [field,raw,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem initial_run (x : Input.T) : run initial x=⟨x.2.2,3,0,True⟩ := by
  simp [initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem arguments_run (r k i : ℕ) (I : ℂ) (record : Tape ℕ)
    (v0 v : Tape DFTModelAffine.Tagged.T) :
    run arguments (rowInput r k i I record v0 v)=
      ⟨DFTModelRecursiveYDirection.input (record.look 1 0) (record.look 2 0) r
        (8+(record.look 2 0+1)*i) k I record v,
        57,max 8 (max 2 (max (record.look 2 0+1)
          (max ((record.look 2 0+1)*i) (8+(record.look 2 0+1)*i)))),True⟩ := by
  simp [arguments,rowBase,original,index,old,rest,raw,field,binary,rowInput,input,
    DFTModelRecursiveYDirection.input,DFTModelRecursiveYMask.input,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

def steps (R : ℕ) (x : Input.T) (count : ℕ) : Bill Node.T :=
  Bill.steps x.2.2 (fun i z => run (body R) (x,(i,z))) count

theorem program_run (R : ℕ) (x : Input.T) :
    run (program R) x=(steps R x (x.2.1.look 6 0)).pay 11 6 := by
  simp only [program,run,Code.run]
  change ((run (field 6) x).pass (fun l => (run initial x).pass
    (fun y => Bill.steps y (fun i z => run (body R) (x,(i,z))) l))).pay 1 0=_
  rw [field_run,initial_run]
  simp only [Bill.pass,Bill.pay,steps,true_and,zero_max,max_comm]
  congr 1
  omega

end
end ExactFourierCircuits.DFTModelSavingY
