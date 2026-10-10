import DFTModelSavingScalar
import DFTModelSavingResidual
import DFTModelSavingYSource
import DFTModelRecursiveExchangeSource
import DFTModelCacheUnit

set_option autoImplicit false

/-! Concrete chronological saving-record interpreter. The finite opcode
branches below contain the actual typed primitives. The only internal port
is the same strictly smaller tensor child, carrying both affine channels. -/
namespace ExactFourierCircuits.DFTModelSavingRecords
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelResidualCore
noncomputable section

abbrev Input := p w (p (Ty.a w) Node)
abbrev Iter := p Input (p w Node)
abbrev BitInput := p Iter w
abbrev Port := ChildPort

def raw : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def initial : Prog false Input Node := .comp (.atom .snd) (.atom .snd)
def field (j : ℕ) : Prog false Input w :=
  .comp (.fork raw (.atom (.lit j))) (.atom .look)
def original : Prog false Iter Input := .atom .fst
def index : Prog false Iter w := .comp (.atom .snd) (.atom .fst)
def current : Prog false Iter Node := .comp (.atom .snd) (.atom .snd)
def width : Prog false Iter w := .comp original (field 2)
def bitAddress : Prog false BitInput w := binary .add
  (binary .add (.atom (.lit 8))
    (binary .mul (.comp (.atom .fst) width) (.comp (.atom .fst) index)))
  (.atom .snd)
def bit : Prog false BitInput w := .comp
  (.fork (.comp (.atom .fst) (.comp original raw)) bitAddress) (.atom .look)
def bits : Prog false Iter (Ty.a w) := .tab width bit

def directionArgs : Prog false Iter DFTModelSavingResidualSetup.Input :=
  .fork (.fork (.comp original (field 1))
    (.fork width (.fork (.comp original (.atom .fst)) bits)))
    (.fork (.comp original (field 3)) (.fork (.comp original (field 5)) current))
def direction : Code false Port Iter Node :=
  .comp (.importClosed directionArgs) DFTModelSavingResidual.program
/-- Every original inline direction is processed in ascending descriptor order. -/
def residual : Code false Port Input Node :=
  .loop (.importClosed (field 6)) (.importClosed initial) direction

/-- Fresh actual unit record for the current padding role, then the same
SAME-q residual loop. No large-exponent ordinary transform is used here. -/
def unitArgs : Prog false Iter (p w w) := .fork
  (.comp original (field 1))
  (binary .add (.comp original (field 3)) index)
def paddingArgs : Prog false Iter Input := .fork
  (.comp original (.atom .fst))
  (.fork (.comp unitArgs DFTModelCacheRecords.unit) current)
def paddingBody : Code false Port Iter Node :=
  .comp (.importClosed paddingArgs) residual

def padding : Code false Port Input Node :=
  .loop (.importClosed (field 4)) (.importClosed initial) paddingBody

def scalarArgs : Prog false Input DFTModelSavingScalar.Input := .fork raw initial
def exchangeArgs : Prog false Input (p (Ty.a w) Node) := .fork raw initial

def opcodeTest (j : ℕ) : Prog false Input w :=
  binary .sub (field 0) (.atom (.lit j))

def dispatch (R : ℕ) : Code false Port Input Node :=
  .ifz (.importClosed (field 0)) residual
    (.ifz (.importClosed (opcodeTest 1))
      (.comp (.importClosed scalarArgs) (.importClosed (DFTModelSavingScalar.program R)))
      (.ifz (.importClosed (opcodeTest 2)) (.importClosed initial)
        (.ifz (.importClosed (opcodeTest 3)) (.importClosed (DFTModelSavingY.program R))
          (.ifz (.importClosed (opcodeTest 4))
            (.comp (.importClosed exchangeArgs) (.importClosed (DFTModelRecursiveExchange.program R)))
            (.ifz (.importClosed (opcodeTest 5)) padding (.importClosed initial))))))

abbrev StreamInput := p w (p (Ty.a (Ty.a w)) Node)
abbrev StreamIter := p StreamInput (p w Node)
def records : Prog false StreamInput (Ty.a (Ty.a w)) := .comp (.atom .snd) (.atom .fst)
def streamInitial : Prog false StreamInput Node := .comp (.atom .snd) (.atom .snd)
def recordArgs : Prog false StreamIter Input := .fork
  (.comp (.atom .fst) (.atom .fst))
  (.fork (.comp (.fork (.comp (.atom .fst) records)
    (.comp (.atom .snd) (.atom .fst))) (.atom .look))
    (.comp (.atom .snd) (.atom .snd)))
def recordBody (R : ℕ) : Code false Port StreamIter Node :=
  .comp (.importClosed recordArgs) (dispatch R)
def stream (R : ℕ) : Code false Port StreamInput Node :=
  .loop (.importClosed (.comp records (.atom .len)))
    (.importClosed streamInitial) (recordBody R)

attribute [local irreducible] DFTModelSavingResidual.program
  DFTModelCacheRecords.unit DFTModelSavingY.program DFTModelRecursiveExchange.program

theorem field_value (j rest : ℕ) (rawTape : Tape ℕ) (node : Node.T) :
    (run (field j) (rest,(rawTape,node))).val=rawTape.look j 0 := rfl

theorem bit_value (rest i j : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run bit (((rest,(rawTape,old)),(i,node)),j)).val=
      rawTape.look (8+rawTape.look 2 0*i+j) 0 := by
  simp [bit,bitAddress,width,original,raw,field,index,binary,run,Code.run,
    Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem bits_value (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run bits ((rest,(rawTape,old)),(i,node))).val=
      Tape.tab (rawTape.look 2 0) (fun j=>rawTape.look (8+rawTape.look 2 0*i+j) 0) := by
  rw [bits,DFTModelRecursiveScalar.tab_run]
  change (Bill.tab (rawTape.look 2 0) w.blank (fun j=>run bit (((rest,(rawTape,old)),(i,node)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (fun j=>bit_value rest i j rawTape old node))

attribute [local irreducible] bits

theorem directionArgs_value (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run directionArgs ((rest,(rawTape,old)),(i,node))).val=
      ((rawTape.look 1 0,(rawTape.look 2 0,(rest,
        Tape.tab (rawTape.look 2 0) (fun j=>rawTape.look (8+rawTape.look 2 0*i+j) 0)))),
       (rawTape.look 3 0,(rawTape.look 5 0,node))) := by
  simp only [directionArgs,DFTModelRecursiveScalarCore.fork_run,
    DFTModelRecursiveScalarCore.comp_run,original,width,current,field,raw,
    DFTModelRecursiveScalarCore.atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  rw [bits_value]

theorem recordArgs_value (rest i : ℕ) (rs : Tape (Tape ℕ)) (old node : Node.T) :
    (run recordArgs ((rest,(rs,old)),(i,node))).val=
      (rest,(rs.look i (Tape.empty ℕ),node)) := rfl

attribute [local irreducible] dispatch

theorem code_loop_value {s t : Ty} (n : Code false Port s w)
    (initial : Code false Port s t) (f : Code false Port (p s (p w t)) t)
    (h : Handler Port) (x : s.T) :
    (Code.run (.loop n initial f) h x).val=
      (Bill.steps (Code.run initial h x).val
        (fun i z=>Code.run f h (x,(i,z))) (Code.run n h x).val).val := rfl

theorem steps_value_congr {α : Type} (x : α) (f g : ℕ→α→Bill α)
    (eq : ∀i z,(f i z).val=(g i z).val) (n : ℕ) :
    (Bill.steps x f n).val=(Bill.steps x g n).val := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change (f n (Bill.steps x f n).val).val=(g n (Bill.steps x g n).val).val
    rw [ih,eq]

/-- The runtime stream really advances one physical record at a time. -/
theorem stream_value (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler Port) :
    (Code.run (stream R) h (rest,(rs,node))).val=
      (Bill.steps node (fun i z=>Code.run (dispatch R) h
        (rest,(rs.look i (Tape.empty ℕ),z))) rs.len).val := by
  rw [stream,code_loop_value]
  change (Bill.steps node (fun i z=>Code.run (recordBody R) h
    ((rest,(rs,node)),(i,z))) rs.len).val=_
  apply steps_value_congr
  intro i z
  rw [recordBody,DFTModelClockBatch.code_comp_value]
  change (Code.run (dispatch R) h (run recordArgs ((rest,(rs,node)),(i,z))).val).val=_
  rw [recordArgs_value]

end
end ExactFourierCircuits.DFTModelSavingRecords
