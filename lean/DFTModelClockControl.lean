import DFTModelClockBatch
import DFTModelAffineCore
import UniformNativeScheduleSemantics

set_option autoImplicit false

/-! Typed sequencing and bounded-recursion assembly only. These templates
do not instantiate the missing residual/native instruction emitters and do
not assert that the saving program has been compiled. The actual packed C
kernel is in DFTModelClock; efficient complete child batches are in
DFTModelClockBatch. -/
namespace ExactFourierCircuits.DFTModelClockControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Each recursive call carries its exponent, the supplied prepared I, and
ONE tape whose Tagged elements contain BOTH affine channels. -/
abbrev Node := p (p w sc) (Ty.a DFTModelAffine.Tagged)
abbrev Result := Ty.a DFTModelAffine.Tagged
abbrev ChildPort := some (Node,Result)

def sequence {s : Ty} {r : RAM.Port} : List (Code false r s s) → Code false r s s
  | [] => .atom .id
  | f::fs => .comp f (sequence fs)

def trace {s : Ty} {r : RAM.Port} (h : Handler r) :
    List (Code false r s s) → s.T → Bill s.T
  | [],x => Bill.one x
  | f::fs,x => ((Code.run f h x).pass (trace h fs)).pay 1 0

theorem sequence_run {s : Ty} {r : RAM.Port} (fs : List (Code false r s s))
    (h : Handler r) (x : s.T) : Code.run (sequence fs) h x=trace h fs x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change ((Code.run f h x).pass (Code.run (sequence fs) h)).pay 1 0=_
    unfold trace
    congr 1
    apply congrArg (Bill.pass (Code.run f h x))
    exact funext ih

theorem sequence_value {s : Ty} {r : RAM.Port} (fs : List (Code false r s s))
    (h : Handler r) (x : s.T) :
    (Code.run (sequence fs) h x).val=fs.foldl (fun y f=>(Code.run f h y).val) x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change (Code.run (sequence fs) h (Code.run f h x).val).val=_
    exact ih _

def traceWork {s : Ty} {r : RAM.Port} (h : Handler r) :
    List (Code false r s s) → s.T → ℕ
  | [],_ => 0
  | f::fs,x => (Code.run f h x).work+traceWork h fs (Code.run f h x).val

theorem sequence_work {s : Ty} {r : RAM.Port} (fs : List (Code false r s s))
    (h : Handler r) (x : s.T) :
    (Code.run (sequence fs) h x).work=1+fs.length+traceWork h fs x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change (Code.run f h x).work+(Code.run (sequence fs) h (Code.run f h x).val).work+1=_
    rw [ih]
    simp only [List.length_cons,traceWork]
    omega

def traceValid {s : Ty} {r : RAM.Port} (h : Handler r) :
    List (Code false r s s) → s.T → Prop
  | [],_ => True
  | f::fs,x => (Code.run f h x).valid ∧ traceValid h fs (Code.run f h x).val

theorem sequence_valid {s : Ty} {r : RAM.Port} (fs : List (Code false r s s))
    (h : Handler r) (x : s.T) :
    (Code.run (sequence fs) h x).valid ↔ traceValid h fs x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change ((Code.run f h x).valid ∧
      (Code.run (sequence fs) h (Code.run f h x).val).valid) ↔ _
    rw [ih]
    rfl

def tracePeak {s : Ty} {r : RAM.Port} (h : Handler r) :
    List (Code false r s s) → s.T → ℕ
  | [],_ => 0
  | f::fs,x => max (Code.run f h x).peak (tracePeak h fs (Code.run f h x).val)

theorem sequence_peak {s : Ty} {r : RAM.Port} (fs : List (Code false r s s))
    (h : Handler r) (x : s.T) :
    (Code.run (sequence fs) h x).peak=tracePeak h fs x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change max (max (Code.run f h x).peak
      (Code.run (sequence fs) h (Code.run f h x).val).peak) 0=_
    rw [ih,max_zero]
    rfl

/-- A syntax assembler, with the actual fixed instruction chronology. The
argument is an emitter of Code terms, not a semantic handler. No emitter for
all six substantive instruction classes is supplied by this module. -/
def recordTemplate {s : Ty} {r : RAM.Port}
    (emit : UniformNativeScheduleSemantics.Instruction → Code false r s s) :
    Code false r s s := sequence (UniformNativeScheduleSemantics.instructions.map emit)

theorem recordTemplate_chronology {s : Ty} {r : RAM.Port}
    (emit : UniformNativeScheduleSemantics.Instruction → Code false r s s)
    (h : Handler r) (x : s.T) :
    (Code.run (recordTemplate emit) h x).val=
      UniformNativeScheduleSemantics.instructions.foldl
        (fun y i=>(Code.run (emit i) h y).val) x := by
  rw [recordTemplate,sequence_value,List.foldl_map]

theorem actual_record_order (q : ℕ) :
    UniformNativeScheduleSemantics.instructions.map
      (UniformNativeScheduleSemantics.Instruction.record q)=
      UniformFixedNetworkScheduleMachine.scheduleRecords q :=
  UniformNativeScheduleSemantics.records_actual q

/-- Fuel is obtained from the actual input exponent by charged projections.
The internal recursive call returns the paired-channel tape once. A complete
compiler still has to provide the concrete base and body Code terms. -/
def descendTemplate (base : Prog false Node Result)
    (body : Code false ChildPort Node Result) : Prog false Node Result :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .id))
    (.descend base body)

theorem descendTemplate_run (base : Prog false Node Result)
    (body : Code false ChildPort Node Result) (k : ℕ) (I : ℂ)
    (v : Tape DFTModelAffine.Tagged.T) :
    run (descendTemplate base body) ((k,I),v)=
      (depthRun (base.run ()) (body.run) k ((k,I),v)).pay 7 k := by
  simp [descendTemplate,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

end
end ExactFourierCircuits.DFTModelClockControl
