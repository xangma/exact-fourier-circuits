import DFTModelCacheDirectChronologyEvaluation

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDirectLeaf
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology
open scoped BigOperators
noncomputable section

/-- Raw width, physical offset, start time, coefficient base. -/
abbrev Input := p w (p w (p w w))
abbrev StampInput := p Input Record4
abbrev TabInput := p (p Input (Ty.a Record4)) w

def argV : Prog false StampInput w := .comp (.atom .fst) (.atom .fst)
def argO : Prog false StampInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def argT : Prog false StampInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def kind : Prog false StampInput w := .comp (.atom .snd) (.atom .fst)
def dest : Prog false StampInput w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def source : Prog false StampInput w :=
  .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def targetIndex : Prog false StampInput w := integer .sub dest argO
def rowTime : Prog false StampInput w :=
  integer .add argT
    (integer .add (integer .sub (integer .sub argV (.atom (.lit 1))) targetIndex)
      (integer .mul (.atom (.lit 14))
        (integer .sub (integer .mul argV (integer .sub argV (.atom (.lit 1))))
          (integer .mul targetIndex (integer .add targetIndex (.atom (.lit 1)))))))
def stampTime : Prog false StampInput w :=
  .ifz kind rowTime
    (integer .add rowTime (integer .add (.atom (.lit 1))
      (integer .mul (.atom (.lit 28)) (integer .sub source argO))))
def nativeKind : Prog false StampInput w :=
  .ifz kind (.atom (.lit 1)) (.atom (.lit 0))
def stamp : Prog false StampInput Event :=
  .fork stampTime (.fork nativeKind (.atom .snd))
def readRecord : Prog false TabInput Record4 :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def cell : Prog false TabInput Event :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) readRecord) stamp
def annotate : Prog false (p Input (Ty.a Record4)) (Ty.a Event) :=
  .tab (.comp (.atom .snd) (.atom .len)) cell
def forwardArgs : Prog false Input DFTModelCacheDirectLeaf.Input :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.atom .fst))
    (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
/-- One actual forward producer call, followed by charged record tabulation. -/
def program : Prog false Input (Ty.a Event) :=
  .comp (.fork (.atom .id) (.comp forwardArgs forward)) annotate

theorem stamp_value (v o t K : ℕ) (q : Record) :
    (run stamp ((v,(o,(t,K))),encode q)).val=event v o t q := by
  simp only [stamp,fork_value,stampTime,ifz_value,rowTime,integer_value,
    nativeKind,targetIndex,integer_value]
  by_cases h:q.kind=0 <;>
    simp [argV,argO,argT,kind,dest,source,event,timestamp,rowOffset,cacheKind,encode,run,Code.run,
      Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,h]

theorem stamp_valid (v o t K : ℕ) (q : Record) :
    (run stamp ((v,(o,(t,K))),encode q)).valid := by
  simp only [stamp,fork_valid,stampTime,ifz_valid,rowTime,integer_valid,
    nativeKind,targetIndex,integer_valid]
  by_cases h:q.kind=0 <;>
    simp [argV,argO,argT,kind,dest,source,encode,run,Code.run,Atom.run,
      Bill.word,Bill.one,Bill.pass,Bill.pay,h]

theorem stamp_work (v o t K : ℕ) (q : Record) :
    (run stamp ((v,(o,(t,K))),encode q)).work≤300 := by
  simp only [stamp,fork_work,stampTime,ifz_work,rowTime,integer_work,
    nativeKind,targetIndex,integer_work]
  by_cases h:q.kind=0 <;>
    simp [argV,argO,argT,kind,dest,source,encode,run,Code.run,Atom.run,
      Bill.word,Bill.one,Bill.pass,Bill.pay,h]

theorem cell_run (v o t K : ℕ) (qs : Tape Record4.T) (j : ℕ) :
    run cell (((v,(o,(t,K))),qs),j)=
      (run stamp ((v,(o,(t,K))),qs.look j Record4.blank)).pay 12 0 := by
  simp [cell,readRecord,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem annotate_run (a : Input.T) (qs : Tape Record4.T) :
    run annotate (a,qs)=
      (Bill.tab qs.len Event.blank (fun j=>run cell ((a,qs),j))).pay 4 qs.len := by
  simp [annotate,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] forward annotate

theorem forwardArgs_run (v o t K : ℕ) :
    run forwardArgs (v,(o,(t,K)))=⟨(v,(o,K)),11,0,True⟩ := by
  simp [forwardArgs,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem program_run (v o t K : ℕ) :
    run program (v,(o,(t,K)))=
      ((run forward (v,(o,K))).pass
        (fun qs=>run annotate ((v,(o,(t,K))),qs))).pay 15 0 := by
  change (((Bill.one (v,(o,(t,K)))).pass (fun a=>
    (((run forwardArgs (v,(o,(t,K)))).pass (fun f=>run forward f)).pay 1 0).pass
      (fun qs=>Bill.one (a,qs)))).pass (fun x=>run annotate x)).pay 1 0 = _
  rw [forwardArgs_run]
  simp [Bill.one,Bill.pass,Bill.pay]
  omega

end
end ExactFourierCircuits.DFTModelCacheDirectChronology
