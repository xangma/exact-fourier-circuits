import DFTModelCacheDirectLeafRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev BodyInput := p Input (p w (Ty.a Record4))
def zeroRecord {s : Ty} : Prog false s Record4 :=
  .fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.fork (.atom (.lit 0)) (.atom (.lit 0))))
def empty : Prog false Input (Ty.a Record4) := .tab (.atom (.lit 0)) zeroRecord
def bodyArgument : Prog false BodyInput RowInput :=
  .fork (.comp (.atom .fst) (.atom .snd)) (.comp (.atom .snd) (.atom .fst))
def body : Prog false BodyInput (Ty.a Record4) :=
  .comp (.fork (.comp bodyArgument row) (.comp (.atom .snd) (.atom .snd)))
    (DFTModelCacheTraversal.append Record4)
/-- Ascending loop indices prepend a row, yielding descending target order. -/
def forward : Prog false Input (Ty.a Record4) := .loop (.atom .fst) empty body

attribute [local irreducible] row DFTModelCacheTraversal.append

theorem empty_run (v o K : ℕ) :
    run empty (v,(o,K))=⟨DFTModelCacheTraversal.ofList [],4,0,True⟩ := by
  simp [empty,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay,Bill.tab,Bill.sow,Bill.steps]
  apply DFTModelCacheTraversal.tape_ext (Tape.tab 0 (fun _=>Record4.blank))
    (DFTModelCacheTraversal.ofList ([] : List Record4.T)) Record4.blank rfl
  intro j hj; exact False.elim (Nat.not_lt_zero j hj)

theorem body_run (v o K i : ℕ) (old : Tape Record4.T) :
    run body ((v,(o,K)),(i,old))=
      ((run row ((o,K),i)).pass (fun rs=>run (DFTModelCacheTraversal.append Record4) (rs,old))).pay 13 0 := by
  simp [body,bodyArgument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

def ticks (v o K j : ℕ) : Bill (Tape Record4.T) :=
  Bill.steps (run empty (v,(o,K))).val (fun i old=>run body ((v,(o,K)),(i,old))) j

theorem ticks_value (v o K j : ℕ) :
    (ticks v o K j).val=DFTModelCacheTraversal.ofList ((records o K j).map encode) := by
  induction j with
  | zero=>exact congrArg Bill.val (empty_run v o K)
  | succ j ih=>
    change (run body ((v,(o,K)),(j,(ticks v o K j).val))).val=_
    rw [body_run]
    change (run (DFTModelCacheTraversal.append Record4) ((run row ((o,K),j)).val,
      (ticks v o K j).val)).val=_
    rw [row_value,ih,DFTModelCacheTraversal.append_value,DFTModelCacheTraversal.append_lists]
    simp only [records,List.map_append]

theorem forward_run (v o K : ℕ) :
    run forward (v,(o,K))=(ticks v o K v).pay 6 0 := by
  change ((Bill.one v).pass (fun j=>(run empty (v,(o,K))).pass
    (fun old=>Bill.steps old (fun i a=>run body ((v,(o,K)),(i,a))) j))).pay 1 0=_
  rw[empty_run]
  unfold ticks
  rw[empty_run]
  simp [Bill.pass,Bill.pay,Bill.one]
  ac_rfl

theorem forward_value (v o K : ℕ) :
    (run forward (v,(o,K))).val=
      DFTModelCacheTraversal.ofList ((UniformTransposeDescriptorMachine.leafRecords v o K).map encode) := by
  rw[forward_run]
  exact (ticks_value v o K v).trans (by rw[records_native])

theorem ticks_valid (v o K j : ℕ) : (ticks v o K j).valid := by
  induction j with
  | zero=>trivial
  | succ j ih=>
    change (ticks v o K j).valid ∧ (run body ((v,(o,K)),(j,_))).valid
    rw[body_run]
    exact ⟨ih,row_valid _ _ _,DFTModelCacheTraversal.append_valid _ _ _⟩

theorem forward_valid (v o K : ℕ) : (run forward (v,(o,K))).valid := by
  rw[forward_run];exact ticks_valid _ _ _ _

theorem ticks_work (v o K j : ℕ) :
    (ticks v o K j).work≤200*(j+1)^3 := by
  induction j with
  | zero=>change 1≤_;omega
  | succ j ih=>
    have rwk:=row_work o K j
    have aw:=DFTModelCacheTraversal.append_work Record4
      (run row ((o,K),j)).val (ticks v o K j).val
    have lenRow:(run row ((o,K),j)).val.len=j+1 := by
      rw[row_value];simp[rowRecords,DFTModelCacheTraversal.ofList]
    have lenOld:(ticks v o K j).val.len≤(j+1)^2 := by
      rw[ticks_value];simpa[DFTModelCacheTraversal.ofList] using records_length_bound j o K
    change (ticks v o K j).work+(run body ((v,(o,K)),(j,_))).work+1≤_
    rw[body_run]
    change (ticks v o K j).work+((run row ((o,K),j)).work+
      (run (DFTModelCacheTraversal.append Record4) ((run row ((o,K),j)).val,_)).work+13)+1≤_
    rw[lenRow] at aw
    have m:=Nat.mul_le_mul_left 29 (Nat.add_le_add_left lenOld (j+1))
    dsimp only [ticks] at *
    nlinarith

theorem forward_work (v o K : ℕ) : (run forward (v,(o,K))).work≤200*(v+1)^3+6 := by
  rw[forward_run];exact Nat.add_le_add_right (ticks_work _ _ _ _) 6

theorem ticks_peak (v o K j : ℕ) :
    (ticks v o K j).peak≤o+K+2*(j+1)^2 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have rp:=row_peak o K j
    have ap:=DFTModelCacheTraversal.append_peak Record4
      (run row ((o,K),j)).val (ticks v o K j).val
    have lenRow:(run row ((o,K),j)).val.len=j+1 := by
      rw[row_value];simp[rowRecords,DFTModelCacheTraversal.ofList]
    have lenOld:(ticks v o K j).val.len≤(j+1)^2 := by
      rw[ticks_value];simpa[DFTModelCacheTraversal.ofList] using records_length_bound j o K
    change max (max (ticks v o K j).peak (run body ((v,(o,K)),(j,_))).peak) (j+1)≤_
    rw[body_run]
    change max (max (ticks v o K j).peak
      (max (max (run row ((o,K),j)).peak
        (run (DFTModelCacheTraversal.append Record4) ((run row ((o,K),j)).val,_)).peak) 0)) (j+1)≤_
    rw[lenRow] at ap
    dsimp only [ticks] at *
    simp only [max_zero,max_le_iff]
    constructor
    · constructor
      · nlinarith
      · constructor
        · nlinarith
        · nlinarith
    · nlinarith

theorem forward_peak (v o K : ℕ) :
    (run forward (v,(o,K))).peak≤o+K+2*(v+1)^2 := by
  rw[forward_run];simpa[Bill.pay] using ticks_peak v o K v

end
end ExactFourierCircuits.DFTModelCacheDirectLeaf
