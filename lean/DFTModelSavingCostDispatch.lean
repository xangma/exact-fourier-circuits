import DFTModelSavingCostRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

theorem code_ifz_work {s t : Ty} (test : Code false ChildPort s w)
    (f g : Code false ChildPort s t) (h : Handler ChildPort) (x : s.T) :
    (Code.run (.ifz test f g) h x).work=(Code.run test h x).work+
      (if (Code.run test h x).val=0 then (Code.run f h x).work else (Code.run g h x).work)+1 := by
  change (Code.run test h x).work+
    (if (Code.run test h x).val=0 then Code.run f h x else Code.run g h x).work+1=_
  split_ifs <;> rfl

theorem code_import_work {s t : Ty} (f : Prog false s t) (h : Handler ChildPort) (x : s.T) :
    (Code.run (.importClosed f) h x).work=(run f x).work+1 := rfl

theorem code_import_value {s t : Ty} (f : Prog false s t) (h : Handler ChildPort) (x : s.T) :
    (Code.run (.importClosed f) h x).val=(run f x).val := rfl

theorem code_comp_work {s t u : Ty} (f : Code false ChildPort s t)
    (g : Code false ChildPort t u) (h : Handler ChildPort) (x : s.T) :
    (Code.run (.comp f g) h x).work=(Code.run f h x).work+
      (Code.run g h (Code.run f h x).val).work+1 := rfl

theorem record_field_run (j r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run (DFTModelSavingRecords.field j) (r,(raw,node))=⟨raw.look j 0,7,j,True⟩ := by
  simp [DFTModelSavingRecords.field,DFTModelSavingRecords.raw,run,Code.run,
    Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem opcodeTest_work (j r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (run (DFTModelSavingRecords.opcodeTest j) (r,(raw,node))).work=11 := rfl

theorem opcodeTest_value (j r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (run (DFTModelSavingRecords.opcodeTest j) (r,(raw,node))).val=raw.look 0 0-j := rfl

theorem scalarArgs_run (r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run DFTModelSavingRecords.scalarArgs (r,(raw,node))=⟨(raw,node),7,0,True⟩ := by
  simp [DFTModelSavingRecords.scalarArgs,
    DFTModelSavingRecords.raw,DFTModelSavingRecords.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem exchangeArgs_run (r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run DFTModelSavingRecords.exchangeArgs (r,(raw,node))=⟨(raw,node),7,0,True⟩ := by
  simp [DFTModelSavingRecords.exchangeArgs,
    DFTModelSavingRecords.raw,DFTModelSavingRecords.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem initial_run (r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run DFTModelSavingRecords.initial (r,(raw,node))=⟨node,3,0,True⟩ := by
  simp [DFTModelSavingRecords.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem field_ifz_work {t : Ty} (j r : ℕ) (raw : Tape ℕ) (node : Node.T)
    (f g : Code false ChildPort DFTModelSavingRecords.Input t) (h : Handler ChildPort) :
    (Code.run (.ifz (.importClosed (DFTModelSavingRecords.field j)) f g) h (r,(raw,node))).work=
      9+(if raw.look j 0=0 then (Code.run f h (r,(raw,node))).work else (Code.run g h (r,(raw,node))).work) := by
  change ((((run (DFTModelSavingRecords.field j) (r,(raw,node))).pay 1 0).pass
    (fun a=>if a=0 then Code.run f h (r,(raw,node)) else Code.run g h (r,(raw,node)))).pay 1 0).work=_
  rw [record_field_run]
  by_cases hc:raw.look j 0=0 <;> simp [Bill.pass,Bill.pay,hc] <;> omega

theorem opcode_ifz_work {t : Ty} (j r : ℕ) (raw : Tape ℕ) (node : Node.T)
    (f g : Code false ChildPort DFTModelSavingRecords.Input t) (h : Handler ChildPort) :
    (Code.run (.ifz (.importClosed (DFTModelSavingRecords.opcodeTest j)) f g) h (r,(raw,node))).work=
      13+(if raw.look 0 0-j=0 then (Code.run f h (r,(raw,node))).work else (Code.run g h (r,(raw,node))).work) := by
  simp only [DFTModelSavingRecords.opcodeTest,DFTModelResidualCore.binary,Code.run,
    DFTModelSavingRecords.field,DFTModelSavingRecords.raw,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  by_cases hc:raw.look 0 0-j=0 <;> simp [hc] <;> omega

/-- Exact billing of the real opcode tests and the selected concrete handler.
Only the selected branch is charged; in particular residual and padding
recursive calls are never both added. -/
theorem dispatch_work (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work=
      if raw.look 0 0=0 then
        (Code.run DFTModelSavingRecords.residual h (rest,(raw,node))).work+9
      else if raw.look 0 0-1=0 then
        (run (DFTModelSavingScalar.program R) (raw,node)).work+32
      else if raw.look 0 0-2=0 then 39
      else if raw.look 0 0-3=0 then
        (run (DFTModelSavingY.program R) (rest,(raw,node))).work+49
      else if raw.look 0 0-4=0 then
        (run (DFTModelRecursiveExchange.program R) (raw,node)).work+71
      else if raw.look 0 0-5=0 then
        (Code.run DFTModelSavingRecords.padding h (rest,(raw,node))).work+74
      else 78 := by
  rw [DFTModelSavingRecords.dispatch,field_ifz_work]
  rw [opcode_ifz_work,opcode_ifz_work,opcode_ifz_work,opcode_ifz_work,opcode_ifz_work]
  simp only [code_comp_work,code_import_work,code_import_value]
  rw [scalarArgs_run,exchangeArgs_run,initial_run]
  dsimp only [Bill.val,Bill.work]
  split_ifs <;> omega

end
end ExactFourierCircuits.DFTModelSavingCost
