import DFTModelSavingDirection

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPadding
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelCacheRecords.unit

theorem unitArgs_run (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    run unitArgs ((rest,(rawTape,old)),(i,node)) =
      ⟨(rawTape.look 1 0,rawTape.look 3 0+i),25,max 3 (rawTape.look 3 0+i),True⟩ := by
  simp [unitArgs,original,field,raw,index,DFTModelResidualCore.binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

def argumentsWith (U : Prog false (p w w) (Ty.a w)) : Prog false Iter Input := .fork
  (.comp original (.atom .fst)) (.fork (.comp unitArgs U) current)

theorem argumentsWith_run (U : Prog false (p w w) (Ty.a w)) (rest i : ℕ)
    (rawTape : Tape ℕ) (old node : Node.T) :
    run (argumentsWith U) ((rest,(rawTape,old)),(i,node)) =
      let result := run U (rawTape.look 1 0,rawTape.look 3 0+i)
      ⟨(rest,(result.val,node)),result.work+34,
       max (max 3 (rawTape.look 3 0+i)) result.peak,result.valid⟩ := by
  simp only [argumentsWith,DFTModelRecursiveScalarCore.fork_run,
    DFTModelRecursiveScalarCore.comp_run,original,current,
    DFTModelRecursiveScalarCore.atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [unitArgs_run]
  simp only [true_and,and_true,
    zero_max,max_zero]
  congr 1
  omega

theorem arguments_run (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    run paddingArgs ((rest,(rawTape,old)),(i,node)) =
      let result := run DFTModelCacheRecords.unit (rawTape.look 1 0,rawTape.look 3 0+i)
      ⟨(rest,(result.val,node)),result.work+34,
       max (max 3 (rawTape.look 3 0+i)) result.peak,result.valid⟩ :=
  argumentsWith_run DFTModelCacheRecords.unit rest i rawTape old node

theorem arguments_value (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run paddingArgs ((rest,(rawTape,old)),(i,node))).val=
      (rest,((run DFTModelCacheRecords.unit (rawTape.look 1 0,rawTape.look 3 0+i)).val,node)) := by
  exact congrArg Bill.val (arguments_run rest i rawTape old node)

theorem arguments_work (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run paddingArgs ((rest,(rawTape,old)),(i,node))).work=
      (run DFTModelCacheRecords.unit (rawTape.look 1 0,rawTape.look 3 0+i)).work+34 := by
  exact congrArg Bill.work (arguments_run rest i rawTape old node)

theorem arguments_valid (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run paddingArgs ((rest,(rawTape,old)),(i,node))).valid := by
  rw [arguments_run]
  exact DFTModelCacheRecords.unit_valid (rawTape.look 1 0) (rawTape.look 3 0+i)

theorem arguments_peak (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run paddingArgs ((rest,(rawTape,old)),(i,node))).peak=
      max (max 3 (rawTape.look 3 0+i))
        (run DFTModelCacheRecords.unit (rawTape.look 1 0,rawTape.look 3 0+i)).peak := by
  exact congrArg Bill.peak (arguments_run rest i rawTape old node)

def roleBillWith (U : Prog false (p w w) (Ty.a w)) (h : Handler Port)
    (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) : Bill Node.T :=
  (Code.run residual h (rest,((run U (rawTape.look 1 0,rawTape.look 3 0+i)).val,node))).pay
    ((run U (rawTape.look 1 0,rawTape.look 3 0+i)).work+36)
    (run (argumentsWith U) ((rest,(rawTape,old)),(i,node))).peak

def roleBill (h : Handler Port) (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) : Bill Node.T :=
  roleBillWith DFTModelCacheRecords.unit h rest i rawTape old node

theorem body_run (h : Handler Port) (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    Code.run paddingBody h ((rest,(rawTape,old)),(i,node))=roleBill h rest i rawTape old node := by
  rw [paddingBody,DFTModelSavingDirection.imported_comp_run paddingArgs residual h _
    (arguments_valid rest i rawTape old node)]
  rw [arguments_value,arguments_work]
  rfl

def steps (h : Handler Port) (rest : ℕ) (rawTape : Tape ℕ) (node : Node.T) (count : ℕ) : Bill Node.T :=
  Bill.steps node (fun i old => roleBill h rest i rawTape node old) count

theorem padding_run (h : Handler Port) (rest : ℕ) (rawTape : Tape ℕ) (node : Node.T) :
    Code.run padding h (rest,(rawTape,node))=
      (steps h rest rawTape node (rawTape.look 4 0)).pay 13 4 := by
  have body : (fun i old => Code.run paddingBody h ((rest,(rawTape,node)),(i,old)))=
      (fun i old => roleBill h rest i rawTape node old) := by
    funext i old
    exact body_run h rest i rawTape node old
  change (((run (field 4) (rest,(rawTape,node))).pay 1 0).pass (fun l =>
    ((run initial (rest,(rawTape,node))).pay 1 0).pass (fun old =>
      Bill.steps old (fun i z => Code.run paddingBody h ((rest,(rawTape,node)),(i,z))) l))).pay 1 0=_
  rw [body]
  simp only [field,raw,initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    steps,Ty.blank,true_and,zero_max,max_zero]
  congr 1 <;> omega

end
end ExactFourierCircuits.DFTModelSavingPadding
