import DFTModelCacheSelectedCoefficientsNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] constants decode cell program setup finish

theorem cell_run (K C T P j : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) (cs : Tape ℂ) :
    run cell ((args K C T P b rs,cs),j)=
      (run decode (argument C T P (rs.look j Row.blank).2.2 b cs)).pay 36 0 := by
  simp [cell,decodeArgument,label,currentRow,rows,args,argument,
    run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem count_run (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) (cs : Tape ℂ) :
    run count (args K C T P b rs,cs)=⟨rs.len,7,rs.len,True⟩ := by
  simp [count,rows,args,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem finish_run (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) (cs : Tape ℂ) :
    run finish (args K C T P b rs,cs)=
      ((Bill.tab rs.len (p sc sc).blank (fun j=>run cell ((args K C T P b rs,cs),j))).pass
        (fun z=>Bill.one (args K C T P b rs,(cs,z)))).pay 11 rs.len := by
  rw [finish,fork_run,fork_run]
  simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  have hc:=count_run K C T P b rs cs
  change Code.run count () (args K C T P b rs,cs)=_ at hc
  rw [hc]
  simp only [max_zero,zero_max,true_and,and_true]
  congr 1 <;> omega

theorem setup_run (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) :
    run setup (args K C T P b rs)=
      ((run constants K).pass (fun cs=>Bill.one (args K C T P b rs,cs))).pay 5 0 := by
  simp [setup,rawHeight,args,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem program_run (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) :
    run program (args K C T P b rs)=
      ((run constants K).pass (fun cs=>
        (Bill.tab rs.len (p sc sc).blank (fun j=>run cell ((args K C T P b rs,cs),j))).pass
          (fun z=>Bill.one (args K C T P b rs,(cs,z))))).pay 18 rs.len := by
  rw [program,comp_run,setup_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [finish_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero,and_true]
  congr 1 <;> omega

theorem program_value (K C T P : ℕ) (b : Tape (ℂ × ℂ)) (rs : Tape Row.T) :
    (run program (args K C T P b rs)).val=
      (args K C T P b rs,(constantValues K,Tape.tab rs.len (fun j=>
        (run decode (argument C T P (rs.look j Row.blank).2.2 b (constantValues K))).val))) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one,constants_value]
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 2
  apply congrArg (Tape.tab rs.len)
  funext j
  simpa only [Bill.pay] using congrArg Bill.val (cell_run K C T P j b rs (constantValues K))

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
