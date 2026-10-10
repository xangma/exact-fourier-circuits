import DFTModelCacheMatchingNatProgram
import DFTModelRecursiveScalarCore

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section

theorem select_value {s t : Ty} (f : Prog false s w) (n : ℕ)
    (yes no : Prog false s t) (x : s.T) :
    (run (select f n yes no) x).val=
      if (run f x).val=n then (run yes x).val else (run no x).val := by
  have eq:((run f x).val-n)+(n-(run f x).val)=0 ↔ (run f x).val=n :=
    ModelEquivalenceInterpreter.distance_eq_zero_iff _ _
  simp only [select,eqTest,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,eq]
  split_ifs <;> rfl

theorem registerCell_value (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run registerCell ((r,z),j)).val=registerValue r z.len j := by
  simp only [registerCell,select_value,radix,count,permutationBase,widthsBase,
    markersBase,axisBase,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,registerValue,P,W,U,A]
  rfl

theorem endpoint_value (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run endpoint ((r,z),j)).val=endpointValue z j := by
  simp only [endpoint,select_value,rowOffset,row,rowIndex,nat,run,Code.run,
    Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,endpointValue,Ty.blank]
  rfl

theorem heapCell_value (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run heapCell ((r,z),j)).val=heapValue z j := by
  have h:=endpoint_value r z j
  simp only [heapCell,sourceTest,permutationBase,count,nat,run,Code.run,
    Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,heapValue]
  by_cases yes:j<3*z.len
  · simp only [yes,ite_true,Nat.one_ne_zero,ite_false]
    exact congrArg (fun t=>(1,t)) h
  · simp only [yes,ite_false,ite_true]

private theorem heap_arithmetic (r M : ℕ) :
    867+(3*M+r+r+r)=866+(3*M+r+r+r)+1 ∧
    max 3 (max M (867+(3*M+r+r+r)))=866+(3*M+r+r+r)+1 := by omega

theorem heapLength_run (r : ℕ) (z : Tape Row.T) :
    run heapLength (r,z)=⟨heapSize r z.len,23,
      max 867 (heapSize r z.len),True⟩ := by
  simp [heapLength,axisBase,markersBase,widthsBase,permutationBase,count,radix,
    nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    heapSize,wordBound,A,U,W,P]
  exact heap_arithmetic r z.len

theorem tab_run {s t : Ty} (n : Prog false s w) (f : Prog false (p s w) t) (x : s.T) :
    run (.tab n f) x=((run n x).pass (fun len=>Bill.tab len t.blank
      (fun j=>run f (x,j)))).pay 1 0 := rfl

theorem fork_value {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).val=((run f x).val,(run g x).val) := rfl

theorem tab_value_code {s t : Ty} (n : Prog false s w)
    (f : Prog false (p s w) t) (x : s.T) :
    (run (.tab n f) x).val=Tape.tab (run n x).val (fun j=>(run f (x,j)).val) := by
  rw [tab_run]
  exact ModelEquivalenceInterpreter.tab_value _ _ _

attribute [local irreducible] Code.run

theorem initialize_value (r : ℕ) (z : Tape Row.T) :
    (run initializeProgram (r,z)).val=initialValue r z := by
  unfold initializeProgram
  rw [fork_value,fork_value,tab_value_code,tab_value_code,heapLength_run]
  simp only [atom_run,Atom.run,Bill.word]
  exact congrArg (fun ts=>(0,ts)) (Prod.ext
    (congrArg (Tape.tab 862) (funext (registerCell_value r z)))
    (congrArg (Tape.tab (heapSize r z.len)) (funext (heapCell_value r z))))

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
