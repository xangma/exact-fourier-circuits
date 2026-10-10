import DFTModelResidualCore
import DFTModelAffinePaired
import UniformRoleInputMachine

set_option autoImplicit false

/-! Paper §5.3, the three-transform reduction: actual outer stages 8 and 12
load data in role 0, the alpha-permuted prepared kernel in role 1, and exact
prepared zeros in all remaining roles. The alpha table and the two input
banks are explicit produced entry values; no clock or cache producer is
assumed implemented by this module. -/
namespace ExactFourierCircuits.DFTModelOuterAssemblyRole
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Input := p (p w w) (p (Ty.a w) (p (Ty.a Datum) (Ty.a sc)))
abbrev CellInput := p Input w

def roles : Prog false Input w := .comp (.atom .fst) (.atom .fst)
def volume : Prog false Input w := .comp (.atom .fst) (.atom .snd)
def alpha : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .fst)
def data : Prog false Input (Ty.a Datum) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def kernel : Prog false Input (Ty.a sc) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def size : Prog false Input w := binary .mul roles volume
def role : Prog false CellInput w :=
  binary .div (.atom .snd) (.comp (.atom .fst) volume)
def coordinate : Prog false CellInput w :=
  binary .mod (.atom .snd) (.comp (.atom .fst) volume)
def dataRead : Prog false CellInput Datum :=
  .comp (.fork (.comp (.atom .fst) data) coordinate) (.atom .look)
def alphaRead : Prog false CellInput w :=
  .comp (.fork (.comp (.atom .fst) alpha) coordinate) (.atom .look)
def kernelRead : Prog false CellInput sc :=
  .comp (.fork (.comp (.atom .fst) kernel) alphaRead) (.atom .look)
def preparedKernel : Prog false CellInput Datum :=
  .fork (.atom (.lit 0)) (.comp kernelRead DFTModelAffine.prepared)
def zero : Prog false CellInput Datum :=
  .fork (.atom (.lit 0)) (.fork (.atom (.cz .scalar)) (.atom (.cz .left)))
def cell : Prog false CellInput Datum :=
  .ifz role dataRead
    (.ifz (binary .sub role (.atom (.lit 1))) preparedKernel zero)
def program : Prog false Input (Ty.a Datum) := .tab size cell

def input (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) : Input.T :=
  ((W,V),(a,(x,k)))
def value (V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) : Datum.T :=
  if j/V=0 then x.look (j%V) (0,(0,0))
  else if j/V=1 then (0,(k.look (a.look (j%V) 0) 0,0))
  else (0,(0,0))

theorem size_run (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    run size (input W V a x k) = ⟨W*V,9,W*V,True⟩ := by
  simp [size,roles,volume,input,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem cell_run (W V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    run cell (input W V a x k,j) =
      if j/V=0 then ⟨x.look (j%V) (0,(0,0)),29,max (j/V) (j%V),True⟩
      else if j/V=1 then ⟨(0,(k.look (a.look (j%V) 0) 0,0)),57,
        max (j/V) (max 1 (j%V)),True⟩
      else ⟨(0,(0,0)),29,max (j/V) 1,True⟩ := by
  by_cases h0 : j/V=0
  · simp [cell,role,coordinate,dataRead,data,volume,alphaRead,alpha,
      preparedKernel,kernelRead,kernel,zero,input,binary,
      DFTModelAffine.prepared,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,h0,Ty.blank]
  · by_cases h1 : j/V=1
    · simp [cell,role,coordinate,dataRead,data,volume,alphaRead,alpha,
        preparedKernel,kernelRead,kernel,zero,input,binary,
        DFTModelAffine.prepared,run,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,h1,Ty.blank]
    · have hs : j/V-1≠0 := by
        intro h
        exact h1 (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp h)
          (Nat.one_le_iff_ne_zero.mpr h0))
      simp [cell,role,coordinate,dataRead,data,volume,alphaRead,alpha,
        preparedKernel,kernelRead,kernel,zero,input,binary,
        DFTModelAffine.prepared,run,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,h0,h1,hs]

theorem cell_value (W V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run cell (input W V a x k,j)).val = value V j a x k := by
  rw [cell_run]
  split <;> simp_all [value]
  split <;> simp_all

theorem cell_work (W V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run cell (input W V a x k,j)).work ≤ 57 := by
  rw [cell_run]
  split <;> simp_all
  split <;> simp

theorem cell_valid (W V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run cell (input W V a x k,j)).valid := by
  rw [cell_run]
  split <;> simp_all
  split <;> trivial

theorem cell_peak (W V j : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run cell (input W V a x k,j)).peak ≤ max (max (j/V) (j%V)) 1 := by
  rw [cell_run]
  split
  · dsimp only [Bill.peak]; omega
  · split <;> dsimp only [Bill.peak] <;> omega

theorem program_value (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run program (input W V a x k)).val = Tape.tab (W*V) (fun j => value V j a x k) := by
  change (Bill.tab (run size _).val Datum.blank
    (fun j => run cell (input W V a x k,j))).val = _
  rw [size_run,ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (W*V)) (funext (fun j => cell_value W V j a x k))

theorem program_valid (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run program (input W V a x k)).valid := by
  change (run size _).valid ∧ (Bill.tab (run size _).val Datum.blank
    (fun j => run cell (input W V a x k,j))).valid
  rw [size_run]
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _ => cell_valid W V j a x k)⟩

theorem program_work (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run program (input W V a x k)).work ≤ 61*(W*V)+12 := by
  change (run size _).work+(Bill.tab (run size _).val Datum.blank
    (fun j => run cell (input W V a x k,j))).work+1 ≤ _
  rw [size_run,ModelEquivalenceInterpreter.tab_work]
  dsimp only [Bill.work,Bill.val]
  have h : (∑j ∈ Finset.range (W*V), (run cell (input W V a x k,j)).work) ≤ 57*(W*V) := by
    calc
      _ ≤ ∑_j ∈ Finset.range (W*V), 57 :=
        Finset.sum_le_sum (fun j _ => cell_work W V j a x k)
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem program_peak (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ)
    (roles : 2≤W) :
    (run program (input W V a x k)).peak ≤ W*V := by
  change max (max (run size _).peak (Bill.tab (run size _).val Datum.blank
    (fun j => run cell (input W V a x k,j))).peak) 0 ≤ _
  rw [size_run,ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,max_le_iff,le_refl,true_and]
  apply Finset.sup_le
  intro j hj
  have hj' : j<W*V := Finset.mem_range.mp hj
  have vp : 0<V := by
    by_contra h
    have hv : V=0 := by omega
    rw [hv,Nat.mul_zero] at hj'
    omega
  have d : j/V≤j := Nat.div_le_self _ _
  have m : j%V<V := Nat.mod_lt _ vp
  have v : V≤W*V := by nlinarith
  exact (cell_peak W V j a x k).trans (by omega)

theorem work_preserved (W V : ℕ) (a : Tape ℕ) (x : Tape Datum.T) (k : Tape ℂ) :
    (run program (input W V a x k)).work ≤ 13*(5*(W*V)+16*V+24) := by
  have h := program_work W V a x k
  omega

end
end ExactFourierCircuits.DFTModelOuterAssemblyRole
