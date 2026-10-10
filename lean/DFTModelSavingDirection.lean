import DFTModelSavingRecords
import DFTModelSavingDirectionData

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
open DFTModelSavingRecords
open scoped BigOperators
noncomputable section

attribute [local irreducible] DFTModelSavingResidual.program

def row (m i : ℕ) (rawTape : Tape ℕ) : Tape ℕ :=
  Tape.tab m (fun j => rawTape.look (8+m*i+j) 0)
def decoded (rest i : ℕ) (rawTape : Tape ℕ) (node : Node.T) :
    DFTModelSavingResidualSetup.Input.T :=
  ((rawTape.look 1 0,(rawTape.look 2 0,(rest,row (rawTape.look 2 0) i rawTape))),
    (rawTape.look 3 0,(rawTape.look 5 0,node)))

theorem bit_run (rest i j : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    run bit (((rest,(rawTape,old)),(i,node)),j)=
      ⟨rawTape.look (8+rawTape.look 2 0*i+j) 0,37,8+rawTape.look 2 0*i+j,True⟩ := by
  simp [bit,bitAddress,width,original,raw,field,index,DFTModelResidualCore.binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  omega

theorem bits_work (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run bits ((rest,(rawTape,old)),(i,node))).work=41*rawTape.look 2 0+12 := by
  change 9+(Bill.tab (rawTape.look 2 0) w.blank
    (fun j => run bit (((rest,(rawTape,old)),(i,node)),j))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run bit (((rest,(rawTape,old)),(i,node)),j)).work)=(fun _ => 37) := by
    funext j
    exact congrArg Bill.work (bit_run rest i j rawTape old node)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem bits_valid (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run bits ((rest,(rawTape,old)),(i,node))).valid := by
  have bv : (Bill.tab (rawTape.look 2 0) w.blank
      (fun j => run bit (((rest,(rawTape,old)),(i,node)),j))).valid := by
    apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    intro j _
    rw [bit_run]
    trivial
  simpa only [bits,width,original,field,raw,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,true_and,and_true] using bv

theorem bits_peak (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run bits ((rest,(rawTape,old)),(i,node))).peak≤8+rawTape.look 2 0*i+rawTape.look 2 0 := by
  change max (max 2 (Bill.tab (rawTape.look 2 0) w.blank
    (fun j => run bit (((rest,(rawTape,old)),(i,node)),j))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero,max_le_iff]
  refine ⟨by omega,by omega,Finset.sup_le ?_⟩
  intro j hj
  rw [bit_run]
  have h:=Finset.mem_range.mp hj
  dsimp only [Bill.peak]
  omega

attribute [local irreducible] bits

theorem arguments_value (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run directionArgs ((rest,(rawTape,old)),(i,node))).val=decoded rest i rawTape node :=
  directionArgs_value rest i rawTape old node

theorem arguments_work (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run directionArgs ((rest,(rawTape,old)),(i,node))).work=41*rawTape.look 2 0+60 := by
  have b:=bits_work rest i rawTape old node
  simp only [directionArgs,width,original,raw,field,current,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  dsimp only [run] at b
  omega

theorem arguments_valid (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run directionArgs ((rest,(rawTape,old)),(i,node))).valid := by
  have b:=bits_valid rest i rawTape old node
  simpa only [directionArgs,width,original,raw,field,current,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,and_true,true_and] using b

theorem arguments_peak (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    (run directionArgs ((rest,(rawTape,old)),(i,node))).peak≤8+rawTape.look 2 0*i+rawTape.look 2 0 := by
  have b:=bits_peak rest i rawTape old node
  simp only [directionArgs,width,original,raw,field,current,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  dsimp only [run] at b
  omega

def rowBill (h : Handler Port) (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) : Bill Node.T :=
  (Code.run DFTModelSavingResidual.program h (decoded rest i rawTape node)).pay
    (41*rawTape.look 2 0+62) (run directionArgs ((rest,(rawTape,old)),(i,node))).peak

theorem imported_comp_run {a b c : Ty} (f : Prog false a b)
    (g : Code false Port b c) (h : Handler Port) (x : a.T)
    (valid : (run f x).valid) :
    Code.run (.comp (.importClosed f) g) h x =
      (Code.run g h (run f x).val).pay ((run f x).work+2) (run f x).peak := by
  change (((run f x).pay 1 0).pass (Code.run g h)).pay 1 0=_
  simp only [Bill.pass,Bill.pay,valid,true_and,max_zero]
  congr 1
  · omega
  · exact max_comm _ _

theorem direction_run (h : Handler Port) (rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T) :
    Code.run direction h ((rest,(rawTape,old)),(i,node))=rowBill h rest i rawTape old node := by
  rw [direction,imported_comp_run directionArgs DFTModelSavingResidual.program h _
    (arguments_valid rest i rawTape old node)]
  rw [arguments_value,arguments_work]
  rfl

def steps (h : Handler Port) (rest : ℕ) (rawTape : Tape ℕ) (node : Node.T) (count : ℕ) : Bill Node.T :=
  Bill.steps node (fun i old => rowBill h rest i rawTape node old) count

theorem residual_run (h : Handler Port) (rest : ℕ) (rawTape : Tape ℕ) (node : Node.T) :
    Code.run residual h (rest,(rawTape,node))=
      (steps h rest rawTape node (rawTape.look 6 0)).pay 13 6 := by
  have body : (fun i old => Code.run direction h ((rest,(rawTape,node)),(i,old)))=
      (fun i old => rowBill h rest i rawTape node old) := by
    funext i old
    exact direction_run h rest i rawTape node old
  change (((run (field 6) (rest,(rawTape,node))).pay 1 0).pass (fun l =>
    ((run initial (rest,(rawTape,node))).pay 1 0).pass (fun old =>
      Bill.steps old (fun i z => Code.run direction h ((rest,(rawTape,node)),(i,z))) l))).pay 1 0=_
  rw [body]
  simp only [field,raw,initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    steps,Ty.blank,true_and,zero_max,max_zero]
  congr 1 <;> omega

end
end ExactFourierCircuits.DFTModelSavingDirection
