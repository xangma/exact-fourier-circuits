import DFTModelResidual

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem xor_zero : (run DFTModelResidualXor.program (0,(0,0))).val=0 := by rfl
theorem xor_one : (run DFTModelResidualXor.program (1,(1,0))).val=1 := by rfl
theorem xor_cancel : (run DFTModelResidualXor.program (3,(5,5))).val=0 := by rfl
theorem xor_mixed : (run DFTModelResidualXor.program (3,(5,3))).val=6 := by rfl
theorem xor_work : (run DFTModelResidualXor.program (3,(5,3))).work=270 := by rfl
theorem xor_peak : (run DFTModelResidualXor.program (3,(5,3))).peak=8 := by rfl
theorem xor_valid : (run DFTModelResidualXor.program (3,(5,3))).valid := by trivial

theorem table_zero_length : (run DFTModelResidualTable.program 0).val.len=1 := by rfl
theorem table_two_length : (run DFTModelResidualTable.program 2).val.len=16 := by rfl
theorem table_entry : (run DFTModelResidualTable.program 2).val.look 11 0=1 := by rfl
theorem table_work : (run DFTModelResidualTable.program 2).work=3359 := by rfl
theorem table_peak_bound : (run DFTModelResidualTable.program 2).peak≤22 := by
  simpa using DFTModelResidualTable.program_peak 2

theorem block_xor : (run DFTModelResidualBlockXor.program
    (DFTModelResidualBlockXor.input 2 2 13 6)).val=11 := by rfl
theorem block_work : (run DFTModelResidualBlockXor.program
    (DFTModelResidualBlockXor.input 2 2 13 6)).work=256 := by rfl

def images : Tape ℕ := Tape.tab 3 (fun i=>if i=0 then 5 else if i=1 then 2 else 4)
def addresses : Tape ℕ :=
  (run DFTModelResidualAddresses.program (3,DFTModelResidualAddresses.parameters 1 3 images)).val

theorem address_length : addresses.len=8 := by rfl
theorem address_zero : addresses.look 0 99=0 := by rfl
theorem address_first : addresses.look 1 99=5 := by rfl
theorem address_second : addresses.look 2 99=2 := by rfl
theorem address_third : addresses.look 3 99=7 := by rfl
theorem address_last : addresses.look 7 99=3 := by rfl

/-- A non-involutive 3-cycle; scatter must differ from gather. -/
def cycle : Tape ℕ := Tape.tab 3 (fun j=>if j=0 then 1 else if j=1 then 2 else 0)
def dirty : Tape DFTModelAffine.Tagged.T := Tape.tab 3
  (fun j=>if j=0 then DFTModelAffine.tagged true 2 3 else if j=1 then
    DFTModelAffine.tagged false 7 0 else DFTModelAffine.tagged true (-4) Complex.I)
def gathered := (run (DFTModelResidualMovement.gather DFTModelAffine.Tagged) (cycle,dirty)).val
def scattered := (run (DFTModelResidualMovement.scatter DFTModelAffine.Tagged) (cycle,dirty)).val

theorem gather_tag : (gathered.look 0 DFTModelAffine.Tagged.blank).1=0 := by rfl
theorem gather_offset : (gathered.look 0 DFTModelAffine.Tagged.blank).2.1=7 := by rfl
theorem gather_linear : (gathered.look 1 DFTModelAffine.Tagged.blank).2.2=Complex.I := by rfl
theorem scatter_tag : (scattered.look 0 DFTModelAffine.Tagged.blank).1=1 := by rfl
theorem scatter_offset : (scattered.look 0 DFTModelAffine.Tagged.blank).2.1=(-4:ℂ) := by rfl
theorem scatter_linear : (scattered.look 0 DFTModelAffine.Tagged.blank).2.2=Complex.I := by rfl
theorem scatter_inverse_coordinate : scattered.look 1 DFTModelAffine.Tagged.blank=
    dirty.look 0 DFTModelAffine.Tagged.blank := by rfl
theorem gather_scatter_distinct : gathered.look 0 DFTModelAffine.Tagged.blank≠
    scattered.look 0 DFTModelAffine.Tagged.blank := by
  intro h
  have tags:=congrArg Prod.fst h
  change (0:ℕ)=1 at tags
  omega

theorem gather_work :
    (run (DFTModelResidualMovement.gather DFTModelAffine.Tagged) (cycle,dirty)).work=57 := by rfl
theorem scatter_work :
    (run (DFTModelResidualMovement.scatter DFTModelAffine.Tagged) (cycle,dirty)).work=63 := by rfl
theorem gather_peak :
    (run (DFTModelResidualMovement.gather DFTModelAffine.Tagged) (cycle,dirty)).peak=3 := by rfl
theorem scatter_peak :
    (run (DFTModelResidualMovement.scatter DFTModelAffine.Tagged) (cycle,dirty)).peak=3 := by rfl

def empty : Tape ℕ := Tape.empty ℕ
theorem gather_empty : (run (DFTModelResidualMovement.gather w) (empty,empty)).val.len=0 := by rfl
theorem scatter_empty : (run (DFTModelResidualMovement.scatter w) (empty,empty)).val.len=0 := by rfl
theorem gather_empty_work : (run (DFTModelResidualMovement.gather w) (empty,empty)).work=6 := by rfl
theorem scatter_empty_work : (run (DFTModelResidualMovement.scatter w) (empty,empty)).work=9 := by rfl

end
end ExactFourierCircuits.DFTModelResidualFixtures
