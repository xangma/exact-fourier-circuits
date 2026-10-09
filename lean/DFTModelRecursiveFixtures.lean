import DFTModelRecursiveScalarSource
import DFTModelRecursiveBinary
import DFTModelRecursiveMetadata

set_option autoImplicit false

/-! Small exact upstream-Code fixtures for the bounded recursive-body packet.
They certify the concrete scalar and binary-stage components, not a complete
saving-body compiler or its recursive execution. -/
namespace ExactFourierCircuits.DFTModelRecursiveFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine
noncomputable section
namespace Coefficient
open DFTModelRecursiveScalarCore

theorem negative_one : (run (coefficient (s:=w) (0 : Fin 5)) (0 : ℕ)).val=(-1 : ℂ) := by
  rw [coefficient_run]; rfl
theorem negative_half : (run (coefficient (s:=w) (1 : Fin 5)) (0 : ℕ)).val=(-1/2 : ℂ) := by
  rw [coefficient_run]; rfl
theorem zero : (run (coefficient (s:=w) (2 : Fin 5)) (0 : ℕ)).val=(0 : ℂ) := by
  rw [coefficient_run]; rfl
theorem half : (run (coefficient (s:=w) (3 : Fin 5)) (0 : ℕ)).val=(1/2 : ℂ) := by
  rw [coefficient_run]; rfl
theorem one : (run (coefficient (s:=w) (4 : Fin 5)) (0 : ℕ)).val=(1 : ℂ) := by
  rw [coefficient_run]; rfl
theorem all_valid (c : Fin 5) : (run (coefficient (s:=w) c) (0 : ℕ)).valid := by
  rw [coefficient_run]; trivial
theorem all_charged (c : Fin 5) : (run (coefficient (s:=w) c) (0 : ℕ)).work≤11 := by
  rw [coefficient_run]; exact coefficient_work_bound c
end Coefficient

namespace Scalar
open DFTModelRecursiveScalarSource

def data (i : Fin 2) (_j : Fin 2) : UniformMachine.Scalar :=
  if i.val=0 then ⟨1+Complex.I,false⟩ else ⟨-2+3*Complex.I,true⟩
def baseline (i : Fin 2) (_j : Fin 2) : UniformMachine.Scalar :=
  if i.val=0 then ⟨3,false⟩ else ⟨4,true⟩
def output (c : Fin 5) : Tape Tagged.T :=
  (run (DFTModelRecursiveScalar.program 2 0 1 c)
    ((1,Complex.I),paired data baseline)).val.2

theorem zero_still_depends : ((output 2).look 0 Tagged.blank).1=1 := by
  have h:=program_lookup (0 : Fin 2) (1 : Fin 2) (2 : Fin 5) (by omega)
    data baseline 1 Complex.I (0 : Fin 2) (0 : Fin 2)
  change (output 2).look 0 Tagged.blank=_ at h
  rw [h]
  rfl
theorem zero_offset : ((output 2).look 0 Tagged.blank).2.1=3 := by
  have h:=program_lookup (0 : Fin 2) (1 : Fin 2) (2 : Fin 5) (by omega)
    data baseline 1 Complex.I (0 : Fin 2) (0 : Fin 2)
  change (output 2).look 0 Tagged.blank=_ at h
  rw [h]
  change (3 : ℂ)+0*4=3
  ring
theorem nonreal_half_homogeneous :
    ((output 3).look 0 Tagged.blank).2.2=(-5+5*Complex.I/2 : ℂ) := by
  have h:=program_lookup (0 : Fin 2) (1 : Fin 2) (3 : Fin 5) (by omega)
    data baseline 1 Complex.I (0 : Fin 2) (0 : Fin 2)
  change (output 3).look 0 Tagged.blank=_ at h
  rw [h]
  change ((1 : ℂ)+Complex.I+(1/2)*(-2+3*Complex.I))-(3+(1/2)*4)=_
  ring
theorem source_retained (c : Fin 5) :
    (output c).look 3 Tagged.blank=encodePaired (data 1 1) (baseline 1 1) := by
  have h:=program_lookup (0 : Fin 2) (1 : Fin 2) c (by omega)
    data baseline 1 Complex.I (1 : Fin 2) (1 : Fin 2)
  change (output c).look 3 Tagged.blank=_ at h
  exact h
theorem length (c : Fin 5) : (output c).len=4 := by
  rw [output,DFTModelRecursiveScalar.program_value]
  rfl
theorem every_coefficient_exact (c : Fin 5) (i j : Fin 2) :
    (output c).look (i.val*2+j.val) Tagged.blank =
      encodePaired (Child.values 0 1 (UniformFixedCoefficientCodec.decode c) data i j)
        (Child.values 0 1 (UniformFixedCoefficientCodec.decode c) baseline i j) := by
  exact program_lookup (0 : Fin 2) (1 : Fin 2) c (by omega)
    data baseline 1 Complex.I i j
end Scalar

namespace Binary
open DFTModelRecursiveBinary

def dirty : Tape Tagged.T := Tape.tab 4
  (fun j => if j=0 then (1,(2,Complex.I)) else
    if j=1 then (0,(-3,0)) else (1,(0,-Complex.I)))
theorem zero_axes : (run program ((0,Complex.I),dirty)).val=dirty := by
  rw [program_value]; rfl
theorem zero_work : (run program ((0,Complex.I),dirty)).work=10 := by
  rw [program_work _ _ _ (by rfl)]; rfl
theorem two_work : (run program ((2,Complex.I),dirty)).work=1924 := by
  rw [program_work _ _ _ (by rfl)]; rfl
theorem stride_two : (states Complex.I dirty 2).1=4 := by
  rw [states_stride]; rfl
theorem two_length : (run program ((2,Complex.I),dirty)).val.len=4 := by
  rw [program_len _ _ _ (by rfl)]; rfl
theorem two_valid : (run program ((2,Complex.I),dirty)).valid :=
  program_valid _ _ _
end Binary

namespace Metadata
open DFTModelRecursiveMetadata

theorem empty : (run (literalTape (s:=w) []) 9).val.len=0 := by
  rw [literalTape_value]; rfl
theorem empty_work : (run (literalTape (s:=w) []) 9).work=4 := by rfl
theorem zero_literal : (run (literalTape (s:=w) [0,7,2]) 9).val.look 0 99=0 := by
  rw [literalTape_value]; rfl
theorem middle_literal : (run (literalTape (s:=w) [0,7,2]) 9).val.look 1 99=7 := by
  rw [literalTape_value]; rfl
theorem outside_default : (run (literalTape (s:=w) [0,7,2]) 9).val.look 3 99=99 := by
  rw [literalTape_value]; rfl
theorem cell_outside_zero : (run (literalCell [0,7,2]) 4).val=0 := by
  rw [literalCell_value]; rfl
theorem valid : (run (literalTape (s:=w) [0,7,2]) 9).valid := literalTape_valid _ _
end Metadata
end
end ExactFourierCircuits.DFTModelRecursiveFixtures
