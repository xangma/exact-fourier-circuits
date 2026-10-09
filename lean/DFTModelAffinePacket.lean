import DFTModelAffinePaired

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

theorem represented_form {z : Tagged.T} {a : Scalar} (rep : Represents z a) :
    z = tagged a.dependent z.2.1 z.2.2 := by
  exact Prod.ext rep.1 rfl

theorem field_packet (op : FieldOp) (a b result : Scalar) (za zb : Tagged.T)
    (ra : Represents za a) (rb : Represents zb b)
    (success : evalField op a b = some result) :
    (run (field op) (za,zb)).valid ∧ Represents (run (field op) (za,zb)).val result ∧
    (run (field op) (za,zb)).work ≤ 39 ∧ (run (field op) (za,zb)).peak ≤ 1 := by
  have fa := represented_form ra
  have fb := represented_form rb
  have ra' : Represents (tagged a.dependent za.2.1 za.2.2) a := by rw [←fa]; exact ra
  have rb' : Represents (tagged b.dependent zb.2.1 zb.2.2) b := by rw [←fb]; exact rb
  have h := field_success op a b result za.2.1 za.2.2 zb.2.1 zb.2.2 ra' rb' success
  have budget := field_budget op a.dependent b.dependent za.2.1 za.2.2 zb.2.1 zb.2.2
  simpa only [←fa,←fb] using And.intro h.1 (And.intro h.2 budget)

/-- The zero-input primitive run is produced from the actual successful one. -/
theorem paired_field_simulation (op : FieldOp) (a b a0 b0 result : Scalar)
    (sameA : ScalarMatch a a0) (sameB : ScalarMatch b b0)
    (actual : evalField op a b = some result) :
    ∃ result0, evalField op a0 b0 = some result0 ∧
      (run (field op) (encodePaired a a0,encodePaired b b0)).valid ∧
      (run (field op) (encodePaired a a0,encodePaired b b0)).val =
        encodePaired result result0 ∧ ScalarMatch result result0 ∧
      (run (field op) (encodePaired a a0,encodePaired b b0)).work ≤ 39 ∧
      (run (field op) (encodePaired a a0,encodePaired b b0)).peak ≤ 1 := by
  obtain ⟨result0,baseline,_same⟩ := evalField_match sameA sameB actual
  exact ⟨result0,baseline,paired_field_success op a b a0 b0 result result0
    sameA sameB actual baseline⟩

/-- This embeds the closed primitive in any recursive caller port. -/
def fieldAt {r : Port} (op : FieldOp) : Code false r BinaryInput Tagged :=
  .importClosed (field op)

theorem fieldAt_run {r : Port} (op : FieldOp) (handler : Handler r) (z : BinaryInput.T) :
    (fieldAt op).run handler z = (run (field op) z).pay 1 0 := rfl

theorem paired_fieldAt_success {r : Port} (handler : Handler r) (op : FieldOp)
    (a b a0 b0 result result0 : Scalar)
    (sameA : ScalarMatch a a0) (sameB : ScalarMatch b b0)
    (actual : evalField op a b = some result)
    (baseline : evalField op a0 b0 = some result0) :
    ((fieldAt op).run handler (encodePaired a a0,encodePaired b b0)).valid ∧
    ((fieldAt op).run handler (encodePaired a a0,encodePaired b b0)).val =
      encodePaired result result0 ∧
    ((fieldAt op).run handler (encodePaired a a0,encodePaired b b0)).work ≤ 40 ∧
    ((fieldAt op).run handler (encodePaired a a0,encodePaired b b0)).peak ≤ 1 := by
  obtain ⟨valid,value,_same,work,peak⟩ := paired_field_success op a b a0 b0
    result result0 sameA sameB actual baseline
  simp only [fieldAt_run,Bill.pay]
  exact ⟨valid,value,by omega,by omega⟩

end
end ExactFourierCircuits.DFTModelAffine
