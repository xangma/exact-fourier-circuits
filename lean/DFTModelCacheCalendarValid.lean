import DFTModelCacheCalendarCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode indexCode indexCode_valid)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node prepare correction finish sequence

theorem code_comp_valid {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r t u)
    (h : Handler r) (x : s.T) : (Code.run (.comp f g) h x).valid ↔
      (Code.run f h x).valid ∧ (Code.run g h (Code.run f h x).val).valid := by
  simp only [Code.run,Bill.pass,Bill.pay]

theorem code_fork_valid {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r s u)
    (h : Handler r) (x : s.T) : (Code.run (.fork f g) h x).valid ↔
      (Code.run f h x).valid ∧ (Code.run g h x).valid := by
  simp only [Code.run,Bill.pass,Bill.one,and_true]

theorem code_ifz_valid {r : Port} {s t : Ty} (q : Code false r s w) (f g : Code false r s t)
    (h : Handler r) (x : s.T) : (Code.run (.ifz q f g) h x).valid ↔
      (Code.run q h x).valid ∧
        (if (Code.run q h x).val=0 then (Code.run f h x).valid else (Code.run g h x).valid) := by
  change (Code.run q h x).valid ∧ (if (Code.run q h x).val=0 then Code.run f h x else Code.run g h x).valid ↔ _
  split_ifs <;> rfl

theorem code_import_valid {r : Port} {s t : Ty} (f : Prog false s t) (h : Handler r) (x : s.T) :
    (Code.run (.importClosed f) h x).valid ↔ (run f x).valid := by
  simp only [Code.run,Bill.pay]

theorem direct_valid (v o t : ℕ) : (run direct (v,(o,t))).valid :=
  indexCode_valid direct (by decide) () _

theorem prepare_valid (v o t : ℕ) : (run prepare (v,(o,t))).valid := by
  rw [prepare,code_fork_valid,code_comp_valid]
  exact ⟨trivial,⟨indexCode_valid (.fork width offset) (by decide) () _,DFTModelCacheDescriptor.node_valid v o⟩⟩

theorem correction_valid (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).valid := by
  rw [correction,code_comp_valid]
  refine ⟨indexCode_valid (.fork correctionStart (.comp (.atom .fst) nodeRows)) (by decide) () _,?_⟩
  change (run sequence ((run correctionStart _).val,ofList (L.map rectangleEncode))).valid
  exact sequence_valid _ L

theorem finish_valid (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run finish (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).valid := by
  rw [finish,code_comp_valid,code_fork_valid]
  exact ⟨⟨trivial,correction_valid v o t b L l r⟩,indexCode_valid (.fork finishedDuration finishedEvents) (by decide) () _⟩

theorem directCode_valid (h : Handler RecPort) (nf : NodeFrame.T) :
    (directCode.run h nf).valid := by
  rw [directCode,code_comp_valid,code_import_valid]
  exact ⟨trivial,direct_valid nf.1.1 nf.1.2.1 nf.1.2.2⟩

theorem splitCode_valid (h : Handler RecPort) (v o t b : ℕ) (L : List Row)
    (hl:(h (v/2,(o,t))).valid) (hr:(h (v-v/2,(o+v/2,t))).valid) :
    (splitCode.run h ((v,(o,t)),(b,ofList (L.map rectangleEncode)))).valid := by
  rw [splitCode,code_comp_valid,code_fork_valid,code_fork_valid,
    code_comp_valid,code_comp_valid,code_import_valid,code_import_valid]
  refine ⟨⟨trivial,⟨⟨indexCode_valid leftInput (by decide) () _,?_⟩,
    ⟨indexCode_valid rightInput (by decide) () _,?_⟩⟩⟩,?_⟩
  · exact hl
  · exact hr
  · rw [code_import_valid]
    change (run finish (((v,(o,t)),(b,ofList (L.map rectangleEncode))),
      ((h (v/2,(o,t))).val,(h (v-v/2,(o+v/2,t))).val))).valid
    exact finish_valid _ _ _ _ _ _ _

theorem body_valid (h : Handler RecPort) (v o t : ℕ)
    (hh:¬(v<2 ∨ selected v=0) → (h (v/2,(o,t))).valid ∧ (h (v-v/2,(o+v/2,t))).valid) :
    (body.run h (v,(o,t))).valid := by
  rw [body,code_comp_valid,code_import_valid]
  refine ⟨prepare_valid v o t,?_⟩
  rw [code_import_value,prepare_value,branch,code_ifz_valid]
  refine ⟨indexCode_valid (.importClosed nodeSmall) (by decide) h _,?_⟩
  have cmp:(Code.run (.importClosed nodeSmall) h
      ((v,(o,t)),(selected v,ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode)))).val=
      if v<2 then 1 else 0 := rfl
  rw [cmp]
  by_cases hv:v<2
  · simp only [hv,ite_true,Nat.one_ne_zero,ite_false]
    exact directCode_valid h _
  · simp only [hv,ite_false,ite_true]
    rw [code_ifz_valid]
    refine ⟨indexCode_valid (.comp (.atom .snd) (.atom .fst)) (by decide) h _,?_⟩
    change if selected v=0 then _ else _
    by_cases hb:selected v=0
    · rw [ite_eq_left hb]
      exact directCode_valid h _
    · rw [ite_eq_right hb]
      have hs:=hh (by omega)
      exact splitCode_valid h v o t _ _ hs.1 hs.2

attribute [local irreducible] result body

theorem result_valid (fuel v o t : ℕ) (hv:v<fuel) : (result fuel v o t).valid := by
  induction fuel generalizing v o t with
  | zero => omega
  | succ fuel ih =>
    rw [result_succ]
    apply body_valid _ v o t
    intro hd
    exact ⟨ih _ _ _ (by omega),ih _ _ _ (by omega)⟩

theorem program_valid (v o t : ℕ) : (run program (v,(o,t))).valid := by
  rw [program_run]
  exact result_valid (v+1) v o t (by omega)

end
end ExactFourierCircuits.DFTModelCacheCalendar
