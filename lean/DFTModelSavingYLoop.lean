import DFTModelSavingYData

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
open UniformNativeYRecordMachine (Direction actions values)
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section
attribute [local irreducible] DFTModelRecursiveYDirection.program

theorem tape_ext {α : Type} (blank : α) {a b : Tape α}
    (len : a.len=b.len) (look : ∀j,a.look j blank=b.look j blank) : a=b := by
  cases a with | mk n a =>
    cases b with | mk m b =>
      dsimp only at len
      subst m
      congr
      funext j
      have h:=look j.val
      simpa only [Tape.look,j.isLt,dite_true] using h

theorem paired_ext {R V : ℕ} (f f0 : Fin R → Fin V → Scalar)
    (v : Tape Tagged.T) (len : v.len=R*V)
    (lookup : ∀ b j,v.look (b.val*V+j.val) Tagged.blank=encodePaired (f b j) (f0 b j)) :
    v=paired f f0 := by
  apply tape_ext Tagged.blank len
  intro z
  by_cases hz : z<R*V
  · let ij := (finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).symm ⟨z,hz⟩
    have eq : ij.1.val*V+ij.2.val=z := by
      have h:=congrArg Fin.val ((finProdFinEquiv : Fin R × Fin V ≃ Fin (R*V)).apply_symm_apply ⟨z,hz⟩)
      simpa only [ij,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using h
    rw [←eq,lookup,paired_lookup]
  · rw [Tape.look_of_le _ _ (by omega),Tape.look_of_le _ _ (by change R*V≤z;omega)]

theorem body_paired {R m : ℕ} (q r k i : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v0 : Tape Tagged.T) (ds : List (Direction R m)) (hi : i<ds.length)
    (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q) :
    (run (body R) (rowInput r k i I raw v0 (paired f f0))).val=
      ((k,I),paired (values q m k (ds[i]'hi) f) (values q m k (ds[i]'hi) f0)) := by
  have hdr:=source.headers
  have row:=source.direction i hi
  change (run (DFTModelRecursiveYDirection.program R)
    (run arguments (rowInput r k i I raw v0 (paired f f0))).val).val=_
  rw [arguments_run]
  dsimp only [Bill.val]
  rw [hdr.1,hdr.2.1]
  have pv:=DFTModelRecursiveYDirection.program_value q r (8+(m+1)*i) k I raw
    (paired f f0) (ds[i]'hi) positive rfl shape qp row.1 row.2
  rw [pv]
  congr 1
  apply paired_ext _ _ _ rfl
  intro b j
  have pl:=DFTModelRecursiveYDirection.lookup_paired q r (8+(m+1)*i) k I raw
    (paired f f0) (ds[i]'hi) f f0 positive rfl shape qp row.1 row.2
    (paired_lookup f f0) b j
  rw [pv] at pl
  exact pl

theorem steps_value {R m : ℕ} (q r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q)
    (i : ℕ) (hi : i≤ds.length) :
    (steps R (input r k I raw (paired f f0)) i).val=
      ((k,I),paired (actions q m k (ds.take i) f) (actions q m k (ds.take i) f0)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hil:i<ds.length:=by omega
    change (run (body R) (input r k I raw (paired f f0),
      (i,(steps R (input r k I raw (paired f f0)) i).val))).val=_
    rw [ih (by omega)]
    rw [show (input r k I raw (paired f f0),
      (i,((k,I),paired (actions q m k (ds.take i) f) (actions q m k (ds.take i) f0))))=
      rowInput r k i I raw (paired f f0)
        (paired (actions q m k (ds.take i) f) (actions q m k (ds.take i) f0)) from rfl]
    rw [body_paired q r k i I raw (paired f f0) ds hil source _ _ positive shape qp]
    rw [List.take_succ_eq_append_getElem hil]
    simp only [actions,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem program_value {R m : ℕ} (q r k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (Direction R m)) (source : RecordSource q ds raw)
    (f f0 : Fin R → Fin (UniformResidualNativeTranslationMachine.volume k) → Scalar)
    (positive : 0<R) (shape : k=q*m+r) (qp : 1≤q) :
    (run (program R) (input r k I raw (paired f f0))).val=
      ((k,I),paired (actions q m k ds f) (actions q m k ds f0)) := by
  rw [program_run]
  change (steps R (input r k I raw (paired f f0)) (raw.look 6 0)).val=_
  rw [source.headers.2.2,steps_value q r k I raw ds source f f0 positive shape qp ds.length le_rfl,
    List.take_length]

end
end ExactFourierCircuits.DFTModelSavingY
