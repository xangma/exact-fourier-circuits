import DFTModelSavingProgram
import DFTModelSavingDirectionCongruence
import DFTModelSavingPaddingCongruence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
open DFTModelSavingRecords
noncomputable section

attribute [local irreducible] DFTModelSavingResidual.program
  DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program
  DFTModelCacheRecords.unit DFTModelCacheRecords.seed
  DFTModelSavingBinarySuffix.program

lemma code_ifz_value {s t : Ty} (test : Code false Port s w)
    (f g : Code false Port s t) (h : Handler Port) (x : s.T) :
    ((Code.ifz test f g).run h x).val=
      if (test.run h x).val=0 then (f.run h x).val else (g.run h x).val := by
  change (if (test.run h x).val=0 then f.run h x else g.run h x).val=_
  split_ifs <;> rfl

lemma ifz_value_congr {s t : Ty} (test : Prog false s w)
    (f g : Code false Port s t) (h h' : Handler Port) (x : s.T)
    (hf : (f.run h x).val=(f.run h' x).val)
    (hg : (g.run h x).val=(g.run h' x).val) :
    ((Code.ifz (.importClosed test) f g).run h x).val=
      ((Code.ifz (.importClosed test) f g).run h' x).val := by
  change (if (run test x).val=0 then f.run h x else g.run h x).val=
    (if (run test x).val=0 then f.run h' x else g.run h' x).val
  split_ifs <;> assumption

lemma steps_value_congr_range {α : Type} (x : α) (f g : ℕ→α→Bill α)
    (n : ℕ) (eq : ∀i<n,∀z,(f i z).val=(g i z).val) :
    (Bill.steps x f n).val=(Bill.steps x g n).val := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change (f n (Bill.steps x f n).val).val=(g n (Bill.steps x g n).val).val
    rw [ih (fun i hi z=>eq i (by omega) z),eq n (by omega)]

lemma record_column (r : UniformFixedNetworkScheduleMachine.Record) :
    (DFTModelCacheRecords.dataTape r.data).look 1 0=r.columns := by
  simp [DFTModelCacheRecords.dataTape,Tape.look,Tape.tab,
    UniformFixedNetworkScheduleMachine.Record.data,UniformFixedNetworkScheduleMachine.Record.header]

lemma tape_columns (rs : List UniformFixedNetworkScheduleMachine.Record) (q i : ℕ)
    (hi : i<rs.length) :
    ((DFTModelCacheRecords.recordTape
      (rs.map (UniformFixedNetworkScheduleMachine.Record.withColumns q))).look i (Tape.empty ℕ)).look 1 0=q := by
  have outer : (DFTModelCacheRecords.recordTape
      (rs.map (UniformFixedNetworkScheduleMachine.Record.withColumns q))).look i (Tape.empty ℕ)=
      DFTModelCacheRecords.dataTape ((rs[i]).withColumns q).data := by
    simp [DFTModelCacheRecords.recordTape,Tape.look,Tape.tab,hi,List.getElem?_map]
  rw [outer,record_column]
  rfl

lemma seed_columns (q i : ℕ) (hi : i<(run DFTModelCacheRecords.seed q).val.len) :
    ((run DFTModelCacheRecords.seed q).val.look i (Tape.empty ℕ)).look 1 0=q := by
  rw [DFTModelCacheRecords.seed_value] at hi ⊢
  change i<(UniformFixedNetworkScheduleMachine.scheduleRecords q).length at hi
  exact tape_columns UniformFixedNetworkScheduleMachine.baseSchedule q i (by simpa only
    [UniformFixedNetworkScheduleMachine.scheduleRecords,List.length_map] using hi)

lemma closed_value_congr {s t : Ty} (f : Prog false s t)
    (h h' : Handler Port) (x : s.T) :
    ((Code.importClosed f).run h x).val=((Code.importClosed f).run h' x).val := rfl
lemma closed_comp_value_congr {s t u : Ty} (f : Prog false s t) (g : Prog false t u)
    (h h' : Handler Port) (x : s.T) :
    ((Code.comp (.importClosed f) (.importClosed g)).run h x).val=
      ((Code.comp (.importClosed f) (.importClosed g)).run h' x).val := rfl

lemma dispatch_value_congr (R q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q)
    (same : DFTModelSavingDirection.HandlerEq q h h') :
    ((dispatch R).run h (rest,(rawTape,node))).val=
      ((dispatch R).run h' (rest,(rawTape,node))).val := by
  unfold dispatch
  apply ifz_value_congr
  · exact DFTModelSavingDirection.residual_value_congr q rest rawTape node h h' columns same
  · apply ifz_value_congr
    · exact closed_comp_value_congr _ _ _ _ _
    · apply ifz_value_congr
      · exact closed_value_congr _ _ _ _
      · apply ifz_value_congr
        · exact closed_value_congr _ _ _ _
        · apply ifz_value_congr
          · exact closed_comp_value_congr _ _ _ _ _
          · apply ifz_value_congr
            · exact DFTModelSavingPadding.padding_value_congr q rest rawTape node h h' columns same
            · exact closed_value_congr _ _ _ _

lemma stream_value_congr (R q rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h h' : Handler Port) (columns : ∀i<rs.len,(rs.look i (Tape.empty ℕ)).look 1 0=q)
    (same : DFTModelSavingDirection.HandlerEq q h h') :
    ((stream R).run h (rest,(rs,node))).val=((stream R).run h' (rest,(rs,node))).val := by
  rw [stream_value,stream_value]
  apply steps_value_congr_range
  intro i hi z
  exact dispatch_value_congr R q rest _ z h h' (columns i hi) same

namespace P
export DFTModelSavingProgram (Large Finished setup seedArgs suffixArgs large ordinary small body program)
end P
attribute [local irreducible] DFTModelSavingRecords.stream P.ordinary

theorem suffixArgs_value (q rest : ℕ) (old node : Node.T) :
    (run P.suffixArgs ((q,(rest,old)),node)).val=(q*UniformFixedNetwork.m,node) := rfl

theorem large_value (h : Handler Port) (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (P.large.run h ((k,I),v)).val=
      (run DFTModelSavingBinarySuffix.program
        (k/UniformFixedNetwork.m*UniformFixedNetwork.m,
          ((stream UniformBatching.width).run h
            (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val,
              ((k,I),v)))).val)).val.2 := by
  simp only [P.large,DFTModelClockBatch.code_comp_value,DFTModelClockBatch.code_fork_value]
  change (run DFTModelSavingBinarySuffix.program
    (run P.suffixArgs ((run P.setup ((k,I),v)).val,
      ((stream UniformBatching.width).run h (run P.seedArgs (run P.setup ((k,I),v)).val).val).val)).val).val.2=_
  rw [DFTModelSavingProgram.setup_run,DFTModelSavingProgram.seedArgs_value,suffixArgs_value,
    DFTModelCacheRecords.seed_value]

theorem large_value_congr (h h' : Handler Port) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (same : DFTModelSavingDirection.HandlerEq (k/UniformFixedNetwork.m) h h') :
    (P.large.run h ((k,I),v)).val=(P.large.run h' ((k,I),v)).val := by
  rw [large_value,large_value]
  rw [stream_value_congr UniformBatching.width (k/UniformFixedNetwork.m) (k%UniformFixedNetwork.m)
    _ ((k,I),v) h h' (seed_columns _) same]

attribute [local irreducible] P.large
lemma body_value (h : Handler Port) (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (P.body.run h ((k,I),v)).val=
      if k<UniformRecursiveSavingProgram.threshold then (run P.ordinary ((k,I),v)).val
      else (P.large.run h ((k,I),v)).val := by
  rw [P.body,code_ifz_value]
  change (if (run P.small ((k,I),v)).val=0 then (P.large.run h ((k,I),v)).val
    else (run P.ordinary ((k,I),v)).val)=_
  rw [DFTModelSavingProgram.small_run]
  by_cases hk:k<UniformRecursiveSavingProgram.threshold <;> simp [hk]

end
end ExactFourierCircuits.DFTModelSavingControl
