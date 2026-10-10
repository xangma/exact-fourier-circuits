import DFTModelCacheLeafCoefficientsSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients.Forest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] banks body annotate DFTModelCacheDirectLeaf.forest

abbrev Seed := p Input (p Banks DFTModelCacheDirectLeaf.ForestOutput)
abbrev Cell := p Seed w
abbrev Output := p Banks (p DFTModelCacheDirectLeaf.ForestOutput (Ty.a (p Pairs Pairs)))
def seedBanks : Prog false Seed Banks := .comp (.atom .snd) (.atom .fst)
def seedForest : Prog false Seed DFTModelCacheDirectLeaf.ForestOutput := .comp (.atom .snd) (.atom .snd)
def setup : Prog false Input Seed :=
  .fork (.atom .id) (.fork (.comp (.atom .fst) banks)
    (.comp (.atom .snd) DFTModelCacheDirectLeaf.forest))
def records : Prog false Cell DFTModelCacheDirectLeaf.Orientations :=
  .comp (.fork (.comp (.atom .fst) (.comp seedForest (.atom .snd))) (.atom .snd)) (.atom .look)
def argument : Prog false Cell DFTModelCacheLeafCoefficients.Seed :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork (.comp (.atom .fst) seedBanks) records)
def cell : Prog false Cell (p Pairs Pairs) :=
  .comp (.comp argument body) (.comp (.atom .snd) (.atom .snd))
def count : Prog false Seed w := .comp seedForest (.comp (.atom .snd) (.atom .len))
def finish : Prog false Seed Output :=
  .fork seedBanks (.fork seedForest (.tab count cell))
/-- Actual traversal, both native descriptor tapes, and scalar annotations. The
inverse-H banks are produced once and retained for the whole forest. -/
def program : Prog false Input Output := .comp setup finish

theorem setup_run (r v o K : ℕ) (omega : ℂ) : run setup ((r,omega),(v,(o,K)))=
    ⟨(((r,omega),(v,(o,K))),((run banks (r,omega)).val,
      (run DFTModelCacheDirectLeaf.forest (v,(o,K))).val)),
      (run banks (r,omega)).work+(run DFTModelCacheDirectLeaf.forest (v,(o,K))).work+7,
      max (run banks (r,omega)).peak (run DFTModelCacheDirectLeaf.forest (v,(o,K))).peak,
      (run banks (r,omega)).valid ∧ (run DFTModelCacheDirectLeaf.forest (v,(o,K))).valid⟩ := by
  simp [setup,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem cell_run (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) (i : ℕ) :
    run cell ((input,((h,hc),f)),i)=
      ⟨(run body (input,((h,hc),f.2.look i DFTModelCacheDirectLeaf.Orientations.blank))).val.2.2,
        (run body (input,((h,hc),f.2.look i DFTModelCacheDirectLeaf.Orientations.blank))).work+26,
        (run body (input,((h,hc),f.2.look i DFTModelCacheDirectLeaf.Orientations.blank))).peak,
        (run body (input,((h,hc),f.2.look i DFTModelCacheDirectLeaf.Orientations.blank))).valid⟩ := by
  simp [cell,argument,records,seedForest,seedBanks,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  omega

theorem finish_run (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) :
    run finish (input,((h,hc),f))=
      ((Bill.tab f.2.len (p Pairs Pairs).blank
        (fun i=>run cell ((input,((h,hc),f)),i))).pass
          (fun pairs=>Bill.one ((h,hc),(f,pairs)))).pay 15 f.2.len := by
  simp [finish,count,seedBanks,seedForest,run,Code.run,Atom.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  constructor
  · omega
  · ac_rfl

theorem finish_value (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) :
    (run finish (input,((h,hc),f))).val=((h,hc),(f,Tape.tab f.2.len (fun i=>
      ((run annotate ((input.2.2.2,(h,hc)),(f.2.look i DFTModelCacheDirectLeaf.Orientations.blank).1)).val,
        (run annotate ((input.2.2.2,(h,hc)),(f.2.look i DFTModelCacheDirectLeaf.Orientations.blank).2)).val)))) := by
  rw [finish_run]
  change ((h,hc),(f,(Bill.tab _ _ _).val))=_
  rw [ModelEquivalenceInterpreter.tab_value]
  congr 2
  apply congrArg (Tape.tab f.2.len)
  funext i
  rw [cell_run,body_value]

theorem finish_valid (input : Input.T) (h hc : Tape ℂ)
    (f : DFTModelCacheDirectLeaf.ForestOutput.T) : (run finish (input,((h,hc),f))).valid := by
  rw [finish_run]
  refine ⟨(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr ?_,trivial⟩
  intro i _
  rw [cell_run]
  exact body_valid _ _ _ _ _

theorem program_value (r v o K : ℕ) (omega : ℂ) :
    (run program ((r,omega),(v,(o,K)))).val=
      ((inverseH r omega,inverseH r omega⁻¹),
        ((run DFTModelCacheDirectLeaf.forest (v,(o,K))).val,
          Tape.tab (run DFTModelCacheDirectLeaf.forest (v,(o,K))).val.2.len (fun i=>
            ((run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
              ((run DFTModelCacheDirectLeaf.forest (v,(o,K))).val.2.look i
                DFTModelCacheDirectLeaf.Orientations.blank).1)).val,
              (run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
              ((run DFTModelCacheDirectLeaf.forest (v,(o,K))).val.2.look i
                DFTModelCacheDirectLeaf.Orientations.blank).2)).val)))) := by
  change (run finish (run setup _).val).val=_
  rw [setup_run,banks_value,finish_value]

theorem tab_lookup {α : Type} (n : ℕ) (f : ℕ→α) (i : ℕ) (hi : i<n) (z : α) :
    (Tape.tab n f).look i z=f i := by
  rw [Tape.look_of_lt _ _ hi]
  rfl

theorem annotate_empty (K : ℕ) (h hc : Tape ℂ) :
    (run annotate ((K,(h,hc)),DFTModelCacheTraversal.ofList [])).val=
      DFTModelCacheTraversal.ofList [] := by
  rw [annotate_value]
  apply DFTModelCacheTraversal.tape_ext _ _ (p sc sc).blank
  · rfl
  · intro i hi
    exact False.elim (Nat.not_lt_zero i hi)

/-- Genuine native node provenance and exact coefficient record order for each
leaf; split nodes have empty pair tapes. Both orientations remain separate. -/
theorem node_pairs (r v o K : ℕ) (omega : ℂ) (extent : o+v≤r)
    (i : ℕ) (hi : i<(DFTModelCacheDirectLeaf.visits v o).length) :
    ((run program ((r,omega),(v,(o,K)))).val.2.2.look i (p Pairs Pairs).blank)=
      let q:=(DFTModelCacheDirectLeaf.visits v o)[i]
      if DFTModelCacheDirectLeaf.leaf q then
        (coefficientPairs omega K (UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K),
          coefficientPairs omega K ((UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K).reverse.map
            UniformTransposeDescriptorMachine.Record.transpose))
      else (DFTModelCacheTraversal.ofList [],DFTModelCacheTraversal.ofList []) := by
  rw [program_value,DFTModelCacheDirectLeaf.forest_value]
  have len : i<(DFTModelCacheTraversal.ofList
      ((DFTModelCacheDirectLeaf.visits v o).map (DFTModelCacheDirectLeaf.leafValue K))).len := by
    simpa [DFTModelCacheTraversal.ofList] using hi
  rw [tab_lookup _ _ _ len]
  change ((run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
    ((DFTModelCacheTraversal.ofList ((DFTModelCacheDirectLeaf.visits v o).map
      (DFTModelCacheDirectLeaf.leafValue K))).look i DFTModelCacheDirectLeaf.Orientations.blank).1)).val,
    (run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
    ((DFTModelCacheTraversal.ofList ((DFTModelCacheDirectLeaf.visits v o).map
      (DFTModelCacheDirectLeaf.leafValue K))).look i DFTModelCacheDirectLeaf.Orientations.blank).2)).val)=_
  rw [Tape.look_of_lt _ _ len]
  simp only [DFTModelCacheTraversal.ofList,List.getElem_map]
  let q:=(DFTModelCacheDirectLeaf.visits v o)[i]
  have qe : q.task.offset+q.task.width≤r :=
    (DFTModelCacheDirectLeaf.visit_bounds v o q (List.getElem_mem hi)).2.trans extent
  change ((run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
    (DFTModelCacheDirectLeaf.leafValue K q).1)).val,
    (run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),
    (DFTModelCacheDirectLeaf.leafValue K q).2)).val)=
    (if DFTModelCacheDirectLeaf.leaf q then
      (coefficientPairs omega K (UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K),
        coefficientPairs omega K ((UniformTransposeDescriptorMachine.leafRecords q.task.width q.task.offset K).reverse.map
          UniformTransposeDescriptorMachine.Record.transpose))
      else (DFTModelCacheTraversal.ofList [],DFTModelCacheTraversal.ofList []))
  by_cases leaf : DFTModelCacheDirectLeaf.leaf q
  · simp only [DFTModelCacheDirectLeaf.leafValue,leaf,ite_true]
    apply Prod.ext
    · exact annotate_produced _ _ _ _ (fun p hp=>
        (UniformDirectLeafCacheChronology.leaf_valid _ _ _ _ qe p hp).1)
    · exact annotate_produced _ _ _ _ (fun p hp=>by
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
        have good:=UniformDirectLeafCacheChronology.leaf_valid _ _ _ _ qe a (List.mem_reverse.mp ha)
        exact (UniformDirectLeafCacheChronology.transpose_valid r K a good.1 good.2).1)
  · simp only [DFTModelCacheDirectLeaf.leafValue,leaf,ite_false]
    exact Prod.ext (annotate_empty K _ _) (annotate_empty K _ _)

theorem program_valid {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) (v o K : ℕ) :
    (run program ((r,omega),(v,(o,K)))).valid := by
  change (run setup _).valid ∧ (run finish (run setup _).val).valid
  constructor
  · rw [setup_run]
    exact ⟨banks_valid hr primitive,DFTModelCacheDirectLeaf.forest_valid _ _ _⟩
  · rw [setup_run]
    exact finish_valid _ _ _ _

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients.Forest
