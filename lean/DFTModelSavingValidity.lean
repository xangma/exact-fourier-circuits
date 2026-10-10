import DFTModelSavingProgram
import DFTModelSavingScalarBounds
import DFTModelSavingYBounds
import DFTModelSavingBinarySuffixSemantics

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingValidity
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
namespace R
export DFTModelSavingRecords (Input Iter BitInput Port raw initial field original index current width
  bitAddress bit bits directionArgs direction residual unitArgs paddingArgs paddingBody padding
  scalarArgs exchangeArgs opcodeTest dispatch StreamInput StreamIter records streamInitial recordArgs recordBody stream)
end R
namespace P
export DFTModelSavingProgram (Large Finished bits quotient remainder setup q rest node seedArgs suffixArgs large ordinary small body program)
end P
noncomputable section

lemma comp_valid {r : RAM.Port} {s t u : Ty} (f : Code false r s t)
    (g : Code false r t u) (h : Handler r) (x : s.T)
    (hf : (f.run h x).valid) (hg : (g.run h (f.run h x).val).valid) :
    ((Code.comp f g).run h x).valid := ⟨hf,hg⟩
lemma fork_valid {r : RAM.Port} {s t u : Ty} (f : Code false r s t)
    (g : Code false r s u) (h : Handler r) (x : s.T)
    (hf : (f.run h x).valid) (hg : (g.run h x).valid) :
    ((Code.fork f g).run h x).valid := ⟨hf,hg,trivial⟩
lemma import_valid {r : RAM.Port} {s t : Ty} (f : Prog false s t)
    (h : Handler r) (x : s.T) (hf : (run f x).valid) :
    ((Code.importClosed f).run h x).valid := hf
lemma imported_comp_valid {r : RAM.Port} {s t u : Ty}
    (f : Prog false s t) (g : Code false r t u) (h : Handler r) (x : s.T)
    (hf : (run f x).valid) (hg : ∀y,(g.run h y).valid) :
    ((Code.comp (.importClosed f) g).run h x).valid :=
  comp_valid _ _ _ _ (import_valid f h x hf) (hg _)
lemma ifz_valid {r : RAM.Port} {s t : Ty} (test : Code false r s w)
    (f g : Code false r s t) (h : Handler r) (x : s.T)
    (ht : (test.run h x).valid) (hf : (f.run h x).valid) (hg : (g.run h x).valid) :
    ((Code.ifz test f g).run h x).valid := by
  change (test.run h x).valid ∧ (if (test.run h x).val=0 then f.run h x else g.run h x).valid
  exact ⟨ht,by split_ifs <;> assumption⟩
lemma steps_valid {α : Type} (x : α) (f : ℕ→α→Bill α)
    (hf : ∀i z,(f i z).valid) (n : ℕ) : (Bill.steps x f n).valid := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨ih,hf _ _⟩
lemma loop_valid {r : RAM.Port} {s t : Ty} (count : Code false r s w)
    (initial : Code false r s t) (f : Code false r (p s (p w t)) t)
    (h : Handler r) (x : s.T) (hc : (count.run h x).valid)
    (hi : (initial.run h x).valid) (hf : ∀i z,(f.run h (x,(i,z))).valid) :
    ((Code.loop count initial f).run h x).valid :=
  ⟨hc,hi,steps_valid _ _ hf _⟩

lemma field_valid (j : ℕ) (x : R.Input.T) : (run (R.field j) x).valid := by
  simp [R.field,R.raw,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
lemma initial_valid (x : R.Input.T) : (run R.initial x).valid := by
  simp [R.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
lemma bit_valid (x : R.BitInput.T) : (run R.bit x).valid := by
  simp [R.bit,R.bitAddress,R.width,R.original,R.raw,R.field,R.index,
    DFTModelResidualCore.binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
lemma bits_valid (x : R.Iter.T) : (run R.bits x).valid := by
  rw [DFTModelSavingRecords.bits,DFTModelRecursiveScalar.tab_run]
  refine ⟨?_,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  · simp [R.width,R.original,R.field,R.raw,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  · intro j _;exact bit_valid _

attribute [local irreducible] DFTModelSavingRecords.bits
lemma directionArgs_valid (x : R.Iter.T) : (run R.directionArgs x).valid := by
  simpa only [R.directionArgs,R.original,R.width,R.current,R.field,R.raw,
    run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    true_and,and_true] using bits_valid x

lemma direction_valid (h : Handler R.Port) (children : ∀x,(h x).valid) (x : R.Iter.T) :
    ((R.direction).run h x).valid := by
  apply comp_valid
  · exact directionArgs_valid x
  · exact DFTModelSavingResidual.valid h _ (fun _ _=>children _)
lemma residual_valid (h : Handler R.Port) (children : ∀x,(h x).valid) (x : R.Input.T) :
    (R.residual.run h x).valid := by
  apply loop_valid
  · exact field_valid 6 x
  · exact initial_valid x
  · intro i z;exact direction_valid h children _

attribute [local irreducible] DFTModelCacheRecords.unit
lemma paddingArgs_valid (x : R.Iter.T) : (run R.paddingArgs x).valid := by
  unfold DFTModelSavingRecords.paddingArgs
  apply fork_valid
  · trivial
  · apply fork_valid
    · apply comp_valid
      · trivial
      · exact DFTModelCacheRecords.unit_valid _ _
    · trivial
attribute [local irreducible] DFTModelSavingRecords.residual
lemma padding_valid (h : Handler R.Port) (children : ∀x,(h x).valid) (x : R.Input.T) :
    (R.padding.run h x).valid := by
  apply loop_valid
  · exact field_valid 4 x
  · exact initial_valid x
  · intro i z
    exact imported_comp_valid R.paddingArgs R.residual h _
      (paddingArgs_valid _) (residual_valid h children)

attribute [local irreducible] DFTModelSavingResidual.program
  DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program
lemma scalarArgs_valid (x : R.Input.T) : (run R.scalarArgs x).valid := by
  simp [R.scalarArgs,R.raw,R.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
lemma exchangeArgs_valid (x : R.Input.T) : (run R.exchangeArgs x).valid := by
  simp [R.exchangeArgs,R.raw,R.initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
lemma opcodeTest_valid (j : ℕ) (x : R.Input.T) : (run (R.opcodeTest j) x).valid := by
  simp [R.opcodeTest,R.field,R.raw,DFTModelResidualCore.binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

attribute [local irreducible] DFTModelSavingRecords.field DFTModelSavingRecords.opcodeTest
  DFTModelSavingRecords.scalarArgs DFTModelSavingRecords.exchangeArgs DFTModelSavingRecords.initial
lemma dispatch_valid (R : ℕ) (h : Handler DFTModelSavingRecords.Port)
    (children : ∀x,(h x).valid) (x : DFTModelSavingRecords.Input.T) :
    ((DFTModelSavingRecords.dispatch R).run h x).valid := by
  unfold DFTModelSavingRecords.dispatch
  apply ifz_valid
  · exact field_valid 0 x
  · exact residual_valid h children x
  · apply ifz_valid
    · exact opcodeTest_valid 1 x
    · apply comp_valid
      · exact scalarArgs_valid x
      · exact DFTModelSavingScalar.program_valid R _ _ _ _
    · apply ifz_valid
      · exact opcodeTest_valid 2 x
      · exact initial_valid x
      · apply ifz_valid
        · exact opcodeTest_valid 3 x
        · exact DFTModelSavingY.program_valid R x
        · apply ifz_valid
          · exact opcodeTest_valid 4 x
          · apply comp_valid
            · exact exchangeArgs_valid x
            · exact DFTModelRecursiveExchange.program_valid R _ _
          · apply ifz_valid
            · exact opcodeTest_valid 5 x
            · exact padding_valid h children x
            · exact initial_valid x

lemma recordArgs_valid (x : R.StreamIter.T) : (run R.recordArgs x).valid := by
  simp [R.recordArgs,R.records,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
lemma stream_valid (roles : ℕ) (h : Handler R.Port) (children : ∀x,(h x).valid)
    (x : R.StreamInput.T) : ((R.stream roles).run h x).valid := by
  apply loop_valid
  · simp [R.records,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  · trivial
  · intro i z
    apply comp_valid
    · exact recordArgs_valid _
    · exact dispatch_valid roles h children _


attribute [local irreducible] DFTModelCacheRecords.seed DFTModelSavingRecords.stream
  DFTModelSavingBinarySuffix.program
lemma setup_valid (x : Node.T) : (run P.setup x).valid := by
  rcases x with ⟨⟨k,I⟩,v⟩
  rw [DFTModelSavingProgram.setup_run]
  trivial
lemma seedArgs_valid (x : P.Large.T) : (run P.seedArgs x).valid := by
  simpa only [P.seedArgs,P.rest,P.q,P.node,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    true_and,and_true] using DFTModelCacheRecords.seed_valid x.1
lemma suffixArgs_valid (x : P.Finished.T) : (run P.suffixArgs x).valid := by
  simp [P.suffixArgs,P.q,DFTModelResidualCore.binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
lemma large_valid (h : Handler ChildPort) (children : ∀x,(h x).valid) (x : Node.T) :
    (P.large.run h x).valid := by
  unfold DFTModelSavingProgram.large
  apply comp_valid
  · exact setup_valid x
  · apply comp_valid
    · apply fork_valid
      · trivial
      · apply comp_valid
        · exact seedArgs_valid _
        · exact stream_valid UniformBatching.width h children _
    · apply comp_valid
      · exact suffixArgs_valid _
      · apply comp_valid
        · exact DFTModelSavingBinarySuffix.program_valid _ _ _ _
        · trivial
lemma ordinary_valid (x : Node.T) : (run P.ordinary x).valid := by
  exact DFTModelRecursiveBinary.program_valid x.1.1 x.1.2 x.2
lemma small_valid (x : Node.T) : (run P.small x).valid := by
  rcases x with ⟨⟨k,I⟩,v⟩
  rw [DFTModelSavingProgram.small_run]
  trivial
lemma body_valid (h : Handler ChildPort) (children : ∀x,(h x).valid) (x : Node.T) :
    (P.body.run h x).valid := by
  unfold DFTModelSavingProgram.body
  apply ifz_valid
  · exact small_valid x
  · exact large_valid h children x
  · exact ordinary_valid x

/-- All internal calls are evaluated by descend itself. No validity oracle
or completed child action is an input of the closed program. -/
theorem depth_valid (fuel : ℕ) (x : Node.T) :
    (depthRun (P.ordinary.run ()) P.body.run fuel x).valid := by
  induction fuel generalizing x with
  | zero=>exact ordinary_valid x
  | succ fuel ih=>exact body_valid _ ih x

/-- Every executed scalar reciprocal is a proved prepared constant. -/
theorem program_valid (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run P.program ((k,I),v)).valid := by
  rw [DFTModelSavingProgram.program_run]
  exact depth_valid k _

end
end ExactFourierCircuits.DFTModelSavingValidity
