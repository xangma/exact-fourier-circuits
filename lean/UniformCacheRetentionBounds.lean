import UniformCacheRetentionRegions
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRetentionRegions
open UniformMachine
noncomputable section
structure OriginalNatEnds (c:Config) (H:ℕ) : Prop where
 fft : c.d+3*UniformRadixTwoDAG.count c.exponent ≤ H
 conv : c.conv+5*UniformToeplitzCrossTopologyMachine.G c.exponent ≤ H
 tape : c.tape+5*c.gates ≤ H
 depth : c.depth+c.e+1+c.gates ≤ H
 order : c.order+c.gates*(c.gates+1) ≤ H
 directory : c.directory+c.gates+2 ≤ H
 rows : UniformCrossHeightPreparationMachine.rowBase c.height (8*c.exponent+7) ≤ H
 colors : UniformCrossHeightPreparationMachine.colorBase c.height (8*c.exponent+7) ≤ H
 palette : c.palette+12 ≤ H
 heightDirectory : UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7) ≤ H
lemma OriginalNatEnds.high {c:Config} {H:ℕ} (ends:OriginalNatEnds c H) (i:ℕ) (hi:H ≤ i) : OriginalNat c i := by
 exact ⟨Or.inr (ends.fft.trans hi),Or.inr (ends.conv.trans hi),Or.inr (ends.tape.trans hi),Or.inr (ends.depth.trans hi),Or.inr (ends.order.trans hi),Or.inr (ends.directory.trans hi),Or.inr (ends.rows.trans hi),Or.inr (ends.colors.trans hi),Or.inr (ends.palette.trans hi),Or.inr (ends.heightDirectory.trans hi)⟩

structure OriginalScalarEnds (c:Config) (H:ℕ) : Prop where
 rank : c.S+6*c.width ≤ H
 fft : UniformPreparedFFTMachine.rootAddress c.exponent c.A+1 ≤ H
 positive : c.C+7*c.width+1 ≤ H
 negative : c.negative+7*c.width ≤ H
 constants : c.constants+6 ≤ H
lemma OriginalScalarEnds.high {c:Config} {H:ℕ} (ends:OriginalScalarEnds c H) (i:ℕ) (hi:H ≤ i) : OriginalScalar c i := by
 exact ⟨Or.inr (ends.rank.trans hi),Or.inr (ends.fft.trans hi),Or.inr (ends.positive.trans hi),Or.inr (ends.negative.trans hi),Or.inr (ends.constants.trans hi)⟩

structure ConjugateNatEnds (p:Params) (H:ℕ) : Prop where
 fft : p.d+3*UniformRadixTwoDAG.count p.K ≤ H
 conv : p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K ≤ H
 tape : p.tape+5*UniformRankCrossPreparationMachine.Shape p ≤ H
 depth : p.depth+p.e+1+UniformRankCrossPreparationMachine.Shape p ≤ H
lemma ConjugateNatEnds.high {p:Params} {H:ℕ} (ends:ConjugateNatEnds p H) (i:ℕ) (hi:H ≤ i) : ConjugateNat p i := by
 exact ⟨Or.inr (ends.fft.trans hi),Or.inr (ends.conv.trans hi),Or.inr (ends.tape.trans hi),Or.inr (ends.depth.trans hi)⟩

structure ConjugateScalarEnds (p:Params) (dest:ℕ) (H:ℕ) : Prop where
 rank : p.S+6*UniformRadixTwoDAG.width p.K ≤ H
 fft : UniformPreparedFFTMachine.rootAddress p.K p.A+1 ≤ H
 positive : p.C+7*UniformRadixTwoDAG.width p.K+1 ≤ H
 reversed : dest+7*UniformRadixTwoDAG.width p.K ≤ H
lemma ConjugateScalarEnds.high {p:Params} {dest:ℕ} {H:ℕ} (ends:ConjugateScalarEnds p dest H) (i:ℕ) (hi:H ≤ i) : ConjugateScalar p dest i := by
 exact ⟨Or.inr (ends.rank.trans hi),Or.inr (ends.fft.trans hi),Or.inr (ends.positive.trans hi),Or.inr (ends.reversed.trans hi)⟩

structure DisabledNatEnds (v:UniformCrossHeightPreparationMachine.Parameters) (H:ℕ) : Prop where
 rows : UniformCrossHeightPreparationMachine.rowBase v (UniformCrossHeightPreparationMachine.height v) ≤ H
 colors : UniformCrossHeightPreparationMachine.colorBase v (UniformCrossHeightPreparationMachine.height v) ≤ H
 palette : v.U+12 ≤ H
 directory : UniformCrossHeightPreparationMachine.recordBase v (UniformCrossHeightPreparationMachine.height v) ≤ H
lemma DisabledNatEnds.high {v:UniformCrossHeightPreparationMachine.Parameters} {H:ℕ} (ends:DisabledNatEnds v H) (i:ℕ) (hi:H ≤ i) : DisabledNat v i := by
 exact ⟨Or.inr (ends.rows.trans hi),Or.inr (ends.colors.trans hi),Or.inr (ends.palette.trans hi),Or.inr (ends.directory.trans hi)⟩

structure PhaseEnds (c:Config) (p:Params) (dest A:ℕ)
 (v:UniformCrossHeightPreparationMachine.Parameters) (H:ℕ) : Prop where
 originalNat : OriginalNatEnds c H
 originalScalar : OriginalScalarEnds c H
 conjugateNat : ConjugateNatEnds p H
 conjugateScalar : ConjugateScalarEnds p dest H
 slots : A+55*UniformLocalReplayAssembly.phasePrefix (8*c.exponent+6) 6 ≤ H
 disabled : DisabledNatEnds v H

lemma PhaseFrame.high {c:Config} {p:Params} {dest A H:ℕ}
 {v:UniformCrossHeightPreparationMachine.Parameters} {s u:State}
 (frame:PhaseFrame c p dest A v s u) (ends:PhaseEnds c p dest A v H) :
 (∀i,H ≤ i → u.natHeap i=s.natHeap i) ∧ (∀i,H ≤ i → u.scalarHeap i=s.scalarHeap i) := by
 constructor
 · intro i hi
   exact frame.1 i (ends.originalNat.high i hi) (ends.conjugateNat.high i hi)
    (Or.inr (ends.slots.trans hi)) (ends.disabled.high i hi)
 · intro i hi
   exact frame.2 i (ends.originalScalar.high i hi) (ends.conjugateScalar.high i hi)

lemma originalNat_low (c:Config) (D i:ℕ)
 (before:∀base∈[c.d,c.conv,c.tape,c.depth,c.order,c.directory,c.rows,c.colors,c.palette,c.heightDirectory],D+7≤base)
 (hi:i<D+7) : OriginalNat c i := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals apply Or.inl
 all_goals exact lt_of_lt_of_le hi (before _ (by simp))

/-- Low seven-word source retention follows from ordinary physical placement.
No source value or produced-bank certificate is added to the entry. -/
lemma PhaseFrame.row {n:ℕ} (hn:0<n) (j:Fin (UniformAllAxisSeedPreparation.axisCount n))
 (D:ℕ) (q:UniformLocalRectangleDescriptors.Row) (original:Config) (work:Params)
 (dest A FD FF FU FJ B:ℕ) (x:Fin n→ℂ) (s u:State)
 (layout:UniformSeedHeightPreparation.Layout n j (UniformLocalRectanglePhaseBanks.actual q original) B)
 (entry:UniformLocalRectanglePhaseBanks.Entry hn j D q original work dest A B x s layout)
 (falseLayout:UniformCrossHeightPreparationMachine.Layout
  (UniformLocalDisabledHeightMachine.disabled (UniformLocalRectanglePhaseBanks.actual q original).height FD FF FU FJ))
 (trueBefore:UniformCrossHeightPreparationMachine.recordBase (UniformLocalRectanglePhaseBanks.actual q original).height
  (8*(UniformLocalRectanglePhaseBanks.actual q original).exponent+7) ≤ FD)
 (frame:PhaseFrame (UniformLocalRectanglePhaseBanks.actual q original)
  (UniformLocalRectanglePhaseBanks.nextParameters n j q original work) dest A
  (UniformLocalDisabledHeightMachine.disabled (UniformLocalRectanglePhaseBanks.actual q original).height FD FF FU FJ) s u) :
 UniformLocalRectangleBankMachine.RowSource D q u := by
 let c:=UniformLocalRectanglePhaseBanks.actual q original
 have endBefore:D+7≤UniformCrossHeightPreparationMachine.recordBase c.height (8*c.exponent+7):=by
  have h:=entry.rowBefore c.heightDirectory (by simp [c])
  change D+7≤c.heightDirectory+3*(8*c.exponent+7)
  omega
 have df:FD≤FF:=by
  have h:=falseLayout.rows
  change FD+6*_*_≤FF at h
  omega
 have fu:FF≤FU:=by
  have h:=falseLayout.colors
  change FF+2*_*_≤FU at h
  omega
 have uj:FU≤FJ:=by
  have h:=falseLayout.palette
  change FU+12≤FJ at h
  omega
 intro f
 have hi:D+f.val<D+7:=by have:=f.isLt;omega
 apply Eq.trans _ (entry.source f)
 apply frame.1
 · exact originalNat_low c D _ entry.rowBefore hi
 · refine ⟨Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
   all_goals apply lt_of_lt_of_le hi
   all_goals apply endBefore.trans
   all_goals apply entry.nativeBefore
   all_goals simp [UniformLocalRectanglePhaseBanks.nextParameters,UniformLocalRectangleCoefficientMachine.nextParameters,UniformConjugateRankSpectrumPreparation.relocated]
 · exact Or.inl (lt_of_lt_of_le hi (endBefore.trans entry.slotsFresh))
 · refine ⟨Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
   · exact lt_of_lt_of_le hi (endBefore.trans trueBefore)
   · exact lt_of_lt_of_le hi (endBefore.trans (trueBefore.trans df))
   · exact lt_of_lt_of_le hi (endBefore.trans (trueBefore.trans (df.trans fu)))
   · exact lt_of_lt_of_le hi (endBefore.trans (trueBefore.trans (df.trans (fu.trans uj))))
end
end ExactFourierCircuits.UniformCacheRetentionRegions
