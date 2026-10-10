import DFTModelCacheAmbientPoolProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheAmbientPool
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheSelectedCoefficients (Row)
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section
attribute [local irreducible] program translate DFTModelCacheMatchingProduced.program

theorem translated_rows {M:ℕ} (o:ℕ) (E:Fin M→Edge) (rs:Tape Row.T)
 (rows:DFTModelCacheMatchingNat.Rows E rs) :
 DFTModelCacheMatchingNat.Rows (fun i=>UniformTranslatedMatchingRows.edge o (E i))
  (run translate (o,rs)).val := by
 refine ⟨(translate_length o rs).trans rows.length,?_⟩
 intro i
 change ((run translate (o,rs)).val.look i.val Row.blank).1=_ ∧
  ((run translate (o,rs)).val.look i.val Row.blank).2.1=_
 rw [translate_lookup o rs i.val (rows.length.symm ▸ i.isLt)]
 have h:=rows.endpoints i
 exact ⟨congrArg (fun q=>o+q) h.1,congrArg (fun q=>o+q) h.2⟩

theorem translated_labels {M R:ℕ} (o C T P:ℕ) (rs:Tape Row.T)
 (labels:Fin M→UniformMatchingConjugateLoadMachine.Coefficient R)
 (source:DFTModelCacheSelectedCoefficients.RowSource C T P rs labels) :
 DFTModelCacheSelectedCoefficients.RowSource C T P (run translate (o,rs)).val labels := by
 refine ⟨(translate_length o rs).trans source.1,?_⟩
 intro i
 rw [translate_lookup o rs i.val (source.1.symm ▸ i.isLt)]
 exact source.2 i

theorem translated_peak {M:ℕ} (o v ambient:ℕ) (E:Fin M→Edge) (rs:Tape Row.T)
 (rows:DFTModelCacheMatchingNat.Rows E rs) (hr:InRange v E) (fit:o+v≤ambient) :
 (run translate (o,rs)).peak≤ max M ambient := by
 have h:=translate_peak o v rs (by
  intro j hj
  let i:Fin M:=⟨j,rows.length ▸ hj⟩
  have ends:=rows.endpoints i
  change (rs.look i.val (0,(0,0))).1<v ∧ (rs.look i.val (0,(0,0))).2.1<v
  rw [ends.1,ends.2]
  exact hr i)
 rw [rows.length] at h
 exact h.trans (max_le_max_left _ fit)

/-- One charged translation and one genuine proper7N/matching/constants pool
producer. Root order, seed radix, local width, offset, and ambient radix are
independent quantities joined only by the stated ordinary geometry. -/
theorem specification {M:ℕ} (o v ambient seedRadix D:ℕ)
 (p:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape p seedRadix) (K C T P:ℕ)
 (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
 (radixDiv:seedRadix∣D) (fftDiv:UniformRadixTwoDAG.width K∣D) (h4:4∣D)
 (rs:Tape Row.T) (E:Fin M→Edge)
 (rows:DFTModelCacheMatchingNat.Rows E rs) (hm:Matching E) (hr:InRange v E)
 (fit:o+v≤ambient) (radix:2≤ambient)
 (labels:Fin M→UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize K))
 (rowLabels:DFTModelCacheSelectedCoefficients.RowSource C T P rs labels)
 (positive:C+UniformToeplitzCrossDAG.bankSize K≤T)
 (negative:T+UniformToeplitzCrossDAG.bankSize K≤P) :
 let raw:=(DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D))
 let x:=args o ambient K C T P raw rs
 let bank:=UniformToeplitzCrossDAG.sharedBank K
  (DFTModelCacheSpectrum.rankKernels seedRadix p K (OAI.ExactFourier.zeta seedRadix))
 (run program x).valid ∧
 (run program x).work≤DFTModelCacheMatchingProduced.mixedWorkBudget ambient seedRadix D p K M+49*M+41 ∧
 (run program x).peak≤ max (max M ambient)
  (DFTModelCacheMatchingProduced.mixedPeakBudget ambient seedRadix D p K M) ∧
 (run program x).val.1=(x,argumentValue x) ∧
 (run program x).val.2.2.len=9*ambient ∧
 ∀lane:Fin 9,∀d:Fin ambient,
  (run program x).val.2.2.look (lane.val*ambient+d.val) 0=
   UniformGlobalMatchingScaleBankBridge.nativeFactor
    (fun i=>UniformTranslatedMatchingRows.edge o (E i))
    (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i)) lane d.val := by
 dsimp only
 let raw:=(DFTModelCacheDisplacement.metadata seedRadix p,(D,OAI.ExactFourier.zeta D))
 let x:=args o ambient K C T P raw rs
 let shiftedRows:=(run translate (o,rs)).val
 have child:=DFTModelCacheMatchingProduced.mixed_specification ambient seedRadix D p shape
  K C T P width hD radixDiv fftDiv h4 shiftedRows _
  (translated_rows o E rs rows) (UniformTranslatedMatchingRows.matching o E hm)
  (UniformTranslatedMatchingRows.inRange o E hr fit) radix labels
  (translated_labels o C T P rs labels rowLabels) positive negative
 have arg:argumentValue x=DFTModelCacheMatchingProduced.args ambient K C T P raw shiftedRows := by
  dsimp only [x,args,argumentValue,shiftedRows,DFTModelCacheMatchingProduced.args,DFTModelCacheSelectedCoefficients.producedArgs]
  rw [translate_value]
 have translated: (run translate (x.1,x.2.2.2.2)).work=49*M+6 := by
  change (run translate (o,rs)).work=_
  rw [translate_work,rows.length]
 have peak:(run translate (x.1,x.2.2.2.2)).peak≤ max M ambient :=
  translated_peak o v ambient E rs rows hr fit
 rw [program_run,arg]
 refine ⟨⟨translate_valid o rs,child.2.1⟩,?_,max_le_max peak child.2.2.2.1,rfl,
  child.2.2.2.2.1,child.2.2.2.2.2⟩
 have work:=child.2.2.1
 change (run DFTModelCacheMatchingProduced.program (DFTModelCacheMatchingProduced.args ambient K C T P raw shiftedRows)).work≤DFTModelCacheMatchingProduced.mixedWorkBudget ambient seedRadix D p K M at work
 change (run translate (x.1,x.2.2.2.2)).work+_+35≤_
 rw [translated]
 omega

end
end ExactFourierCircuits.DFTModelCacheAmbientPool
