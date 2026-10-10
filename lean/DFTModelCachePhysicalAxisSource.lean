import DFTModelCachePhysicalAxisProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCachePhysicalAxis
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section

/-- Compact physical metadata, with no native address allocation. -/
def encodeAxis (a:UniformSectorPacking.Axis) : Axis.T :=
  (a.widths.sum,(DFTModelGlobalClockRecords.listTape a.widths,
    DFTModelGlobalClockRecords.listTape (List.ofFn (fun j=>(a.originalPermutation j).val))))

theorem permutation_native {M:ℕ} (r:ℕ) (E:Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (positive:2≤r) (p:Tape ℕ)
    (hp:DFTModelCacheMatchingFactors.PermutationSource r E hm hr p) :
    p=DFTModelGlobalClockRecords.listTape (List.ofFn
      (fun j=>((geometry r E hm hr positive).originalPermutation j).val)) := by
  have sum:(geometry r E hm hr positive).widths.sum=r:=
    widths_sum r M (matching_capacity r E hm hr)
  apply DFTModelGlobalClockRecords.tape_ext 0
  · simpa only [DFTModelGlobalClockRecords.listTape,List.length_ofFn,sum] using hp.1
  · intro j hj
    have jr:j<r:=by simpa only [hp.1] using hj
    have js:j<(geometry r E hm hr positive).widths.sum:=by rw [sum];exact jr
    have coord : ((geometry r E hm hr positive).originalPermutation ⟨j,js⟩).val=
        (originalPermutation r E hm hr ⟨j,jr⟩).val := rfl
    simpa [DFTModelGlobalClockRecords.listTape,Tape.look,js] using (hp.2 ⟨j,jr⟩).trans coord.symm

theorem axis_native {M:ℕ} (r W P:ℕ) (E:Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (positive:2≤r) (p:Tape ℕ)
    (hp:DFTModelCacheMatchingFactors.PermutationSource r E hm hr p) :
    (r,((run widths (r,M)).val,p))=
      encodeAxis (physicalAxis r W P E hm hr positive).geometry := by
  rw [widths_native r M (matching_capacity r E hm hr),permutation_native r E hm hr positive p hp]
  apply Prod.ext
  · exact (widths_sum r M (matching_capacity r E hm hr)).symm
  · rfl

/-- The same genuine invocation produces the native physical axis and its
nine-lane scalar factors. Raw matching rows, labels and master/rectangle
geometry are entry conditions, never generated permutation/width inputs. -/
theorem specification {M:ℕ} (r D:ℕ) (p:UniformRankKernelMachine.Parameters)
    (shape:DFTModelCacheDisplacement.Shape p r) (K C T P Wbase Pbase:ℕ)
    (width:p.N=UniformRadixTwoDAG.width K) (hD:0<D)
    (radixDiv:r∣D) (fftDiv:UniformRadixTwoDAG.width K∣D) (h4:4∣D)
    (rs:Tape DFTModelCacheSelectedCoefficients.Row.T) (E:Fin M→Edge)
    (rowEndpoints:DFTModelCacheMatchingNat.Rows E rs)
    (hm:Matching E) (hr:InRange r E) (radixTwo:2≤r)
    (labels:Fin M→UniformMatchingConjugateLoadMachine.Coefficient (UniformToeplitzCrossDAG.bankSize K))
    (rowLabels:DFTModelCacheSelectedCoefficients.RowSource C T P rs labels)
    (positive:C+UniformToeplitzCrossDAG.bankSize K≤T)
    (negative:T+UniformToeplitzCrossDAG.bankSize K≤P) :
    let raw:=(DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D))
    let x:=DFTModelCacheMatchingProduced.args r K C T P raw rs
    let bank:=UniformToeplitzCrossDAG.sharedBank K
      (DFTModelCacheSpectrum.rankKernels r p K (OAI.ExactFourier.zeta r))
    (run program x).val.1=encodeAxis (physicalAxis r Wbase Pbase E hm hr radixTwo).geometry ∧
    (run program x).val.2.1=r ∧ (run program x).val.2.2.len=9*r ∧
    (∀lane:Fin 9,∀d:Fin r,(run program x).val.2.2.look (lane.val*r+d.val) 0=
      UniformGlobalMatchingScaleBankBridge.nativeFactor E
        (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i)) lane d.val) ∧
    (run program x).valid ∧
    (run program x).work≤DFTModelCacheMatchingProduced.workBudget r D p K M+13*r+65 ∧
    (run program x).peak ≤ max (DFTModelCacheMatchingProduced.peakBudget r D p K M) r := by
  dsimp only
  let x:=DFTModelCacheMatchingProduced.args r K C T P
    (DFTModelCacheDisplacement.metadata r p,(D,OAI.ExactFourier.zeta D)) rs
  have h:=DFTModelCacheMatchingProduced.specification r D p shape K C T P width hD
    radixDiv fftDiv h4 rs E rowEndpoints hm hr radixTwo labels rowLabels positive negative
  have perm:=DFTModelCacheMatchingProduced.matching_specification r rs E rowEndpoints hm hr
  have val:=program_value x
  have rslen:rs.len=M:=rowEndpoints.length
  have count:M≤r:=by have cap:=matching_capacity r E hm hr;omega
  refine ⟨?_,?_,?_,?_,program_valid x h.2.1,?_,?_⟩
  · rw [val]
    change (r,((run widths (r,rs.len)).val,
      (run DFTModelCacheMatchingNat.program (r,rs)).val.2))=_
    rw [rslen]
    exact axis_native r Wbase Pbase E hm hr radixTwo _ perm.1
  · rw [val];rfl
  · rw [val];exact h.2.2.2.2.1
  · rw [val];exact h.2.2.2.2.2
  · rw [program_work]
    have work:=h.2.2.1
    change (run DFTModelCacheMatchingProduced.program x).work≤_ at work
    change (run DFTModelCacheMatchingProduced.program x).work+13*(r-rs.len)+65≤_
    have sub:r-rs.len≤r:=Nat.sub_le _ _
    omega
  · have hp:=program_peak x
    change (run program x).peak ≤ max (run DFTModelCacheMatchingProduced.program x).peak
      (max rs.len (max 2 (r-rs.len))) at hp
    apply hp.trans
    apply max_le_max h.2.2.2.1
    rw [rslen]
    exact max_le count (max_le radixTwo (Nat.sub_le _ _))

end
end ExactFourierCircuits.DFTModelCachePhysicalAxis
