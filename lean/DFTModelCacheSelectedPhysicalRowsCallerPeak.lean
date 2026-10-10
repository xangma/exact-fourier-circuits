import DFTModelCacheSelectedPhysicalRowsCallerCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheHeight (Words)
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheHeightColorCaller.program
 DFTModelCacheSelectedPhysicalRowsProduced.program

def wordBound (p:UniformChunkMatchingPreparation.Parameters) (C T P M:ℕ) : ℕ :=
 p.radix+p.source+p.height.e+p.target+p.height.a+
 UniformCrossHeightPreparationMachine.gates p.height+M+C+T+P+
 UniformToeplitzCrossDAG.bankSize p.height.K+5

theorem coefficient_bound {R:ℕ} (C T P:ℕ) (c:UniformReplayPrint.Coefficient R) :
 (UniformCrossShearTableMachine.locations R C T P).address c≤C+T+P+R+2 := by
 cases c with
 | rational q =>
  simp only [UniformInPlaceMachine.Locations.address,UniformCrossShearTableMachine.locations]
  split_ifs <;> omega
 | prepared i sign =>
  have :=i.isLt
  cases sign <;>
   simp only [UniformInPlaceMachine.Locations.address,UniformCrossShearTableMachine.locations,
    Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- The mapper word envelope follows from actual native selected occurrences
and ordinary geometry; it is never supplied as a row-bank certificate. -/
theorem native_words (p:UniformChunkMatchingPreparation.Parameters)
 (W:List (UniformReplayPrint.ShearCode ℕ (UniformToeplitzCrossDAG.bankSize p.height.K)))
 (domain:UniformChunkMatchingPreparation.CodesDomain p W) (C T P:ℕ) :
 Words DFTModelCacheSelectedPhysicalRows.Input
  (wordBound p C T P (UniformChunkMatchingPreparation.indices p W).length)
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p,
   DFTModelCacheSelectedPhysicalRows.rowTape (UniformChunkMatchingPreparation.selectedRows p W
    (UniformCrossShearTableMachine.locations _ C T P))) := by
 let bound:=wordBound p C T P (UniformChunkMatchingPreparation.indices p W).length
 let loc:=UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize p.height.K) C T P
 let rows:=UniformChunkMatchingPreparation.selectedRows p W loc
 have count:rows.length=(UniformChunkMatchingPreparation.indices p W).length:=by
  simp only [rows,UniformChunkMatchingPreparation.selectedRows,List.length_map]
 have geo:Words DFTModelCacheSelectedPhysicalRows.Geometry bound
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p) := by
  change p.radix≤bound ∧ p.source≤bound ∧ p.height.e≤bound ∧
   p.target≤bound ∧ p.height.a≤bound ∧ UniformCrossHeightPreparationMachine.gates p.height≤bound
  dsimp [bound,wordBound]
  omega
 refine ⟨geo,?_,?_⟩
 · change rows.length≤bound
   rw [count]
   dsimp [bound,wordBound]
   omega
 · intro i
   change Words DFTModelCacheColor.Row bound
    ((DFTModelCacheSelectedPhysicalRows.rowTape rows).pos i)
   have hi:i.val<rows.length:=i.isLt
   have read:(DFTModelCacheSelectedPhysicalRows.rowTape rows).look i.val DFTModelCacheColor.Row.blank=
    (DFTModelCacheSelectedPhysicalRows.rowTape rows).pos i:=Tape.look_of_lt _ _ hi
   rw [←read]
   change Words DFTModelCacheColor.Row bound
    ((DFTModelCacheSelectedCoefficients.physicalRows rows).look i.val DFTModelCacheColor.Row.blank)
   rw [DFTModelCacheSelectedCoefficients.physicalRows_lookup rows ⟨i.val,hi⟩]
   have member:rows[i.val]∈rows:=List.getElem_mem hi
   have ports:=UniformChunkMatchingPreparation.selected_rows_domain loc domain rows[i.val] member
   change UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height)
    p.height.a rows[i.val].dst ∧
    UniformChunkPortMachine.Domain p.height.e (UniformCrossHeightPreparationMachine.gates p.height)
    p.height.a rows[i.val].src at ports
   have coeff:rows[i.val].coefficient≤C+T+P+UniformToeplitzCrossDAG.bankSize p.height.K+2 := by
    obtain ⟨j,hj,eqn⟩:=List.mem_map.mp member
    have jr:j<W.length:=(UniformColorLayerTableMachine.selected_mem _ _ _ _).mp hj |>.1
    rw [←eqn,UniformChunkMatchingPreparation.rowFunction,dite_eq_left jr]
    exact coefficient_bound C T P W[j].coefficient
   change rows[i.val].dst≤bound ∧ rows[i.val].src≤bound ∧ rows[i.val].coefficient≤bound
   unfold UniformChunkPortMachine.Domain at ports
   dsimp [bound,wordBound]
   omega

def peakBudget (p:UniformChunkMatchingPreparation.Parameters) (D:ℕ)
 (kernel:UniformRankKernelMachine.Parameters) (C T P M:ℕ) : ℕ :=
 max (DFTModelCacheHeightColorCaller.peakBudget p.color p.height.a p.height.e 0 C P p.depth)
  (max ((wordBound p C T P M)^DFTModelCacheSelectedPhysicalRows.wordDegree)
   (DFTModelCacheMatchingProduced.peakBudget p.radix D kernel p.height.K M))

theorem peak {B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (computed:p.height.K=DFTModelCacheTopology.exponent p.height.a p.height.e)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (height:p.depth≤8*p.height.K+6)
 (D:ℕ) (kernel:UniformRankKernelMachine.Parameters)
 (shape:DFTModelCacheDisplacement.Shape kernel p.radix)
 (width:kernel.N=UniformRadixTwoDAG.width p.height.K) (hD:0<D)
 (radixDiv:p.radix∣D) (fftDiv:UniformRadixTwoDAG.width p.height.K∣D) (h4:4∣D)
 (C T P:ℕ) (positive:C+UniformToeplitzCrossDAG.bankSize p.height.K≤T)
 (negative:T+UniformToeplitzCrossDAG.bankSize p.height.K≤P) :
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 (run program (nativeInput p C T P raw)).peak≤
 peakBudget p D kernel C T P (UniformChunkMatchingPreparation.indices p W).length := by
 dsimp only
 have hd:p.depth≤8*DFTModelCacheTopology.exponent p.height.a p.height.e+6:=by simpa only [computed] using height
 have first:=DFTModelCacheHeightColorCaller.program_peak p.color p.height.a p.height.e 0 C P p.depth p.height.enabled hd
 have second:=DFTModelCacheSelectedPhysicalRowsProduced.peak p layout
  (UniformChunkMatchingPreparation.crossWord p ha he)
  (UniformChunkMatchingPreparation.cross_domain p ha he)
  (UniformChunkMatchingPreparation.cross_degree p ha he)
  D kernel shape width hD radixDiv fftDiv h4 C T P positive negative
  (wordBound p C T P (UniformChunkMatchingPreparation.indices p (UniformChunkMatchingPreparation.crossWord p ha he)).length)
  (by unfold wordBound;omega)
  (native_words p _ (UniformChunkMatchingPreparation.cross_domain p ha he) C T P)
 let raw:DFTModelCacheSpectrum.Input.T:=
  (DFTModelCacheDisplacement.metadata p.radix kernel,(D,OAI.ExactFourier.zeta D))
 rw [program_run,native_argument p computed ha he height C T P raw]
 exact max_le_max first second

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRowsCaller
