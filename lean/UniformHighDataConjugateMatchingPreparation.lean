import UniformHighDataPackingPreparation
import UniformMatchingCoefficientValueBridge

set_option autoImplicit false
namespace ExactFourierCircuits.UniformHighDataConjugateMatchingPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC applyBlock)
open UniformAllAxisSeedPreparation (axisCount)

def program : Program :=
 UniformHighDataPackingPreparation.program.map (relocate 0 167) ++
 UniformConjugatePackedMatchingPreparation.program.map (relocate 167 1365) ++ [.halt]
lemma program_length : program.length=1366 := by
 simp only [program,List.length_append,List.length_map,UniformHighDataPackingPreparation.program_length,
  UniformConjugatePackedMatchingPreparation.program_length,List.length_singleton]
attribute [local irreducible] UniformHighDataPackingPreparation.program UniformConjugatePackedMatchingPreparation.program
lemma packing_code : CodeAt UniformHighDataPackingPreparation.program program 0 167 := by
 have eq:program=[]++UniformHighDataPackingPreparation.program.map (relocate 0 167)++
  (UniformConjugatePackedMatchingPreparation.program.map (relocate 167 1365)++[.halt]) := by
  simp only [program,List.nil_append,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code [] _ _ 0 167 rfl
lemma matching_code : CodeAt UniformConjugatePackedMatchingPreparation.program program 167 1365 :=
 UniformRankCrossPreparationMachine.segment_code
  (UniformHighDataPackingPreparation.program.map (relocate 0 167)) [.halt] _ 167 1365
  (by rw [List.length_map,UniformHighDataPackingPreparation.program_length])
lemma halt_at : program[1365]?=some .halt := by
 let pre:=UniformHighDataPackingPreparation.program.map (relocate 0 167)++
  UniformConjugatePackedMatchingPreparation.program.map (relocate 167 1365)
 have len:pre.length=1365 := by
  simp only [pre,List.length_append,List.length_map,UniformHighDataPackingPreparation.program_length,
   UniformConjugatePackedMatchingPreparation.program_length]
 change (pre++[.halt])[1365]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
variable {n B : ℕ} {j : Fin (axisCount n)} {seed : UniformSeedChunkPreparation.Config}
abbrev M (p : UniformSeedChunkPackingPreparation.Layout n j seed B) :=
 UniformPackedMatchingShearMachine.seedRows p
lemma selected_count (p : UniformSeedChunkPackingPreparation.Layout n j seed B) :
 (M p).length=(UniformChunkMatchingPreparation.indices (seed.chunk n j)
  (UniformPackedMatchingShearMachine.seedWord n j seed)).length :=
 UniformPackedMatchingShearMachine.mappedRows_length _ _ _ _
attribute [local irreducible] UniformToeplitzCrossDAG.crossDAG
 UniformChunkMatchingPreparation.crossWord UniformChunkMatchingPreparation.colors

lemma spectrum_arguments_transport {p : UniformRankCrossPreparationMachine.Parameters} {V : ℕ} {s u : State}
 (f : UniformHighDataPackingPreparation.Frame s u)
 (h : UniformConjugateRankSpectrumPreparation.Arguments n j p V s) :
 UniformConjugateRankSpectrumPreparation.Arguments n j p V u := by
 refine ⟨(f.2.2.1 1820 (by unfold UniformHighDataPackingPreparation.Protected;omega)).trans h.1,
  (f.2.2.1 1821 (by unfold UniformHighDataPackingPreparation.Protected;omega)).trans h.2.1,?_⟩
 intro q hq h0 h1 h2 h3
 have hp:UniformHighDataPackingPreparation.Protected q := by
  simp only [UniformRankCrossPreparationMachine.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold UniformHighDataPackingPreparation.Protected;omega
 exact (f.2.2.1 q hp).trans (h.2.2 q hq h0 h1 h2 h3)
lemma matching_arguments_transport {c : UniformPackedMatchingShearMachine.Config} {s u : State}
 (f : UniformHighDataPackingPreparation.Frame s u)
 (h : UniformConjugatePackedMatchingPreparation.HeaderArgs c s) :
 UniformConjugatePackedMatchingPreparation.HeaderArgs c u := by
 intro q h0 h1
 exact (f.2.2.1 q (by unfold UniformHighDataPackingPreparation.Protected;omega)).trans (h q h0 h1)

def pairLeft (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (cap : 2*(M p).length ≤ p.packing.total) (i : Fin (M p).length) : Fin p.packing.total :=
 ⟨2*i.val,by have:=i.isLt;omega⟩
def pairRight (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (cap : 2*(M p).length ≤ p.packing.total) (i : Fin (M p).length) : Fin p.packing.total :=
 ⟨2*i.val+1,by have:=i.isLt;omega⟩

def logicalCoefficient (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (i : Fin (M p).length) : ℂ :=
 (UniformMatchingCoefficientValueBridge.selectedReference (seed.chunk n j)
  (UniformPackedMatchingShearMachine.seedWord n j seed)
  ⟨i.val,Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq (selected_count p))⟩).eval
  (UniformConjugatePackedMatchingPreparation.coefficients n j seed)

def LogicalPairs (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (cap : 2*(M p).length ≤ p.packing.total) (original : Fin p.packing.total→Scalar) (u : State) : Prop :=
 ∀i : Fin (M p).length,
 let left:=UniformSeedChunkPackingPreparation.unpacking p (pairLeft p cap i)
 let right:=UniformSeedChunkPackingPreparation.unpacking p (pairRight p cap i)
 u.scalarHeap (p.packing.source+left.val)=some
  ⟨(original left).value+logicalCoefficient p i*(original right).value,
   (original left).dependent||(original right).dependent⟩ ∧
 u.scalarHeap (p.packing.source+right.val)=some
  ⟨(original right).value,(original left).dependent||(original right).dependent⟩

/-- Full native-axis output, including untouched tail cells and actual tags. -/
def FullAction (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 (original : Fin p.packing.total→Scalar) (u : State) : Prop :=
 ∀i : Fin p.packing.total,u.scalarHeap (p.packing.source+i.val)=some
  (UniformPackedMatchingShearMachine.matchingAction seed.seed.exponent
   (UniformConjugatePackedMatchingPreparation.coefficients n j seed)
   (UniformPackedMatchingShearMachine.seedLabels n j seed) 0 (M p).length
   (UniformConjugatePackedMatchingPreparation.packedValues p original)
   ((UniformSeedChunkPackingPreparation.unpacking p).symm i).val)

lemma matched_full_action (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 {V mu bar : ℕ} {original : Fin p.packing.total→Scalar} {s u : State}
 (h : UniformConjugatePackedMatchingPreparation.MatchedResult p V mu bar original s u) :
 FullAction p original u := h.destination

lemma matched_logical_pairs (p : UniformSeedChunkPackingPreparation.Layout n j seed B)
 {V mu bar : ℕ} (cap : 2*(M p).length ≤ p.packing.total)
 {original : Fin p.packing.total→Scalar} {s u : State}
 (h : UniformConjugatePackedMatchingPreparation.MatchedResult p V mu bar original s u) :
 LogicalPairs p cap original u := by
 intro i
 let ii:Fin (UniformChunkMatchingPreparation.indices (seed.chunk n j)
  (UniformPackedMatchingShearMachine.seedWord n j seed)).length:=
  ⟨i.val,Nat.lt_of_lt_of_le i.isLt (Nat.le_of_eq (selected_count p))⟩
 have result:=UniformMatchingCoefficientValueBridge.seed_result_pair_values p
  (c:=UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar)
  (bank:=UniformConjugatePackedMatchingPreparation.coefficients n j seed)
  (phi:=UniformSeedChunkPackingPreparation.unpacking p)
  (v:=UniformConjugatePackedMatchingPreparation.packedValues p original)
  (s:=s) (u:=setPC u 421) h cap ii
 have l:2*i.val<p.packing.total:=by have:=i.isLt;omega
 have r:2*i.val+1<p.packing.total:=by have:=i.isLt;omega
 simp only [pairLeft,pairRight,logicalCoefficient,ii,
  UniformConjugatePackedMatchingPreparation.matchingConfig,UniformPackedMatchingShearMachine.packingConfig,
  UniformConjugatePackedMatchingPreparation.packedValues,dite_eq_left l,dite_eq_left r,setPC] at result ⊢
 convert result using 1

/-- One fixed continuous program: actual high-data relocation/packing, actual
conjugate-spectrum production and actual six-C matching/scatter. All guards,
headers, helper returns and the final halt are charged. Entry contains genuine
retained seeds and original SeedChunk output, not a Packed/action certificate. -/
theorem execution (hn : 0<n) (x : Fin n→ℂ)
 (p : UniformSeedChunkPackingPreparation.Layout n j seed B) (low : ℕ)
 (original : Fin p.packing.total→Scalar) (s : State)
 (post : UniformSeedChunkPreparation.Result n j seed B hn p.seed s)
 (packingArgs : UniformSeedChunkPackingPreparation.Args p s) (lowArg : s.natReg 2240=low)
 (present : ∀i,s.scalarHeap (low+i.val)=some (original i))
 (separated : low+p.packing.total ≤ p.packing.source)
 (placement : UniformHighDataPackingPreparation.RetentionPlacement p)
 (work : UniformRankCrossPreparationMachine.Parameters) (V mu bar : ℕ)
 (a : UniformConjugatePackedMatchingPreparation.Allocation p work V mu bar)
 (spectrumArgs : UniformConjugateRankSpectrumPreparation.Arguments n j
  (UniformConjugatePackedMatchingPreparation.workParameters n j seed work) V s)
 (matchingArgs : UniformConjugatePackedMatchingPreparation.HeaderArgs
  (UniformConjugatePackedMatchingPreparation.matchingConfig p V mu bar) s)
 (metadata : UniformPermutationInversePreparation.Metadata n s)
 (ops : UniformInitialPreparation.Operands n x s)
 (retained : UniformAllAxisSeedPreparation.Retained n (axisCount n) s)
 (conjugate : UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (pc : s.pc=0) (bound : WordBound B s) : ∃u ticks,
 BoundedExecution program n x B s ticks u ∧
 ticks ≤ UniformConjugatePackedMatchingPreparation.runtimeBudget p work+220*p.packing.total+45 ∧
 u.pc=1365 ∧ FullAction p original u ∧ LogicalPairs p a.matching.capacity original u ∧
 UniformAllAxisSeedPreparation.Retained n (axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have code:=p.code
 obtain ⟨v,t,origin,first,cost,vpc,genuine,packed,rv,cv,mv,ov,_,f⟩:=
  UniformHighDataPackingPreparation.execution_retained hn x p low original s post packingArgs lowArg present
   separated (UniformHighDataPackingPreparation.BankPlacement.of_matching p a) placement
   retained conjugate metadata ops pc bound
 have firstPlaced:=UniformBoundedAssembly.boundedExecution_placed packing_code
  (by rw [UniformHighDataPackingPreparation.program_length];omega) (by omega) first
 rw [show placed 0 s=s by cases s;simp [placed]] at firstPlaced
 let b:=setPC v 167
 let entry:=setPC b 0
 have packedEntry:UniformSeedChunkPackingPreparation.Packed p original origin entry:=
  ⟨packed.inverse,packed.values,packed.scalarOutside,packed.natOutside,packed.frame⟩
 obtain ⟨z,tm,mid,last,mcost,zpc,_,_,matched,rz,cz,mz,oz,out,roots,_,_,_⟩:=
  UniformConjugatePackedMatchingPreparation.execution hn x p work V mu bar origin entry genuine original packedEntry
   (mv.transport (fun _ _=>rfl) (fun _ _=>rfl)) (ov.transport rfl) rv.withPC cv.withPC
   (spectrum_arguments_transport f spectrumArgs) (matching_arguments_transport f matchingArgs)
   a rfl (changePC_bound B b 0 firstPlaced.final_bound (by omega))
 have matchingPlaced:=UniformBoundedAssembly.boundedExecution_placed matching_code
  (by rw [UniformConjugatePackedMatchingPreparation.program_length];omega) (by omega) last
 rw [UniformSeedRankCrossPreparation.placed_zero b 167 rfl] at matchingPlaced
 let u:=setPC z 1365
 have stop:BoundedExecution program n x B u 1 u:=.halt matchingPlaced.final_bound
  (by simp [step,u,setPC,halt_at])
 have logical:LogicalPairs p a.matching.capacity original u:=matched_logical_pairs p a.matching.capacity matched
 exact ⟨u,t+tm+1,firstPlaced.executes (matchingPlaced.executes stop),by omega,rfl,
  matched_full_action p matched,logical,
  rz.withPC,cz.withPC,mz.transport (fun _ _=>rfl) (fun _ _=>rfl),oz.transport rfl,
  out.trans f.1,roots.trans f.2.1⟩

end
end ExactFourierCircuits.UniformHighDataConjugateMatchingPreparation
