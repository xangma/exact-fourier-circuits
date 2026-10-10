import DFTModelCacheMatchingFactorsNative
import UniformActualCalendarRectangleFactors

set_option autoImplicit false

/-! Correspondence with the genuine source permutation/factor banks and with
all three selected rectangle coefficient branches. Materialized typed input
tapes are explicit boundaries; this file does not compile their producers. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformColoring UniformMatchingAxisTableMachine
open UniformGlobalMatchingScaleBankBridge
noncomputable section
attribute [local irreducible] program scalar

/-- Matching55's actual ordered bank identifies the readonly typed tape. -/
theorem permutation_from_bank {M : ℕ} (r P : ℕ) (E : Fin M→Edge)
    (hm : Matching E) (hr : InRange r E) (s : UniformMachine.State) (p : Tape ℕ)
    (bank : Bank P (ordered r E) s) (length : p.len=r)
    (read : ∀j:Fin r,s.natHeap (P+j.val)=some (p.look j.val 0)) :
    PermutationSource r E hm hr p := by
  refine ⟨length,?_⟩
  intro j
  apply Option.some.inj
  exact (read j).symm.trans (bank j.val (by rw [ordered_length r E hm hr];exact j.isLt))

/-- Exact comparison with the physically produced139 matching factor pool.
The actual native source decoder fixes mu; it is not a supplied factor action. -/
theorem source_pool {R K pool r : ℕ} {rows : List UniformInPlaceMachine.Row}
    {bank : Fin R→ℂ} {co : Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R}
    {s : UniformMachine.State} (different : UniformGlobalMatchingPoolPreparation.Different rows)
    (matching : UniformGlobalMatchingPoolPreparation.Matching rows)
    (bounds : UniformGlobalMatchingPoolPreparation.Bounds r rows) (radix : 2≤r)
    (done : UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r rows bank co rows.length s)
    (p : Tape ℕ) (z : Tape (ℂ × ℂ))
    (permutation : PermutationSource r (rowEdges rows different)
      (rowEdges_matching rows different matching) (rowEdges_range r rows different bounds) p)
    (coefficients : CoefficientSource z (fun i=>UniformMatchingConjugateLoadMachine.value K bank (co i))) :
    ∀l:Fin 9,∀d:Fin r,
      s.scalarHeap (pool+l.val*r+d.val)=some (UniformPairMachine.prepared
        ((run program (args r p z Complex.I ExactFourierCircuits.a⁻¹)).val.look (l.val*r+d.val) 0)) := by
  have produced:=produces_native r (rowEdges rows different) (rowEdges_matching rows different matching)
    (rowEdges_range r rows different bounds) radix p z _ permutation coefficients
  intro l d
  rw [produced.2.2.2.2 l d]
  exact pool_coefficients different matching done l d

open UniformLocalFactorDispatchMachine UniformLocalCacheSlotConductorMachine
open UniformActualCalendarMatchingSource

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
  (slot : UniformLocalCacheChronology.Slot)
  (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
  (bl : BroadcastLayout c q B)
  (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
  (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
  (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def rectanglePermutation : Fin c.ambient≃Fin c.ambient :=
  originalPermutation c.ambient (UniformActualCalendarRectangleEvent.edges c q slot l bl ha he)
    (rowEdges_matching (printedRows c q slot l bl ha he)
      (dispatched_geometry c q slot l bl ha he).2.1
      (dispatched_geometry c q slot l bl ha he).2.2)
    (rowEdges_range c.ambient (printedRows c q slot l bl ha he)
      (dispatched_geometry c q slot l bl ha he).2.1
      (dispatched_geometry c q slot l bl ha he).1)

/-- Forward selectedValue, inverse selectedValue, and broadcast plus/minus one all
instantiate the same literal producer; no branch supplies factor values. -/
theorem selected_values (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (radix : 2≤c.ambient)
    (length : p.len=c.ambient)
    (permutation : ∀j:Fin c.ambient,p.look j.val 0=(rectanglePermutation c q slot l bl ha he j).val)
    (coefficients : CoefficientSource z
      (UniformActualCalendarRectangleEvent.coefficients c q slot l bl ha he bank)) :
    (run program (args c.ambient p z Complex.I ExactFourierCircuits.a⁻¹)).valid ∧
    (run program (args c.ambient p z Complex.I ExactFourierCircuits.a⁻¹)).work≤2781*c.ambient+13 ∧
    (run program (args c.ambient p z Complex.I ExactFourierCircuits.a⁻¹)).peak≤9*c.ambient ∧
    (run program (args c.ambient p z Complex.I ExactFourierCircuits.a⁻¹)).val.len=9*c.ambient ∧
    ∀lane:Fin 9,∀d:Fin c.ambient,
      (run program (args c.ambient p z Complex.I ExactFourierCircuits.a⁻¹)).val.look
        (lane.val*c.ambient+d.val) 0=
          UniformActualCalendarRectangleEvent.values c q slot l bl ha he bank lane d := by
  let geometry:=dispatched_geometry c q slot l bl ha he
  have output:=produces_native c.ambient (UniformActualCalendarRectangleEvent.edges c q slot l bl ha he)
    (rowEdges_matching _ geometry.2.1 geometry.2.2)
    (rowEdges_range c.ambient _ geometry.2.1 geometry.1)
    radix p z (UniformActualCalendarRectangleEvent.coefficients c q slot l bl ha he bank)
    ⟨length,permutation⟩ coefficients
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2.1,?_⟩
  intro lane d
  exact (output.2.2.2.2 lane d).trans
    (UniformActualCalendarRectangleEvent.values_native c q slot l bl ha he bank lane d).symm

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors
