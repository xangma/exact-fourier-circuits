import UniformSectorPacking
import Mathlib.Data.List.OfFn

namespace ExactFourierCircuits.UniformSectorTraversalOrder

open UniformTraversal UniformSectorPacking

/-- Leaves in child-index order. This is a mathematical specification, not a RAM oracle. -/
def lexOutcomes {α : Type*} : List (Layer α) → α → List α
  | [], s => [s]
  | l :: ls, s => (List.finRange l.radix).flatMap (fun d => lexOutcomes ls (l.advance d s))

theorem foldl_output {α β : Type*} (xs : List β) (step : Acc α → β → Acc α)
    (f : β → List α) (hs : ∀ a d, (step a d).output = (f d).reverse ++ a.output)
    (acc : Acc α) :
    (xs.foldl step acc).output = (xs.flatMap f).reverse ++ acc.output := by
  induction xs generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, hs]
    simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem traverse_output {α : Type*} (ls : List (Layer α)) (s : α) (acc : Acc α) :
    (traverse ls s acc).output = (lexOutcomes ls s).reverse ++ acc.output := by
  induction ls generalizing s acc with
  | nil => simp [UniformTraversal.traverse, lexOutcomes]
  | cons l ls ih =>
    exact foldl_output (List.finRange l.radix)
      (fun a d => traverse ls (l.advance d s) a)
      (fun d => lexOutcomes ls (l.advance d s)) (fun a d => ih _ _) _

theorem run_output_reverse {α : Type*} (ls : List (Layer α)) (s : α) :
    (run ls s).output.reverse = lexOutcomes ls s := by
  simp [run, traverse_output]

/-- The existing mixed-radix codec enumerates exactly the traversal's child order. -/
theorem block_lex_ofFn (axes : List Axis) (s : BlockState) :
    lexOutcomes (blockLayers axes) s =
      List.ofFn (fun i : Fin (blockCounts axes).prod =>
        follow (blockLayers axes)
          (blockTraversalEquiv axes ((mixedEquiv (blockCounts axes)).symm i)) s) := by
  induction axes generalizing s with
  | nil => simp [blockLayers, lexOutcomes, blockCounts, blockTraversalEquiv, follow]
  | cons a axes ih =>
    change (List.finRange a.widths.length).flatMap (fun d =>
      lexOutcomes (blockLayers axes)
        (blockAdvance a (UniformSectorPacking.radices axes).prod d s)) =
      List.ofFn (fun i : Fin (a.widths.length * (blockCounts axes).prod) =>
        follow (blockLayers axes)
          (blockTraversalEquiv axes ((mixedEquiv (blockCounts axes)).symm
            (finProdFinEquiv.symm i).2))
          (blockAdvance a (UniformSectorPacking.radices axes).prod
            (finProdFinEquiv.symm i).1 s))
    simp_rw [ih]
    change ((List.finRange a.widths.length).map (fun d =>
      List.ofFn (fun i : Fin (blockCounts axes).prod =>
        follow (blockLayers axes)
          (blockTraversalEquiv axes ((mixedEquiv (blockCounts axes)).symm i))
          (blockAdvance a (UniformSectorPacking.radices axes).prod d s)))).flatten = _
    rw [← List.ofFn_eq_map]
    rw [List.ofFn_mul]
    congr 1
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    have hi : (⟨i.val * (blockCounts axes).prod + j.val,
        by nlinarith [i.isLt, j.isLt]⟩ : Fin (a.widths.length * (blockCounts axes).prod)) =
        finProdFinEquiv (i, j) := by
      apply Fin.ext
      change i.val * (blockCounts axes).prod + j.val =
        j.val + (blockCounts axes).prod * i.val
      ring
    rw [hi, Equiv.symm_apply_apply]

theorem block_lex_sectorStates (axes : List Axis) :
    lexOutcomes (blockLayers axes) initialBlockState = sectorStates axes := by
  rw [block_lex_ofFn]
  simp_rw [follow_block_initial]
  rw [List.ofFn_congr (sectorWidths_length axes).symm]
  rfl

theorem run_sectorStates (axes : List Axis) :
    (run (blockLayers axes) initialBlockState).output.reverse = sectorStates axes := by
  rw [run_output_reverse, block_lex_sectorStates]

end ExactFourierCircuits.UniformSectorTraversalOrder
