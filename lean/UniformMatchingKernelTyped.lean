import UniformMatchingKernelGeometry
import UniformGlobalCalendarMatchingPhase
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingKernelTyped
noncomputable section
open OAI.ExactFourier UniformReplayPrint UniformToeplitzChunkWord UniformSectorPacking UniformSectorTensor
open UniformMatchingAxisTableMachine UniformMatchingKernelGeometry
open UniformGlobalCalendarMatchingPhase

lemma edges_range {v R:ℕ} (W:List (ShearCode (Fin v) R)):InRange v (edges W):=by
 intro i
 exact ⟨(W.get i).dst.isLt,(W.get i).src.isLt⟩

def axis {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):Axis:=geometry v (edges W) (edges_matching W hm) (edges_range W) hp
lemma axis_sum {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):(axis W hm hp).widths.sum=v:=
 widths_sum v W.length (matching_capacity v (edges W) (edges_matching W hm) (edges_range W))
def radixCoordinate {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):Fin (axis W hm hp).widths.sum ≃ Fin v:=finCongr (axis_sum W hm hp)
def orderedPosition {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):(Σ _:Fin W.length,Fin 2) ↪ Fin v:=
 (position v (edges W) (edges_matching W hm) (edges_range W) hp).trans (radixCoordinate W hm hp).toEmbedding

/-- The actual55 permutation preserves the literal typed destination/source order. -/
theorem ordered_position {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):orderedPosition W hm hp=UniformToeplitzChunkWord.pairPosition W hm:=by
 apply Function.Embedding.ext
 rintro ⟨i,t⟩
 apply Fin.ext
 change (position v (edges W) (edges_matching W hm) (edges_range W) hp ⟨i,t⟩).val=_
 rw[position_value]
 fin_cases t <;> rfl

/-- The printed physical kernel, in ambient radix order, is exactly the
ordered C family used by the actual typed matching layers. -/
theorem local_kernel {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):
 Matrix.reindex (radixCoordinate W hm hp) (radixCoordinate W hm hp) (localKernel (axis W hm hp))=
 Embedded.matrix (UniformToeplitzChunkWord.pairPosition W hm) (Matrix.blockDiagonal' (fun _:Fin W.length=>C)):=by
 let e:=radixCoordinate W hm hp
 let pos:=position v (edges W) (edges_matching W hm) (edges_range W) hp
 let blocks:=Matrix.blockDiagonal' (fun _:Fin W.length=>C)
 have core:localKernel (axis W hm hp)=Embedded.matrix pos blocks:=
  kernel_matrix v (edges W) (edges_matching W hm) (edges_range W) hp
 calc
  Matrix.reindex e e (localKernel (axis W hm hp))=
   Embedded.matrix e.toEmbedding (localKernel (axis W hm hp)):=(Embedded.matrix_equiv e _).symm
  _=Embedded.matrix e.toEmbedding (Embedded.matrix pos blocks):=congrArg (Embedded.matrix e.toEmbedding) core
  _=Embedded.matrix (pos.trans e.toEmbedding) blocks:=Embedded.matrix_comp pos e.toEmbedding blocks
  _=Embedded.matrix (UniformToeplitzChunkWord.pairPosition W hm) blocks:=
   congrArg (fun p=>Embedded.matrix p blocks) (ordered_position W hm hp)

lemma unary_volume {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):(radices [axis W hm hp]).prod=v:=by
 simpa only[radices,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one] using axis_sum W hm hp

/-- Unary originalTensor produced by the real55 axis is the same physical
C kernel as the literal typed matching schedule. -/
theorem original_kernel {v R:ℕ} (W:List (ShearCode (Fin v) R)) (hm:UniformToeplitzChunkWord.Matching W)
 (hp:2 ≤ v):
 Matrix.reindex (finCongr (unary_volume W hm hp)) (finCongr (unary_volume W hm hp))
  (originalTensor [axis W hm hp])=
 Embedded.matrix (UniformToeplitzChunkWord.pairPosition W hm) (Matrix.blockDiagonal' (fun _:Fin W.length=>C)):=by
 rw[←local_kernel W hm hp]
 ext i j
 have h:=congrArg (fun A:Matrix (Fin (axis W hm hp).widths.sum) (Fin (axis W hm hp).widths.sum) ℂ=>
  A ((radixCoordinate W hm hp).symm i) ((radixCoordinate W hm hp).symm j))
   (single_original (axis W hm hp))
 exact h
/-- Each literal cached matching phase is the native diagonal or the
originalTensor of the real printed55 axis, with the exact phase offset. -/
theorem physical_phase {v R:ℕ} (bank:Fin R→ℂ) (W:List (ShearCode (Fin v) R))
 (hm:UniformToeplitzChunkWord.Matching W) (hp:2 ≤ v) (t:Fin 28):
 ((UniformLocalFourierLayers.matchingLayers bank W hm).get
   ⟨t.val,by rw[UniformLocalFourierLayers.matchingLayers_length];exact t.isLt⟩).matrix=
 match UniformGlobalMatchingScaleMachine.phases.get
   ⟨t.val,by rw[UniformGlobalMatchingScaleMachine.phases_length];exact t.isLt⟩ with
 | .diagonal lane=>Matrix.diagonal (fun i:Fin v=>
    UniformGlobalMatchingScaleBankBridge.nativeFactor (edges W) (coefficients bank W) lane i.val)
 | .kernel=>Matrix.reindex (finCongr (unary_volume W hm hp)) (finCongr (unary_volume W hm hp))
    (originalTensor [axis W hm hp]):=by
 rw[matching_phase_matrix]
 generalize UniformGlobalMatchingScaleMachine.phases.get
  ⟨t.val,by rw[UniformGlobalMatchingScaleMachine.phases_length];exact t.isLt⟩=phase
 cases phase with
 | diagonal lane=>exact matching_diagonal bank W hm lane
 | kernel=>exact (original_kernel W hm hp).symm
end
end ExactFourierCircuits.UniformMatchingKernelTyped
