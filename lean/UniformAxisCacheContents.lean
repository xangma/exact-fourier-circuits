import UniformAxisCacheForestExecution
import UniformAxisCacheRectangleTransport
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheContents
open UniformMachine UniformAxisCacheStartupMachine UniformJointCacheAllocation
open UniformAxisCacheForestEntry UniformAxisCacheForestGeometry UniformAxisCacheCanonicalRequests
open UniformAxisCacheForestExecution UniformAxisCachePhysical
noncomputable section

/-- Every persistent rectangle factor and forward leaf factor of one actual axis. -/
structure Contents (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (s:State):Prop where
 leaves:UniformDirectLeafForestContents.Contents (parameters c n j) (visits c n j)
  (UniformAllAxisSeedPreparation.axisBase n j.val) (positive c n hn j) s
 rectangles:∀i (hi:i<(canonical c n j).length),UniformLocalRequestGeometry.Complete c n j
  (canonical c n j) (axis c n j).requests (axis c n j).requestStarts (geometry c n hn j) i hi s

lemma of_outcome {c n hn j x s u} (h:Outcome c n hn j x s u):Contents c n hn j u:=
 ⟨h.contents,h.rectangles⟩

/-- Later axis preparations transport the actual produced cells, including
their coefficient semantics, through exact allocated interval equalities. -/
theorem transport {c n hn j s u} (h:Contents c n hn j s) (frame:Heaps c n j s u):Contents c n hn j u:=by
 have l:=placement c n hn j
 have b:=bounds c n hn j
 have nodeEnd:(axis c n j).nodes≤(axis c n j).endNat:=by dsimp only[axis,axisBank];omega
 have cacheEnd:(parameters c n j).start.permutation+
   (3*(parameters c n j).radix+11)*UniformDirectLeafForestModel.demand (visits c n j)≤(axis c n j).endNat:=by
  have bound:=b.cacheEnd
  have leafEnd:(axis c n j).leafForward≤(axis c n j).endNat:=by have:=b.leafFit;omega
  simpa only[parameters,Nat.mul_add,Nat.add_assoc] using bound.trans leafEnd
 refine ⟨?_,fun i hi=>UniformAxisCacheRectangleTransport.complete (geometry c n hn j) i hi (h.rectangles i hi) frame⟩
 apply UniformDirectLeafForestContents.transport h.leaves l (UniformAxisCacheForestEntry.facts c n j)
  (N:=(axis c n j).tasks) (H:=(axis c n j).endNat)
  (S:=(axis c n j).pool) (E:=(axis c n j).endScalar) (le_refl _) cacheEnd
 · exact l.headerEnd.trans nodeEnd
 · change (axis c n j).tasks≤(axis c n j).durations
   dsimp only[axis,axisBank]
   omega
 · change (axis c n j).durations<(axis c n j).endNat
   dsimp only[axis,axisBank]
   omega
 · change (axis c n j).pool≤(axis c n j).pool+9*UniformAllAxisSeedPreparation.radix n j*rectangleCount c n j
   omega
 · simpa only[parameters,Nat.mul_add,Nat.add_assoc] using b.scalarEnd
 · exact frame.nat
 · exact frame.scalar

end
end ExactFourierCircuits.UniformAxisCacheContents
