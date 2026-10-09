import UniformRecursiveResidualFiberValues
import UniformNativeResidualSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualSignedValues
open UniformMachine BinaryFrames UniformBinaryTensorCoordinates UniformBinaryXorCoordinates
open UniformResidualExtendedPermutation UniformResidualFibers
open UniformNativeResidualSemantics UniformNativeCopiedInverse
noncomputable section

/-- Physical gather fibers and the signed copied-column compiler use the same
explicit native coordinates, including every high spectator bit. -/
lemma signed_fiber (q w r:ℕ)(v:Vec (Fin (w+1)))(hv:dot v v=1)
 (p:Fin (w+1))(hp:v p=1)(decreasing:Bool)(X:Fin (2^(q*(w+1)+r))→ℂ)
 (b:Fin (2^(q*w+r)))(t:Fin (2^q)):
 (spectatorMatrix (q*(w+1)) r (nativeWordMatrix (signedColumnWord q v hv decreasing))).mulVec X
  (fibers q w r v p hp (b,t))=
 (physicalMatrix q).mulVec (fun z=>X (fibers q w r v p hp (b,z)))
  (if inverseOrientation v decreasing then xorIndex t (UniformPhysicalBinaryInverse.mask q) else t):=by
 have coord(z:Fin (2^q)):fibers q w r v p hp (b,z)=
  (spectatorSplit (q*(w+1)) r).symm
   ((UniformResidualSpectators.split (q*w) r b).1,
    UniformResidualNativeCoordinates.nativeFiber q w v p hp ((UniformResidualSpectators.split (q*w) r b).2,z)):=by
  apply (spectatorSplit (q*(w+1)) r).injective
  rw [Equiv.apply_symm_apply]
  exact fibers_coordinates q w r v p hp b z
 rw [coord t]
 simpa only [coord] using native_signed_spectator_array q w r v hv p hp decreasing X
  (UniformResidualSpectators.split (q*w) r b).1 (UniformResidualSpectators.split (q*w) r b).2 t

/-- Actual returned recursive Scalars and physical scatter give the exact
signed residual matrix. Presence and numeric values are established together;
tags are whatever the executed child arithmetic returned. -/
theorem scatter_signed (q w r D E:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (qk:q ≤ q*(w+1)+r)(v:Vec (Fin (w+1)))(hv:dot v v=1)(p:Fin (w+1))(hp:v p=1)
 (decreasing:Bool)(X:Fin (2^(q*(w+1)+r))→Scalar)(a u:State)
 (bank:UniformRecursiveGroupLoop.Bank q (UniformRecursiveBatchGroupMachine.groupCount q w r) D
  (UniformRecursiveBatchGroupMachine.groupCount q w r)
  (UniformRecursiveResidualFiberValues.input q w r fits v p hp X) a)
 (scatter:∀z,u.scalarHeap (E+(UniformResidualSpectators.extend (q*(w+1)) r
  (UniformResidualPermutation.permutation q w v p hp) z).val)=some
  (UniformRecursiveResidualOutput.selected (q*(w+1)+r) q qk (inverseOrientation v decreasing)
   (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) a) z)):
 ∀z:Fin (2^(q*(w+1)+r)),(u.scalarHeap (E+z.val)).isSome=true ∧
 (u.scalarHeap (E+z.val)).map Scalar.value=some
  ((spectatorMatrix (q*(w+1)) r (nativeWordMatrix (signedColumnWord q v hv decreasing))).mulVec
   (fun y=>(X y).value) z):=by
 intro z
 obtain ⟨⟨b,t⟩,rfl⟩:=(fibers q w r v p hp).surjective z
 have h:=UniformRecursiveResidualFiberValues.scatter_values q w r D E fits qk
  (inverseOrientation v decreasing) v p hp X a u bank scatter b t
 rw [signed_fiber q w r v hv p hp decreasing (fun y=>(X y).value) b t]
 exact h
end
end ExactFourierCircuits.UniformRecursiveResidualSignedValues
