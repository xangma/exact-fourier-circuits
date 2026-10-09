import UniformRecursiveResidualOutput
import UniformResidualExtendedPermutation
import UniformNativeLowXor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualFiberValues
open UniformMachine BinaryFrames UniformBinaryTensorCoordinates UniformBinaryXorCoordinates
open UniformResidualExtendedPermutation
noncomputable section
abbrev W:=UniformRecursiveSelfCallMachine.W

def representative (q w r:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r):
 (Fin (UniformRecursiveBatchGroupMachine.groupCount q w r)×Fin W)≃Fin (2^(q*w+r)):=
 finProdFinEquiv.trans (finCongr (by
  have width:W=2^ExplicitSeedBudget.roleBits:=UniformRecursiveBatchGroupMachine.W_eq
  rw [UniformRecursiveBatchGroupMachine.groupCount,width,←Nat.pow_add]
  congr 1
  omega))
lemma representative_value_generic(a b c:ℕ)(eq:a*b=c)(g:Fin a)(i:Fin b):
 ((finProdFinEquiv.trans (finCongr eq)) (g,i)).val=g.val*b+i.val:=by
 simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
lemma representative_value(q w r:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (g:Fin (UniformRecursiveBatchGroupMachine.groupCount q w r))(i:Fin W):
 (representative q w r fits (g,i)).val=g.val*W+i.val:=by
 exact representative_value_generic _ _ _ _ g i

lemma flatten_fiber(q w r:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (g:Fin (UniformRecursiveBatchGroupMachine.groupCount q w r))(i:Fin W)(t:Fin (2^q)):
 UniformRecursiveGroupBank.flatten (UniformRecursiveBatchGroupMachine.groupCount q w r) W (2^q)
  (2^(q*(w+1)+r)) (UniformRecursiveBatchGroupMachine.partition q w r fits) (g,(i,t))=
 flat q w r (representative q w r fits (g,i),t):=by
 apply Fin.ext
 rw [UniformRecursiveGroupBank.flatten_value,flat_value,representative_value]
 ring

def input(q w r:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (v:Vec (Fin (w+1)))(p:Fin (w+1))(hp:v p=1)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (g:Fin (UniformRecursiveBatchGroupMachine.groupCount q w r))(i:Fin W)(t:Fin (2^q)):Scalar:=
 X (fibers q w r v p hp (representative q w r fits (g,i),t))

/-- The actual complete returned group bank evaluates exactly on every original
spectator/representative fiber, with the original q bits still inner. -/
theorem complete_values(q w r D:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (v:Vec (Fin (w+1)))(p:Fin (w+1))(hp:v p=1)(X:Fin (2^(q*(w+1)+r))→Scalar)(s:State)
 (bank:UniformRecursiveGroupLoop.Bank q (UniformRecursiveBatchGroupMachine.groupCount q w r) D
  (UniformRecursiveBatchGroupMachine.groupCount q w r) (input q w r fits v p hp X) s)
 (b:Fin (2^(q*w+r)))(t:Fin (2^q)):
 (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) s (flat q w r (b,t))).value=
 (physicalMatrix q).mulVec (fun z=>(X (fibers q w r v p hp (b,z))).value) t:=by
 obtain ⟨⟨g,i⟩,eq⟩:=(representative q w r fits).surjective b
 have h:=UniformRecursiveGroupBank.complete_values (UniformRecursiveBatchGroupMachine.partition q w r fits) bank g i t
 rw [flatten_fiber q w r fits g i t,eq] at h
 simpa only [input,eq] using h

lemma selected_flat(q w r:ℕ)(qk:q ≤ q*(w+1)+r)
 (b:Fin (2^(q*w+r)))(t:Fin (2^q)):
 (⟨(flat q w r (b,t)).val^^^(2^q-1),Nat.xor_lt_two_pow (flat q w r (b,t)).isLt
  (by have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk;have p:=Nat.two_pow_pos q;omega)⟩:
  Fin (2^(q*(w+1)+r)))=
 flat q w r (b,xorIndex t (UniformPhysicalBinaryInverse.mask q)):=by
 apply Fin.ext
 change (flat q w r (b,t)).val^^^(2^q-1)=(flat q w r (b,xorIndex t (UniformPhysicalBinaryInverse.mask q))).val
 rw [flat_value,flat_value]
 change (b.val*2^q+t.val)^^^(2^q-1)=b.val*2^q+(t.val^^^(UniformPhysicalBinaryInverse.mask q).val)
 rw [UniformPhysicalBinaryInverse.mask_value]
 exact UniformNativeLowXor.low_mask q b.val t.val t.isLt

/-- Inverse orientation is an explicit effective Boolean. It must include the
original residual's weight-three phase; this lemma does not identify it with
an uncorrected geometric flag. -/
theorem selected_values(q w r D:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)(qk:q ≤ q*(w+1)+r)
 (inv:Bool)(v:Vec (Fin (w+1)))(p:Fin (w+1))(hp:v p=1)(X:Fin (2^(q*(w+1)+r))→Scalar)(s:State)
 (bank:UniformRecursiveGroupLoop.Bank q (UniformRecursiveBatchGroupMachine.groupCount q w r) D
  (UniformRecursiveBatchGroupMachine.groupCount q w r) (input q w r fits v p hp X) s)
 (b:Fin (2^(q*w+r)))(t:Fin (2^q)):
 (UniformRecursiveResidualOutput.selected (q*(w+1)+r) q qk inv
  (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) s) (flat q w r (b,t))).value=
 (physicalMatrix q).mulVec (fun z=>(X (fibers q w r v p hp (b,z))).value)
  (if inv then xorIndex t (UniformPhysicalBinaryInverse.mask q) else t):=by
 cases inv
 · simpa only [UniformRecursiveResidualOutput.selected,Bool.false_eq_true,ite_false] using
   complete_values q w r D fits v p hp X s bank b t
 · simp only [UniformRecursiveResidualOutput.selected,ite_true]
   rw [selected_flat q w r qk b t]
   exact complete_values q w r D fits v p hp X s bank b _

/-- The physical scatter addresses exactly the original native copied-column
fibers; flags remain actual Scalars returned by the real recursive groups. -/
theorem scatter_values(q w r D E:ℕ)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)(qk:q ≤ q*(w+1)+r)
 (inv:Bool)(v:Vec (Fin (w+1)))(p:Fin (w+1))(hp:v p=1)(X:Fin (2^(q*(w+1)+r))→Scalar)(a u:State)
 (bank:UniformRecursiveGroupLoop.Bank q (UniformRecursiveBatchGroupMachine.groupCount q w r) D
  (UniformRecursiveBatchGroupMachine.groupCount q w r) (input q w r fits v p hp X) a)
 (scatter:∀z,u.scalarHeap (E+(UniformResidualSpectators.extend (q*(w+1)) r
  (UniformResidualPermutation.permutation q w v p hp) z).val)=some
  (UniformRecursiveResidualOutput.selected (q*(w+1)+r) q qk inv
   (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) a) z))
 (b:Fin (2^(q*w+r)))(t:Fin (2^q)):
 (u.scalarHeap (E+(fibers q w r v p hp (b,t)).val)).isSome=true ∧
 (u.scalarHeap (E+(fibers q w r v p hp (b,t)).val)).map Scalar.value=some
  ((physicalMatrix q).mulVec (fun z=>(X (fibers q w r v p hp (b,z))).value)
   (if inv then xorIndex t (UniformPhysicalBinaryInverse.mask q) else t)):=by
 have h:=scatter (flat q w r (b,t))
 rw [fibers_flat] at h
 rw [h]
 simp only [Option.isSome_some,Option.map_some,true_and]
 congr 1
 exact selected_values q w r D fits qk inv v p hp X a bank b t
end
end ExactFourierCircuits.UniformRecursiveResidualFiberValues
