import UniformRecursivePaddingFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingArrays
open UniformMachine
open UniformFixedNetworkShearChildMachine (Present roleBase role_bound role_outside)
noncomputable section

def values {R V:ℕ}(f:Fin R→Fin V→Scalar):Fin R→Fin V→ℂ:=fun i j=>(f i j).value
def lowMatrix (q w r:ℕ):Matrix (Fin (2^(q*(w+1)+r))) (Fin (2^(q*(w+1)+r))) ℂ:=
 UniformNativeCopiedInverse.spectatorMatrix (q*(w+1)) r (UniformBinaryTensorCoordinates.physicalMatrix (q*(w+1)))
def applyRole (q w r R:ℕ)(role:Fin R)(f:Fin R→Fin (2^(q*(w+1)+r))→ℂ):
 Fin R→Fin (2^(q*(w+1)+r))→ℂ:=Function.update f role ((lowMatrix q w r).mulVec (f role))
def action (q w r R:ℕ)(L:List (Fin R))(f:Fin R→Fin (2^(q*(w+1)+r))→ℂ):
 Fin R→Fin (2^(q*(w+1)+r))→ℂ:=L.foldl (fun a i=>applyRole q w r R i a) f

lemma present_update {A R V F:ℕ}{s u:State}{f:Fin R→Fin V→Scalar}(role:Fin R)(Y:Fin V→Scalar)
 (present:Present A R V f s)(endBound:A+R*V ≤ F)
 (data:∀z,u.scalarHeap (A+role.val*V+z.val)=some (Y z))
 (frame:∀z,z<F→(z<A+role.val*V∨A+(role.val+1)*V ≤ z)→u.scalarHeap z=s.scalarHeap z):
 Present A R V (Function.update f role Y) u:=by
 intro i z
 by_cases eq:i=role
 · subst i;simpa only[Function.update_self] using data z
 · have upper:=role_bound A V i
   have zBound:=z.isLt
   have inside:A+i.val*V+z.val<F:=by unfold roleBase at upper;omega
   have outside:=role_outside A role i eq z
   unfold roleBase at outside
   rw[frame _ inside (by simpa only[Nat.add_mul,Nat.one_mul,Nat.add_assoc] using outside),Function.update_of_ne eq]
   exact present i z

lemma values_update {q w r R:ℕ}(role:Fin R)(f:Fin R→Fin (2^(q*(w+1)+r))→Scalar)
 (Y:Fin (2^(q*(w+1)+r))→Scalar)
 (value:∀z,(Y z).value=(lowMatrix q w r).mulVec (values f role) z):
 values (Function.update f role Y)=applyRole q w r R role (values f):=by
 funext i z
 by_cases eq:i=role
 · subst i;simpa only[values,applyRole,Function.update_self] using value z
 · simp only[values,applyRole,Function.update_of_ne eq]

/-- The actual ascending counter applies the low matrix once to each remaining
physical role, retaining every earlier role exactly. -/
lemma action_indices (q w r R start fuel:ℕ)(h:start+fuel=R)
 (f:Fin R→Fin (2^(q*(w+1)+r))→ℂ)(i:Fin R):
 action q w r R (UniformRecursiveResidualDirectionLoop.indices R start fuel h) f i=
 if start ≤ i.val then (lowMatrix q w r).mulVec (f i) else f i:=by
 induction fuel generalizing start f with
 | zero=>
  have notLE:¬start ≤ i.val:=by have hi:=i.isLt;omega
  simp only[UniformRecursiveResidualDirectionLoop.indices,action,List.foldl_nil,notLE,ite_false]
 | succ fuel ih=>
  let j:Fin R:=⟨start,by omega⟩
  change action q w r R (UniformRecursiveResidualDirectionLoop.indices R (start+1) fuel (by omega))
   (applyRole q w r R j f) i=_
  rw[ih]
  by_cases eq:i.val=start
  · have ij:i=j:=Fin.ext eq
    have no:¬start+1 ≤ i.val:=by omega
    have yes:start ≤ i.val:=by omega
    rw[ite_eq_right no,ite_eq_left yes]
    simp only[applyRole,ij,Function.update_self]
  · have ij:i≠j:=by intro h;exact eq (congrArg Fin.val h)
    simp only[applyRole,Function.update_of_ne ij]
    by_cases yes:start ≤ i.val
    · rw[ite_eq_left yes,ite_eq_left (by omega:start+1 ≤ i.val)]
    · rw[ite_eq_right yes,ite_eq_right (by omega:¬start+1 ≤ i.val)]
end
end ExactFourierCircuits.UniformRecursivePaddingArrays
