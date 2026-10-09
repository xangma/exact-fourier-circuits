import UniformRecursiveTypedBody
import UniformRecursiveFrontierRoom
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveBodyGeometry
open UniformMachine UniformFixedNetwork UniformRecursiveTypedBody UniformRecursiveNodePreparation
noncomputable section

lemma reserve_le {F reserve k B:ℕ}(room:F+reserve*(k+1)*2^k ≤ B):reserve ≤ B:=by
 have v:1 ≤ 2^k:=Nat.two_pow_pos k
 have p:=Nat.mul_le_mul_left reserve (show 1 ≤ k+1 by omega)
 have t:=Nat.mul_le_mul_left (reserve*(k+1)) v
 simp only [Nat.mul_one] at p t
 omega

/-- The actual printer allocation and child reserve fit inside the incoming
same-budget room. No generated Geometry predicate is an entry assumption. -/
theorem geometry (B A F M l q rest stack depth stackTop reserve:ℕ)
 (qp:1 ≤ q)(rp:rest < m)(smaller:q < q*m+rest)
 (reserveFit:M+l+11 ≤ reserve)(widthFit:m+1 ≤ reserve)
 (parentRoom:F+reserve*(q*m+rest+1)*2^(q*m+rest) ≤ B)
 (arrayEnd:A+W*2^(q*m+rest) ≤ F)(base:3 ≤ A)
 (stackRoom:stack+34*(depth+(q*m+rest)+1) ≤ stackTop)
 (square:(2^(q*m+rest))^2 ≤ B)
 (code:UniformRecursiveSavingProgram.program.length ≤ B):
 Geometry B A (workBase F M l) q rest stack depth stackTop reserve:=by
 have rb:reserve ≤ B:=reserve_le parentRoom
 have room:=UniformRecursiveFrontierRoom.child_room F (M+l+6) reserve (q*m+rest) q B smaller
  (by omega) parentRoom
 have room':workBase F M l+5*2^(q*m+rest)+reserve*(q+1)*2^q ≤ B:=by
  simpa only [workBase,unitBase,Nat.add_assoc] using room
 have geom:71 ≤ q*(m-1)+rest:=by
  have mBound:71 ≤ m-1:=by norm_num [m,ExplicitSeedBudget.m]
  have h:=Nat.mul_le_mul_right (m-1) qp
  simp only [Nat.one_mul] at h
  omega
 refine ⟨qp,rp,smaller,?_,widthFit.trans rb,?_,?_,square,?_,base,?_,room',code⟩
 · simpa only [ExplicitSeedBudget.roleBits] using geom
 · unfold workBase unitBase;omega
 · omega
 · unfold workBase unitBase;omega
 · have h:=Nat.mul_le_mul_left 34 (show depth+q+2 ≤ depth+(q*m+rest)+1 by omega)
   omega
end
end ExactFourierCircuits.UniformRecursiveBodyGeometry
