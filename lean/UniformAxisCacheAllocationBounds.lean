import UniformAxisCacheAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAllocationMachine
open UniformMachine UniformNatBlockMachine
noncomputable section
attribute [local irreducible] Nat.mul

lemma endNat_formula (r N S : ℕ) :
 (C.axisBank r N S).endNat=N+13*(2*r+2)+7*(2*r+2)*r^2+9*r^2+
  (3*r+11)*UniformJointCacheExtent.capacity r := by
 dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank]
 ring

lemma computed_capacity (r : ℕ) : r*r*(D.amount (2*r) 0/28+4)=UniformJointCacheExtent.capacity r := by
 rw [capacity_amount]
 simp only [UniformJointCacheExtent.capacity,pow_two]

structure NumericBounds (r N S B : ℕ) : Prop where
 code:100≤B
 rowBudget:D.budget (2*r) 0≤B
 amount:D.amount (2*r) 0≤B
 quotient:D.amount (2*r) 0/28≤B
 slots:D.amount (2*r) 0/28+4≤B
 twice:2*r≤B
 nodeCount:2*r+2≤B
 square:r*r≤B
 capacity:UniformJointCacheExtent.capacity r≤B
 stack:4*(2*r+2)≤B
 directory:7*(2*r+2)≤B
 rectangles:7*(2*r+2)*(r*r)≤B
 triple:3*r≤B
 stride:3*r+11≤B
 cache:(3*r+11)*UniformJointCacheExtent.capacity r≤B
 fourSquare:4*(r*r)≤B
 eightSquare:8*(r*r)≤B
 twoCount:2*(2*r+2)≤B
 nineRadix:9*r≤B
 factors:9*r*UniformJointCacheExtent.capacity r≤B
 natFrontier:N≤B
 scalarFrontier:S≤B
 endpoints:∀a∈[(C.axisBank r N S).tasks,(C.axisBank r N S).nodes,
  (C.axisBank r N S).requests,(C.axisBank r N S).control,(C.axisBank r N S).leafForward,
  (C.axisBank r N S).leafTranspose,(C.axisBank r N S).durations,(C.axisBank r N S).nodeStarts,
  (C.axisBank r N S).requestStarts,(C.axisBank r N S).endNat,(C.axisBank r N S).pool,
  (C.axisBank r N S).endScalar],a≤B

lemma numeric_bounds (r N S : ℕ) : NumericBounds r N S (wordBudget r N S) := by
 let B:=wordBudget r N S
 let E:=(C.axisBank r N S).endNat
 let F:=(C.axisBank r N S).endScalar
 let cap:=UniformJointCacheExtent.capacity r
 have log:Nat.clog 2 (4*r)≤4*r:=Nat.clog_le_of_le_pow
  (UniformRecursiveBatchHeaderMachine.index_le_power (4*r))
 have row:D.budget (2*r) 0≤B:=by dsimp only [B,wordBudget];omega
 have rowFormula:D.budget (2*r) 0=20000*(2*r+1):=rfl
 have amount:D.amount (2*r) 0≤D.budget (2*r) 0:=by
  unfold D.amount
  rw [show 2*(2*r+0)=4*r by omega,rowFormula]
  omega
 have slots:D.amount (2*r) 0/28+4≤D.budget (2*r) 0:=by
  rw [capacity_amount,UniformJointCacheExtent.slotCount_formula,rowFormula]
  omega
 have natEnd:E≤B:=by dsimp only [B,E,wordBudget];omega
 have scalarEnd:F≤B:=by dsimp only [B,F,wordBudget];omega
 have natFormula:E=N+13*(2*r+2)+7*(2*r+2)*r^2+9*r^2+(3*r+11)*cap:=endNat_formula r N S
 have scalarFormula:F=S+9*r*cap:=rfl
 have square:r*r≤E:=by rw [pow_two] at natFormula;omega
 have cache:(3*r+11)*cap≤E:=by omega
 have capacity:cap≤E:=by nlinarith only [cache]
 constructor
 · have:100≤D.budget (2*r) 0:=by rw [rowFormula];omega
   exact this.trans row
 · exact row
 · exact amount.trans row
 · exact (Nat.div_le_self _ _).trans (amount.trans row)
 · exact slots.trans row
 · have:2*r≤D.budget (2*r) 0:=by rw [rowFormula];omega
   exact this.trans row
 · have:2*r+2≤E:=by omega
   exact this.trans natEnd
 · exact square.trans natEnd
 · exact capacity.trans natEnd
 · have:4*(2*r+2)≤E:=by omega
   exact this.trans natEnd
 · have:7*(2*r+2)≤E:=by omega
   exact this.trans natEnd
 · have:7*(2*r+2)*(r*r)≤E:=by rw [pow_two] at natFormula;omega
   exact this.trans natEnd
 · have:3*r≤D.budget (2*r) 0:=by rw [rowFormula];omega
   exact this.trans row
 · have:3*r+11≤D.budget (2*r) 0:=by rw [rowFormula];omega
   exact this.trans row
 · exact cache.trans natEnd
 · have:4*(r*r)≤E:=by rw [pow_two] at natFormula;omega
   exact this.trans natEnd
 · have:8*(r*r)≤E:=by rw [pow_two] at natFormula;omega
   exact this.trans natEnd
 · have:2*(2*r+2)≤E:=by omega
   exact this.trans natEnd
 · have:9*r≤D.budget (2*r) 0:=by rw [rowFormula];omega
   exact this.trans row
 · have:9*r*cap≤F:=by omega
   exact this.trans scalarEnd
 · have:N≤E:=by omega
   exact this.trans natEnd
 · have:S≤F:=by omega
   exact this.trans scalarEnd
 · intro a ha
   simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
   dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank] at ha
   change N+4*(2*r+2)+7*(2*r+2)+7*(2*r+2)*r^2+
    (3*r+11)*cap+8*r^2+2*(2*r+2)+r^2≤B at natEnd
   change S+9*r*cap≤B at scalarEnd
   dsimp only [cap] at natEnd scalarEnd
   rcases ha with h|h|h|h|h|h|h|h|h|h|h|h
   all_goals subst a;omega

lemma NumericBounds.mono {r N S A B : ℕ} (h : NumericBounds r N S A) (bound : A≤B) :
 NumericBounds r N S B := by
 rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w⟩
 exact ⟨a.trans bound,b.trans bound,c.trans bound,d.trans bound,e.trans bound,f.trans bound,
  g.trans bound,h.trans bound,i.trans bound,j.trans bound,k.trans bound,l.trans bound,m.trans bound,
  n.trans bound,o.trans bound,p.trans bound,q.trans bound,r.trans bound,s.trans bound,t.trans bound,
  u.trans bound,v.trans bound,fun z hz=>(w z hz).trans bound⟩
end
end ExactFourierCircuits.UniformAxisCacheAllocationMachine
