import UniformNatBlockMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNatHeaderFrame
open UniformMachine UniformNatBlockMachine
noncomputable section

def keeps (o:Op)(q:ℕ):Prop:=match o with
 | .literal d _=>q≠d
 | .binary _ d _ _=>q≠d
 | .load d _=>q≠d
 | .store _ _=>True
lemma op_natReg(o:Op)(s:State)(q:ℕ)(keep:keeps o q):
 (o.apply s).natReg q=s.natReg q:=by
 cases o <;>simp_all[keeps,Op.apply,writeNat,next]
lemma block_natReg(ops:List Op)(s:State)(q:ℕ)(keep:∀o∈ops,keeps o q):
 (applyBlock ops s).natReg q=s.natReg q:=by
 induction ops generalizing s with
 | nil=>rfl
 | cons o ops ih=>
  rw[applyBlock,ih (o.apply s) (by intro p hp;exact keep p (by simp[hp]))]
  exact op_natReg o s q (keep o (by simp))

end
end ExactFourierCircuits.UniformNatHeaderFrame
