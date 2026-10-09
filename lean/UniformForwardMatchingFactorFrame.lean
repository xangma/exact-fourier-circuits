import UniformForwardMatchingFactorSetup
set_option autoImplicit false
namespace ExactFourierCircuits.UniformForwardMatchingFactorPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
structure PreludeFrame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalar:u.scalarHeap=s.scalarHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 high:∀q,4410≤q→q≤4429→u.natReg q=s.natReg q
 zero:u.natReg 4430=0
 saved:∀q,100≤q→q≤106→u.natReg q=s.natReg q
lemma PreludeFrame.setup (s:State):PreludeFrame s (applyBlock chunkSetup s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_,setup_zero s,?_⟩
 · intro q lo hi;exact setup_nat s q (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
 · intro q lo hi;exact setup_nat s q (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
lemma PreludeFrame.withPC {s u:State} (h:PreludeFrame s u) (p:ℕ):PreludeFrame s (setPC u p):=
 ⟨h.natHeap,h.scalar,h.outputs,h.roots,h.high,h.zero,h.saved⟩
end
end ExactFourierCircuits.UniformForwardMatchingFactorPreparation
