import DFTModelCacheTopologyArithmetic

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

def exponent (a e : ℕ) := Nat.clog 2 (2*(a+e))
def localWidth (a e : ℕ) := UniformRadixTwoDAG.width (exponent a e)

theorem target_run (a e : ℕ) : run target (a,e)=⟨2*(a+e),9,max 2 (2*(a+e)),True⟩ := by
  simp only [target,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    max_zero,zero_max,true_and]
  congr 1; omega

theorem prepare_spec (a e : ℕ) :
    (run prepare (a,e)).val=config (exponent a e) a e ∧
    (run prepare (a,e)).valid ∧
    (run prepare (a,e)).work=28*exponent a e+35 ∧
    (run prepare (a,e)).peak≤4*(a+e)+2 := by
  have h:=DFTModelCacheDescriptor.logarithm_spec (2*(a+e))
  rw [prepare,fork_run,comp_run,target_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,h.1,h.2.1,
    h.2.2.1,zero_max,max_zero,true_and]
  refine ⟨?_,?_,?_⟩
  · simp only [config,exponent,UniformRadixTwoDAG.width_eq]
  · unfold exponent;omega
  · have hp:=h.2.2.2
    omega

theorem dimensions_fit (a e : ℕ) : a≤localWidth a e ∧ e≤localWidth a e := by
  have enough:=Nat.le_pow_clog (by decide :1<2) (2*(a+e))
  unfold localWidth exponent
  rw [UniformRadixTwoDAG.width_eq]
  omega

theorem localWidth_bound (a e : ℕ) : localWidth a e≤4*(a+e)+1 := by
  have h:=UniformWorkspaceSearchMachine.clog_width_bound (2*(a+e))
  unfold localWidth exponent
  rw [UniformRadixTwoDAG.width_eq]
  omega

end
end ExactFourierCircuits.DFTModelCacheTopology
