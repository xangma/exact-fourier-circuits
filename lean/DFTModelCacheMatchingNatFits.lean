import DFTModelCacheMatchingNatProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

def Footprint : DFTModelCacheNatControl.Instruction→Prop
  | .literal d x => d<862 ∧ x≤862
  | .binary _ d l r => d<862 ∧ l<862 ∧ r<862
  | .load d addr => d<862 ∧ addr<862
  | .store addr src => addr<862 ∧ src<862
  | .branch l r y n => l<862 ∧ r<862 ∧ y≤862 ∧ n≤862
  | .jump t => t≤862
  | .halt => True

theorem instructions_footprint : ∀i∈instructions,Footprint i := by simp [instructions,Footprint]

/-- One spare heap cell turns the source non-strict word bound into genuine
finite tape access. This is derived on every actual native state. -/
theorem fits {i : DFTModelCacheNatControl.Instruction} {v : LocalValue}
    {s : UniformMachine.State} {B : ℕ} (foot : Footprint i)
    (registers : v.2.1.len=862) (heap : v.2.2.len=B+1)
    (rep : Represents v s) (bound : UniformMachine.WordBound B s) : Fits i v := by
  have address : ∀j,j<862→ reg v j<B+1 := by
    intro j hj
    have eq:=rep.registers j (by omega)
    have hj:=bound.2.1 j
    omega
  cases i with
  | literal d value => change d<862 ∧ value≤862 at foot;simpa only [Fits,registers] using foot.1
  | binary op d l r => change d<862 ∧ l<862 ∧ r<862 at foot;simpa only [Fits,registers] using foot
  | load d addr =>
    change d<862 ∧ addr<862 at foot
    exact ⟨by omega,by omega,by rw [heap];exact address addr foot.2⟩
  | store addr src =>
    change addr<862 ∧ src<862 at foot
    exact ⟨by omega,by omega,by rw [heap];exact address addr foot.1⟩
  | branch l r y no => change l<862 ∧ r<862 ∧ y≤862 ∧ no≤862 at foot;exact ⟨by omega,by omega⟩
  | jump _ | halt => trivial

theorem peak {i : DFTModelCacheNatControl.Instruction} {v : LocalValue}
    {s u : UniformMachine.State} {B n : ℕ} {x : Fin n→ℂ}
    (p : UniformMachine.Program) (foot : Footprint i) (large : 862≤B)
    (registers : v.2.1.len=862) (heap : v.2.2.len=B+1)
    (rep : Represents v s) (before : UniformMachine.WordBound B s)
    (after : UniformMachine.WordBound B u) (code : p[s.pc]?=some i.native)
    (step : UniformMachine.step p n x s=.running u) : PeakBound i v (B+1) := by
  refine ⟨by omega,by have :=before.1;rw [rep.pc];omega,by omega,by omega,?_⟩
  cases i with
  | literal d value => exact ⟨by have :=foot.1;omega,by have :=foot.2;omega⟩
  | binary op d l r =>
    rcases foot with ⟨hd,hl,hr⟩
    have vl:=rep.registers l (by omega)
    have vr:=rep.registers r (by omega)
    refine ⟨by omega,by omega,by omega,?_⟩
    cases eq:UniformMachine.evalNat op (s.natReg l) (s.natReg r) with
    | none => simp [Instruction.native,UniformMachine.step,code,eq] at step
    | some value =>
      simp only [Instruction.native,UniformMachine.step,code,eq,
        UniformMachine.StepResult.running.injEq] at step
      subst u
      have h:=((ModelEquivalenceNat.evalNat_some_iff op _ _ value).1 eq).2
      rw [vl,vr,h]
      have hv:=after.2.1 d
      simp only [UniformMachine.writeNat,UniformMachine.next,Function.update_self] at hv
      omega
  | load d addr => rcases foot with ⟨hd,ha⟩;exact ⟨by omega,by omega⟩
  | store addr src =>
    rcases foot with ⟨ha,hs⟩
    have eq:=rep.registers addr (by omega)
    have hv:=before.2.1 addr
    exact ⟨by omega,by omega,by omega⟩
  | branch l r y no =>
    rcases foot with ⟨hl,hr,hy,hn⟩
    exact ⟨by omega,by omega,by omega,by omega⟩
  | jump t => change t≤862 at foot;omega
  | halt => trivial

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
