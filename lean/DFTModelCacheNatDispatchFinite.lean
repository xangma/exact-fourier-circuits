import DFTModelCacheNatDispatchBounded

set_option autoImplicit false

/-! Generic finite-arena safety for fixed natural instruction lists.
No execution or prepared output is supplied by the footprint. -/
namespace ExactFourierCircuits.DFTModelCacheNatDispatchFinite
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

def Footprint (R L : ℕ) : Instruction→Prop
  | .literal d x=>d<R ∧ x≤L
  | .binary _ d l r=>d<R ∧ l<R ∧ r<R
  | .load d addr=>d<R ∧ addr<R
  | .store addr src=>addr<R ∧ src<R
  | .branch l r yes no=>l<R ∧ r<R ∧ yes≤L ∧ no≤L
  | .jump target=>target≤L
  | .halt=>True

def wordBound (R L B : ℕ) := max (max R L) (B+1)

theorem registers_le (R L B : ℕ) : R≤wordBound R L B :=
  (le_max_left R L).trans (le_max_left _ _)
theorem literals_le (R L B : ℕ) : L≤wordBound R L B :=
  (le_max_right R L).trans (le_max_left _ _)
theorem source_le (R L B : ℕ) : B+1≤wordBound R L B := le_max_right _ _

/-- A spare heap cell converts the source non-strict address bound to a
strict finite-tape bound on every represented native state. -/
theorem fits {i : Instruction} {v : LocalValue} {s : UniformMachine.State}
    {R L B : ℕ} (foot : Footprint R L i)
    (registers : v.2.1.len=R) (heap : v.2.2.len=B+1)
    (rep : Represents v s) (bound : UniformMachine.WordBound B s) : Fits i v := by
  have address:∀j,j<R→ reg v j<B+1 := by
    intro j hj
    have equal:=rep.registers j (by omega)
    have value:=bound.2.1 j
    omega
  cases i with
  | literal d value=>simpa only [Fits,registers] using foot.1
  | binary op d l r=>simpa only [Fits,registers,Footprint] using foot
  | load d addr=>exact ⟨by have:=foot.1;omega,by have:=foot.2;omega,
      by rw [heap];exact address addr foot.2⟩
  | store addr src=>exact ⟨by have:=foot.1;omega,by have:=foot.2;omega,
      by rw [heap];exact address addr foot.1⟩
  | branch l r yes no=>exact ⟨by have:=foot.1;omega,by have:=foot.2.1;omega⟩
  | jump _ | halt=>trivial

/-- Binary output bounds come from the SAME actual successful native step and
its after-state word bound; they are not a presumed operation result. -/
theorem peak {i : Instruction} {v : LocalValue} {s u : UniformMachine.State}
    {R L B n : ℕ} {x : Fin n→ℂ} (p : UniformMachine.Program)
    (foot : Footprint R L i) (registers : v.2.1.len=R) (heap : v.2.2.len=B+1)
    (rep : Represents v s) (before : UniformMachine.WordBound B s)
    (after : UniformMachine.WordBound B u) (code : p[s.pc]?=some i.native)
    (step : UniformMachine.step p n x s=.running u) : PeakBound i v (wordBound R L B) := by
  have hR:=registers_le R L B
  have hL:=literals_le R L B
  have hB:=source_le R L B
  refine ⟨by omega,?_,by omega,by omega,?_⟩
  · rw [rep.pc];have:=before.1;omega
  · cases i with
    | literal d value=>exact ⟨by have:=foot.1;omega,by have:=foot.2;omega⟩
    | binary op d l r=>
      rcases foot with ⟨hd,hl,hr⟩
      have vl:=rep.registers l (by omega)
      have vr:=rep.registers r (by omega)
      refine ⟨by omega,by omega,by omega,?_⟩
      cases eq:UniformMachine.evalNat op (s.natReg l) (s.natReg r) with
      | none=>simp [Instruction.native,UniformMachine.step,code,eq] at step
      | some value=>
        simp only [Instruction.native,UniformMachine.step,code,eq,
          UniformMachine.StepResult.running.injEq] at step
        subst u
        have result:=((ModelEquivalenceNat.evalNat_some_iff op _ _ value).1 eq).2
        rw [vl,vr,result]
        have hv:=after.2.1 d
        simp only [UniformMachine.writeNat,UniformMachine.next,Function.update_self] at hv
        omega
    | load d addr=>rcases foot with ⟨hd,ha⟩;exact ⟨by omega,by omega⟩
    | store addr src=>
      rcases foot with ⟨ha,hs⟩
      have equal:=rep.registers addr (by omega)
      have value:=before.2.1 addr
      exact ⟨by omega,by omega,by omega⟩
    | branch l r yes no=>
      rcases foot with ⟨hl,hr,hy,hn⟩
      exact ⟨by omega,by omega,by omega,by omega⟩
    | jump target=>change target≤L at foot;omega
    | halt=>trivial

theorem running_safety (code : List Instruction) (n : ℕ) (x : Fin n→ℂ) (B R L : ℕ)
    (footprint : ∀i∈code,Footprint R L i) :
    DFTModelCacheNatDispatch.RunningSafety code n x B (wordBound R L B) R (B+1) := by
  intro v s u i rep regs heap before after selected step
  have foot:=footprint i (List.mem_of_getElem? selected)
  refine ⟨fits foot regs heap rep before,?_⟩
  exact peak (DFTModelCacheNatDispatch.native code) foot regs heap rep before after
    (DFTModelCacheNatDispatch.native_at code v s rep i selected) step

theorem halt_safety (B R L : ℕ) :
    DFTModelCacheNatDispatch.HaltSafety B (wordBound R L B) R (B+1) := by
  intro v s rep regs heap before
  have hR:=registers_le R L B
  have hB:=source_le R L B
  refine ⟨by omega,?_,by omega,by omega,trivial⟩
  rw [rep.pc];have:=before.1;omega

end
end ExactFourierCircuits.DFTModelCacheNatDispatchFinite
