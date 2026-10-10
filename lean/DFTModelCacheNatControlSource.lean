import DFTModelCacheNatControlCore

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Only finite local natural banks are represented. Scalar state is unrelated. -/
structure Represents (v : LocalValue) (s : UniformMachine.State) : Prop where
  pc : v.1=s.pc
  registers : ∀j,j<v.2.1.len→ reg v j=s.natReg j
  heap : ∀j,j<v.2.2.len→ModelEquivalenceInterpreter.decodeNatCell (cell v j)=s.natHeap j

def Fits (i : Instruction) (v : LocalValue) : Prop :=
  match i with
  | .literal d _ => d<v.2.1.len
  | .binary _ d l r => d<v.2.1.len ∧ l<v.2.1.len ∧ r<v.2.1.len
  | .load d addr => d<v.2.1.len ∧ addr<v.2.1.len ∧ reg v addr<v.2.2.len
  | .store addr src => addr<v.2.1.len ∧ src<v.2.1.len ∧ reg v addr<v.2.2.len
  | .branch l r _ _ => l<v.2.1.len ∧ r<v.2.1.len
  | .jump _ | .halt => True

theorem put_represents {v : LocalValue} {s : UniformMachine.State} (h : Represents v s)
    (d x : ℕ) (hd : d<v.2.1.len) : Represents (put v d x) (UniformMachine.writeNat s d x) := by
  refine ⟨congrArg (fun n=>n+1) h.pc,?_,?_⟩
  · intro j hj
    change (v.2.1.set d x).look j 0=Function.update s.natReg d x j
    rw [ModelEquivalenceInterpreter.tape_set_look]
    by_cases he:j=d
    · subst j;simp only [hd,and_self,ite_true,Function.update_self]
    · simp only [he,false_and,ite_false,Function.update_of_ne he]
      exact h.registers j hj
  · exact h.heap

theorem setPC_represents {v : LocalValue} {s : UniformMachine.State} (h : Represents v s)
    (t : ℕ) : Represents (setPC v t) {s with pc:=t} := ⟨rfl,h.registers,h.heap⟩

theorem putHeap_represents {v : LocalValue} {s : UniformMachine.State} (h : Represents v s)
    (addr x : ℕ) (ha : addr<v.2.2.len) : Represents (putHeap v addr x)
      {UniformMachine.next s with natHeap:=Function.update s.natHeap addr (some x)} := by
  refine ⟨congrArg (fun n=>n+1) h.pc,h.registers,?_⟩
  intro j hj
  change ModelEquivalenceInterpreter.decodeNatCell ((v.2.2.set addr (1,x)).look j (0,0))=_
  rw [ModelEquivalenceInterpreter.tape_set_look]
  by_cases he:j=addr
  · subst j;simp [ha,ModelEquivalenceInterpreter.decodeNatCell]
  · simp only [he,false_and,ite_false,Function.update_of_ne he]
    exact h.heap j hj

/-- One successful actual native instruction is compiled to the same finite
natural state. Neither its returned bank nor its output transition is assumed. -/
theorem running_source {i : Instruction} {v : LocalValue} {s u : UniformMachine.State}
    (p : UniformMachine.Program) (n : ℕ) (x : Fin n→ℂ)
    (h : Represents v s) (fit : Fits i v) (code : p[s.pc]?=some i.native)
    (step : UniformMachine.step p n x s=.running u) :
    (run (instruction i) v).valid ∧ Represents (run (instruction i) v).val u := by
  rw [instruction_valid,instruction_value]
  cases i with
  | literal d value =>
    simp only [Instruction.native,UniformMachine.step,code,UniformMachine.StepResult.running.injEq] at step
    subst u
    exact ⟨trivial,put_represents h d value fit⟩
  | binary op d l r =>
    rcases fit with ⟨hd,hl,hr⟩
    have vl:=h.registers l hl
    have vr:=h.registers r hr
    cases he:UniformMachine.evalNat op (s.natReg l) (s.natReg r) with
    | none => simp [Instruction.native,UniformMachine.step,code,he] at step
    | some value =>
      simp only [Instruction.native,UniformMachine.step,code,he,
        UniformMachine.StepResult.running.injEq] at step
      subst u
      have good:ModelEquivalenceNat.ValidOperands op (reg v l) (reg v r) ∧
          ((ModelEquivalenceNat.toUpstream op).run (reg v l,reg v r)).val=value := by
        apply (ModelEquivalenceNat.evalNat_some_iff op _ _ value).1
        simpa only [vl,vr] using he
      refine ⟨good.1,?_⟩
      simpa only [result,good.2] using put_represents h d value hd
  | load d addr =>
    rcases fit with ⟨hd,ha,haddress⟩
    have va:=h.registers addr ha
    have heap:=h.heap (reg v addr) haddress
    rw [va] at heap
    cases he:s.natHeap (s.natReg addr) with
    | none => simp [Instruction.native,UniformMachine.step,code,he] at step
    | some value =>
      simp only [Instruction.native,UniformMachine.step,code,he,
        UniformMachine.StepResult.running.injEq] at step
      subst u
      rw [he] at heap
      have flag:(cell v (reg v addr)).1≠0 := by
        intro hz
        rw [←va] at heap
        simp [ModelEquivalenceInterpreter.decodeNatCell,hz] at heap
      have payload:(cell v (reg v addr)).2=value := by
        rw [←va] at heap
        simpa [ModelEquivalenceInterpreter.decodeNatCell,flag] using heap
      refine ⟨flag,?_⟩
      simpa only [result,flag,ite_false,payload] using put_represents h d value hd
  | store addr src =>
    rcases fit with ⟨ha,hs,haddress⟩
    simp only [Instruction.native,UniformMachine.step,code,UniformMachine.StepResult.running.injEq] at step
    subst u
    refine ⟨trivial,?_⟩
    simpa only [result,h.registers addr ha,h.registers src hs] using
      putHeap_represents h (reg v addr) (reg v src) haddress
  | branch l r y no =>
    rcases fit with ⟨hl,hr⟩
    simp only [Instruction.native,UniformMachine.step,code,UniformMachine.StepResult.running.injEq] at step
    subst u
    refine ⟨trivial,?_⟩
    simpa only [result,h.registers l hl,h.registers r hr] using
      setPC_represents h (if reg v l<reg v r then y else no)
  | jump t =>
    simp only [Instruction.native,UniformMachine.step,code,UniformMachine.StepResult.running.injEq] at step
    subst u
    exact ⟨trivial,setPC_represents h t⟩
  | halt => simp [Instruction.native,UniformMachine.step,code] at step

theorem halted_source {v : LocalValue} {s : UniformMachine.State} (h : Represents v s) :
    (run (instruction .halt) v).valid ∧ Represents (run (instruction .halt) v).val s := ⟨trivial,h⟩

end
end ExactFourierCircuits.DFTModelCacheNatControl
