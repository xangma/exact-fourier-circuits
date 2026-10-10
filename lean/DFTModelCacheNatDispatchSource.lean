import DFTModelCacheNatDispatchFuel

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

def native (code : List Instruction) : UniformMachine.Program := code.map Instruction.native

theorem native_at (code : List Instruction) (v : LocalValue) (s : UniformMachine.State)
    (rep : Represents v s) (i : Instruction) (selected : code[v.1]?=some i) :
    (native code)[s.pc]?=some i.native := by
  rw [←rep.pc,native,List.getElem?_map,selected];rfl

theorem selected_of_running (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (v : LocalValue) (s u : UniformMachine.State) (rep : Represents v s)
    (step : UniformMachine.step (native code) n x s=.running u) :
    ∃i,code[v.1]?=some i := by
  cases selected:code[v.1]? with
  | none=>
    have missing:(native code)[s.pc]?=none := by
      rw [←rep.pc,native,List.getElem?_map,selected];rfl
    simp only [UniformMachine.step,missing] at step
    cases step
  | some i=>exact ⟨i,rfl⟩

theorem selected_of_halted (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (v : LocalValue) (s : UniformMachine.State) (rep : Represents v s)
    (step : UniformMachine.step (native code) n x s=.halted s) :
    code[v.1]?=some .halt := by
  cases selected:code[v.1]? with
  | none=>
    have missing:(native code)[s.pc]?=none := by
      rw [←rep.pc,native,List.getElem?_map,selected];rfl
    simp only [UniformMachine.step,missing] at step
    cases step
  | some i=>
    have codeAt:=native_at code v s rep i selected
    cases i with
    | halt=>rfl
    | binary op d l r=>
      cases h:UniformMachine.evalNat op (s.natReg l) (s.natReg r) <;>
        simp [UniformMachine.step,codeAt,Instruction.native,h] at step
    | load d addr=>
      cases h:s.natHeap (s.natReg addr) <;>
        simp [UniformMachine.step,codeAt,Instruction.native,h] at step
    | literal d value | store addr src | branch l r yes no | jump target=>
      simp [UniformMachine.step,codeAt,Instruction.native] at step

theorem running_program_source (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (v : LocalValue) (s u : UniformMachine.State) (rep : Represents v s)
    (fits : ∀i,code[v.1]?=some i→Fits i v)
    (step : UniformMachine.step (native code) n x s=.running u) :
    Accepted code v ∧ Represents (next code v) u := by
  obtain ⟨i,selected⟩:=selected_of_running code n x v s u rep step
  have one:=running_source (native code) n x rep (fits i selected)
    (native_at code v s rep i selected) step
  have domain:Domain i v := (instruction_valid i v).mp one.1
  have value:next code v=(run (instruction i) v).val := by
    rw [instruction_value];simp only [next,selected]
  exact ⟨⟨i,selected,domain⟩,value.symm ▸ one.2⟩

theorem trajectory_shift (code : List Instruction) (v : LocalValue) (j : ℕ) :
    trajectory code (next code v) j=trajectory code v (j+1) := by
  induction j with
  | zero=>rfl
  | succ j ih=>exact congrArg (next code) ih

theorem trajectory_add (code : List Instruction) (v : LocalValue) (j k : ℕ) :
    trajectory code v (j+k)=trajectory code (trajectory code v j) k := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact congrArg (next code) ih

theorem trajectory_halt (code : List Instruction) (v : LocalValue)
    (halt : code[v.1]?=some .halt) (j : ℕ) : trajectory code v j=v := by
  induction j with
  | zero=>rfl
  | succ j ih=>simp only [trajectory,ih,next,halt,result]

/-- Finite representation/Fits along the actual successful native prefix.
The count includes the native halt, whose translation preserves the state. -/
theorem executes_trajectory (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (s u : UniformMachine.State) (count : ℕ)
    (execution : UniformMachine.Executes (native code) n x s count u)
    (v : LocalValue) (rep : Represents v s)
    (fits : ∀j,j<count→∀i,code[(trajectory code v j).1]?=some i→
      Fits i (trajectory code v j)) :
    Represents (trajectory code v count) u ∧
      (∀j,j<count→Accepted code (trajectory code v j)) ∧
      code[(trajectory code v count).1]?=some .halt := by
  induction execution generalizing v with
  | halt step=>
    have selected:=selected_of_halted code n x v _ rep step
    have stable:=trajectory_halt code v selected
    refine ⟨?_,?_,?_⟩
    · rw [stable];exact rep
    · intro j hj
      have zero:j=0 := by omega
      subst j;exact ⟨.halt,selected,trivial⟩
    · rw [stable];exact selected
  | @next s middle u t step tail ih=>
    obtain ⟨accepted,after⟩:=running_program_source code n x v s middle rep
      (fits 0 (by omega)) step
    have rest:=ih (next code v) after (by
      intro j hj i selected
      rw [trajectory_shift] at selected ⊢
      exact fits (j+1) (by omega) i selected)
    refine ⟨?_,?_,?_⟩
    · rw [←trajectory_shift];exact rest.1
    · intro j hj
      cases j with
      | zero=>exact accepted
      | succ j=>
        rw [←trajectory_shift]
        exact rest.2.1 j (by omega)
    · rw [←trajectory_shift];exact rest.2.2

theorem executes_source (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (s u : UniformMachine.State) (count : ℕ)
    (execution : UniformMachine.Executes (native code) n x s count u)
    (v : LocalValue) (rep : Represents v s)
    (fits : ∀j,j<count→∀i,code[(trajectory code v j).1]?=some i→
      Fits i (trajectory code v j)) :
    (run (fuelProgram code) (count,v)).valid ∧
      Represents (run (fuelProgram code) (count,v)).val u := by
  have actual:=executes_trajectory code n x s u count execution v rep fits
  exact ⟨(fuel_valid code count v).mpr actual.2.1,by rw [fuel_value];exact actual.1⟩

/-- Extra fuel executes charged halt stutters. Its number is deliberately
separate from the native execution count. -/
theorem executes_padded_source (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (s u : UniformMachine.State) (count padding : ℕ)
    (execution : UniformMachine.Executes (native code) n x s count u)
    (v : LocalValue) (rep : Represents v s)
    (fits : ∀j,j<count→∀i,code[(trajectory code v j).1]?=some i→
      Fits i (trajectory code v j)) :
    (run (fuelProgram code) (count+padding,v)).valid ∧
      Represents (run (fuelProgram code) (count+padding,v)).val u ∧
      (run (fuelProgram code) (count+padding,v)).val=
        (run (fuelProgram code) (count,v)).val := by
  have actual:=executes_trajectory code n x s u count execution v rep fits
  have stable:∀k,trajectory code v (count+k)=trajectory code v count := by
    intro k;rw [trajectory_add];exact trajectory_halt code _ actual.2.2 k
  refine ⟨(fuel_valid code (count+padding) v).mpr ?_,?_,?_⟩
  · intro j hj
    by_cases before:j<count
    · exact actual.2.1 j before
    · have equal:j=count+(j-count) := by omega
      rw [equal,stable]
      exact ⟨.halt,actual.2.2,trivial⟩
  · rw [fuel_value,stable];exact actual.1
  · rw [fuel_value,fuel_value,stable]

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
