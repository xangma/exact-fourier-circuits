import DFTModelCacheNatDispatchSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatDispatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheNatControl
noncomputable section

/-- A finite-arena safety condition, not an execution or output certificate.
Clients prove these inequalities from their static operands and word bounds. -/
def RunningSafety (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (nativeB wordB R H : ℕ) : Prop :=
  ∀(v : LocalValue)(s u : UniformMachine.State)(i : Instruction),
    Represents v s→v.2.1.len=R→v.2.2.len=H→
    UniformMachine.WordBound nativeB s→UniformMachine.WordBound nativeB u→
    code[v.1]?=some i→UniformMachine.step (native code) n x s=.running u→
    Fits i v ∧ PeakBound i v wordB

def HaltSafety (nativeB wordB R H : ℕ) : Prop :=
  ∀(v : LocalValue)(s : UniformMachine.State),Represents v s→
    v.2.1.len=R→v.2.2.len=H→UniformMachine.WordBound nativeB s→
    PeakBound .halt v wordB

theorem peakBound_mono (i : Instruction) (v : LocalValue) {B C : ℕ}
    (bound : PeakBound i v B) (le : B≤C) : PeakBound i v C := by
  cases i <;> simp only [PeakBound] at bound ⊢ <;>
    rcases bound with ⟨one,pc,regs,heap,rest⟩ <;>
    refine ⟨one.trans le,pc.trans le,regs.trans le,heap.trans le,?_⟩
  all_goals aesop (add safe forward le_trans)

structure TraceBounds (code : List Instruction) (v : LocalValue) (count wordB : ℕ)
    (u : UniformMachine.State) : Prop where
  represents : Represents (trajectory code v count) u
  accepted : ∀j,j<count→Accepted code (trajectory code v j)
  pc : ∀j,j<count→(trajectory code v j).1≤wordB
  peak : ∀j,j<count→∀i,code[(trajectory code v j).1]?=some i→
    PeakBound i (trajectory code v j) wordB
  halted : code[(trajectory code v count).1]?=some .halt

theorem bounded_trajectory (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (nativeB wordB R H : ℕ) (s u : UniformMachine.State) (count : ℕ)
    (execution : UniformMachine.BoundedExecution (native code) n x nativeB s count u)
    (v : LocalValue) (rep : Represents v s) (regs : v.2.1.len=R) (heap : v.2.2.len=H)
    (words : nativeB≤wordB)
    (runningSafe : RunningSafety code n x nativeB wordB R H)
    (haltSafe : HaltSafety nativeB wordB R H) : TraceBounds code v count wordB u := by
  induction execution generalizing v with
  | halt bound step=>
    have selected:=selected_of_halted code n x v _ rep step
    have stable:=trajectory_halt code v selected
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [stable];exact rep
    · intro j hj;rw [stable];exact ⟨.halt,selected,trivial⟩
    · intro j hj;rw [stable,rep.pc];exact bound.1.trans words
    · intro j hj i chosen
      rw [stable] at chosen ⊢
      rw [selected] at chosen
      have equal:i=.halt := (Option.some.inj chosen).symm
      subst i;exact haltSafe v _ rep regs heap bound
    · rw [stable];exact selected
  | @next s middle u t bound step tail ih=>
    obtain ⟨i,selected⟩:=selected_of_running code n x v s middle rep step
    have safe:=runningSafe v s middle i rep regs heap bound
      (by cases tail with | halt h _=>exact h | next h _ _=>exact h) selected step
    have one:=running_source (native code) n x rep safe.1
      (native_at code v s rep i selected) step
    have after:Represents (next code v) middle := by
      rw [instruction_value] at one
      simpa only [next,selected] using one.2
    have lengths:=next_lengths code v
    have rest:=ih (next code v) after (lengths.1.trans regs) (lengths.2.trans heap)
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [←trajectory_shift];exact rest.represents
    · intro j hj
      cases j with
      | zero=>exact ⟨i,selected,(instruction_valid i v).mp one.1⟩
      | succ j=>rw [←trajectory_shift];exact rest.accepted j (by omega)
    · intro j hj
      cases j with
      | zero=>exact rep.pc ▸ bound.1.trans words
      | succ j=>rw [←trajectory_shift];exact rest.pc j (by omega)
    · intro j hj k chosen
      cases j with
      | zero=>
        change code[v.1]?=some k at chosen
        rw [selected] at chosen
        have equal:k=i := (Option.some.inj chosen).symm
        subst k;exact safe.2
      | succ j=>
        rw [←trajectory_shift] at chosen ⊢
        exact rest.peak j (by omega) k chosen
    · rw [←trajectory_shift];exact rest.halted

/-- A bounded native run yields a genuine charged typed run. The only client
conditions are the explicit finite-arena safety rules above. -/
theorem bounded_source (code : List Instruction) (n : ℕ) (x : Fin n→ℂ)
    (nativeB wordB R H : ℕ) (s u : UniformMachine.State) (count : ℕ)
    (execution : UniformMachine.BoundedExecution (native code) n x nativeB s count u)
    (v : LocalValue) (rep : Represents v s) (regs : v.2.1.len=R) (heap : v.2.2.len=H)
    (words : nativeB≤wordB)
    (runningSafe : RunningSafety code n x nativeB wordB R H)
    (haltSafe : HaltSafety nativeB wordB R H) :
    (run (fuelProgram code) (count,v)).valid ∧
      Represents (run (fuelProgram code) (count,v)).val u ∧
      (run (fuelProgram code) (count,v)).work≤4+count*(35*(R+H)+105+6*code.length) ∧
      (run (fuelProgram code) (count,v)).peak≤ max count wordB := by
  have trace:=bounded_trajectory code n x nativeB wordB R H s u count execution
    v rep regs heap words runningSafe haltSafe
  refine ⟨(fuel_valid code count v).mpr trace.accepted,?_,?_,?_⟩
  · rw [fuel_value];exact trace.represents
  · simpa only [regs,heap] using fuel_work code count v
  · apply fuel_peak code count v (max count wordB) (le_max_left _ _)
    · intro j hj;exact (trace.pc j hj).trans (le_max_right _ _)
    · intro j hj i selected
      exact peakBound_mono i _ (trace.peak j hj i selected) (le_max_right _ _)

end
end ExactFourierCircuits.DFTModelCacheNatDispatch
