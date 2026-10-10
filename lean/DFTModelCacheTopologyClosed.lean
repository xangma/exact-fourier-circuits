import DFTModelCacheTopologyCorrect
import DFTModelCacheTopologyReadbackBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTopology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelCacheMatchingNat DFTModelCacheNatControl
noncomputable section

attribute [local irreducible] Code.run Bill.tab

def bodyWork (K a e : ℕ) := 210000+204*H K a e+
  T K a*(35*(600+H K a e)+105+6*271)+5120*C K a
def bodyPeak (K a e : ℕ) :=2*H K a e+T K a+20000

private theorem runtime_peak_room (h t : ℕ) :
    max t (max (max 600 600) h)≤2*h+t+20000 := by omega
private theorem compiled_work_room (h w : ℕ) :
    1000+(200000+204*h)+1+(4+w)+1≤201006+204*h+w := by omega
private theorem body_work_room (h w c : ℕ) :
    1+(201006+204*h+w)+1+(4000+5120*c)+1≤210000+204*h+w+5120*c := by omega
private theorem final_work_room (body k : ℕ) :
    28*k+35+body+1≤body+28*k+36 := by omega

theorem body_budget (K a e : ℕ) :
    Budget (run body (config K a e)) (bodyWork K a e) (bodyPeak K a e) := by
  obtain ⟨u,t,_actual,_time,_pc,_rows,valid,_rep,work,peak⟩:=interpreted_source K a e
  have setup:=initialize_bounds K a e
  have f:=fuel_bounds K a e
  have fuelBudget:Budget (run fuel (config K a e)) 1000 (bodyPeak K a e) :=
    ⟨f.1,f.2.1,f.2.2.trans (by unfold bodyPeak;omega)⟩
  have initBudget:Budget (run initializeProgram (config K a e))
      (200000+204*H K a e) (bodyPeak K a e) :=
    ⟨setup.1,setup.2.1,setup.2.2.trans (by unfold bodyPeak;omega)⟩
  have both:=fork_budget fuel initializeProgram (config K a e) 1000
    (200000+204*H K a e) (bodyPeak K a e) fuelBudget initBudget
  have rt:Budget (run (DFTModelCacheNatDispatch.fuelProgram instructions)
      (run (.fork fuel initializeProgram) (config K a e)).val)
      (4+T K a*(35*(600+H K a e)+105+6*271)) (bodyPeak K a e) := by
    rw [DFTModelCacheMatchingNat.fork_value,fuel_value,initialize_value]
    refine ⟨valid,work,peak.trans ?_⟩
    exact runtime_peak_room (H K a e) (T K a)
  have comp:=comp_budget (.fork fuel initializeProgram) (DFTModelCacheNatDispatch.fuelProgram instructions)
    (config K a e) (1000+(200000+204*H K a e)+1)
    (4+T K a*(35*(600+H K a e)+105+6*271)) (bodyPeak K a e) both rt
  have cb:Budget (run compiled (config K a e))
      (201006+204*H K a e+T K a*(35*(600+H K a e)+105+6*271)) (bodyPeak K a e) :=
    budget_mono comp (compiled_work_room _ _)
  have identity:Budget (run (.atom .id : Prog false Config Config) (config K a e)) 1 (bodyPeak K a e) := by
    rw [atom_run];exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  have calculated:=fork_budget (.atom .id) compiled (config K a e) 1
    (201006+204*H K a e+T K a*(35*(600+H K a e)+105+6*271)) (bodyPeak K a e) identity cb
  have rb:Budget (run readback (run computed (config K a e)).val)
      (4000+5120*C K a) (bodyPeak K a e) := by
    rw [computed_value]
    have b:=readback_bounds K a e (run compiled (config K a e)).val
    exact ⟨b.1,b.2.1,b.2.2.trans (by unfold bodyPeak H;omega)⟩
  have composed:=comp_budget computed readback (config K a e)
    (1+(201006+204*H K a e+T K a*(35*(600+H K a e)+105+6*271))+1)
    (4000+5120*C K a) (bodyPeak K a e) calculated rb
  exact budget_mono composed (body_work_room _ _ _)

def workBudget (a e : ℕ) :=bodyWork (exponent a e) a e+28*exponent a e+36
def peakBudget (a e : ℕ) :=bodyPeak (exponent a e) a e

/-- Closed typed client of the real topology printer. Raw dimensions are the
only input; no topology tape, initialized state, execution or safety oracle is supplied. -/
theorem execution (a e : ℕ) :
    ∃u ticks,Result a e u ticks ∧
    Budget (run program (a,e)) (workBudget a e) (peakBudget a e) := by
  obtain ⟨u,t,result⟩:=execution_values a e
  have prep:=prepare_spec a e
  have tail:=UniformToeplitzCrossTopologyMachine.budget_tail (exponent a e) a e 0 (D (exponent a e))
  have prepBudget:Budget (run prepare (a,e)) (28*exponent a e+35) (peakBudget a e) :=
    ⟨prep.2.1,prep.2.2.1.le,prep.2.2.2.trans (by unfold peakBudget bodyPeak H B;omega)⟩
  have main:=body_budget (exponent a e) a e
  have next:Budget (run body (run prepare (a,e)).val) (bodyWork (exponent a e) a e) (peakBudget a e) := by
    rw [prep.1];exact main
  have done:=comp_budget prepare body (a,e) (28*exponent a e+35)
    (bodyWork (exponent a e) a e) (peakBudget a e) prepBudget next
  exact ⟨u,t,result,budget_mono done (final_work_room _ _)⟩

end
end ExactFourierCircuits.DFTModelCacheTopology
