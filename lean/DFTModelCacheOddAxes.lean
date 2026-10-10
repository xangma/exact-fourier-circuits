import DFTModelCacheAxisRootsCorrect
import DFTModelCacheKernelBanks

set_option autoImplicit false

/-! Charged application to the generated odd-axis root rows. The final binary
row is excluded: its Fourier preparation follows the binary C path. This is
local Newton preparation, not a complete global forest/calendar compiler.
Paper: revision adc7f1241b42e322a6451854ab7e4b4c146bf78a, §3.1–3.5,
pp.13–18 (especially results 3.12–3.14, pp.17–18). -/
namespace ExactFourierCircuits.DFTModelCacheOddAxes
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev RootBank := Ty.a (p w sc)

def count : Prog false RootBank w :=
  .comp (.fork (.atom .len) (.atom (.lit 1))) (.atom (.int .sub))

def applyOdd {t : Ty} (f : Prog false (p w sc) t) : Prog false RootBank (Ty.a t) :=
  .tab count (.comp (.atom .look) f)

theorem count_run (roots : Tape (ℕ × ℂ)) :
    run count roots=⟨roots.len-1,5,max roots.len 1,True⟩ := by
  simp [count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem cell_run {t : Ty} (f : Prog false (p w sc) t)
    (roots : Tape (ℕ × ℂ)) (j : ℕ) :
    run (.comp (.atom .look) f) (roots,j)=
      ⟨(run f (roots.look j (0,0))).val,(run f (roots.look j (0,0))).work+2,
        (run f (roots.look j (0,0))).peak,(run f (roots.look j (0,0))).valid⟩ := by
  simp [comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,Ty.blank]
  omega

theorem apply_run {t : Ty} (f : Prog false (p w sc) t) (roots : Tape (ℕ × ℂ)) :
    run (applyOdd f) roots=
      (Bill.tab (roots.len-1) t.blank
        (fun j=>run (.comp (.atom .look) f) (roots,j))).pay 6 (max roots.len 1) := by
  change ((run count roots).pass (fun k=>Bill.tab k t.blank
    (fun j=>run (.comp (.atom .look) f) (roots,j)))).pay 1 0=_
  rw [count_run]
  simp only [Bill.pass,Bill.pay,max_zero,true_and]
  congr 1
  · omega
  · exact max_comm _ _

theorem apply_value {t : Ty} (f : Prog false (p w sc) t) (roots : Tape (ℕ × ℂ)) :
    (run (applyOdd f) roots).val=Tape.tab (roots.len-1)
      (fun j=>(run f (roots.look j (0,0))).val) := by
  rw [apply_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab (roots.len-1))
  funext j
  rw [cell_run]

theorem apply_valid {t : Ty} (f : Prog false (p w sc) t) (roots : Tape (ℕ × ℂ))
    (h : ∀j,j<roots.len-1→(run f (roots.look j (0,0))).valid) :
    (run (applyOdd f) roots).valid := by
  rw [apply_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j hj
  rw [cell_run]
  exact h j hj

theorem apply_work {t : Ty} (f : Prog false (p w sc) t) (roots : Tape (ℕ × ℂ)) :
    (run (applyOdd f) roots).work=8+6*(roots.len-1)+
      ∑j∈Finset.range (roots.len-1),(run f (roots.look j (0,0))).work := by
  rw [apply_run]
  change (Bill.tab _ _ _).work+6=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j∈Finset.range (roots.len-1),
      (run (.comp (.atom .look) f) (roots,j)).work)=
      ∑j∈Finset.range (roots.len-1),((run f (roots.look j (0,0))).work+2) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [cell_run]
  rw [hs,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem apply_peak {t : Ty} (f : Prog false (p w sc) t) (roots : Tape (ℕ × ℂ))
    (B : ℕ) (hlen : roots.len≤B) (h1 : 1≤B)
    (h : ∀j,j<roots.len-1→(run f (roots.look j (0,0))).peak≤B) :
    (run (applyOdd f) roots).peak≤B := by
  rw [apply_run]
  change max (Bill.tab _ _ _).peak (max roots.len 1)≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (by omega) ?_) (max_le hlen h1)
  exact Finset.sup_le (fun j hj=>by
    rw [cell_run]
    exact h j (Finset.mem_range.mp hj))

/-- Closed raw-length/master-root producer. The component is fixed syntax,
not a runtime function argument or a supplied Newton table. -/
def program : Prog false (p w sc) (Ty.a DFTModelCacheKernelBanks.Output) :=
  .comp DFTModelCacheAxisRoots.program (applyOdd DFTModelCacheKernelBanks.program)

end
end ExactFourierCircuits.DFTModelCacheOddAxes
