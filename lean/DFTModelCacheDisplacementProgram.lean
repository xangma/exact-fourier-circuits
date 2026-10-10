import DFTModelCacheDisplacementBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDisplacement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDisplacementSum (integer)
open scoped BigOperators
noncomputable section

attribute [local irreducible] cell

def kernel (b : Fin 6) : Prog false Env (Ty.a sc) :=
  .tab (.comp (.atom .fst) size) (cell b)

def liftKernel (b : Fin 6) : Prog false (p Env w) (Ty.a sc) :=
  .comp (.atom .fst) (kernel b)

def dispatch : Prog false (p Env w) (Ty.a sc) :=
  .ifz (.atom .snd) (liftKernel 0)
  (.ifz (integer .sub (.atom .snd) (.atom (.lit 1))) (liftKernel 1)
  (.ifz (integer .sub (.atom .snd) (.atom (.lit 2))) (liftKernel 2)
  (.ifz (integer .sub (.atom .snd) (.atom (.lit 3))) (liftKernel 3)
  (.ifz (integer .sub (.atom .snd) (.atom (.lit 4))) (liftKernel 4) (liftKernel 5)))))

def rawProgram : Prog false Env (Ty.a (Ty.a sc)) := .tab (.atom (.lit 6)) dispatch

def rawValues (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) : Tape (Tape ℂ) :=
  Tape.tab 6 (fun b=>Tape.tab p.N (cellValue p h g ⟨b%6,Nat.mod_lt _ (by decide)⟩))

theorem kernel_run (b : Fin 6) (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) :
    run (kernel b) (metadata r p,(h,g))=
      (Bill.tab p.N sc.blank (fun j=>run (cell b) ((metadata r p,(h,g)),j))).pay 10 0 := by
  have count:run (.comp (.atom .fst) size : Prog false Env w) (metadata r p,(h,g))=
      (⟨p.N,9,0,True⟩:Bill ℕ) := by
    simp [size,metadata,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  change ((run (.comp (.atom .fst) size) _).pass (fun n=>
    Bill.tab n sc.blank (fun j=>run (cell b) ((metadata r p,(h,g)),j)))).pay 1 0=_
  rw [count]
  simp [Bill.pass,Bill.pay]
  omega

attribute [local irreducible] kernel

theorem kernel_value (b : Fin 6) (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) :
    (run (kernel b) (metadata r p,(h,g))).val=Tape.tab p.N (cellValue p h g b) := by
  rw [kernel_run]
  change (Bill.tab p.N sc.blank (fun j=>run (cell b) ((metadata r p,(h,g)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab p.N)
  funext j
  exact cell_value r p h g b j

theorem kernel_valid (b : Fin 6) (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) : (run (kernel b) (metadata r p,(h,g))).valid := by
  rw [kernel_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  exact cell_valid r p h g b j

theorem kernel_work (b : Fin 6) (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) :
    (run (kernel b) (metadata r p,(h,g))).work≤p.N*(52*p.split+204)+12 := by
  rw [kernel_run]
  change (Bill.tab p.N sc.blank (fun j=>run (cell b) ((metadata r p,(h,g)),j))).work+10≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum: (∑j∈Finset.range p.N,(run (cell b) ((metadata r p,(h,g)),j)).work)
      ≤p.N*(52*p.split+200) := by
    calc
      _≤∑_j∈Finset.range p.N,(52*p.split+200) := by
        apply Finset.sum_le_sum
        intro j _
        exact cell_work r p h g b j
      _=_ := by simp
  nlinarith

theorem kernel_peak (b : Fin 6) (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (shape:Shape p r) :
    (run (kernel b) (metadata r p,(h,g))).peak≤ max p.N r := by
  rw [kernel_run]
  change max (Bill.tab p.N sc.blank (fun j=>run (cell b) ((metadata r p,(h,g)),j))).peak 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (le_max_left _ _) ?_) (Nat.zero_le _)
  apply Finset.sup_le
  intro j _
  exact (cell_peak r p h g b j shape).trans (le_max_right _ _)

theorem dispatch_run (b : Fin 6) (x : Env.T) :
    run dispatch (x,b.val)=(run (kernel b) x).pay (4+6*min b.val 4) (min b.val 4) := by
  fin_cases b <;>
    simp [dispatch,liftKernel,integer,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
  all_goals omega

attribute [local irreducible] dispatch

theorem rawProgram_run (x : Env.T) :
    run rawProgram x=(Bill.tab 6 (Ty.a sc).blank (fun b=>run dispatch (x,b))).pay 2 6 := by
  change ((Bill.word 6).pass (fun n=>Bill.tab n (Ty.a sc).blank
    (fun b=>run dispatch (x,b)))).pay 1 0=_
  simp [Bill.word,Bill.pass,Bill.pay]
  omega

theorem rawProgram_value (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) :
    (run rawProgram (metadata r p,(h,g))).val=rawValues p h g := by
  rw [rawProgram_run]
  change (Bill.tab 6 (Ty.a sc).blank (fun b=>run dispatch ((metadata r p,(h,g)),b))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  unfold Tape.tab rawValues
  congr 1
  funext b
  change (run dispatch ((metadata r p,(h,g)),b.val)).val=
    Tape.tab p.N (cellValue p h g ⟨b.val%6,Nat.mod_lt _ (by decide)⟩)
  rw [dispatch_run b]
  change (run (kernel b) (metadata r p,(h,g))).val=_
  rw [kernel_value]
  simp [Nat.mod_eq_of_lt b.isLt]

theorem rawProgram_valid (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) :
    (run rawProgram (metadata r p,(h,g))).valid := by
  rw [rawProgram_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro b hb
  rw [dispatch_run ⟨b,hb⟩]
  exact kernel_valid ⟨b,hb⟩ r p h g

theorem rawProgram_work (r : ℕ) (p : UniformRankKernelMachine.Parameters) (h g : Tape ℂ) :
    (run rawProgram (metadata r p,(h,g))).work≤6*p.N*(52*p.split+300)+500 := by
  rw [rawProgram_run]
  change (Bill.tab 6 (Ty.a sc).blank (fun b=>run dispatch ((metadata r p,(h,g)),b))).work+2≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum:(∑b∈Finset.range 6,(run dispatch ((metadata r p,(h,g)),b)).work)
      ≤6*(p.N*(52*p.split+204)+40) := by
    calc
      _≤∑_b∈Finset.range 6,(p.N*(52*p.split+204)+40) := by
        apply Finset.sum_le_sum
        intro b hb
        rw [dispatch_run ⟨b,Finset.mem_range.mp hb⟩]
        have bound:=kernel_work ⟨b,Finset.mem_range.mp hb⟩ r p h g
        change (run (kernel ⟨b,Finset.mem_range.mp hb⟩) _).work+(4+6*min b 4)≤_
        have :min b 4≤4:=min_le_right _ _
        omega
      _=_ := by simp
  nlinarith

theorem rawProgram_peak (r : ℕ) (p : UniformRankKernelMachine.Parameters)
    (h g : Tape ℂ) (shape:Shape p r) :
    (run rawProgram (metadata r p,(h,g))).peak≤ max 6 (max p.N r) := by
  rw [rawProgram_run]
  change max (Bill.tab 6 (Ty.a sc).blank
    (fun b=>run dispatch ((metadata r p,(h,g)),b))).peak 6≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le (le_max_left _ _) ?_) (le_max_left _ _)
  apply Finset.sup_le
  intro b hb
  rw [dispatch_run ⟨b,Finset.mem_range.mp hb⟩]
  change max (run (kernel ⟨b,Finset.mem_range.mp hb⟩) _).peak (min b 4)≤_
  refine max_le ((kernel_peak _ r p h g shape).trans (le_max_right _ _)) ?_
  exact (min_le_right b 4).trans ((by omega:4≤6).trans (le_max_left _ _))

end
end ExactFourierCircuits.DFTModelCacheDisplacement
