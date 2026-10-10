import DFTModelCacheColorInitialization

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open DFTModelCacheMatchingNat (Budget budget_mono select_budget fork_budget tab_program_budget)
noncomputable section

theorem registerCell_bounds (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    Budget (run registerCell ((r,z),j)) 200 (H r z.len+j+824) := by
  let Q:=H r z.len+j+824
  have index:Budget (run (.atom .snd : Prog false Indexed w) ((r,z),j)) 1 Q :=
    ⟨trivial,le_rfl,Nat.zero_le _⟩
  have val:(run (.atom .snd : Prog false Indexed w) ((r,z),j)).val≤Q := by
    change j≤Q;dsimp [Q];omega
  have data : ∀f∈([count,colorBase,paletteBase] : List (Prog false Input w)),
      Budget (run (.comp (.atom .fst : Prog false Indexed Input) f) ((r,z),j)) 21 Q := by
    intro f member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h <;> subst f <;>
      simp [Budget,count,colorBase,paletteBase,nat,DFTModelCacheMatchingNat.count,
        DFTModelCacheMatchingNat.nat,run,Code.run,Atom.run,NOp.run,
        Bill.one,Bill.word,Bill.pass,Bill.pay,Q,H,B,U] <;> omega
  have zero:Budget (run (.atom (.lit 0) : Prog false Indexed w) ((r,z),j)) 21 Q :=
    by change True ∧ 1≤21 ∧ 0≤Q;exact ⟨trivial,by decide,Nat.zero_le _⟩
  have inner:=select_budget (.atom .snd : Prog false Indexed w) 803 _ _ ((r,z),j)
    1 21 Q index val (by dsimp [Q];omega) (data paletteBase (by simp)) zero
  have middle:=select_budget (.atom .snd : Prog false Indexed w) 802 _ _ ((r,z),j)
    1 35 Q index val (by dsimp [Q];omega)
    (budget_mono (data colorBase (by simp)) (by decide)) inner
  exact budget_mono (select_budget (.atom .snd : Prog false Indexed w) 800 _ _ ((r,z),j)
    1 49 Q index val (by dsimp [Q];omega)
    (budget_mono (data count (by simp)) (by decide)) middle) (by decide)

private theorem register_room (heap j : ℕ) (hj : j<824) :
    heap+j+824≤4*heap+3000 := by omega

private theorem heap_room (r M j : ℕ) (hj : j<H r M) :
    DFTModelCacheMatchingNat.heapSize r M+j+862≤4*H r M+3000 := by
  dsimp [H,B,U,DFTModelCacheMatchingNat.heapSize,DFTModelCacheMatchingNat.wordBound,
    DFTModelCacheMatchingNat.A,DFTModelCacheMatchingNat.U,DFTModelCacheMatchingNat.W,
    DFTModelCacheMatchingNat.P] at *
  omega

attribute [local irreducible] Code.run

/-- Every allocation, literal comparison, endpoint lookup and third-word zero
write is charged before native execution. -/
theorem initialize_bounds (r : ℕ) (z : Tape Row.T) :
    Budget (run initializeProgram (r,z)) (200000+204*H r z.len) (4*H r z.len+3000) := by
  let heap:=H r z.len
  let Q:=4*heap+3000
  have regs:=tab_program_budget (.atom (.lit 824)) registerCell (r,z) 200 Q
    (by rw [atom_run];trivial) (by
      intro j hj
      rw [atom_run] at hj
      change j<824 at hj
      have h:=registerCell_bounds r z j
      exact ⟨h.1,h.2.1,h.2.2.trans (register_room (H r z.len) j hj)⟩)
  have regBudget:Budget (run (.tab (.atom (.lit 824)) registerCell) (r,z)) 168100 Q := by
    rw [atom_run] at regs
    have eq:max 824 (max 824 Q)=Q := by dsimp [Q];omega
    simpa only [Atom.run,Bill.word,Bill.work,Bill.val,Bill.peak,eq] using regs
  have cells:=tab_program_budget heapLength DFTModelCacheMatchingNat.heapCell (r,z) 200 Q
    (by rw [heapLength_run];trivial) (by
      intro j hj
      rw [heapLength_run] at hj
      dsimp only [Bill.val] at hj
      have h:=DFTModelCacheMatchingNat.heapCell_bounds r z j
      exact ⟨h.1,h.2.1,h.2.2.trans (heap_room r z.len j hj)⟩)
  have heapBudget:Budget (run (.tab heapLength DFTModelCacheMatchingNat.heapCell) (r,z))
      (18+204*heap) Q := by
    rw [heapLength_run] at cells
    have eq:max heap (max heap Q)=Q := by dsimp [Q];omega
    change Budget (run (.tab heapLength DFTModelCacheMatchingNat.heapCell) (r,z))
      (18+204*heap) (max heap (max heap Q)) at cells
    rw [eq] at cells
    exact cells
  have zero:Budget (run (.atom (.lit 0) : Prog false Input w) (r,z)) 1 Q :=
    by rw [atom_run];exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  exact budget_mono (fork_budget (.atom (.lit 0))
    (.fork (.tab (.atom (.lit 824)) registerCell)
      (.tab heapLength DFTModelCacheMatchingNat.heapCell)) (r,z) 1 (168100+(18+204*heap)+1) Q
      zero (fork_budget (.tab (.atom (.lit 824)) registerCell)
        (.tab heapLength DFTModelCacheMatchingNat.heapCell) (r,z) 168100 (18+204*heap) Q
        regBudget heapBudget)) (by omega)

end
end ExactFourierCircuits.DFTModelCacheColor
