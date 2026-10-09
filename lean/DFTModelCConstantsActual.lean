import DFTModelCConstants

set_option autoImplicit false

/-! The closed prepared producer agrees with the actual C-constant suffix and
with the genuine initial-state preparation. The source requests one master
root; the target accepts that supplied root and derives its own five cells. -/
namespace ExactFourierCircuits.DFTModelCConstants
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier UniformMachine
noncomputable section

attribute [local irreducible] program

theorem denominators_nonzero : (2 : ℂ)≠0 ∧ a≠0 :=
  ⟨by norm_num,a_ne_zero⟩

theorem selected_specification {n : ℕ} (hn : 0<n) :
    (run program (UniformMasterRootMachine.order n,
      zeta (UniformMasterRootMachine.order n))).val=bank ∧
    (run program (UniformMasterRootMachine.order n,
      zeta (UniformMasterRootMachine.order n))).valid ∧
    (run program (UniformMasterRootMachine.order n,
      zeta (UniformMasterRootMachine.order n))).work≤
        400*(UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/4)+1) ∧
    (run program (UniformMasterRootMachine.order n,
      zeta (UniformMasterRootMachine.order n))).peak≤UniformMasterRootMachine.order n+2 :=
  specification _ (UniformMasterRootMachine.order_bounds hn).1
    (UniformCKernelPreparation.four_dvd_order hn)

theorem source_bank_cell {n : ℕ} (hn : 0<n) (j : Fin 5) :
    (run program (UniformMasterRootMachine.order n,
      zeta (UniformMasterRootMachine.order n))).val.look j.val 0=
        UniformCConstantsMachine.bank n j.succ := by
  rw [(selected_specification hn).1,bank_cell]
  fin_cases j <;> rfl

theorem suffix_heap (s : State) (ha : s.scalarReg 0=UniformPairMachine.prepared a)
    (hb : s.scalarReg 1=UniformPairMachine.prepared b) (j : Fin 5) :
    (UniformCConstantsMachine.finalState s).scalarHeap (j.val+1)=
      some (UniformPairMachine.prepared (bank.look j.val 0)) := by
  rw [UniformCConstantsMachine.final_heap s ha hb,bank_cell]
  fin_cases j <;> simp

/-- Exact correspondence to the same fifteen source instructions, with no
ready-table premise. The source suffix starts at its ordinary a,b registers. -/
theorem actual_suffix (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (pc : s.pc=0) (ha : s.scalarReg 0=UniformPairMachine.prepared a)
    (hb : s.scalarReg 1=UniformPairMachine.prepared b)
    (code : 15≤B) (wb : WordBound B s) :
    BoundedExecution UniformCConstantsMachine.suffix n x B s 15
      (UniformCConstantsMachine.finalState s) ∧
    (∀j : Fin 5,(UniformCConstantsMachine.finalState s).scalarHeap (j.val+1)=
      some (UniformPairMachine.prepared (bank.look j.val 0))) ∧
    (UniformCConstantsMachine.finalState s).rootOrders=s.rootOrders :=
  ⟨UniformCConstantsMachine.suffix_execution n x B s pc ha hb code wb,
    suffix_heap s ha hb,(UniformCConstantsMachine.final_frame s).2.2.1⟩

/-- The genuine initial-state source preparation produces exactly the closed
five-cell target bank and requests only its original master root. -/
theorem actual_preparation {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) : ∃ ticks u,
    BoundedExecution UniformCConstantsMachine.program n x ((n+2)^14) initial ticks u ∧
    (∀j : Fin 5,u.scalarHeap (j.val+1)=some (UniformPairMachine.prepared
      ((run program (UniformMasterRootMachine.order n,
        zeta (UniformMasterRootMachine.order n))).val.look j.val 0))) ∧
    u.scalarHeap 0=some (UniformPairMachine.prepared
      (zeta (UniformMasterRootMachine.order n))) ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧
    u.pc=104 ∧ ticks≤UniformCConstantsMachine.preparationBudget n := by
  obtain ⟨ticks,u,exec,_header,_order,_length,_a,_b,heap,roots,_out,pc,cost⟩ :=
    UniformCConstantsMachine.preparation_execution hn x
  refine ⟨ticks,u,exec,?_,?_,roots,pc,cost⟩
  · intro j
    rw [source_bank_cell hn j]
    exact heap j.succ
  · exact heap 0

end
end ExactFourierCircuits.DFTModelCConstants
