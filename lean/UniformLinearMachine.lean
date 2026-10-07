import UniformPreparationMachine

set_option autoImplicit false

/-! The same fixed interpreter executes linear data DAGs as well as prepared
scalar DAGs. Validity uses the machine's actual field-operation guard: add/sub
allow dependent operands, multiplication requires a prepared operand, and
division remains confined to prepared scalars. Producing the tables and linking
DFT topologies to them are separate obligations. -/
namespace ExactFourierCircuits.UniformLinearMachine
open UniformMachine UniformPreparationMachine
noncomputable section

def Ready (row : Row) (s : State) (a b v : Scalar) : Prop :=
  s.pc = 3 ∧ s.natReg 1 < s.natReg 0 ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 3 ∧
  s.natHeap (3*s.natReg 1) = some (opcode row.op) ∧
  s.natHeap (3*s.natReg 1+1) = some row.left ∧
  s.natHeap (3*s.natReg 1+2) = some row.right ∧
  s.scalarHeap row.left = some a ∧ s.scalarHeap row.right = some b ∧
  evalField row.op a b = some v

theorem prefix_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s 10 (dispatch row s a b) := by
  obtain ⟨hpc, hi, h1, h3, hop, hl, hr, ha, hb, _⟩ := hr
  refine .next (u := entered s) ?_ (.next (u := pointer s) ?_ (.next (u := tagState row s) ?_ (.next (u := leftPointer row s) ?_ (.next (u := leftState row s) ?_ (.next (u := rightPointer row s) ?_ (.next (u := rightState row s) ?_ (.next (u := leftValue row s a) ?_ (.next (u := rightValue row s a b) ?_ (.next (u := dispatch row s a b) ?_ (.refl _))))))))))
  all_goals simp [step, program, entered, pointer, tagState, leftPointer, leftState,
    rightPointer, rightState, leftValue, rightValue, dispatch, writeNat, writeScalar,
    next, hpc, hi, h1, h3, hop, hl, hr, ha, hb, evalNat, Nat.mul_comm]

theorem row_runs (n : ℕ) (x : Fin n → ℂ) (row : Row) (s : State) (a b v : Scalar)
    (hr : Ready row s a b v) : Runs program n x s (rowCost row.op) (rowEnd row s a b v) := by
  have h := (prefix_runs n x row s a b v hr).trans
    ((dispatch_runs n x row s a b).trans
      (suffix_runs n x row s a b v hr.2.2.1 hr.2.2.2.2.2.2.2.2.2))
  cases hop : row.op <;> simpa [rowCost,hop] using h

inductive ValidSchedule : List Row → State → State → Prop where
  | nil (s : State) : ValidSchedule [] s s
  | cons {row : Row} {rows : List Row} {s u : State} {a b v : Scalar}
      (ready : Ready row s a b v)
      (tail : ValidSchedule rows (rowEnd row s a b v) u) :
      ValidSchedule (row :: rows) s u

theorem ValidSchedule.runs {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) (n : ℕ) (x : Fin n → ℂ) :
    Runs program n x s (totalCost rows) u := by
  induction h with
  | nil s => exact .refl s
  | @cons row rows s u a b v hr _ ih =>
    simpa [totalCost] using (row_runs n x row s a b v hr).trans ih

theorem ValidSchedule.pc {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) (hpc : s.pc = 3) : u.pc = 3 := by
  induction h with
  | nil s => exact hpc
  | @cons row rows s u a b v hr _ ih => exact ih (row_frame row s a b v).1

theorem ValidSchedule.counters {rows : List Row} {s u : State}
    (h : ValidSchedule rows s u) :
    u.natReg 1 = s.natReg 1 + rows.length ∧
    u.natReg 9 = s.natReg 9 + rows.length ∧
    u.natReg 0 = s.natReg 0 ∧ u.natHeap = s.natHeap ∧
    u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders := by
  induction h with
  | nil s => simp
  | @cons row rows s u a b v hr _ ih =>
    have hf := row_frame row s a b v
    obtain ⟨_,h0,h1,_,_,h9,hn,_,ho,hd⟩ := hf
    simpa [h0,h1,h9,hn,ho,hd, Nat.add_assoc, Nat.add_left_comm,Nat.add_comm] using ih


theorem interpreted_schedule (n : ℕ) (x : Fin n → ℂ) (rows : List Row) (a B : ℕ)
    (s u : State) (hB : 4*rows.length+a+40 ≤ B)
    (hpc : s.pc = 0) (hk : s.natReg 0 = rows.length) (ha : s.natReg 9 = a)
    (hb : WordBound B s) (valid : ValidSchedule rows (initialized s) u) :
    BoundedExecution program n x B s (totalCost rows+5) {u with pc := 30} ∧
      totalCost rows+5 ≤ 21*rows.length+5 ∧
      u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧ u.natHeap = s.natHeap := by
  have hstart := startup_bounded n x rows.length a B s hB hpc hb
  have hc := initialized_counters rows.length a s hpc hk ha
  have hi : Interior rows.length a B (initialized s) := ⟨hstart.final_bound,hc⟩
  have hr := valid.runs n x
  have hrun := hr.bounded_of_invariant (Interior rows.length a B) hi
    (fun _ h => h.1) (fun s u h => step_interior n x rows.length a B s u hB h)
  have hufit := hrun.final_bound
  have hfinal := valid.counters
  have huc : Counters rows.length a u := by
    have hpres : ∀ s u, Interior rows.length a B s → step program n x s = .running u →
        Interior rows.length a B u := fun s u h => step_interior n x rows.length a B s u hB h
    -- Recover the same invariant from the actual segment, without assuming its end state.
    have general : ∀ {s u t}, Runs program n x s t u → Interior rows.length a B s →
        Interior rows.length a B u := by
      intro s u t h
      induction h with
      | refl _ => exact id
      | next hs _ ih => intro h; exact ih (hpres _ _ h hs)
    exact (general hr hi).2
  have hcounter : u.natReg 1 = rows.length := by
    simpa [initialized,writeNat,next] using hfinal.1
  have hu0 := huc.2.2.1
  have hupc := valid.pc (by simp [initialized,writeNat,next,hpc])
  have hex := exit_executes n x u hupc (by omega)
  have hbexit := hex.bounded_of_invariant (Interior rows.length a B)
    ⟨hufit,huc⟩ (fun _ h => h.1)
    (fun s u h => step_interior n x rows.length a B s u hB h)
  refine ⟨?_,by have h := totalCost_bound rows; omega,?_,?_,?_⟩
  · convert hstart.executes (hrun.executes hbexit) using 1; omega
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.1
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.2.2
  · simpa [initialized,writeNat,next] using hfinal.2.2.2.1


/-- The earlier prepared-scalar proof remains a special case. -/
theorem prepared_ready (row : Row) (s : State) (a b v : Scalar)
    (h : UniformPreparationMachine.Ready row s a b v) : Ready row s a b v := by
  rcases h with ⟨hp,hi,h1,h3,ho,hl,hr,ha,hb,_,_,hv⟩
  exact ⟨hp,hi,h1,h3,ho,hl,hr,ha,hb,hv⟩

theorem prepared_schedule {rows : List Row} {s u : State}
    (h : UniformPreparationMachine.ValidSchedule rows s u) : ValidSchedule rows s u := by
  induction h with
  | nil s => exact .nil s
  | cons hr _ ih => exact .cons (prepared_ready _ _ _ _ _ hr) ih

end
end ExactFourierCircuits.UniformLinearMachine
