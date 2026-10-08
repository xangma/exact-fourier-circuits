import UniformMachineRuns

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMachineConjugation
open UniformMachine
noncomputable section

/-- Semantic reflection only. The physical instruction set gains no conjugation
operation, and this map does not manufacture a charged starting state. -/
def conjScalar (v : Scalar) : Scalar := ⟨starRingEnd ℂ v.value,v.dependent⟩
def conjState (s : State) : State :=
  { s with
    scalarReg := fun j => conjScalar (s.scalarReg j)
    scalarHeap := fun j => (s.scalarHeap j).map conjScalar
    outputs := fun j => (s.outputs j).map (starRingEnd ℂ) }
def conjResult : StepResult→StepResult
  | .running s=>.running (conjState s)
  | .halted s=>.halted (conjState s)
  | .failed=>.failed

/-- Length/output instructions are permitted. Input and fresh-root instructions
are excluded because their external supplies are not changed by this reflection. -/
def instructionAllowed : Instruction→Bool
  | .input .. | .root ..=>false
  | _=>true
def Allowed (p : Program) : Prop := ∀i∈p,instructionAllowed i=true

@[simp] lemma conjScalar_value (v : Scalar) : (conjScalar v).value=starRingEnd ℂ v.value := rfl
@[simp] lemma conjScalar_dependent (v : Scalar) : (conjScalar v).dependent=v.dependent := rfl
@[simp] lemma conjScalar_zero : conjScalar Scalar.zero=Scalar.zero := by simp [conjScalar,Scalar.zero]
@[simp] lemma conjScalar_twice (v : Scalar) : conjScalar (conjScalar v)=v := by
  cases v
  simp [conjScalar]
@[simp] lemma conjScalar_rational (q : ℚ) : conjScalar ⟨q,false⟩=⟨q,false⟩ := by simp [conjScalar]
@[simp] lemma conjState_pc (s : State) : (conjState s).pc=s.pc := rfl
@[simp] lemma conjState_natReg (s : State) : (conjState s).natReg=s.natReg := rfl
@[simp] lemma conjState_natHeap (s : State) : (conjState s).natHeap=s.natHeap := rfl
@[simp] lemma conjState_rootOrders (s : State) : (conjState s).rootOrders=s.rootOrders := rfl
@[simp] lemma conjState_scalarReg (s : State) (j : ℕ) :
    (conjState s).scalarReg j=conjScalar (s.scalarReg j) := rfl
@[simp] lemma conjState_scalarHeap (s : State) (j : ℕ) :
    (conjState s).scalarHeap j=(s.scalarHeap j).map conjScalar := rfl
@[simp] lemma conjState_outputs (s : State) (j : ℕ) :
    (conjState s).outputs j=(s.outputs j).map (starRingEnd ℂ) := rfl
@[simp] lemma conjState_twice (s : State) : conjState (conjState s)=s := by
  cases s
  simp [conjState,Option.map_map,Function.comp_def]
@[simp] lemma conjResult_twice (r : StepResult) : conjResult (conjResult r)=r := by
  cases r <;> simp [conjResult]

lemma map_update {α β : Type} (f : α→β) (v : ℕ→α) (j : ℕ) (x : α) :
    (fun q=>f (Function.update v j x q))=Function.update (fun q=>f (v q)) j (f x) := by
  funext q
  by_cases h:q=j <;> simp [h]
@[simp] lemma conjState_next (s : State) : conjState (next s)=next (conjState s) := rfl
@[simp] lemma conjState_writeNat (s : State) (j v : ℕ) :
    conjState (writeNat s j v)=writeNat (conjState s) j v := rfl
@[simp] lemma conjState_writeScalar (s : State) (j : ℕ) (v : Scalar) :
    conjState (writeScalar s j v)=writeScalar (conjState s) j (conjScalar v) := by
  simp only [conjState,writeScalar,next,map_update]
@[simp] lemma conjState_storeNat (s : State) (a v : ℕ) :
    conjState {next s with natHeap:=Function.update s.natHeap a (some v)}=
    {next (conjState s) with natHeap:=Function.update s.natHeap a (some v)} := rfl
@[simp] lemma conjState_storeScalar (s : State) (a : ℕ) (v : Scalar) :
    conjState {next s with scalarHeap:=Function.update s.scalarHeap a (some v)}=
    {next (conjState s) with scalarHeap:=Function.update (conjState s).scalarHeap a (some (conjScalar v))} := by
  simp only [conjState,next,map_update,Option.map_some]
@[simp] lemma conjState_output (s : State) (a : ℕ) (v : ℂ) :
    conjState {next s with outputs:=Function.update s.outputs a (some v)}=
    {next (conjState s) with outputs:=Function.update (conjState s).outputs a (some (starRingEnd ℂ v))} := by
  simp only [conjState,next,map_update,Option.map_some]
@[simp] lemma conjState_setPC (s : State) (pc : ℕ) :
    conjState {s with pc:=pc}={conjState s with pc:=pc} := rfl

/-- The same Boolean/zero guards accept or reject the reflected operands. -/
theorem evalField_conjugate (op : FieldOp) (a b : Scalar) :
    evalField op (conjScalar a) (conjScalar b)=(evalField op a b).map conjScalar := by
  cases op with
  | add=>simp [evalField,conjScalar]
  | sub=>simp [evalField,conjScalar]
  | mul=>cases ha:a.dependent <;> cases hb:b.dependent <;> simp [evalField,conjScalar,ha,hb]
  | div=>
    cases ha:a.dependent <;> cases hb:b.dependent <;> simp [evalField,conjScalar,ha,hb]
    by_cases hz:b.value=0 <;> simp [hz,conjScalar]
theorem evalField_failure_iff (op : FieldOp) (a b : Scalar) :
    evalField op (conjScalar a) (conjScalar b)=none ↔ evalField op a b=none := by
  rw [evalField_conjugate]
  simp

/-- All actual success/failure/halt outcomes commute, including absent reads,
partial division, output index guards and unchanged Nat branch decisions. -/
theorem step_conjugate (p : Program) (hp : Allowed p) (n : ℕ)
    (x : Fin n→ℂ) (s : State) : step p n x (conjState s)=conjResult (step p n x s) := by
  cases hf:p[s.pc]? with
  | none=>simp [step,hf,conjResult]
  | some i=>
    have hi:=hp i (List.mem_of_getElem? hf)
    cases i with
    | input dst index=>simp [instructionAllowed] at hi
    | root dst order=>simp [instructionAllowed] at hi
    | natLiteral dst v=>simp [step,hf,conjResult]
    | length dst=>simp [step,hf,conjResult]
    | scalarLiteral dst v=>simp [step,hf,conjResult]
    | natBinary op dst l r=>
      cases hv:evalNat op (s.natReg l) (s.natReg r) <;> simp [step,hf,hv,conjResult]
    | fieldBinary op dst l r=>
      simp only [step,conjState_pc,hf,conjState_scalarReg,evalField_conjugate]
      cases evalField op (s.scalarReg l) (s.scalarReg r) <;> simp [conjResult]
    | loadNat dst address=>
      cases hv:s.natHeap (s.natReg address) <;> simp [step,hf,hv,conjResult]
    | storeNat address src=>simp [step,hf,conjResult]
    | loadScalar dst address=>
      cases hv:s.scalarHeap (s.natReg address) <;> simp [step,hf,hv,conjResult]
    | storeScalar address src=>simp [step,hf,conjResult]
    | output index src=>
      by_cases h:s.natReg index<n <;> simp [step,hf,h,conjResult]
    | branchLT l r y no=>simp [step,hf,conjResult];rfl
    | jump target=>simp [step,hf,conjResult]
    | halt=>simp [step,hf,conjResult]

theorem step_failure_iff (p : Program) (hp : Allowed p) (n : ℕ)
    (x : Fin n→ℂ) (s : State) : step p n x (conjState s)=.failed ↔ step p n x s=.failed := by
  rw [step_conjugate p hp]
  cases step p n x s <;> simp [conjResult]

/-- Addresses and presence, not field magnitudes, govern the word envelope. -/
theorem wordBound (B : ℕ) (s : State) (h:WordBound B s) : WordBound B (conjState s) := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.2⟩
  · intro a v ha
    obtain ⟨u,hu,_⟩:=Option.map_eq_some_iff.mp (show _=some v from ha)
    exact h.2.2.2.1 a u hu
  · intro a v ha
    obtain ⟨u,hu,_⟩:=Option.map_eq_some_iff.mp (show _=some v from ha)
    exact h.2.2.2.2.1 a u hu
theorem wordBound_iff (B : ℕ) (s : State) : WordBound B (conjState s) ↔ WordBound B s :=
  ⟨fun h=>by simpa using wordBound B (conjState s) h,wordBound B s⟩

theorem runs {p : Program} (hp : Allowed p) {n t : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Runs p n x s t u) : Runs p n x (conjState s) t (conjState u) := by
  induction h with
  | refl s=>exact .refl _
  | next hs _ ih=>exact .next (by rw [step_conjugate p hp,hs];rfl) ih
theorem bounded_runs {p : Program} (hp : Allowed p) {n B t : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:BoundedRuns p n x B s t u) : BoundedRuns p n x B (conjState s) t (conjState u) := by
  induction h with
  | refl hb=>exact .refl (wordBound B _ hb)
  | next hb hs _ ih=>exact .next (wordBound B _ hb) (by rw [step_conjugate p hp,hs];rfl) ih
theorem executes {p : Program} (hp : Allowed p) {n t : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Executes p n x s t u) : Executes p n x (conjState s) t (conjState u) := by
  induction h with
  | halt hs=>exact .halt (by rw [step_conjugate p hp,hs];rfl)
  | next hs _ ih=>exact .next (by rw [step_conjugate p hp,hs];rfl) ih
theorem bounded_execution {p : Program} (hp : Allowed p) {n B t : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:BoundedExecution p n x B s t u) :
    BoundedExecution p n x B (conjState s) t (conjState u) := by
  induction h with
  | halt hb hs=>exact .halt (wordBound B _ hb) (by rw [step_conjugate p hp,hs];rfl)
  | next hb hs _ ih=>exact .next (wordBound B _ hb) (by rw [step_conjugate p hp,hs];rfl) ih

end
end ExactFourierCircuits.UniformMachineConjugation
