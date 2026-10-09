import DFTModelResidualAddresses

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualAddresses
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformResidualFiberTraversal
noncomputable section

def reference (images : Tape ℕ) (h : ℕ) : Tape ℕ :=
  Tape.tab (2^h) (fun j=>address (fun i=>images.look i 0) h 0 j)

theorem address_acc (image : ℕ→ℕ) (h a j : ℕ) :
    address image h a j = a^^^address image h 0 j := by
  induction h generalizing a j with
  | zero => simp [address]
  | succ h ih =>
    simp only [address]
    split
    · exact ih a j
    · rw [ih (a^^^image h) (j-2^h),Nat.zero_xor,ih (image h) (j-2^h)]
      exact Nat.xor_assoc _ _ _

theorem reference_small (q m k h : ℕ) (images : Tape ℕ) (hk : h≤k)
    (small : ∀i,i<k→images.look i 0<2^(q*m)) (j : ℕ) :
    (reference images h).look j 0<2^(q*m) := by
  by_cases hj : j<2^h
  · simpa [reference,Tape.look,Tape.tab,hj] using
      address_small q m h 0 j (fun i=>images.look i 0) (Nat.two_pow_pos _)
        (fun i hi=>small i (by omega))
  · simp [reference,Tape.look,Tape.tab,hj]

theorem grown_reference (images : Tape ℕ) (h : ℕ) :
    grown (fun i=>images.look i 0) h (reference images h) = reference images (h+1) := by
  have pos:=Nat.two_pow_pos h
  unfold grown reference
  rw [Nat.pow_succ,Nat.mul_comm (2^h) 2]
  dsimp only [Tape.tab,Tape.len]
  congr 1
  funext j
  by_cases hj : j.val<2^h
  · simp [Tape.look,Nat.mod_eq_of_lt hj,hj,address]
  · have rest : j.val-2^h<2^h := by have hh:=j.isLt;omega
    have mod : j.val%2^h=j.val-2^h := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt rest
    simp only [mod,Tape.look,rest,↓reduceDIte,ite_eq_right hj,address,Nat.zero_xor]
    change address (fun i=>images.look i 0) h 0 (j.val-2^h) ^^^
      (if j.val<2^h then 0 else images.look h 0) =
      address (fun i=>images.look i 0) h (images.look h 0) (j.val-2^h)
    rw [ite_eq_right hj]
    simpa only [Nat.xor_comm] using
      (address_acc (fun i=>images.look i 0) h (images.look h 0) (j.val-2^h)).symm

theorem body_value (x : Input.T) (h : ℕ) (v : Tape ℕ) :
    (run body (x,(h,v))).val = (run grow ((x.2,h),v)).val := rfl

theorem body_work (x : Input.T) (h : ℕ) (v : Tape ℕ) :
    (run body (x,(h,v))).work = (run grow ((x.2,h),v)).work+12 := by
  change 11+(run grow ((x.2,h),v)).work+1 = _
  omega

theorem body_valid (x : Input.T) (h : ℕ) (v : Tape ℕ) : (run body (x,(h,v))).valid := by
  simpa only [body,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,and_true,true_and] using
    grow_valid ((x.2,h),v)

theorem initial_value (x : Input.T) (images : Tape ℕ) : (run initial x).val=reference images 0 := by
  change (Bill.tab 1 w.blank (fun _=>Bill.word 0)).val=reference images 0
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem initial_work (x : Input.T) : (run initial x).work=9 := by rfl

theorem initial_valid (x : Input.T) : (run initial x).valid := by trivial

def steps (x : Input.T) (h : ℕ) : Bill (Tape ℕ) :=
  Bill.steps (run initial x).val (fun i v=>run body (x,(i,v))) h

theorem steps_value (q m k h : ℕ) (images : Tape ℕ) (hk : h≤k)
    (small : ∀i,i<k→images.look i 0<2^(q*m)) :
    (steps (k,parameters q m images) h).val=reference images h := by
  induction h with
  | zero => exact initial_value _ _
  | succ h ih =>
    have hh : h≤k := by omega
    change (run body ((k,parameters q m images),
      (h,(steps (k,parameters q m images) h).val))).val = _
    rw [body_value,ih hh,grow_value _ _ _ _ _ (Nat.two_pow_pos h)
      (fun j _=>reference_small q m k h images hh small j) (small h (by omega))]
    exact grown_reference images h

theorem steps_valid (x : Input.T) (h : ℕ) : (steps x h).valid := by
  induction h with
  | zero => trivial
  | succ h ih => exact ⟨ih,body_valid _ _ _⟩

/-- The geometrically increasing construction costs O(m*2^k), including
all repeated table/address reads and fresh-array allocations. -/
theorem steps_work (q m k h : ℕ) (images : Tape ℕ) (hk : h≤k)
    (small : ∀i,i<k→images.look i 0<2^(q*m)) :
    (steps (k,parameters q m images) h).work+11≤(240*m+215)*2^h := by
  induction h with
  | zero => change 1+11≤(240*m+215)*1;omega
  | succ h ih =>
    have hh : h≤k := by omega
    have hv:=steps_value q m k h images hh small
    have growBound:=grow_work m (2^q) h (run DFTModelResidualTable.program q).val
      images (reference images h)
    change (steps (k,parameters q m images) h).work+
      (run body ((k,parameters q m images),
        (h,(steps (k,parameters q m images) h).val))).work+1+11≤_
    rw [body_work,hv]
    have prior:=ih hh
    change (run grow ((parameters q m images,h),reference images h)).work≤
      (120*m+96)*(2*2^h)+10 at growBound
    rw [Nat.pow_succ]
    have pos:=Nat.two_pow_pos h
    nlinarith

theorem program_value (q m k : ℕ) (images : Tape ℕ)
    (small : ∀i,i<k→images.look i 0<2^(q*m)) :
    (run program (k,parameters q m images)).val=reference images k :=
  steps_value q m k k images le_rfl small

theorem program_work (q m k : ℕ) (images : Tape ℕ)
    (small : ∀i,i<k→images.look i 0<2^(q*m)) :
    (run program (k,parameters q m images)).work≤(240*m+215)*2^k := by
  change 1+((run initial (k,parameters q m images)).work+
    (steps (k,parameters q m images) k).work)+1≤_
  rw [initial_work]
  have h:=steps_work q m k k images le_rfl small
  omega

theorem program_valid (x : Input.T) : (run program x).valid := by
  change True ∧ (run initial x).valid ∧ (steps x x.1).valid
  exact ⟨trivial,initial_valid x,steps_valid x x.1⟩

/-- Direct source-DFS correspondence: the same native address value is
computed, with a different efficient fresh-tape implementation. -/
theorem source_written (q m k : ℕ) (images : Tape ℕ)
    (small : ∀i,i<k→images.look i 0<2^(q*m))
    (output : ℕ) (u : UniformMachine.State)
    (written : ∀j,j<2^k→u.natHeap (output+j)=
      some (address (fun i=>images.look i 0) k 0 j)) :
    ∀j,j<2^k→u.natHeap (output+j)=some ((run program (k,parameters q m images)).val.look j 0) := by
  intro j hj
  rw [program_value q m k images small]
  simpa [reference,Tape.look,Tape.tab,hj] using written j hj

end
end ExactFourierCircuits.DFTModelResidualAddresses
