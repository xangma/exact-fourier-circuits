import DFTModelRecursiveMetadata

set_option autoImplicit false

/-! Fresh nested tapes from a fixed finite list of integer expressions.  The
expressions are actual upstream syntax, and every selected branch is charged. -/
namespace ExactFourierCircuits.DFTModelCacheLiteral
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore DFTModelRecursiveMetadata
noncomputable section

theorem tab_ext {α : Type} (n : ℕ) (f g : ℕ→α)
    (h : ∀j,j<n→f j=g j) : Tape.tab n f=Tape.tab n g := by
  apply congrArg (fun z : Fin n→α => (⟨n,z⟩ : Tape α))
  funext j
  exact h j.val j.isLt

def decrement {s : Ty} : Prog false (p s w) (p s w) :=
  .fork (.atom .fst) (.comp (.atom .snd) predecessor)

def choose {s t : Ty} (fallback : Prog false s t) :
    List (Prog false s t) → Prog false (p s w) t
  | [] => .comp (.atom .fst) fallback
  | f::fs => .ifz (.atom .snd) (.comp (.atom .fst) f)
      (.comp decrement (choose fallback fs))

def materialize {s t : Ty} (fallback : Prog false s t)
    (fs : List (Prog false s t)) : Prog false s (Ty.a t) :=
  .tab (.atom (.lit fs.length)) (choose fallback fs)

theorem decrement_run {s : Ty} (x : s.T) (j : ℕ) :
    run decrement (x,j)=⟨(x,j-1),9,max 1 (j-1),True⟩ := by
  simp [decrement,fork_run,comp_run,atom_run,Atom.run,Bill.one,
    Bill.pass,Bill.pay,predecessor_run]

theorem choose_nil {s t : Ty} (f : Prog false s t) (x : s.T) (j : ℕ) :
    run (choose f []) (x,j)=
      ⟨(run f x).val,(run f x).work+2,(run f x).peak,(run f x).valid⟩ := by
  rw [choose,comp_run]
  simp [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem choose_zero {s t : Ty} (d f : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) :
    run (choose d (f::fs)) (x,0)=
      ⟨(run f x).val,(run f x).work+4,(run f x).peak,(run f x).valid⟩ := by
  rw [choose,ifz_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,ite_true,comp_run]
  simp only [zero_max,max_zero,true_and]
  congr 1
  omega

theorem choose_succ {s t : Ty} (d f : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (j : ℕ) :
    run (choose d (f::fs)) (x,j+1)=
      ⟨(run (choose d fs) (x,j)).val,(run (choose d fs) (x,j)).work+12,
        max (max 1 j) (run (choose d fs) (x,j)).peak,
        (run (choose d fs) (x,j)).valid⟩ := by
  rw [choose,ifz_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,Nat.add_one_ne_zero,ite_false]
  rw [comp_run,decrement_run]
  simp only [Bill.pass,Bill.pay,Nat.add_sub_cancel,max_zero,true_and]
  congr 1; ac_rfl

theorem choose_value {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (j : ℕ) :
    (run (choose d fs) (x,j)).val=(run ((fs[j]?).getD d) x).val := by
  induction fs generalizing j with
  | nil => rw [choose_nil];rfl
  | cons f fs ih =>
    cases j with
    | zero => rw [choose_zero];rfl
    | succ j => rw [choose_succ];exact ih j

theorem choose_valid {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (j : ℕ)
    (hd : (run d x).valid) (hf : ∀f∈fs,(run f x).valid) :
    (run (choose d fs) (x,j)).valid := by
  induction fs generalizing j with
  | nil => rw [choose_nil];exact hd
  | cons f fs ih =>
    cases j with
    | zero => rw [choose_zero];exact hf f (by simp)
    | succ j =>
      rw [choose_succ]
      exact ih j (fun f h=>hf f (by simp [h]))

theorem choose_work {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (j : ℕ) :
    (run (choose d fs) (x,j)).work≤
      12*fs.length+(fs.map (fun f=>(run f x).work)).sum+(run d x).work+2 := by
  induction fs generalizing j with
  | nil => rw [choose_nil];simp
  | cons f fs ih =>
    cases j with
    | zero => rw [choose_zero];simp only [List.length_cons,List.map_cons,List.sum_cons];omega
    | succ j =>
      rw [choose_succ]
      have h:=ih j
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega

theorem choose_peak {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (j B : ℕ)
    (hj : j≤B) (h1 : 1≤B) (hd : (run d x).peak≤B)
    (hf : ∀f∈fs,(run f x).peak≤B) :
    (run (choose d fs) (x,j)).peak≤B := by
  induction fs generalizing j with
  | nil => rw [choose_nil];exact hd
  | cons f fs ih =>
    cases j with
    | zero => rw [choose_zero];exact hf f (by simp)
    | succ j =>
      rw [choose_succ]
      exact max_le (max_le h1 (by omega))
        (ih j (by omega) (fun f h=>hf f (by simp [h])))

theorem materialize_value {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) :
    (run (materialize d fs) x).val=
      Tape.tab fs.length (fun j=>(run ((fs[j]?).getD d) x).val) := by
  change (Bill.tab fs.length t.blank (fun j=>run (choose d fs) (x,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab fs.length) (funext (choose_value d fs x))

theorem materialize_valid {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T)
    (hd : (run d x).valid) (hf : ∀f∈fs,(run f x).valid) :
    (run (materialize d fs) x).valid := by
  change True ∧ (Bill.tab fs.length t.blank (fun j=>run (choose d fs) (x,j))).valid
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _=>choose_valid d fs x j hd hf)⟩

theorem materialize_work {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) :
    (run (materialize d fs) x).work≤4+fs.length*
      (12*fs.length+(fs.map (fun f=>(run f x).work)).sum+(run d x).work+6) := by
  change 1+(Bill.tab fs.length t.blank (fun j=>run (choose d fs) (x,j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j∈Finset.range fs.length,(run (choose d fs) (x,j)).work)≤
      fs.length*(12*fs.length+(fs.map (fun f=>(run f x).work)).sum+(run d x).work+2) := by
    calc
      _ ≤ ∑_j∈Finset.range fs.length,
          (12*fs.length+(fs.map (fun f=>(run f x).work)).sum+(run d x).work+2) :=
        Finset.sum_le_sum (fun j _=>choose_work d fs x j)
      _ = _ := by simp
  nlinarith

theorem materialize_peak {s t : Ty} (d : Prog false s t)
    (fs : List (Prog false s t)) (x : s.T) (B : ℕ)
    (hlen : fs.length≤B) (h1 : 1≤B) (hd : (run d x).peak≤B)
    (hf : ∀f∈fs,(run f x).peak≤B) :
    (run (materialize d fs) x).peak≤B := by
  change max (max fs.length (Bill.tab fs.length t.blank
    (fun j=>run (choose d fs) (x,j))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le hlen (max_le hlen ?_)
  exact Finset.sup_le (fun j hj=>choose_peak d fs x j B
    (by have h:=Finset.mem_range.mp hj;omega) h1 hd hf)

end
end ExactFourierCircuits.DFTModelCacheLiteral
