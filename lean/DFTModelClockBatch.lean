import ModelEquivalenceInterpreter
import UniformBatching

set_option autoImplicit false

/-! Actual upstream syntax for complete recursive batches. Each child receives
one fresh contiguous slice; child results are stored as a tape of tapes and
flattened exactly once. No parent-sized tape update occurs inside the child loop.
This module does not supply the saving-network recursive body. -/
namespace ExactFourierCircuits.DFTModelClockBatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input (s t : Ty) := p s (p w (p w (a t)))
abbrev Child (s t : Ty) := p s (a t)
abbrev SliceInput (s t : Ty) := p (Input s t) w
abbrev Port (s t : Ty) := some (Child s t, a t)

def params (s t : Ty) : Prog false (SliceInput s t) s :=
  .comp (.atom .fst) (.atom .fst)
def size (s t : Ty) : Prog false (SliceInput s t) w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def source (s t : Ty) : Prog false (SliceInput s t) (a t) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def sliceCell (s t : Ty) : Prog false (p (SliceInput s t) w) t :=
  .comp (.fork (.comp (.atom .fst) (source s t))
    (.comp (.fork
      (.comp (.fork (.comp (.atom .fst) (.atom .snd))
        (.comp (.atom .fst) (size s t))) (.atom (.int .mul)))
      (.atom .snd)) (.atom (.int .add)))) (.atom .look)
def slice (s t : Ty) : Prog false (SliceInput s t) (a t) :=
  .tab (size s t) (sliceCell s t)
def childArgument (s t : Ty) : Prog false (SliceInput s t) (Child s t) :=
  .fork (params s t) (slice s t)

def calls (s t : Ty) : Code false (Port s t) (Input s t) (a (a t)) :=
  .tab (.comp (.atom .snd) (.atom .fst))
    (.comp (.importClosed (childArgument s t)) .call)

abbrev FlattenInput (t : Ty) := p w (p w (a (a t)))
def flattenCell (t : Ty) : Prog false (p (FlattenInput t) w) t :=
  .comp (.fork
    (.comp (.fork
      (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd)))
      (.comp (.fork (.atom .snd)
        (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))))
        (.atom (.int .div)))) (.atom .look))
    (.comp (.fork (.atom .snd)
      (.comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))))
      (.atom (.int .mod)))) (.atom .look)
def flattenLength (t : Ty) : Prog false (FlattenInput t) w :=
  .comp (.fork (.atom .fst) (.comp (.atom .snd) (.atom .fst))) (.atom (.int .mul))
def flatten (t : Ty) : Prog false (FlattenInput t) (a t) :=
  .tab (flattenLength t) (flattenCell t)

theorem flattenLength_run (t : Ty) (G T : ℕ) (v : Tape (Tape t.T)) :
    run (flattenLength t) (G,(T,v)) = ⟨G*T,7,G*T,True⟩ := by
  simp [flattenLength,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

def results (s t : Ty) (child : Prog false (Child s t) (a t)) :
    Prog false (Input s t) (a (a t)) :=
  .tab (.comp (.atom .snd) (.atom .fst))
    (.comp (childArgument s t) child)

def geometry (s t : Ty) : Prog false (Input s t) (p w w) :=
  .comp (.atom .snd) (.fork (.atom .fst) (.comp (.atom .snd) (.atom .fst)))
def arrange (t : Ty) : Prog false (p (p w w) (a (a t))) (FlattenInput t) :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd))

/-- A closed, finite program when the child is a closed finite program. -/
def program (s t : Ty) (child : Prog false (Child s t) (a t)) :
    Prog false (Input s t) (a t) :=
  .comp (.fork (geometry s t) (results s t child))
    (.comp (arrange t) (flatten t))

theorem code_comp_value {r : RAM.Port} {a b c : Ty}
    (f : Code false r a b) (g : Code false r b c) (h : Handler r) (x : a.T) :
    (Code.run (.comp f g) h x).val = (Code.run g h (Code.run f h x).val).val := rfl

theorem code_fork_value {r : RAM.Port} {a b c : Ty}
    (f : Code false r a b) (g : Code false r a c) (h : Handler r) (x : a.T) :
    (Code.run (.fork f g) h x).val = ((Code.run f h x).val,(Code.run g h x).val) := rfl

theorem geometry_value (s t : Ty) (p : s.T) (G T : ℕ) (v : Tape t.T) :
    (run (geometry s t) (p,(G,(T,v)))).val = (G,T) := rfl

theorem arrange_value (t : Ty) (G T : ℕ) (v : Tape (Tape t.T)) :
    (run (arrange t) ((G,T),v)).val = (G,(T,v)) := rfl

def sliced {α : Type} (T g : ℕ) (v : Tape α) (z : α) : Tape α :=
  Tape.tab T (fun j => v.look (g*T+j) z)

theorem sliceCell_run (s t : Ty) (p : s.T) (G T g j : ℕ) (v : Tape t.T) :
    run (sliceCell s t) (((p,(G,(T,v))),g),j) =
      ⟨v.look (g*T+j) t.blank,31,g*T+j,True⟩ := by
  simp [sliceCell,source,size,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem slice_value (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (slice s t) ((p,(G,(T,v))),g)).val = sliced T g v t.blank := by
  change (Bill.tab T t.blank (fun j => run (sliceCell s t) (((p,(G,(T,v))),g),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab T) (funext (fun j => congrArg Bill.val
    (sliceCell_run s t p G T g j v)))

theorem slice_work (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (slice s t) ((p,(G,(T,v))),g)).work = 35*T+10 := by
  change 7+(Bill.tab T t.blank (fun j => run (sliceCell s t) (((p,(G,(T,v))),g),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run (sliceCell s t) (((p,(G,(T,v))),g),j)).work) = fun _ => 31 := by
    funext j; exact congrArg Bill.work (sliceCell_run s t p G T g j v)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem slice_valid (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (slice s t) ((p,(G,(T,v))),g)).valid := by
  simp only [slice,run,Code.run,size,Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [true_and]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  change (run (sliceCell s t) (((p,(G,(T,v))),g),j)).valid
  rw [sliceCell_run]; trivial

theorem childArgument_run (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (childArgument s t) ((p,(G,(T,v))),g)).val = (p,sliced T g v t.blank) := by
  change (p,(run (slice s t) ((p,(G,(T,v))),g)).val) = _
  rw [slice_value]

theorem calls_value (s t : Ty) (h : Handler (Port s t)) (p : s.T)
    (G T : ℕ) (v : Tape t.T) :
    (Code.run (calls s t) h (p,(G,(T,v)))).val = Tape.tab G
      (fun g => (h (p,sliced T g v t.blank)).val) := by
  change (Bill.tab G (a t).blank (fun g => Code.run
    (.comp (.importClosed (childArgument s t)) .call) h ((p,(G,(T,v))),g))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab G); funext g
  change (h (run (childArgument s t) ((p,(G,(T,v))),g)).val).val = _
  rw [childArgument_run]

theorem flattenCell_run (t : Ty) (G T j : ℕ) (v : Tape (Tape t.T)) :
    run (flattenCell t) ((G,(T,v)),j) =
      ⟨(v.look (j/T) (Tape.empty t.T)).look (j%T) t.blank,
        29,max (j/T) (j%T),True⟩ := by
  simp [flattenCell,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem flatten_value (t : Ty) (G T : ℕ) (v : Tape (Tape t.T)) :
    (run (flatten t) (G,(T,v))).val = Tape.tab (G*T)
      (fun j => (v.look (j/T) (Tape.empty t.T)).look (j%T) t.blank) := by
  change (Bill.tab (G*T) t.blank (fun j => run (flattenCell t) ((G,(T,v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (G*T)) (funext (fun j => congrArg Bill.val
    (flattenCell_run t G T j v)))

theorem flatten_work (t : Ty) (G T : ℕ) (v : Tape (Tape t.T)) :
    (run (flatten t) (G,(T,v))).work = 33*(G*T)+10 := by
  change 7+(Bill.tab (G*T) t.blank (fun j => run (flattenCell t) ((G,(T,v)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run (flattenCell t) ((G,(T,v)),j)).work) = fun _ => 29 := by
    funext j; exact congrArg Bill.work (flattenCell_run t G T j v)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem flatten_valid (t : Ty) (G T : ℕ) (v : Tape (Tape t.T)) :
    (run (flatten t) (G,(T,v))).valid := by
  simp only [flatten,flattenLength,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  simp only [true_and]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  change (run (flattenCell t) ((G,(T,v)),j)).valid
  rw [flattenCell_run]; trivial

theorem childArgument_work (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (childArgument s t) ((p,(G,(T,v))),g)).work = 35*T+14 := by
  change 3+(run (slice s t) ((p,(G,(T,v))),g)).work+1 = _
  rw [slice_work]
  omega

theorem childArgument_valid (s t : Ty) (p : s.T) (G T g : ℕ) (v : Tape t.T) :
    (run (childArgument s t) ((p,(G,(T,v))),g)).valid := by
  change (True ∧ True) ∧ (run (slice s t) ((p,(G,(T,v))),g)).valid ∧ True
  exact ⟨⟨trivial,trivial⟩,slice_valid s t p G T g v,trivial⟩

theorem calls_work (s t : Ty) (h : Handler (Port s t)) (p : s.T)
    (G T : ℕ) (v : Tape t.T) :
    (Code.run (calls s t) h (p,(G,(T,v)))).work =
      6+G*(35*T+21)+∑g ∈ Finset.range G,(h (p,sliced T g v t.blank)).work := by
  change 3+(Bill.tab G (a t).blank (fun g => Code.run
    (.comp (.importClosed (childArgument s t)) .call) h ((p,(G,(T,v))),g))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have point (g : ℕ) : (Code.run
      (.comp (.importClosed (childArgument s t)) .call) h ((p,(G,(T,v))),g)).work =
      35*T+17+(h (p,sliced T g v t.blank)).work := by
    change (run (childArgument s t) ((p,(G,(T,v))),g)).work+1+
      (h (run (childArgument s t) ((p,(G,(T,v))),g)).val).work+1+1 = _
    rw [childArgument_work,childArgument_run]; omega
  simp_rw [point]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

theorem calls_valid (s t : Ty) (h : Handler (Port s t)) (p : s.T)
    (G T : ℕ) (v : Tape t.T) :
    (Code.run (calls s t) h (p,(G,(T,v)))).valid ↔
      ∀g<G,(h (p,sliced T g v t.blank)).valid := by
  simp only [calls,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [true_and,ModelEquivalenceInterpreter.tab_valid]
  apply forall_congr'; intro g
  apply forall_congr'; intro _
  change ((run (childArgument s t) ((p,(G,(T,v))),g)).valid ∧
    (h (run (childArgument s t) ((p,(G,(T,v))),g)).val).valid) ↔ _
  rw [childArgument_run]
  exact and_iff_right (childArgument_valid s t p G T g v)

theorem results_value (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T) :
    (run (results s t child) (p,(G,(T,v)))).val =
      Tape.tab G (fun g => (run child (p,sliced T g v t.blank)).val) := by
  change (Bill.tab G (a t).blank (fun g =>
    run (.comp (childArgument s t) child) ((p,(G,(T,v))),g))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab G); funext g
  change (run child (run (childArgument s t) ((p,(G,(T,v))),g)).val).val = _
  rw [childArgument_run]

theorem program_value (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T) :
    (run (program s t child) (p,(G,(T,v)))).val = Tape.tab (G*T)
      (fun j => (run child (p,sliced T (j/T) v t.blank)).val.look (j%T) t.blank) := by
  let tapes := Tape.tab G (fun g => (run child (p,sliced T g v t.blank)).val)
  unfold program run
  rw [code_comp_value,code_fork_value]
  change (Code.run (.comp (arrange t) (flatten t)) ()
    ((run (geometry s t) (p,(G,(T,v)))).val,
      (run (results s t child) (p,(G,(T,v)))).val)).val = _
  rw [geometry_value,results_value,code_comp_value]
  change (run (flatten t) (run (arrange t) ((G,T),tapes)).val).val = _
  rw [arrange_value,flatten_value]
  dsimp only [Tape.tab]
  congr 1
  funext j
  have tp : 0<T := by
    have bound := j.isLt
    by_contra h
    have z : T=0 := by omega
    simp [z] at bound
  have hj : j.val/T<G := (Nat.div_lt_iff_lt_mul tp).2 (by
    simpa only [Nat.mul_comm] using j.isLt)
  change (tapes.look (j.val/T) (Tape.empty t.T)).look (j.val%T) t.blank = _
  have looked : tapes.look (j.val/T) (Tape.empty t.T) =
      (run child (p,sliced T (j.val/T) v t.blank)).val := by
    simp only [tapes,Tape.look,Tape.tab,hj,↓reduceDIte]
  rw [looked]

theorem results_work (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T) :
    (run (results s t child) (p,(G,(T,v)))).work =
      6+G*(35*T+19)+∑g ∈ Finset.range G,(run child (p,sliced T g v t.blank)).work := by
  change 3+(Bill.tab G (a t).blank (fun g =>
    run (.comp (childArgument s t) child) ((p,(G,(T,v))),g))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have point (g : ℕ) : (run (.comp (childArgument s t) child)
      ((p,(G,(T,v))),g)).work = 35*T+15+(run child (p,sliced T g v t.blank)).work := by
    change (run (childArgument s t) ((p,(G,(T,v))),g)).work+
      (run child (run (childArgument s t) ((p,(G,(T,v))),g)).val).work+1 = _
    rw [childArgument_work,childArgument_run]; omega
  simp_rw [point]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

theorem program_work (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T) :
    (run (program s t child) (p,(G,(T,v)))).work =
      35+68*(G*T)+19*G+∑g ∈ Finset.range G,(run child (p,sliced T g v t.blank)).work := by
  change (7+(run (results s t child) (p,(G,(T,v)))).work+1)+
    (9+(run (flatten t) (G,(T,(run (results s t child) (p,(G,(T,v)))).val))).work+1)+1 = _
  rw [flatten_work,results_work]
  ring

theorem results_valid (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T)
    (hc : ∀g<G,(run child (p,sliced T g v t.blank)).valid) :
    (run (results s t child) (p,(G,(T,v)))).valid := by
  simp only [results,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [true_and,ModelEquivalenceInterpreter.tab_valid]
  intro g hg
  change (run (childArgument s t) ((p,(G,(T,v))),g)).valid ∧
    (run child (run (childArgument s t) ((p,(G,(T,v))),g)).val).valid
  rw [childArgument_run]
  exact ⟨childArgument_valid s t p G T g v,hc g hg⟩

theorem program_valid (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T : ℕ) (v : Tape t.T)
    (hc : ∀g<G,(run child (p,sliced T g v t.blank)).valid) :
    (run (program s t child) (p,(G,(T,v)))).valid := by
  have good := results_valid s t child p G T v hc
  have final := flatten_valid t G T (run (results s t child) (p,(G,(T,v)))).val
  simpa only [program,geometry,arrange,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    true_and,and_true] using And.intro good final

theorem tab_peak {r : RAM.Port} {s t : Ty} (n : Code false r s w)
    (body : Code false r (p s w) t) (h : Handler r) (x : s.T) :
    (Code.run (.tab n body) h x).peak = max
      (max (Code.run n h x).peak
        (Bill.tab (Code.run n h x).val t.blank (fun j => Code.run body h (x,j))).peak) 0 := rfl

theorem slice_peak (s t : Ty) (p : s.T) (G T g B : ℕ) (v : Tape t.T)
    (sizeFit : T≤B) (endFit : g*T+T≤B) :
    (run (slice s t) ((p,(G,(T,v))),g)).peak ≤ B := by
  unfold slice run
  rw [tab_peak]
  change max (max 0 (Bill.tab T t.blank (fun j =>
    run (sliceCell s t) (((p,(G,(T,v))),g),j))).peak) 0 ≤ B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero]
  refine max_le sizeFit ?_
  apply Finset.sup_le
  intro j hj
  rw [show (run (sliceCell s t) (((p,(G,(T,v))),g),j)).peak=g*T+j from
    congrArg Bill.peak (sliceCell_run s t p G T g j v)]
  have bound := Finset.mem_range.mp hj
  omega

theorem childArgument_peak (s t : Ty) (p : s.T) (G T g B : ℕ) (v : Tape t.T)
    (sizeFit : T≤B) (endFit : g*T+T≤B) :
    (run (childArgument s t) ((p,(G,(T,v))),g)).peak ≤ B := by
  have hs := slice_peak s t p G T g B v sizeFit endFit
  simpa only [childArgument,params,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero] using hs

theorem flatten_peak (t : Ty) (G T B : ℕ) (v : Tape (Tape t.T)) (fit : G*T≤B) :
    (run (flatten t) (G,(T,v))).peak ≤ B := by
  unfold flatten run
  rw [tab_peak]
  change max (max (run (flattenLength t) (G,(T,v))).peak
    (Bill.tab (run (flattenLength t) (G,(T,v))).val t.blank
      (fun j => run (flattenCell t) ((G,(T,v)),j))).peak) 0 ≤ B
  rw [flattenLength_run,ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le fit (max_le fit ?_)
  apply Finset.sup_le
  intro j hj
  rw [show (run (flattenCell t) ((G,(T,v)),j)).peak=max (j/T) (j%T) from
    congrArg Bill.peak (flattenCell_run t G T j v)]
  have bound := Finset.mem_range.mp hj
  exact max_le ((Nat.div_le_self _ _).trans (by omega))
    ((Nat.mod_le _ _).trans (by omega))

theorem results_peak (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T B : ℕ) (v : Tape t.T) (countFit : G≤B) (sizeFit : T≤B)
    (extent : G*T≤B) (hc : ∀g<G,(run child (p,sliced T g v t.blank)).peak≤B) :
    (run (results s t child) (p,(G,(T,v)))).peak≤B := by
  unfold results run
  rw [tab_peak]
  change max (max 0 (Bill.tab G (a t).blank (fun g =>
    run (.comp (childArgument s t) child) ((p,(G,(T,v))),g))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero]
  refine max_le countFit ?_
  apply Finset.sup_le
  intro g hg
  have hg' := Finset.mem_range.mp hg
  have endFit : g*T+T≤B := by
    calc
      g*T+T=(g+1)*T := by ring
      _≤G*T := Nat.mul_le_mul_right T (by omega)
      _≤B := extent
  have hs := childArgument_peak s t p G T g B v sizeFit endFit
  change max (max (run (childArgument s t) ((p,(G,(T,v))),g)).peak
    (run child (run (childArgument s t) ((p,(G,(T,v))),g)).val).peak) 0 ≤ B
  rw [childArgument_run]
  exact max_le (max_le hs (hc g hg')) (Nat.zero_le _)

theorem program_peak (s t : Ty) (child : Prog false (Child s t) (a t))
    (p : s.T) (G T B : ℕ) (v : Tape t.T) (countFit : G≤B) (sizeFit : T≤B)
    (extent : G*T≤B) (hc : ∀g<G,(run child (p,sliced T g v t.blank)).peak≤B) :
    (run (program s t child) (p,(G,(T,v)))).peak≤B := by
  have hr := results_peak s t child p G T B v countFit sizeFit extent hc
  have hf := flatten_peak t G T B (run (results s t child) (p,(G,(T,v)))).val extent
  simpa only [program,geometry,arrange,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero,max_le_iff] using And.intro hr hf

/-- The chunk widths are the actual complete W batches of the held engine;
there is no independent padding of recursive child arrays. -/
theorem actual_partition {k : ℕ} (large : UniformBatching.threshold≤k) :
    UniformBatching.batchCount k*(UniformBatching.width*2^UniformBatching.quotient k)=2^k :=
  UniformBatching.batch_partition large

end
end ExactFourierCircuits.DFTModelClockBatch
