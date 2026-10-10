import DFTModelCacheMatchingNatInitialization

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheMatchingNat
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section

def Budget {α : Type} (b : Bill α) (W B : ℕ) : Prop :=
  b.valid ∧ b.work≤W ∧ b.peak≤B

theorem budget_mono {α : Type} {b : Bill α} {W V B : ℕ}
    (h : Budget b W B) (le : W≤V) : Budget b V B := ⟨h.1,h.2.1.trans le,h.2.2⟩

private theorem distance_bound (a n B : ℕ) (ha : a≤B) (hn : n≤B) :
    a-n+(n-a)≤B := by omega

theorem select_budget {s t : Ty} (f : Prog false s w) (n : ℕ)
    (yes no : Prog false s t) (x : s.T) (F Y B : ℕ)
    (test : Budget (run f x) F B) (value : (run f x).val≤B) (literal : n≤B)
    (left : Budget (run yes x) Y B) (right : Budget (run no x) Y B) :
    Budget (run (select f n yes no) x) (2*F+12+Y) B := by
  rcases test with ⟨tv,tw,tp⟩
  rcases left with ⟨lv,lw,lp⟩
  rcases right with ⟨rv,rw,rp⟩
  simp only [Budget,select,eqTest,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  dsimp only [run] at tv tw tp value lv lw lp rv rw rp
  split_ifs <;> simp_all only [ite_true,ite_false,true_and,and_true]
  all_goals
    have sub1 : (Code.run f () x).val-n≤B := (Nat.sub_le _ _).trans value
    have sub2 : n-(Code.run f () x).val≤B := (Nat.sub_le _ _).trans literal
    have distance : (Code.run f () x).val-n+(n-(Code.run f () x).val)≤B := by
      exact distance_bound _ _ _ value literal
    constructor
    · omega
    · repeat' apply max_le
      all_goals first | exact tp | exact literal | exact lp | exact rp | exact sub1 | exact sub2 | exact distance | exact Nat.zero_le _

theorem ifz_budget {s t : Ty} (f : Prog false s w)
    (yes no : Prog false s t) (x : s.T) (F Y B : ℕ)
    (test : Budget (run f x) F B)
    (left : Budget (run yes x) Y B) (right : Budget (run no x) Y B) :
    Budget (run (.ifz f yes no) x) (F+Y+1) B := by
  rcases test with ⟨tv,tw,tp⟩
  rcases left with ⟨lv,lw,lp⟩
  rcases right with ⟨rv,rw,rp⟩
  rw [ifz_run]
  unfold Budget
  dsimp only [Bill.pass,Bill.pay]
  split_ifs <;> exact ⟨⟨tv,by assumption⟩,by omega,by omega⟩

theorem fork_budget {s t u : Ty} (f : Prog false s t) (g : Prog false s u)
    (x : s.T) (F G B : ℕ) (left : Budget (run f x) F B) (right : Budget (run g x) G B) :
    Budget (run (.fork f g) x) (F+G+1) B := by
  rcases left with ⟨lv,lw,lp⟩
  rcases right with ⟨rv,rw,rp⟩
  rw [fork_run]
  exact ⟨⟨lv,rv,trivial⟩,by dsimp [Bill.pass,Bill.one];omega,
    by dsimp [Bill.pass,Bill.one];omega⟩

theorem registerCell_bounds (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run registerCell ((r,z),j)).valid ∧
    (run registerCell ((r,z),j)).work≤200 ∧
    (run registerCell ((r,z),j)).peak≤heapSize r z.len+j+862 := by
  let B:=heapSize r z.len+j+862
  have bits : ∀n,n≤846→n≤B := by intro n hn;dsimp [B];omega
  have index:Budget (run (.atom .snd : Prog false Indexed w) ((r,z),j)) 1 B := by
    exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  have val:(run (.atom .snd : Prog false Indexed w) ((r,z),j)).val≤B := by
    change j≤B;dsimp [B];omega
  have data : ∀f∈([radix,count,permutationBase,widthsBase,markersBase,axisBase] : List (Prog false Input w)),
      Budget (run (.comp (.atom .fst : Prog false Indexed Input) f) ((r,z),j)) 21 B := by
    intro f member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h|h|h|h <;> subst f <;>
      simp [Budget,radix,count,permutationBase,widthsBase,markersBase,axisBase,nat,
        run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,B,
        heapSize,wordBound,A,U,W,P] <;> omega
  have zero:Budget (run (.atom (.lit 0) : Prog false Indexed w) ((r,z),j)) 21 B :=
    by change True ∧ 1≤_ ∧ 0≤_;exact ⟨trivial,by decide,Nat.zero_le _⟩
  have b6:=select_budget (.atom .snd : Prog false Indexed w) 846 _ _ ((r,z),j) 1 21 B index val
    (bits 846 le_rfl) (data axisBase (by simp)) zero
  have b5:=select_budget (.atom .snd : Prog false Indexed w) 845 _ _ ((r,z),j) 1 35 B index val
    (bits 845 (by decide)) (budget_mono (data markersBase (by simp)) (by decide)) b6
  have b4:=select_budget (.atom .snd : Prog false Indexed w) 844 _ _ ((r,z),j) 1 49 B index val
    (bits 844 (by decide)) (budget_mono (data widthsBase (by simp)) (by decide)) b5
  have b3:=select_budget (.atom .snd : Prog false Indexed w) 843 _ _ ((r,z),j) 1 63 B index val
    (bits 843 (by decide)) (budget_mono (data permutationBase (by simp)) (by decide)) b4
  have b2:=select_budget (.atom .snd : Prog false Indexed w) 841 _ _ ((r,z),j) 1 77 B index val
    (bits 841 (by decide)) (budget_mono (data count (by simp)) (by decide)) b3
  have b1:=select_budget (.atom .snd : Prog false Indexed w) 840 _ _ ((r,z),j) 1 91 B index val
    (bits 840 (by decide)) (budget_mono (data radix (by simp)) (by decide)) b2
  exact budget_mono b1 (by decide)

theorem endpoint_bounds (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    Budget (run endpoint ((r,z),j)) 59 (heapSize r z.len+j+862) := by
  let B:=heapSize r z.len+j+862
  have test:Budget (run rowOffset ((r,z),j)) 5 B := by
    simp [Budget,rowOffset,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,B]
    omega
  have val:(run rowOffset ((r,z),j)).val≤B := by
    change j%3≤B;dsimp [B];omega
  have branches : Budget (run (.comp row (.atom .fst)) ((r,z),j)) 15 B ∧
      Budget (run (.comp row (.comp (.atom .snd) (.atom .fst))) ((r,z),j)) 15 B := by
    simp [Budget,row,rowIndex,nat,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay,B]
    omega
  have zero:Budget (run (.atom (.lit 0) : Prog false Indexed w) ((r,z),j)) 15 B :=
    by change True ∧ 1≤_ ∧ 0≤_;exact ⟨trivial,by decide,Nat.zero_le _⟩
  have inner:=select_budget rowOffset 1 _ _ ((r,z),j) 5 15 B test val (by dsimp [B];omega)
    branches.2 zero
  exact select_budget rowOffset 0 _ _ ((r,z),j) 5 37 B test val (Nat.zero_le _)
    (budget_mono branches.1 (by decide)) inner

theorem heapCell_bounds (r : ℕ) (z : Tape Row.T) (j : ℕ) :
    (run heapCell ((r,z),j)).valid ∧
    (run heapCell ((r,z),j)).work≤200 ∧
    (run heapCell ((r,z),j)).peak≤heapSize r z.len+j+862 := by
  let B:=heapSize r z.len+j+862
  have test:Budget (run sourceTest ((r,z),j)) 13 B := by
    simp [Budget,sourceTest,permutationBase,count,nat,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay,B,heapSize,wordBound,A,U,W,P]
    split_ifs <;> omega
  have zero:Budget (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false Indexed (p w w)) ((r,z),j)) 61 B :=
    by change (True ∧ True ∧ True) ∧ 3≤61 ∧ 0≤B;exact ⟨⟨trivial,trivial,trivial⟩,by decide,Nat.zero_le _⟩
  have nonzero:Budget (run (.fork (.atom (.lit 1)) endpoint) ((r,z),j)) 61 B := by
    have one:Budget (run (.atom (.lit 1) : Prog false Indexed w) ((r,z),j)) 1 B := by
      change True ∧ 1≤1 ∧ 1≤B
      exact ⟨trivial,le_rfl,by dsimp [B];omega⟩
    exact fork_budget (.atom (.lit 1)) endpoint ((r,z),j) 1 59 B one (endpoint_bounds r z j)
  exact budget_mono (ifz_budget sourceTest _ _ ((r,z),j) 13 61 B test zero nonzero) (by decide)

private theorem tab_bounded {α : Type} (n W B : ℕ) (z : α) (f : ℕ→Bill α)
    (h : ∀j,j<n→(f j).valid ∧ (f j).work≤W ∧ (f j).peak≤B) :
    (Bill.tab n z f).valid ∧ (Bill.tab n z f).work≤2+(W+4)*n ∧
      (Bill.tab n z f).peak ≤ max n B := by
  refine ⟨(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr (fun j hj=>(h j hj).1),?_,?_⟩
  · rw [ModelEquivalenceInterpreter.tab_work]
    have sum:(∑j∈Finset.range n,(f j).work)≤n*W := by
      calc
        _≤∑_j∈Finset.range n,W := Finset.sum_le_sum (fun j hj=>(h j (Finset.mem_range.mp hj)).2.1)
        _=n*W := by simp
    rw [Nat.add_mul,Nat.mul_comm W n]
    omega
  · rw [ModelEquivalenceInterpreter.tab_peak]
    exact max_le (le_max_left _ _) ((Finset.sup_le (fun j hj=>(h j (Finset.mem_range.mp hj)).2.2)).trans (le_max_right _ _))

private theorem nat_blank : w.blank=0 := rfl
private theorem cell_blank : DFTModelCacheNatControl.Cell.blank=(0,0) := rfl

attribute [local irreducible] Code.run Bill.tab

theorem tab_program_budget {s t : Ty} (n : Prog false s w)
    (f : Prog false (p s w) t) (x : s.T) (W B : ℕ)
    (valid : (run n x).valid)
    (cells : ∀j,j<(run n x).val→Budget (run f (x,j)) W B) :
    Budget (run (.tab n f) x) ((run n x).work+3+(W+4)*(run n x).val)
      (max (run n x).peak (max (run n x).val B)) := by
  have tab:=tab_bounded (run n x).val W B t.blank (fun j=>run f (x,j)) cells
  rw [tab_run]
  refine ⟨⟨valid,tab.1⟩,?_,?_⟩
  · dsimp only [Bill.pay,Bill.pass]
    have work:=tab.2.1
    omega
  · dsimp only [Bill.pay,Bill.pass]
    rw [max_zero]
    exact max_le_max_left (run n x).peak tab.2.2

private theorem room_register (H j : ℕ) (hj : j<862) :
    H+j+862≤2*H+2000 := by omega

private theorem room_heap (H j : ℕ) (hj : j<H) :
    H+j+862≤2*H+2000 := by omega

/-- All setup projections, literal comparisons, endpoint reads, allocations and
third-word zero writes are charged. The bound is deliberately generous. -/
theorem initialize_bounds (r : ℕ) (z : Tape Row.T) :
    (run initializeProgram (r,z)).valid ∧
    (run initializeProgram (r,z)).work≤200000+204*heapSize r z.len ∧
    (run initializeProgram (r,z)).peak≤2*heapSize r z.len+2000 := by
  let H:=heapSize r z.len
  let B:=2*H+2000
  have regs:=tab_program_budget (.atom (.lit 862)) registerCell (r,z) 200 B (by rw [atom_run];trivial) (by
    intro j hj
    rw [atom_run] at hj
    change j<862 at hj
    have h:=registerCell_bounds r z j
    have room : heapSize r z.len+j+862≤B := room_register H j hj
    exact ⟨h.1,h.2.1,h.2.2.trans room⟩)
  have regBudget:Budget (run (.tab (.atom (.lit 862)) registerCell) (r,z)) 175852 B := by
    rw [atom_run] at regs
    simpa only [Atom.run,Bill.word,Bill.work,Bill.val,Bill.peak,
      show max 862 (max 862 B)=B from by dsimp [B];omega] using regs
  have heap:=tab_program_budget heapLength heapCell (r,z) 200 B
    (by rw [heapLength_run r z];trivial) (by
      intro j hj
      rw [heapLength_run r z] at hj
      dsimp only [Bill.val] at hj
      have h:=heapCell_bounds r z j
      have room : heapSize r z.len+j+862≤B := room_heap H j hj
      exact ⟨h.1,h.2.1,h.2.2.trans room⟩)
  have heapBudget:Budget (run (.tab heapLength heapCell) (r,z)) (26+204*H) B := by
    have eq:max (max 867 H) (max H B)=B := by
      dsimp [B,H,heapSize,wordBound];omega
    rw [heapLength_run r z] at heap
    change Budget (run (.tab heapLength heapCell) (r,z)) (26+204*H)
      (max (max 867 H) (max H B)) at heap
    rw [eq] at heap
    exact heap
  have zero:Budget (run (.atom (.lit 0) : Prog false Input w) (r,z)) 1 B := by
    rw [atom_run]
    exact ⟨trivial,le_rfl,Nat.zero_le _⟩
  have assembled:=fork_budget (.atom (.lit 0))
    (.fork (.tab (.atom (.lit 862)) registerCell) (.tab heapLength heapCell)) (r,z)
      1 (175852+(26+204*H)+1) B zero
      (fork_budget (.tab (.atom (.lit 862)) registerCell) (.tab heapLength heapCell)
        (r,z) 175852 (26+204*H) B regBudget heapBudget)
  exact budget_mono assembled (by omega)

end
end ExactFourierCircuits.DFTModelCacheMatchingNat
