import ModelEquivalenceInterpreter
import UniformLocalCacheTreeCoverage

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

def ofList {α : Type} (xs : List α) : Tape α := ⟨xs.length,fun j=>xs[j.val]⟩

theorem tape_ext {α : Type} (x y : Tape α) (z : α) (len:x.len=y.len)
    (look:∀j,j<x.len→x.look j z=y.look j z) : x=y := by
  cases x with
  | mk n f =>
    cases y with
    | mk m g =>
      change n=m at len
      subst m
      congr 1
      funext j
      simpa [Tape.look,j.isLt] using look j.val j.isLt

theorem ofList_look {α : Type} (xs : List α) (z : α) (j : ℕ) :
    (ofList xs).look j z=xs[j]?.getD z := by
  by_cases hj:j<xs.length
  · simp [ofList,Tape.look,hj]
  · simp [ofList,Tape.look,hj]

def integer {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

def appendLength (t : Ty) : Prog false (p (Ty.a t) (Ty.a t)) w :=
  integer .add (.comp (.atom .fst) (.atom .len)) (.comp (.atom .snd) (.atom .len))
def appendFirstLength (t : Ty) : Prog false (p (p (Ty.a t) (Ty.a t)) w) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .len))
def appendFirst (t : Ty) : Prog false (p (p (Ty.a t) (Ty.a t)) w) t :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) (.atom .look)
def appendSecond (t : Ty) : Prog false (p (p (Ty.a t) (Ty.a t)) w) t :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd))
    (integer .sub (.atom .snd) (appendFirstLength t))) (.atom .look)
def appendCell (t : Ty) : Prog false (p (p (Ty.a t) (Ty.a t)) w) t :=
  .ifz (integer .lt (.atom .snd) (appendFirstLength t)) (appendSecond t) (appendFirst t)
/-- Fresh allocation and every read/copy are charged by the actual tab. -/
def append (t : Ty) : Prog false (p (Ty.a t) (Ty.a t)) (Ty.a t) :=
  .tab (appendLength t) (appendCell t)

def appendValue (t : Ty) (x y : Tape t.T) : Tape t.T :=
  Tape.tab (x.len+y.len) (fun j=>if j<x.len then x.look j t.blank else y.look (j-x.len) t.blank)

theorem appendLength_run (t : Ty) (x y : Tape t.T) :
    run (appendLength t) (x,y)=⟨x.len+y.len,9,x.len+y.len,True⟩ := by
  simp [appendLength,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem appendCell_run (t : Ty) (x y : Tape t.T) (j : ℕ) :
    run (appendCell t) ((x,y),j)=
      ⟨if j<x.len then x.look j t.blank else y.look (j-x.len) t.blank,
        if j<x.len then 17 else 25,
        if j<x.len then x.len else max x.len (j-x.len),True⟩ := by
  by_cases hj:j<x.len <;>
    simp [appendCell,integer,appendFirstLength,appendFirst,appendSecond,
      run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,hj]
  omega

attribute [local irreducible] appendCell

theorem append_run (t : Ty) (x y : Tape t.T) :
    run (append t) (x,y)=
      (Bill.tab (x.len+y.len) t.blank (fun j=>run (appendCell t) ((x,y),j))).pay 10 (x.len+y.len) := by
  change ((run (appendLength t) (x,y)).pass (fun n=>
    Bill.tab n t.blank (fun j=>run (appendCell t) ((x,y),j)))).pay 1 0=_
  rw [appendLength_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem append_value (t : Ty) (x y : Tape t.T) :
    (run (append t) (x,y)).val=appendValue t x y := by
  rw [append_run]
  change (Bill.tab (x.len+y.len) t.blank (fun j=>run (appendCell t) ((x,y),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab (x.len+y.len))
  funext j
  exact congrArg Bill.val (appendCell_run t x y j)

theorem append_valid (t : Ty) (x y : Tape t.T) : (run (append t) (x,y)).valid := by
  rw [append_run]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  rw [appendCell_run]
  trivial

theorem append_work (t : Ty) (x y : Tape t.T) :
    (run (append t) (x,y)).work≤29*(x.len+y.len)+12 := by
  rw [append_run]
  change (Bill.tab (x.len+y.len) t.blank (fun j=>run (appendCell t) ((x,y),j))).work+10≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have bound:(∑j∈Finset.range (x.len+y.len),(run (appendCell t) ((x,y),j)).work)≤25*(x.len+y.len) := by
    calc
      _≤∑_j∈Finset.range (x.len+y.len),25 := by
        apply Finset.sum_le_sum
        intro j _
        rw [appendCell_run]
        dsimp only [Bill.work]
        split_ifs <;> omega
      _=_ := by simp [Nat.mul_comm]
  omega

theorem append_peak (t : Ty) (x y : Tape t.T) :
    (run (append t) (x,y)).peak≤x.len+y.len := by
  rw [append_run]
  change max (Bill.tab (x.len+y.len) t.blank (fun j=>run (appendCell t) ((x,y),j))).peak (x.len+y.len)≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le le_rfl ?_) le_rfl
  apply Finset.sup_le
  intro j hj
  rw [appendCell_run]
  have hj:=Finset.mem_range.mp hj
  dsimp only [Bill.peak]
  split_ifs <;> omega

theorem append_lists (t : Ty) (xs ys : List t.T) :
    appendValue t (ofList xs) (ofList ys)=ofList (xs++ys) := by
  apply tape_ext _ _ t.blank (by simp [appendValue,Tape.tab,ofList])
  intro j hj
  change j<xs.length+ys.length at hj
  rw [Tape.look_of_lt _ _ hj]
  change (if j<xs.length then (ofList xs).look j t.blank else
    (ofList ys).look (j-xs.length) t.blank)=(ofList (xs++ys)).look j t.blank
  rw [ofList_look,ofList_look,ofList_look]
  by_cases hx:j<xs.length
  · simp [hx,List.getElem?_append_left hx]
  · simp [hx,List.getElem?_append_right (by omega:xs.length≤j)]

def singleton (t : Ty) : Prog false t (Ty.a t) := .tab (.atom (.lit 1)) (.atom .fst)

theorem singleton_run (t : Ty) (x : t.T) :
    run (singleton t) x=⟨Tape.tab 1 (fun _=>x),9,1,True⟩ := by
  change ((Bill.word 1).pass (fun n=>Bill.tab n t.blank (fun _=>Bill.one x))).pay 1 0=_
  have hv:=ModelEquivalenceInterpreter.tab_value 1 t.blank (fun _=>Bill.one x)
  have hw:=ModelEquivalenceInterpreter.tab_work 1 t.blank (fun _=>Bill.one x)
  have hp:=ModelEquivalenceInterpreter.tab_peak 1 t.blank (fun _=>Bill.one x)
  have hg: (Bill.tab 1 t.blank (fun _=>Bill.one x)).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (by simp [Bill.one])
  cases hb:Bill.tab 1 t.blank (fun _=>Bill.one x) with
  | mk v w p g =>
    rw [hb] at hv hw hp hg
    change v=Tape.tab 1 (fun _=>x) at hv
    change w=2+4*1+(∑j∈Finset.range 1,(Bill.one x).work) at hw
    change p=max 1 ((Finset.range 1).sup (fun _=>(Bill.one x).peak)) at hp
    change g at hg
    simp [Bill.one] at hv hw hp
    simp only [Bill.word,Bill.pass,Bill.pay]
    rw [hb]
    simp [hv,hw,hp,hg]

end
end ExactFourierCircuits.DFTModelCacheTraversal
