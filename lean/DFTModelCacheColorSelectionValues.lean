import DFTModelCacheColorSelectionProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorSelection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row nat)
noncomputable section
theorem comp_value {a b c:Ty} (f:Prog false a b) (g:Prog false b c) (x:a.T) :
 (run (.comp f g) x).val=(run g (run f x).val).val := rfl

theorem fork_value {a b c:Ty} (f:Prog false a b) (g:Prog false a c) (x:a.T) :
 (run (.fork f g) x).val=((run f x).val,(run g x).val) := rfl

theorem ifz_value {a b:Ty} (q:Prog false a w) (f g:Prog false a b) (x:a.T) :
 (run (.ifz q f g) x).val=if (run q x).val=0 then (run f x).val else (run g x).val := by
 simp only [run,Code.run,Bill.pass,Bill.pay]
 split <;>rfl

theorem atom_value {a b:Ty} (o:Atom false a b) (x:a.T) :
 (run (.atom o) x).val=(o.run x).val := rfl

theorem nat_value {a:Ty} (o:NOp) (f g:Prog false a w) (x:a.T) :
 (run (nat o f g) x).val=(o.run ((run f x).val,(run g x).val)).val := rfl

def choice (xs:List Row.T) (q:ℕ) : State.T := (xs.length,xs[q]?.getD Row.blank)
def advance (x:Input.T) (q j:ℕ) (s:State.T) : State.T :=
 if accepts x j then (s.1+1,if s.1=q then rowValue x j else s.2) else s

theorem equal_value {a : Ty} (u v : Prog false a w) (x : a.T) :
 (run (equal u v) x).val=0 ↔ (run u x).val=(run v x).val := by
 change (run u x).val-(run v x).val+((run v x).val-(run u x).val)=0 ↔ _
 exact ModelEquivalenceInterpreter.distance_eq_zero_iff _ _

attribute [local irreducible] row selector step

theorem row_value (x : Input.T) (j : ℕ) : (run row (x,j)).val=rowValue x j := by rw [row];rfl
theorem count_value (x : Input.T) : (run count x).val=x.2.1.len := rfl

theorem step_value (x : Input.T) (q j : ℕ) (s : State.T) :
 (run step ((x,q),(j,s))).val=advance x q j s := by
 rw [step,ifz_value]
 have condition:(run (equal (.comp (.fork root index) color) (.comp root (.atom .fst)))
   ((x,q),(j,s))).val=0 ↔ accepts x j := (equal_value _ _ _).trans Iff.rfl
 by_cases hp:accepts x j
 · rw [ite_eq_left (condition.mpr hp)]
   rw [fork_value,ifz_value]
   have compare:(run (equal ordinal query) ((x,q),(j,s))).val=0 ↔ s.1=q :=
    (equal_value _ _ _).trans Iff.rfl
   have hn:(run (nat .add ordinal (.atom (.lit 1))) ((x,q),(j,s))).val=s.1+1 := rfl
   have hr:(run (.comp (.fork root index) row) ((x,q),(j,s))).val=rowValue x j := by
    change (run row (x,j)).val=_
    exact row_value x j
   have ho:(run (.comp old (.atom .snd)) ((x,q),(j,s))).val=s.2 := rfl
   by_cases hq:s.1=q
   · rw [ite_eq_left (compare.mpr hq),hn,hr]
     simp only [advance,hp,hq,ite_true]
   · rw [ite_eq_right (fun h=>hq (compare.mp h)),hn,ho]
     simp only [advance,hp,hq,ite_true,ite_false]
 · rw [ite_eq_right (fun h=>hp (condition.mp h))]
   change s=advance x q j s
   simp only [advance,hp,ite_false]

theorem choice_append (xs:List Row.T) (q:ℕ) (a:Row.T) :
 choice (xs++[a]) q=(xs.length+1,if xs.length=q then a else (choice xs q).2) := by
 unfold choice
 simp only [List.length_append,List.length_singleton,Prod.mk.injEq]
 refine ⟨trivial,?_⟩
 by_cases h:q<xs.length
 · have ne:xs.length≠q:=by omega
   simp [List.getElem?_append,h,ne]
 · by_cases eq:xs.length=q
   · subst q;simp
   · simp [List.getElem?_append,h,eq,show q-xs.length≠0 by omega]

theorem rowsPrefix_succ (x:Input.T) (j:ℕ) :
 rowsPrefix x (j+1)=rowsPrefix x j++(if accepts x j then [rowValue x j] else []) := by
 unfold rowsPrefix
 rw [List.range_succ,List.filterMap_append]
 split_ifs <;> simp_all

def steps (x:Input.T) (q j:ℕ) : Bill State.T :=
 Bill.steps (choice [] q) (fun i s=>run step ((x,q),(i,s))) j

theorem steps_value (x:Input.T) (q j:ℕ) :
 (steps x q j).val=choice (rowsPrefix x j) q := by
 induction j with
 | zero=>rfl
 | succ j ih=>
   change (run step ((x,q),(j,(steps x q j).val))).val=_
   rw [step_value,ih,rowsPrefix_succ]
   by_cases h:accepts x j
   · simp only [advance,h,ite_true]
     exact (choice_append (rowsPrefix x j) q (rowValue x j)).symm
   · simp [advance,h]


theorem loop_value {a b:Ty} (n:Prog false a w) (init:Prog false a b)
 (body:Prog false (p a (p w b)) b) (x:a.T) :
 (run (.loop n init body) x).val=
 (Bill.steps (run init x).val (fun i s=>run body (x,(i,s))) (run n x).val).val := rfl

theorem selector_value (x:Input.T) (q:ℕ) :
 (run selector (x,q)).val=choice (rowsPrefix x (x.2.1.len)) q := by
 rw [selector,loop_value]
 simp only [comp_value,atom_value,Atom.run,Bill.one,count_value,fork_value,Bill.word]
 exact steps_value x q (x.2.1.len)

theorem length_value (x:Input.T) : (run length x).val=(rowsPrefix x (x.2.1.len)).length := by
 rw [length,comp_value,comp_value]
 simp only [fork_value,atom_value,Atom.run,Bill.one,Bill.word]
 rw [selector_value];rfl

theorem rowCell_value (x:Input.T) (j:ℕ) :
 (run rowCell (x,j)).val=(rowsPrefix x (x.2.1.len))[j]?.getD Row.blank := by
 rw [rowCell,comp_value]
 simp only [atom_value,Atom.run,Bill.one]
 rw [selector_value];rfl

theorem program_value (x:Input.T) :
 (run program x).val=Tape.tab (rowsPrefix x (x.2.1.len)).length
  (fun j=>(rowsPrefix x (x.2.1.len))[j]?.getD Row.blank) := by
 change (Bill.tab (run length x).val Row.blank (fun j=>run rowCell (x,j))).val=_
 rw [ModelEquivalenceInterpreter.tab_value,length_value]
 exact congrArg (Tape.tab _) (funext (rowCell_value x))

end
end ExactFourierCircuits.DFTModelCacheColorSelection
