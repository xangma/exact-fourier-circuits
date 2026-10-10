import DFTModelCacheHeightProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeight
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDAGDepth (nat)
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

theorem ifz_lt_value {a b:Ty} (u v:Prog false a w) (f g:Prog false a b) (x:a.T) :
 (run (.ifz (nat .lt u v) f g) x).val=
 if (run u x).val<(run v x).val then (run g x).val else (run f x).val := by
 rw [ifz_value]
 change (if (if (run u x).val<(run v x).val then 1 else 0)=0
  then (run f x).val else (run g x).val)=_
 by_cases h:(run u x).val<(run v x).val <;>simp [h]

attribute [local irreducible] row active selector step coefficient source field gate side

theorem gate_value (x:Input.T) (j:ℕ) : (run gate (x,j)).val=gateValue x j := by
 simp only [gate,start,order,directory,height,param,comp_value,fork_value,nat_value,
 atom_value,Atom.run,NOp.run,Bill.one,Bill.word,Ty.blank,gateValue]

theorem field_value (x:Input.T) (j k:ℕ) : (run (field k) (x,j)).val=fieldValue x j k := by
 rw [field]
 simp only [comp_value,fork_value,nat_value,topology,atom_value,Atom.run,NOp.run,Bill.one,Bill.word,Ty.blank,fieldValue]
 rw [gate_value]

theorem side_value (x:Input.T) (j:ℕ) : (run side (x,j)).val=j%2 := by rw [side];rfl

theorem source_value (x:Input.T) (j:ℕ) :
 (run source (x,j)).val=if j%2=0 then fieldValue x j 1 else fieldValue x j 2 := by
 rw [source,ifz_value,side_value]
 split_ifs <;>exact field_value x j _

theorem coefficient_value (x:Input.T) (j:ℕ) : (run coefficient (x,j)).val=
 if j%2=0 then (if fieldValue x j 0<2 then x.1.2.2.2.1 else
  if fieldValue x j 3<1 then (if fieldValue x j 4<2 then x.1.2.2.2.1 else x.1.2.2.2.1+2)
  else x.1.2.2.1+fieldValue x j 4) else x.1.2.2.2.1+fieldValue x j 0 := by
 rw [coefficient,ifz_value,side_value]
 by_cases hs:j%2=0
 · simp only [hs,ite_true]
   rw [ifz_lt_value,field_value]
   change (if fieldValue x j 0<2 then x.1.2.2.2.1 else _)=_
   by_cases ho:fieldValue x j 0<2
   · simp only [ho,ite_true]
   · simp only [ho,ite_false]
     rw [ifz_lt_value,field_value]
     change (if fieldValue x j 3<1 then _ else _)=_
     by_cases hk:fieldValue x j 3<1
     · simp only [hk,ite_true]
       rw [ifz_lt_value,field_value]
       rfl
     · simp only [hk,ite_false]
       simp only [nat_value,comp_value,coefficients,param,atom_value,Atom.run,NOp.run,Bill.one,Bill.word]
       rw [field_value]
 · simp only [hs,ite_false]
   simp only [nat_value,comp_value,constants,param,atom_value,Atom.run,NOp.run,Bill.one,Bill.word]
   rw [field_value]

theorem row_value (x:Input.T) (j:ℕ) : (run row (x,j)).val=rowValue x j := by
 rw [row]
 simp only [fork_value,nat_value,comp_value,
 dataBase,inputs,param,atom_value,Atom.run,NOp.run,Bill.one,Bill.word,rowValue]
 rw [gate_value,source_value,coefficient_value]

theorem accept_value (x:Input.T) (j:ℕ) : (run accept (x,j)).val=
 if (if j%2=0 then fieldValue x j 1 else fieldValue x j 2)<x.1.1 then
 (if x.1.2.2.2.2.2=0 then 0 else 1) else
 (if x.1.1<(if j%2=0 then fieldValue x j 1 else fieldValue x j 2) then 1 else 0) := by
 rw [accept,ifz_lt_value,source_value]
 have hi:(run (.comp (.atom .fst) inputs : Prog false Cell w) (x,j)).val=x.1.1 := rfl
 rw [hi]
 by_cases hn:(if j%2=0 then fieldValue x j 1 else fieldValue x j 2)<x.1.1
 · simp only [hn,ite_true]
   rw [ifz_value]
   rfl
 · simp only [hn,ite_false]
   simp only [nat_value,comp_value,inputs,param,atom_value,Atom.run,NOp.run,Bill.one,Bill.word]
   rw [source_value]
   with_unfolding_all rfl

theorem active_value (x:Input.T) (j:ℕ) :
 (run active (x,j)).val=(if accepts x j then 1 else 0) := by
 rw [active,ifz_value,side_value]
 by_cases hs:j%2=0
 · simp only [hs,ite_true]
   rw [accept_value]
   simp only [accepts,hs,ite_true,true_or,true_and]
   split_ifs <;>simp_all
 · simp only [hs,ite_false]
   rw [ifz_lt_value,field_value]
   change (if fieldValue x j 0<2 then _ else 0)=_
   by_cases ho:fieldValue x j 0<2
   · simp only [ho,ite_true]
     rw [accept_value]
     simp only [accepts,hs,ho,ite_false,false_or,true_and]
     split_ifs <;>simp_all
   · simp [ho,hs,accepts]

theorem slots_value (x:Input.T) : (run slots x).val=slotCount x := by
 simp only [slots,count,finish,start,directory,height,param,comp_value,fork_value,nat_value,atom_value,Atom.run,NOp.run,Bill.one,Bill.word,Ty.blank,slotCount]

def choice (xs:List Row.T) (q:ℕ) : State.T := (xs.length,xs[q]?.getD Row.blank)
def advance (x:Input.T) (q j:ℕ) (s:State.T) : State.T :=
 if accepts x j then (s.1+1,if s.1=q then rowValue x j else s.2) else s

theorem step_value (x:Input.T) (q j:ℕ) (s:State.T) :
 (run step ((x,q),(j,s))).val=advance x q j s := by
 rw [step,ifz_value]
 have ha:(run (.comp (.fork root index) active) ((x,q),(j,s))).val=(run active (x,j)).val := rfl
 have he:(run (.comp (.fork ordinal query) equal) ((x,q),(j,s))).val=(run DFTModelCacheBucket.equal (s.1,q)).val := rfl
 rw [ha,active_value]
 by_cases hp:accepts x j
 · simp only [hp,ite_true,one_ne_zero,ite_false,fork_value]
   rw [ifz_value,he,DFTModelCacheBucket.equal_value]
   have hn:(run (nat .add ordinal (.atom (.lit 1))) ((x,q),(j,s))).val=s.1+1 := rfl
   have ho:(run (.comp old (.atom .snd)) ((x,q),(j,s))).val=s.2 := rfl
   have hr:(run (.comp (.fork root index) row) ((x,q),(j,s))).val=(run row (x,j)).val := rfl
   rw [hn,ho,hr,row_value]
   by_cases hq:s.1=q <;>simp [advance,hp,hq]
 · simp only [hp,ite_false,ite_true]
   change s=advance x q j s
   simp [advance,hp]

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
 (run selector (x,q)).val=choice (rowsPrefix x (slotCount x)) q := by
 rw [selector,loop_value]
 simp only [comp_value,atom_value,Atom.run,Bill.one,slots_value,fork_value,Bill.word]
 exact steps_value x q (slotCount x)

theorem length_value (x:Input.T) : (run length x).val=(rowsPrefix x (slotCount x)).length := by
 rw [length,comp_value,comp_value]
 simp only [fork_value,atom_value,Atom.run,Bill.one,Bill.word]
 rw [selector_value];rfl

theorem rowCell_value (x:Input.T) (j:ℕ) :
 (run rowCell (x,j)).val=(rowsPrefix x (slotCount x))[j]?.getD Row.blank := by
 rw [rowCell,comp_value]
 simp only [atom_value,Atom.run,Bill.one]
 rw [selector_value];rfl

theorem program_value (x:Input.T) :
 (run program x).val=Tape.tab (rowsPrefix x (slotCount x)).length
  (fun j=>(rowsPrefix x (slotCount x))[j]?.getD Row.blank) := by
 change (Bill.tab (run length x).val Row.blank (fun j=>run rowCell (x,j))).val=_
 rw [ModelEquivalenceInterpreter.tab_value,length_value]
 exact congrArg (Tape.tab _) (funext (rowCell_value x))

end
end ExactFourierCircuits.DFTModelCacheHeight
