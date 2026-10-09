import UniformNatBlockMachine
import UniformAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveReturnStackMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- Parent fields needed after a complete W-array recursive child returns.
The stack pointer and its unit register are deliberately excluded. -/
def fields : List ℕ := [2599,2600,2850,3300,3301,3364,3389,
 4060,4061,4062,4063,4064,4065,4066,4067,4068,
 4090,4091,4100,4110,4120,4121,4122,4123,4124,4125,4126,4127,
 4130,4131,4132,4133,4134,4135]
lemma fields_length : fields.length=34 := rfl
lemma fields_safe : ∀r∈fields,r≠4152 ∧ r≠4153 := by decide

def saveFields : List ℕ→List Op
 | []=>[]
 | r::rs=>[.store 4152 r,.binary .add 4152 4152 4153]++saveFields rs
def loadFields : List ℕ→List Op
 | []=>[]
 | r::rs=>[.load r 4152,.binary .add 4152 4152 4153]++loadFields rs
lemma saveFields_length (rs:List ℕ) : (saveFields rs).length=2*rs.length := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp [saveFields,ih];omega
lemma loadFields_length (rs:List ℕ) : (loadFields rs).length=2*rs.length := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp [loadFields,ih];omega
lemma apply_append (a b:List Op) (s:State) : applyBlock (a++b) s=applyBlock b (applyBlock a s) := by
 induction a generalizing s with
 | nil=>rfl
 | cons a as ih=>exact ih _

def Bank (rs:List ℕ) (A:ℕ) (values:ℕ→ℕ) (s:State) : Prop :=
 ∀j,(hj:j<rs.length)→s.natHeap (A+j)=some (values (rs[j]'hj))
lemma Bank.tail {r A:ℕ} {rs:List ℕ} {v:ℕ→ℕ} {s:State} (h:Bank (r::rs) A v s) : Bank rs (A+1) v s := by
 intro j hj
 have ht:=h (j+1) (by simp;omega)
 rw [List.getElem_cons_succ r rs j _] at ht
 simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

lemma save_registers (rs:List ℕ) (s:State) (i:ℕ) (hi:i≠4152) :
 (applyBlock (saveFields rs) s).natReg i=s.natReg i := by
 induction rs generalizing s with
 | nil=>rfl
 | cons r rs ih=>
   rw [saveFields,apply_append,ih]
   simp [applyBlock,Op.apply,evalNat,writeNat,next,hi]
lemma load_registers (rs:List ℕ) (s:State) (i:ℕ) (hi:i≠4152) (none:i∉rs) :
 (applyBlock (loadFields rs) s).natReg i=s.natReg i := by
 induction rs generalizing s with
 | nil=>rfl
 | cons r rs ih=>
   rw [loadFields,apply_append,ih _ (by simp_all)]
   simp (disch:=simp_all) [applyBlock,Op.apply,evalNat,writeNat,next,hi]
lemma load_heap (rs:List ℕ) (s:State) : (applyBlock (loadFields rs) s).natHeap=s.natHeap := by
 induction rs generalizing s with
 | nil=>rfl
 | cons r rs ih=>rw [loadFields,apply_append,ih];rfl
lemma save_scalar (rs:List ℕ) (s:State) :
 (applyBlock (saveFields rs) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (saveFields rs) s).scalarReg=s.scalarReg ∧
 (applyBlock (saveFields rs) s).outputs=s.outputs ∧
 (applyBlock (saveFields rs) s).rootOrders=s.rootOrders := by
 induction rs generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl⟩
 | cons r rs ih=>rw [saveFields,apply_append];exact ih _
lemma load_scalar (rs:List ℕ) (s:State) :
 (applyBlock (loadFields rs) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (loadFields rs) s).scalarReg=s.scalarReg ∧
 (applyBlock (loadFields rs) s).outputs=s.outputs ∧
 (applyBlock (loadFields rs) s).rootOrders=s.rootOrders := by
 induction rs generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl⟩
 | cons r rs ih=>rw [loadFields,apply_append];exact ih _

lemma save_spec (rs:List ℕ) (A:ℕ) (v:ℕ→ℕ) (s:State)
 (safe:∀r∈rs,r≠4152) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (values:∀r∈rs,s.natReg r=v r) :
 Bank rs A v (applyBlock (saveFields rs) s) ∧
 (applyBlock (saveFields rs) s).natReg 4152=A+rs.length ∧
 (∀z,z<A∨A+rs.length≤z→(applyBlock (saveFields rs) s).natHeap z=s.natHeap z) := by
 induction rs generalizing A s with
 | nil=>exact ⟨fun j hj=>by simp at hj,by simpa [saveFields,applyBlock] using ptr,fun _ _=>rfl⟩
 | cons r rs ih=>
   let t:=applyBlock [.store 4152 r,.binary .add 4152 4152 4153] s
   have tp:t.natReg 4152=A+1:=by simp [t,applyBlock,Op.apply,evalNat,writeNat,next,ptr,one]
   have oneAfter:t.natReg 4153=1:=by simpa [t,applyBlock,Op.apply,evalNat,writeNat,next] using one
   have tv:∀z∈rs,t.natReg z=v z:=by
    intro z hz;simpa [t,applyBlock,Op.apply,evalNat,writeNat,next,safe z (by simp [hz])] using values z (by simp [hz])
   obtain ⟨bank,pointer,outside⟩:=ih (A+1) t (by intro z hz;exact safe z (by simp [hz])) tp oneAfter tv
   rw [saveFields,apply_append]
   refine ⟨?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pointer,?_⟩
   · intro j hj
     cases j with
     | zero=>
       have h:=outside A (by left;omega)
       rw [List.getElem_cons_zero r rs _,Nat.add_zero]
       rw [h]
       simp [t,applyBlock,Op.apply,writeNat,next,ptr,values r (by simp)]
     | succ j=>simpa only [List.getElem_cons_succ r rs j _,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bank j (by simp at hj;omega)
   · intro z hz
     rw [outside z (by simp only [List.length_cons] at hz;rcases hz with hz|hz <;> omega)]
     have neq:z≠A:=by simp only [List.length_cons] at hz;omega
     simp [t,applyBlock,Op.apply,writeNat,next,ptr,neq]

lemma save_safe (rs:List ℕ) (A B:ℕ) (s:State)
 (safe:∀r∈rs,r≠4152) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (values:∀r∈rs,s.natReg r≤B) (extent:A+rs.length≤B) :
 readable (saveFields rs) s ∧ peak (saveFields rs) s≤B := by
 induction rs generalizing A s with
 | nil=>simp [saveFields,readable,peak]
 | cons r rs ih=>
   let t:=applyBlock [.store 4152 r,.binary .add 4152 4152 4153] s
   have tp:t.natReg 4152=A+1:=by simp [t,applyBlock,Op.apply,evalNat,writeNat,next,ptr,one]
   have oneAfter:t.natReg 4153=1:=by simpa [t,applyBlock,Op.apply,evalNat,writeNat,next] using one
   have tv:∀z∈rs,t.natReg z≤B:=by
    intro z hz;simpa [t,applyBlock,Op.apply,evalNat,writeNat,next,safe z (by simp [hz])] using values z (by simp [hz])
   have tail:=ih (A+1) t (by intro z hz;exact safe z (by simp [hz])) tp oneAfter tv (by simp only [List.length_cons] at extent;omega)
   have rv:=values r (by simp)
   have ap:A≤B:=by simp only [List.length_cons] at extent;omega
   have an:A+1≤B:=by simp only [List.length_cons] at extent;omega
   simpa [saveFields,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
    ptr,one,rv,ap,an,max_le_iff,t,applyBlock] using tail

lemma load_spec (rs:List ℕ) (A:ℕ) (v:ℕ→ℕ) (s:State)
 (safe:∀r∈rs,r≠4152 ∧ r≠4153) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (bank:Bank rs A v s) :
 (∀z∈rs,(applyBlock (loadFields rs) s).natReg z=v z) ∧
 (applyBlock (loadFields rs) s).natReg 4152=A+rs.length := by
 induction rs generalizing A s with
 | nil=>exact ⟨fun z hz=>by simp at hz,by simpa [loadFields,applyBlock] using ptr⟩
 | cons r rs ih=>
   let t:=applyBlock [.load r 4152,.binary .add 4152 4152 4153] s
   have value:s.natHeap A=some (v r):=by
    have ht:=bank 0 (by simp)
    rw [List.getElem_cons_zero r rs _] at ht
    simpa only [Nat.add_zero] using ht
   have tp:t.natReg 4152=A+1:=by simp [t,applyBlock,Op.apply,evalNat,writeNat,next,ptr,one,value,(safe r (by simp)).1,(safe r (by simp)).2,Ne.symm (safe r (by simp)).1,Ne.symm (safe r (by simp)).2]
   have oneAfter:t.natReg 4153=1:=by simpa [t,applyBlock,Op.apply,evalNat,writeNat,next,(safe r (by simp)).2,Ne.symm (safe r (by simp)).2] using one
   have tb:Bank rs (A+1) v t:=bank.tail
   obtain ⟨rest,last⟩:=ih (A+1) t (by intro z hz;exact safe z (by simp [hz])) tp oneAfter tb
   rw [loadFields,apply_append]
   refine ⟨?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using last⟩
   intro z hz
   rcases List.mem_cons.1 hz with eq|hz
   · rw [eq]
     by_cases again:r∈rs
     · exact rest r again
     · rw [load_registers rs t r (safe r (by simp)).1 again]
       simp [t,applyBlock,Op.apply,evalNat,writeNat,next,ptr,value,(safe r (by simp)).1,(safe r (by simp)).2,Ne.symm (safe r (by simp)).1,Ne.symm (safe r (by simp)).2]
   · exact rest z hz

lemma load_safe (rs:List ℕ) (A B:ℕ) (v:ℕ→ℕ) (s:State)
 (safe:∀r∈rs,r≠4152 ∧ r≠4153) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (bank:Bank rs A v s) (values:∀r∈rs,v r≤B) (extent:A+rs.length≤B) :
 readable (loadFields rs) s ∧ peak (loadFields rs) s≤B := by
 induction rs generalizing A s with
 | nil=>simp [loadFields,readable,peak]
 | cons r rs ih=>
   let t:=applyBlock [.load r 4152,.binary .add 4152 4152 4153] s
   have value:s.natHeap A=some (v r):=by
    have ht:=bank 0 (by simp)
    rw [List.getElem_cons_zero r rs _] at ht
    simpa only [Nat.add_zero] using ht
   have tp:t.natReg 4152=A+1:=by simp [t,applyBlock,Op.apply,evalNat,writeNat,next,ptr,one,value,(safe r (by simp)).1,(safe r (by simp)).2,Ne.symm (safe r (by simp)).1,Ne.symm (safe r (by simp)).2]
   have oneAfter:t.natReg 4153=1:=by simpa [t,applyBlock,Op.apply,evalNat,writeNat,next,(safe r (by simp)).2,Ne.symm (safe r (by simp)).2] using one
   have tb:Bank rs (A+1) v t:=bank.tail
   have tail:=ih (A+1) t (by intro z hz;exact safe z (by simp [hz])) tp oneAfter tb (by intro z hz;exact values z (by simp [hz])) (by simp only [List.length_cons] at extent;omega)
   have rv:=values r (by simp)
   have ap:A≤B:=by simp only [List.length_cons] at extent;omega
   have an:A+1≤B:=by simp only [List.length_cons] at extent;omega
   simpa [loadFields,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
    ptr,one,value,(safe r (by simp)).1,(safe r (by simp)).2,Ne.symm (safe r (by simp)).1,Ne.symm (safe r (by simp)).2,max_le_iff,rv,ap,an,t,applyBlock] using tail

/-- A fixed save/restore pair. Actual callers compose these nonhalting segments
with a child entry and one fixed return site; no indirect jump primitive. -/
def saveProgram : Program := (saveFields fields).map Op.code++[.halt]
def loadProgram : Program := (loadFields fields).map Op.code++[.halt]
lemma saveProgram_length : saveProgram.length=69 := by simp [saveProgram,saveFields_length,fields_length]
lemma loadProgram_length : loadProgram.length=69 := by simp [loadProgram,loadFields_length,fields_length]
lemma save_code : BlockAt (saveFields fields) saveProgram 0 := by
 intro i hi;simp only [Nat.zero_add];unfold saveProgram;rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map];simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma load_code : BlockAt (loadFields fields) loadProgram 0 := by
 intro i hi;simp only [Nat.zero_add];unfold loadProgram;rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map];simp only [List.getElem?_eq_getElem hi,Option.map_some]

/-- Actual field stores with exact constant charged time. -/
theorem save_execution (n B A:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=0) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (bound:WordBound B s) (code:69≤B) (extent:A+34≤B) :
 ∃u,BoundedRuns saveProgram n x B s 68 u ∧ u.pc=68 ∧ Bank fields A s.natReg u ∧
 u.natReg 4152=A+34 ∧
 (∀z,z<A∨A+34≤z→u.natHeap z=s.natHeap z) ∧
 (∀i,i≠4152→u.natReg i=s.natReg i) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have sf:=save_safe fields A B s (fun r h=>(fields_safe r h).1) ptr one (fun r _=>bound.2.1 r) (by simpa [fields_length] using extent)
 have run:=block_runs (saveFields fields) saveProgram 0 n B x s save_code pc bound
  (by rw [saveFields_length,fields_length];omega) sf.1 sf.2
 have post:=save_spec fields A s.natReg s (fun r h=>(fields_safe r h).1) ptr one (fun _ _=>rfl)
 have scalar:=save_scalar fields s
 refine ⟨_,by simpa [saveFields_length,fields_length] using run,?_,post.1,?_,?_,save_registers fields s,scalar.1,scalar.2.1,scalar.2.2.1,scalar.2.2.2⟩
 · have h:∀rs:List ℕ,∀t:State,(applyBlock (saveFields rs) t).pc=t.pc+2*rs.length:=by
    intro rs;induction rs with
    | nil=>intro t;rfl
    | cons r rs ih=>intro t;rw [saveFields,apply_append,ih];simp [applyBlock,Op.apply,writeNat,next];omega
   simpa [pc,fields_length] using h fields s
 · simpa [fields_length] using post.2.1
 · simpa [fields_length] using post.2.2

/-- Actual field loads restore each saved parent control, without touching
arbitrary child-produced Scalars or the heap return frames. -/
theorem load_execution (n B A:ℕ) (v:ℕ→ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=0) (ptr:s.natReg 4152=A) (one:s.natReg 4153=1)
 (bank:Bank fields A v s) (values:∀r∈fields,v r≤B)
 (bound:WordBound B s) (code:69≤B) (extent:A+34≤B) :
 ∃u,BoundedRuns loadProgram n x B s 68 u ∧ u.pc=68 ∧
 (∀r∈fields,u.natReg r=v r) ∧ u.natReg 4152=A+34 ∧ u.natHeap=s.natHeap ∧
 (∀i,i≠4152→i∉fields→u.natReg i=s.natReg i) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have sf:=load_safe fields A B v s fields_safe ptr one bank values (by simpa [fields_length] using extent)
 have run:=block_runs (loadFields fields) loadProgram 0 n B x s load_code pc bound
  (by rw [loadFields_length,fields_length];omega) sf.1 sf.2
 have post:=load_spec fields A v s fields_safe ptr one bank
 have scalar:=load_scalar fields s
 refine ⟨_,by simpa [loadFields_length,fields_length] using run,?_,post.1,?_,load_heap fields s,load_registers fields s,scalar.1,scalar.2.1,scalar.2.2.1,scalar.2.2.2⟩
 · have h:∀rs:List ℕ,∀t:State,(applyBlock (loadFields rs) t).pc=t.pc+2*rs.length:=by
    intro rs;induction rs with
    | nil=>intro t;rfl
    | cons r rs ih=>intro t;rw [loadFields,apply_append,ih];simp [applyBlock,Op.apply,writeNat,next];omega
   simpa [pc,fields_length] using h fields s
 · simpa [fields_length] using post.2

end
end ExactFourierCircuits.UniformRecursiveReturnStackMachine
