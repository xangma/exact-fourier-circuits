import UniformInverseShearTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformScalarReplayMachine
open UniformMachine
open UniformInPlaceMachine (Row prepared product result prepared_mul result_add)
noncomputable section

/-- Nat1160=count,1161=actual three-word table base. Every row read and scalar
update is charged; the coefficient must be a retained prepared scalar. -/
def program : Program :=
  [.natLiteral 1162 1,.natLiteral 1163 3,.natLiteral 1164 0,
   .branchLT 1164 1160 4 19,
   .natBinary .mul 1165 1164 1163,.natBinary .add 1165 1161 1165,
   .loadNat 1166 1165,.natBinary .add 1165 1165 1162,.loadNat 1167 1165,
   .natBinary .add 1165 1165 1162,.loadNat 1168 1165,
   .loadScalar 90 1166,.loadScalar 91 1167,.loadScalar 92 1168,
   .fieldBinary .mul 93 92 91,.fieldBinary .add 90 90 93,
   .storeScalar 1166 90,.natBinary .add 1164 1164 1162,.jump 3,.halt]

theorem program_length : program.length=20 := rfl
abbrev Rows := UniformInverseShearTableMachine.Rows

structure Header (M T : ℕ) (s : State) : Prop where
  count : s.natReg 1160=M
  table : s.natReg 1161=T

structure Ready (row : Row) (s : State) (a b c : Scalar) : Prop where
  pc : s.pc=3
  index : s.natReg 1164<s.natReg 1160
  one : s.natReg 1162=1
  three : s.natReg 1163=3
  dst : s.natHeap (s.natReg 1161+3*s.natReg 1164)=some row.dst
  src : s.natHeap (s.natReg 1161+3*s.natReg 1164+1)=some row.src
  coefficient : s.natHeap (s.natReg 1161+3*s.natReg 1164+2)=some row.coefficient
  dstValue : s.scalarHeap row.dst=some a
  srcValue : s.scalarHeap row.src=some b
  coefficientValue : s.scalarHeap row.coefficient=some c
  coefficientPrepared : c.dependent=false

def initialized (s : State) := writeNat (writeNat (writeNat s 1162 1) 1163 3) 1164 0
def entered (s : State) : State := {s with pc:=4}
def offset (s : State) := writeNat (entered s) 1165 (3*s.natReg 1164)
def pointer (s : State) := writeNat (offset s) 1165 (s.natReg 1161+3*s.natReg 1164)
def dstState (row : Row) (s : State) := writeNat (pointer s) 1166 row.dst
def srcPointer (row : Row) (s : State) := writeNat (dstState row s) 1165 (s.natReg 1161+3*s.natReg 1164+1)
def srcState (row : Row) (s : State) := writeNat (srcPointer row s) 1167 row.src
def coefficientPointer (row : Row) (s : State) := writeNat (srcState row s) 1165 (s.natReg 1161+3*s.natReg 1164+2)
def coefficientState (row : Row) (s : State) := writeNat (coefficientPointer row s) 1168 row.coefficient
def dstValue (row : Row) (s : State) (a : Scalar) := writeScalar (coefficientState row s) 90 a
def srcValue (row : Row) (s : State) (a b : Scalar) := writeScalar (dstValue row s a) 91 b
def coefficientValue (row : Row) (s : State) (a b c : Scalar) := writeScalar (srcValue row s a b) 92 c
def multiplied (row : Row) (s : State) (a b c : Scalar) := writeScalar (coefficientValue row s a b c) 93 (product c b)
def added (row : Row) (s : State) (a b c : Scalar) := writeScalar (multiplied row s a b c) 90 (result a b c)
def stored (row : Row) (s : State) (a b c : Scalar) : State :=
  {next (added row s a b c) with scalarHeap:=Function.update s.scalarHeap row.dst (some (result a b c))}
def advanced (row : Row) (s : State) (a b c : Scalar) := writeNat (stored row s a b c) 1164 (s.natReg 1164+1)
def rowEnd (row : Row) (s : State) (a b c : Scalar) : State := {advanced row s a b c with pc:=3}

theorem row_frame (row : Row) (s : State) (a b c : Scalar) :
    (rowEnd row s a b c).natHeap=s.natHeap ∧
    (rowEnd row s a b c).scalarHeap=Function.update s.scalarHeap row.dst (some (result a b c)) ∧
    (rowEnd row s a b c).outputs=s.outputs ∧ (rowEnd row s a b c).rootOrders=s.rootOrders ∧
    (∀q,(q<1162 ∨ 1169≤q)→(rowEnd row s a b c).natReg q=s.natReg q) ∧
    (∀q,(q<90 ∨ 94≤q)→(rowEnd row s a b c).scalarReg q=s.scalarReg q) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals intro q hq
  all_goals simp (disch:=omega) [rowEnd,advanced,stored,added,multiplied,coefficientValue,
    srcValue,dstValue,coefficientState,coefficientPointer,srcState,srcPointer,dstState,pointer,
    offset,entered,writeNat,writeScalar,next]

theorem startup_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hB:20≤B) (hp:s.pc=0) (hs:WordBound B s) :
    BoundedRuns program n x B s 3 (initialized s) := by
  have h1:=writeNat_bound B s 1162 1 hs (by omega) (by omega)
  have h2:=writeNat_bound B (writeNat s 1162 1) 1163 3 h1 (by simp [writeNat,next];omega) (by omega)
  have h3:=writeNat_bound B (writeNat (writeNat s 1162 1) 1163 3) 1164 0 h2
    (by simp [writeNat,next];omega) (by omega)
  refine .next hs ?_ (.next h1 ?_ (.next h2 ?_ (.refl h3)))
  all_goals simp [step,program,initialized,writeNat,next,hp]

theorem row_bounded (n B M T : ℕ) (x : Fin n→ℂ) (row : Row) (s : State)
    (a b c : Scalar) (hr:Ready row s a b c) (hh:Header M T s)
    (hB:20≤B) (hT:T+3*M≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 16 (rowEnd row s a b c) := by
  have hi:s.natReg 1164<M:=hr.index.trans_eq hh.count
  have hd:row.dst≤B:=(hs.2.2.1 _ _ hr.dst).2
  have hsrc:row.src≤B:=(hs.2.2.1 _ _ hr.src).2
  have hc:row.coefficient≤B:=(hs.2.2.1 _ _ hr.coefficient).2
  have h0:WordBound B (entered s):=changePC_bound B s 4 hs (by omega)
  have h1:WordBound B (offset s):=writeNat_bound B _ _ _ h0 (by change 5≤B;omega) (by omega)
  have h2:WordBound B (pointer s):=writeNat_bound B _ _ _ h1 (by change 6≤B;omega) (by rw [hh.table];omega)
  have h3:WordBound B (dstState row s):=writeNat_bound B _ _ _ h2 (by change 7≤B;omega) hd
  have h4:WordBound B (srcPointer row s):=writeNat_bound B _ _ _ h3 (by change 8≤B;omega) (by rw [hh.table];omega)
  have h5:WordBound B (srcState row s):=writeNat_bound B _ _ _ h4 (by change 9≤B;omega) hsrc
  have h6:WordBound B (coefficientPointer row s):=writeNat_bound B _ _ _ h5 (by change 10≤B;omega) (by rw [hh.table];omega)
  have h7:WordBound B (coefficientState row s):=writeNat_bound B _ _ _ h6 (by change 11≤B;omega) hc
  have h8:WordBound B (dstValue row s a):=writeScalar_bound B _ _ _ h7 (by change 12≤B;omega)
  have h9:WordBound B (srcValue row s a b):=writeScalar_bound B _ _ _ h8 (by change 13≤B;omega)
  have h10:WordBound B (coefficientValue row s a b c):=writeScalar_bound B _ _ _ h9 (by change 14≤B;omega)
  have h11:WordBound B (multiplied row s a b c):=writeScalar_bound B _ _ _ h10 (by change 15≤B;omega)
  have h12:WordBound B (added row s a b c):=writeScalar_bound B _ _ _ h11 (by change 16≤B;omega)
  have h13:WordBound B (stored row s a b c):=UniformInPlaceMachine.storeScalar_bound B _ _ _ h12 (by change 17≤B;omega) hd
  have h14:WordBound B (advanced row s a b c):=writeNat_bound B _ _ _ h13 (by change 18≤B;omega) (by omega)
  have hf:WordBound B (rowEnd row s a b c):=changePC_bound B _ 3 h14 (by omega)
  rcases hr with ⟨hp,hin,hOne,hThree,hD,hS,hC,hA,hBb,hV,hprep⟩
  refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_ (.next h4 ?_
    (.next h5 ?_ (.next h6 ?_ (.next h7 ?_ (.next h8 ?_ (.next h9 ?_ (.next h10 ?_
    (.next h11 ?_ (.next h12 ?_ (.next h13 ?_ (.next h14 ?_ (.refl hf))))))))))))))))
  all_goals simp [step,program,entered,offset,pointer,dstState,srcPointer,srcState,coefficientPointer,
    coefficientState,dstValue,srcValue,coefficientValue,multiplied,added,stored,advanced,rowEnd,
    writeNat,writeScalar,next,evalNat,hp,hin,hOne,hThree,hD,hS,hC,hA,hBb,hV,
    prepared_mul c b hprep,result_add,Nat.mul_comm]

def Table (T : ℕ) : List Row→ℕ→State→Prop
  | [],_,_=>True
  | row::rows,i,s=>s.natHeap (T+3*i)=some row.dst ∧
    s.natHeap (T+3*i+1)=some row.src ∧ s.natHeap (T+3*i+2)=some row.coefficient ∧
    Table T rows (i+1) s
def Data (rows : List Row) (s : State) : Prop :=
  ∀row∈rows,(∃a,s.scalarHeap row.dst=some a) ∧ (∃b,s.scalarHeap row.src=some b)
def Coefficients (rows : List Row) (value : ℕ→ℂ) (s : State) : Prop :=
  ∀row∈rows,s.scalarHeap row.coefficient=some (prepared (value row.coefficient))
def Separated (rows : List Row) : Prop := ∀row∈rows,∀ref∈rows,row.dst≠ref.coefficient
def act (value : ℕ→ℂ) (row : Row) (heap : ℕ→Option Scalar) : ℕ→Option Scalar :=
  Function.update heap row.dst (some (result ((heap row.dst).getD Scalar.zero)
    ((heap row.src).getD Scalar.zero) (prepared (value row.coefficient))))
def action (value : ℕ→ℂ) : List Row→(ℕ→Option Scalar)→(ℕ→Option Scalar)
  | [],heap=>heap
  | row::rows,heap=>action value rows (act value row heap)
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀q,(q<1162 ∨ 1169≤q)→u.natReg q=s.natReg q) ∧
  (∀q,(q<90 ∨ 94≤q)→u.scalarReg q=s.scalarReg q)

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun q hq=>(h'.2.2.2.1 q hq).trans (h.2.2.2.1 q hq),
    fun q hq=>(h'.2.2.2.2 q hq).trans (h.2.2.2.2 q hq)⟩

theorem rowEnd_frame (row : Row) (s : State) (a b c : Scalar) : Frame s (rowEnd row s a b c) :=
  ⟨(row_frame row s a b c).1,(row_frame row s a b c).2.2.1,
    (row_frame row s a b c).2.2.2.1,(row_frame row s a b c).2.2.2.2.1,
    (row_frame row s a b c).2.2.2.2.2⟩

theorem Header.frame {M T : ℕ} {s u : State} (hh:Header M T s) (hf:Frame s u) : Header M T u :=
  ⟨(hf.2.2.2.1 1160 (by omega)).trans hh.count,(hf.2.2.2.1 1161 (by omega)).trans hh.table⟩
theorem Table.transport (T i : ℕ) (rows : List Row) (s u : State) (h:u.natHeap=s.natHeap) :
    Table T rows i u ↔ Table T rows i s := by
  induction rows generalizing i with
  | nil=>rfl
  | cons row rows ih=>simp only [Table,h,ih]

theorem initialized_frame (s : State) : Frame s (initialized s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro q hq;simp (disch:=omega) [initialized,writeNat,next]
  · intro q hq;rfl

theorem action_outside (value : ℕ→ℂ) (rows : List Row) (heap : ℕ→Option Scalar) (q : ℕ)
    (hq:∀row∈rows,q≠row.dst) : action value rows heap q=heap q := by
  induction rows generalizing heap with
  | nil=>rfl
  | cons row rows ih=>
    change action value rows (act value row heap) q=heap q
    rw [ih _ (fun r hr=>hq r (by simp [hr]))]
    exact Function.update_of_ne (hq row (by simp)) _ _

theorem present_update (heap : ℕ→Option Scalar) (d q : ℕ) (v : Scalar)
    (h:∃a,heap q=some a) : ∃a,(Function.update heap d (some v)) q=some a := by
  by_cases hd:q=d
  · subst q;exact ⟨v,by simp⟩
  · obtain ⟨a,ha⟩:=h;exact ⟨a,(Function.update_of_ne hd _ _).trans ha⟩

/-- The whole loop derives each Ready state from original physical tables and
present data. No valid schedule or resulting action is a premise. -/
theorem loop (n B M T i : ℕ) (x : Fin n→ℂ) (rows : List Row) (value : ℕ→ℂ) (s : State)
    (hh:Header M T s) (hp:s.pc=3) (hi:s.natReg 1164=i) (h1:s.natReg 1162=1)
    (h3:s.natReg 1163=3) (hlen:i+rows.length=M) (ht:Table T rows i s)
    (hd:Data rows s) (hc:Coefficients rows value s) (sep:Separated rows)
    (hB:20≤B) (hT:T+3*M≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (16*rows.length+2) u ∧ u.pc=19 ∧
    Header M T u ∧ u.scalarHeap=action value rows s.scalarHeap ∧ Frame s u := by
  induction rows generalizing i s with
  | nil=>
    have stop:¬s.natReg 1164<s.natReg 1160:=by
      rw [hi,hh.count];simp only [List.length_nil,Nat.add_zero] at hlen;omega
    refine ⟨{s with pc:=19},.next hs ?_ (.halt (changePC_bound B s 19 hs (by omega)) ?_),
      rfl,⟨hh.count,hh.table⟩,rfl,Frame.refl s⟩
    all_goals simp [step,program,hp,stop]
  | cons row rows ih=>
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩:=hd row (by simp)
    have hcoef:=hc row (by simp)
    rcases ht with ⟨hD,hS,hC,htail⟩
    have idx:s.natReg 1164<s.natReg 1160:=by rw [hi,hh.count];simp only [List.length_cons] at hlen;omega
    have ready:Ready row s a b (prepared (value row.coefficient)):=
      ⟨hp,idx,h1,h3,by simpa [hh.table,hi] using hD,by simpa [hh.table,hi] using hS,
        by simpa [hh.table,hi] using hC,ha,hb,hcoef,rfl⟩
    let v:=rowEnd row s a b (prepared (value row.coefficient))
    have run:=row_bounded n B M T x row s a b _ ready hh hB hT hs
    have frame:Frame s v:=rowEnd_frame _ _ _ _ _
    have vh:v.scalarHeap=Function.update s.scalarHeap row.dst (some (result a b (prepared (value row.coefficient)))):=rfl
    have dv:Data rows v:=by
      intro r hr
      have h:=hd r (by simp [hr])
      rw [vh]
      exact ⟨present_update _ _ _ _ h.1,present_update _ _ _ _ h.2⟩
    have cv:Coefficients rows value v:=by
      intro r hr
      rw [vh,Function.update_of_ne (sep row (by simp) r (by simp [hr])).symm]
      exact hc r (by simp [hr])
    have tv:Table T rows (i+1) v:=(Table.transport T (i+1) rows s v frame.1).mpr htail
    have sp:Separated rows:=by intro r hr q hq;exact sep r (by simp [hr]) q (by simp [hq])
    have vi:v.natReg 1164=i+1:=by simp [v,rowEnd,advanced,writeNat,next,hi]
    have v1:v.natReg 1162=1:=by simp [v,rowEnd,advanced,stored,added,multiplied,coefficientValue,srcValue,dstValue,
      coefficientState,coefficientPointer,srcState,srcPointer,dstState,pointer,offset,entered,writeNat,writeScalar,next,h1]
    have v3:v.natReg 1163=3:=by simp [v,rowEnd,advanced,stored,added,multiplied,coefficientValue,srcValue,dstValue,
      coefficientState,coefficientPointer,srcState,srcPointer,dstState,pointer,offset,entered,writeNat,writeScalar,next,h3]
    have vl:i+1+rows.length=M:=by simp only [List.length_cons] at hlen;omega
    obtain ⟨u,ru,pu,hu,au,fu⟩:=ih (i+1) v (hh.frame frame) rfl vi v1 v3 vl tv dv cv sp run.final_bound
    refine ⟨u,?_,pu,hu,?_,frame.trans fu⟩
    · simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run.executes ru
    · rw [au];change action value rows v.scalarHeap=action value rows (act value row s.scalarHeap)
      congr 1
      simp [act,vh,ha,hb]

theorem table_of_indexed (T i : ℕ) (rows : List Row) (s : State)
    (h:∀(j : ℕ)(hj:j<rows.length),s.natHeap (T+3*(i+j))=some rows[j].dst ∧
      s.natHeap (T+3*(i+j)+1)=some rows[j].src ∧
      s.natHeap (T+3*(i+j)+2)=some rows[j].coefficient) : Table T rows i s := by
  induction rows generalizing i with
  | nil=>trivial
  | cons row rows ih=>
    have head:=h 0 (by simp)
    refine ⟨by simpa using head.1,by simpa using head.2.1,by simpa using head.2.2,?_⟩
    apply ih (i+1)
    intro j hj
    have tail:=h (j+1) (by simp;omega)
    simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

theorem table_of_rows (T : ℕ) (rows : List Row) (s : State) (h:Rows T rows s) : Table T rows 0 s := by
  apply table_of_indexed
  intro j hj
  simpa using h j hj

/-- One initialized scalar interpreter, exact16M+5 charged instructions, from
the actual produced Nat table and prepared scalar bank. Exact scalar tags flow
through `action`; no numeric cancellation clears an input-dependence tag. -/
theorem execution (n B M T : ℕ) (x : Fin n→ℂ) (rows : List Row) (value : ℕ→ℂ) (s : State)
    (hh:Header M T s) (hp:s.pc=0) (hlen:rows.length=M) (ht:Rows T rows s)
    (hd:Data rows s) (hc:Coefficients rows value s) (sep:Separated rows)
    (hB:20≤B) (hT:T+3*M≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (16*M+5) u ∧ u.pc=19 ∧
    Header M T u ∧ u.scalarHeap=action value rows s.scalarHeap ∧ Frame s u ∧
    ∀q,(∀row∈rows,q≠row.dst)→u.scalarHeap q=s.scalarHeap q := by
  let v:=initialized s
  have start:=startup_bounded n B x s hB hp hs
  have frame:Frame s v:=initialized_frame s
  have pc:v.pc=3:=by simp [v,initialized,writeNat,next,hp]
  have idx:v.natReg 1164=0:=by simp [v,initialized,writeNat,next]
  have one:v.natReg 1162=1:=by simp [v,initialized,writeNat,next]
  have three:v.natReg 1163=3:=by simp [v,initialized,writeNat,next]
  have table:Table T rows 0 v:=(Table.transport T 0 rows s v frame.1).mpr (table_of_rows T rows s ht)
  obtain ⟨u,run,pu,hu,au,fu⟩:=loop n B M T 0 x rows value v (hh.frame frame) pc idx one three
    (by omega) table hd hc sep hB hT start.final_bound
  refine ⟨u,?_,pu,hu,au,frame.trans fu,?_⟩
  · convert start.executes run using 1;omega
  · intro q hq
    rw [au]
    exact action_outside value rows s.scalarHeap q hq

def numeric (heap : ℕ→Option Scalar) (q : ℕ) : ℂ := ((heap q).getD Scalar.zero).value

theorem act_numeric (value : ℕ→ℂ) (row : Row) (heap : ℕ→Option Scalar) :
    numeric (act value row heap)=UniformInverseShearTableMachine.rowAction value row (numeric heap) := by
  funext q
  by_cases h:q=row.dst
  · subst q
    simp [numeric,act,UniformInverseShearTableMachine.rowAction,result,prepared]
  · simp [numeric,act,UniformInverseShearTableMachine.rowAction,h]

theorem action_numeric (value : ℕ→ℂ) (rows : List Row) (heap : ℕ→Option Scalar) :
    numeric (action value rows heap)=UniformInverseShearTableMachine.rowsAction value rows (numeric heap) := by
  induction rows generalizing heap with
  | nil=>rfl
  | cons row rows ih=>
    change numeric (action value rows (act value row heap))=
      UniformInverseShearTableMachine.rowsAction value rows
        (UniformInverseShearTableMachine.rowAction value row (numeric heap))
    rw [ih,act_numeric]

theorem act_dependency (value : ℕ→ℂ) (row : Row) (heap : ℕ→Option Scalar) :
    ((act value row heap row.dst).getD Scalar.zero).dependent=
      (((heap row.dst).getD Scalar.zero).dependent || ((heap row.src).getD Scalar.zero).dependent) := by
  simp [act,result]

theorem coefficients_of_prepared (rows : List Row) (s : State)
    (h:∀row∈rows,∃z,s.scalarHeap row.coefficient=some (prepared z)) :
    Coefficients rows (UniformInverseShearTableMachine.heapCoefficient s) s := by
  intro row hr
  obtain ⟨z,hz⟩:=h row hr
  simp [UniformInverseShearTableMachine.heapCoefficient,hz,UniformPairMachine.prepared,prepared]

/-- Prepared coefficient readability is derived from the actual signed42
banks; this bridge does not assume an already certified replay schedule. -/
theorem coefficients_forward {K C T P : ℕ} (rows : List Row) (bank : ℕ→ℂ) (s : State)
    (pos:UniformReplayCoefficientMachine.Source C (7*UniformRadixTwoDAG.width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*UniformRadixTwoDAG.width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*UniformRadixTwoDAG.width K≤P)
    (domain:∀row∈rows,UniformInverseShearTableMachine.Domain C P (7*UniformRadixTwoDAG.width K) row.coefficient) :
    Coefficients rows (UniformInverseShearTableMachine.heapCoefficient s) s := by
  apply coefficients_of_prepared
  intro row hr
  obtain ⟨z,hz,_⟩:=UniformInverseShearTableMachine.inverse_coefficient pos neg constants sep (domain row hr)
  exact ⟨z,hz⟩

theorem coefficients_inverse {K C T P : ℕ} (rows : List Row) (bank : ℕ→ℂ) (s : State)
    (pos:UniformReplayCoefficientMachine.Source C (7*UniformRadixTwoDAG.width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*UniformRadixTwoDAG.width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*UniformRadixTwoDAG.width K≤P)
    (domain:∀row∈rows,UniformInverseShearTableMachine.Domain C P (7*UniformRadixTwoDAG.width K) row.coefficient) :
    Coefficients (UniformInverseShearTableMachine.inverseRows C T P rows)
      (UniformInverseShearTableMachine.heapCoefficient s) s := by
  apply coefficients_of_prepared
  intro row hr
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hr
  have mem:original∈rows:=List.mem_reverse.mp ho
  obtain ⟨z,_,hz⟩:=UniformInverseShearTableMachine.inverse_coefficient pos neg constants sep (domain original mem)
  exact ⟨-z,hz⟩

theorem execution_numeric (n B M T : ℕ) (x : Fin n→ℂ) (rows : List Row) (value : ℕ→ℂ) (s : State)
    (hh:Header M T s) (hp:s.pc=0) (hlen:rows.length=M) (ht:Rows T rows s)
    (hd:Data rows s) (hc:Coefficients rows value s) (sep:Separated rows)
    (hB:20≤B) (hT:T+3*M≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (16*M+5) u ∧ u.pc=19 ∧ Header M T u ∧
    u.scalarHeap=action value rows s.scalarHeap ∧
    numeric u.scalarHeap=UniformInverseShearTableMachine.rowsAction value rows (numeric s.scalarHeap) ∧
    Frame s u ∧ ∀q,(∀row∈rows,q≠row.dst)→u.scalarHeap q=s.scalarHeap q := by
  obtain ⟨u,run,pu,hu,au,fr,out⟩:=execution n B M T x rows value s hh hp hlen ht hd hc sep hB hT hs
  refine ⟨u,run,pu,hu,au,?_,fr,out⟩
  rw [au,action_numeric]

theorem signed_forward_execution (n B M R K C T P : ℕ) (x : Fin n→ℂ)
    (rows : List Row) (bank : ℕ→ℂ) (s : State)
    (hh:Header M R s) (hp:s.pc=0) (hlen:rows.length=M) (ht:Rows R rows s)
    (hd:Data rows s) (separated:Separated rows)
    (pos:UniformReplayCoefficientMachine.Source C (7*UniformRadixTwoDAG.width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*UniformRadixTwoDAG.width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (sep:C+7*UniformRadixTwoDAG.width K≤P)
    (domain:∀row∈rows,UniformInverseShearTableMachine.Domain C P (7*UniformRadixTwoDAG.width K) row.coefficient)
    (hB:20≤B) (hR:R+3*M≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (16*M+5) u ∧ u.pc=19 ∧ Header M R u ∧
    u.scalarHeap=action (UniformInverseShearTableMachine.heapCoefficient s) rows s.scalarHeap ∧
    numeric u.scalarHeap=UniformInverseShearTableMachine.rowsAction
      (UniformInverseShearTableMachine.heapCoefficient s) rows (numeric s.scalarHeap) ∧
    Frame s u ∧ ∀q,(∀row∈rows,q≠row.dst)→u.scalarHeap q=s.scalarHeap q :=
  execution_numeric n B M R x rows _ s hh hp hlen ht hd
    (coefficients_forward rows bank s pos neg constants sep domain) separated hB hR hs

end
end ExactFourierCircuits.UniformScalarReplayMachine
