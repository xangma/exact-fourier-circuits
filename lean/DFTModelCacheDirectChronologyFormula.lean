import DFTModelCacheDirectLeafProgram

set_option autoImplicit false

/-! Paper E §3.1–3.5: chronological direct Toeplitz leaves. This
formula refers to the actual descending-target, ascending-source record list;
the coefficient address is independent of the physical subtree offset. -/
namespace ExactFourierCircuits.DFTModelCacheDirectChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology
open DFTModelCacheDirectLeaf
noncomputable section

abbrev Event := p w (p w Record4)

def rowOffset (v i : ℕ) : ℕ :=
  (v-1-i)+14*(v*(v-1)-i*(i+1))
def timestamp (v o t : ℕ) (q : Record) : ℕ :=
  t+rowOffset v (q.dest-o)+(if q.kind=0 then 0 else 1+28*(q.source-o))
def event (v o t : ℕ) (q : Record) : Event.T :=
  (timestamp v o t q,(cacheKind q,encode q))
def chronological (t : ℕ) : List Record→List Event.T
  | []=>[]
  | q::qs=>(t,(cacheKind q,encode q))::chronological (t+duration q) qs

theorem chronological_length (t : ℕ) (qs : List Record) :
    (chronological t qs).length=qs.length := by
  induction qs generalizing t with
  | nil=>rfl
  | cons q qs ih=>simp only [chronological,List.length_cons,ih]

theorem chronological_append (t : ℕ) (xs ys : List Record) :
    chronological t (xs++ys)=chronological t xs++chronological (t+elapsed xs) ys := by
  induction xs generalizing t with
  | nil=>simp [chronological,elapsed]
  | cons q xs ih=>
    simp only [List.cons_append,chronological,ih,List.cons_append,elapsed_cons]
    rw [Nat.add_assoc]

theorem chronological_ofFn {n : ℕ} (f : Fin n→Record) (c t : ℕ)
    (hd : ∀j,duration (f j)=c) :
    chronological t (List.ofFn f)=
      List.ofFn (fun j=>(t+c*j.val,(cacheKind (f j),encode (f j)))) := by
  induction n generalizing t with
  | zero=>simp [chronological]
  | succ n ih=>
    rw [List.ofFn_succ,chronological,hd,List.ofFn_succ,
      ih (fun j=>f j.succ) (t+c) (fun j=>hd j.succ)]
    apply congrArg₂ List.cons
    · simp
    · apply congrArg List.ofFn
      funext j
      apply Prod.ext
      · simp only [Fin.val_succ]
        ring
      · rfl

theorem chronological_row (i o K t : ℕ) :
    chronological t (rowRecords i o K)=
      (t,(1,encode ⟨0,o+i,o+i,K⟩))::
        List.ofFn (fun j : Fin i=>(t+1+28*j.val,
          (0,encode ⟨1,o+i,o+j.val,K+(i-j.val)⟩))) := by
  simp only [rowRecords,chronological,duration]
  rw [chronological_ofFn _ 28]
  · rfl
  · intro j; rfl

theorem record_target (v o K : ℕ) (q : Record) (hq:q∈records o K v) :
    o≤q.dest ∧ q.dest-o<v := by
  induction v with
  | zero=>simp [records] at hq
  | succ v ih=>
    rcases List.mem_append.mp hq with hq|hq
    · simp only [rowRecords,List.mem_cons,List.mem_ofFn] at hq
      rcases hq with rfl|⟨j,rfl⟩ <;> simp
    · have h:=ih hq
      exact ⟨h.1,Nat.lt_trans h.2 (Nat.lt_succ_self _)⟩

theorem rowOffset_self (i : ℕ) : rowOffset (i+1) i=0 := by
  simp [rowOffset,Nat.mul_comm]

theorem rowOffset_step (v i : ℕ) (hi:i<v) :
    rowOffset (v+1) i=1+28*v+rowOffset v i := by
  have hv : 0<v := by omega
  have him : i+1≤v := hi
  have hprod : i*(i+1)≤v*(v-1) := by
    have : i≤v-1 := by omega
    calc
      i*(i+1)≤(v-1)*v := Nat.mul_le_mul this him
      _=v*(v-1) := Nat.mul_comm _ _
  have hmul : v*(v-1)+v=v*v := by
    have h : v-1+1=v := by omega
    nlinarith
  unfold rowOffset
  simp only [Nat.add_sub_cancel]
  have hp : (v+1)*v=v*(v-1)+2*v := by nlinarith
  omega

theorem event_step (v o K t : ℕ) (q : Record) (hq:q∈records o K v) :
    event (v+1) o t q=event v o (t+1+28*v) q := by
  have ht:=record_target v o K q hq
  apply Prod.ext
  · change timestamp (v+1) o t q=timestamp v o (t+1+28*v) q
    unfold timestamp
    rw [rowOffset_step v _ ht.2]
    omega
  · rfl

theorem event_row (i o K t : ℕ) :
    (rowRecords i o K).map (event (i+1) o t)=chronological t (rowRecords i o K) := by
  rw [chronological_row]
  simp [rowRecords,event,timestamp,Function.comp_def,rowOffset_self,cacheKind,
    Nat.add_assoc]

theorem events_chronological (v o K t : ℕ) :
    (records o K v).map (event v o t)=chronological t (records o K v) := by
  induction v generalizing t with
  | zero=>rfl
  | succ v ih=>
    rw [records,List.map_append,event_row,chronological_append]
    have hr : elapsed (rowRecords v o K)=1+28*v := by
      simp [rowRecords,elapsed,duration,List.map_ofFn,List.sum_ofFn,Nat.mul_comm]
    rw [hr]
    have hm : (records o K v).map (event (v+1) o t)=
        (records o K v).map (event v o (t+1+28*v)) := by
      apply List.map_congr_left
      exact fun q hq=>event_step v o K t q hq
    rw [hm,ih]
    congr 2
    omega

theorem chronological_get (t : ℕ) (qs : List Record) (j : ℕ) (hj:j<qs.length) :
    (chronological t qs)[j]'(by rw [chronological_length];exact hj)=
      (starts t qs j,(cacheKind qs[j],encode qs[j])) := by
  induction qs generalizing t j with
  | nil=>simp at hj
  | cons q qs ih=>
    cases j with
    | zero=>rfl
    | succ j=>
      have h:j<qs.length := by simpa using hj
      simp only [chronological,List.getElem_cons_succ]
      rw [ih (t+duration q) j h]
      simp [starts,List.take_succ_cons,elapsed_cons,Nat.add_assoc]

theorem native_timestamp (v o K t j : ℕ)
    (hj:j<(leafRecords v o K).length) :
    timestamp v o t (leafRecords v o K)[j]=starts t (leafRecords v o K) j := by
  have eq:=events_chronological v o K t
  rw [records_native] at eq
  have hg:=congrArg (fun L=>L[j]?) eq
  have len : (chronological t (leafRecords v o K)).length=(leafRecords v o K).length := by
    have := congrArg List.length eq
    simpa using this.symm
  rw [List.getElem?_eq_getElem (by simpa using hj),
    List.getElem?_eq_getElem (by omega),List.getElem_map,chronological_get t _ j hj] at hg
  exact congrArg (fun x=>x.1) (Option.some.inj hg)

end
end ExactFourierCircuits.DFTModelCacheDirectChronology
