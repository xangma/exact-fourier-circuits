import UniformSectorPackingMachine
import UniformPermutationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformScalarScatterMachine
open UniformMachine UniformAssembly
open UniformGlobalNatPreparation (PermutationBank)
open scoped BigOperators

/-- Nat1506=length,1507=packed source,1508=original destination,1509=inverse bank.
The loop writes Nat1510..1516 and Scalar90; each real load/store/address operation
and control instruction is charged. -/
def program : Program := [
  .natLiteral 1510 0,.natLiteral 1511 1,.branchLT 1510 1506 3 11,
  .natBinary .add 1513 1509 1510,.loadNat 1514 1513,
  .natBinary .add 1515 1507 1510,.loadScalar 90 1515,
  .natBinary .add 1516 1508 1514,.storeScalar 1516 90,
  .natBinary .add 1510 1510 1511,.jump 2,.halt]

theorem program_length : program.length=12 := rfl

noncomputable section

def Source (L a : ℕ) (heap : ℕ→Option Scalar) : Prop :=
  ∀j:Fin L,∃v,heap (a+j.val)=some v

def Disjoint (a d L : ℕ) : Prop := a+L≤d ∨ d+L≤a

def Outside (d L : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop :=
  ∀j,(j<d ∨ d+L≤j) → s.scalarHeap j=heap j

/-- Original metadata, saved high headers, outputs and root requests are retained. -/
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,r≠90 → u.scalarReg r=s.scalarReg r) ∧
  ∀r,(r<1510 ∨ 1516<r) → u.natReg r=s.natReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

structure Invariant (L a d b k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) : Prop where
  length : s.natReg 1506=L
  source : s.natReg 1507=a
  destination : s.natReg 1508=d
  permutation : s.natReg 1509=b
  index : s.natReg 1510=k
  one : s.natReg 1511=1
  table : PermutationBank L b s.natHeap phi
  copied : ∀j:Fin L,j.val<k → s.scalarHeap (d+(phi j).val)=heap (a+j.val)
  outside : Outside d L heap s

/-- The following names expand only actual individual machine instructions. -/
def tableAddress (s : State) : State :=
  writeNat {s with pc:=3} 1513 (s.natReg 1509+s.natReg 1510)
def tableLoaded (s : State) (digit : ℕ) : State := writeNat (tableAddress s) 1514 digit
def sourceAddress (s : State) (digit : ℕ) : State :=
  writeNat (tableLoaded s digit) 1515 (s.natReg 1507+s.natReg 1510)
def scalarLoaded (s : State) (digit : ℕ) (v : Scalar) : State := writeScalar (sourceAddress s digit) 90 v
def destinationAddress (s : State) (digit : ℕ) (v : Scalar) : State :=
  writeNat (scalarLoaded s digit v) 1516 (s.natReg 1508+digit)
def stored (s : State) (digit : ℕ) (v : Scalar) : State :=
  {next (destinationAddress s digit v) with scalarHeap:=(Function.update s.scalarHeap
    (s.natReg 1508+digit) (some v))}
def advanced (s : State) (digit : ℕ) (v : Scalar) : State :=
  writeNat (stored s digit v) 1510 (s.natReg 1510+1)
def iterationEnd (s : State) (digit : ℕ) (v : Scalar) : State := {advanced s digit v with pc:=2}

theorem store_bound (B : ℕ) (s : State) (address : ℕ) (v : Scalar) (hs:WordBound B s)
    (hp:s.pc+1≤B) (ha:address≤B) :
    WordBound B {next s with scalarHeap:=Function.update s.scalarHeap address (some v)} := by
  refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro j v hj
  by_cases he:j=address
  · subst j;exact ha
  · exact hs.2.2.2.1 j v (by simpa [he] using hj)

theorem iteration_heap (s : State) (digit : ℕ) (v : Scalar) :
    (iterationEnd s digit v).scalarHeap=Function.update s.scalarHeap
      (s.natReg 1508+digit) (some v) := rfl

theorem iteration_frame (s : State) (digit : ℕ) (v : Scalar) : Frame s (iterationEnd s digit v) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hr]
  · intro r hr
    simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,show r≠1510 by omega,show r≠1513 by omega,
      show r≠1514 by omega,show r≠1515 by omega,show r≠1516 by omega]

theorem disjoint_source (a d L : ℕ) (hd:Disjoint a d L) (j : Fin L) :
    a+j.val<d ∨ d+L≤a+j.val := by unfold Disjoint at hd;omega

theorem iteration_invariant (L a d b k : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (v : Scalar)
    (hi:Invariant L a d b k phi heap s) (hk:k<L)
    (hv:heap (a+k)=some v) :
    Invariant L a d b (k+1) phi heap (iterationEnd s (phi ⟨k,hk⟩).val v) := by
  constructor
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.destination
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.permutation
  · simp [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next] using hi.one
  · exact hi.table
  · intro j hj
    rw [iteration_heap,hi.destination]
    by_cases he:j.val=k
    · have he':j=⟨k,hk⟩:=Fin.ext he
      subst j
      simp [hv]
    · have different:d+(phi j).val≠d+(phi ⟨k,hk⟩).val:=by
        intro eqn
        have same:phi j=phi ⟨k,hk⟩:=Fin.ext (by omega)
        have jk:j.val=k:=congrArg Fin.val (phi.injective same)
        exact he jk
      rw [Function.update_of_ne different]
      exact hi.copied j (by omega)
  · intro j hj
    rw [iteration_heap,hi.destination,Function.update_of_ne (by have :=(phi ⟨k,hk⟩).isLt;omega)]
    exact hi.outside j hj

/-- One real nine-instruction iteration, including the branch and both loads. -/
theorem iteration (n : ℕ) (x : Fin n→ℂ) (L a d b k B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant L a d b k phi heap s)
    (hsrc:Source L a heap) (hk:k<L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 9 u ∧ Invariant L a d b (k+1) phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  let j:Fin L:=⟨k,hk⟩
  let digit:ℕ:=(phi j).val
  obtain ⟨v,hv⟩:=hsrc j
  have hload:s.scalarHeap (a+k)=some v:=
    (hi.outside _ (disjoint_source a d L hd j)).trans hv
  have hdigit:digit<L:=(phi j).isLt
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have h1:WordBound B (tableAddress s):=writeNat_bound B {s with pc:=3} 1513 _ he
    (by change 3+1≤B;omega) (by rw [hi.permutation,hi.index];omega)
  have h2:WordBound B (tableLoaded s digit):=writeNat_bound B (tableAddress s) 1514 digit h1
    (by change 4+1≤B;omega) (by omega)
  have h3:WordBound B (sourceAddress s digit):=writeNat_bound B (tableLoaded s digit) 1515 _ h2
    (by change 5+1≤B;omega) (by rw [hi.source,hi.index];omega)
  have h4:WordBound B (scalarLoaded s digit v):=writeScalar_bound B (sourceAddress s digit) 90 v h3
    (by change 6+1≤B;omega)
  have h5:WordBound B (destinationAddress s digit v):=writeNat_bound B (scalarLoaded s digit v) 1516 _ h4
    (by change 7+1≤B;omega) (by rw [hi.destination];omega)
  have h6:WordBound B (stored s digit v):=store_bound B (destinationAddress s digit v) (s.natReg 1508+digit) v h5
    (by change 8+1≤B;omega) (by rw [hi.destination];omega)
  have h7:WordBound B (advanced s digit v):=writeNat_bound B (stored s digit v) 1510 _ h6
    (by change 9+1≤B;omega) (by rw [hi.index];omega)
  have h8:WordBound B (iterationEnd s digit v):=changePC_bound B _ 2 h7 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have t1:step program n x {s with pc:=3}=.running (tableAddress s):=by
    simp [step,program,tableAddress,evalNat]
  have t2:step program n x (tableAddress s)=.running (tableLoaded s digit):=by
    simp [step,program,tableLoaded,tableAddress,writeNat,next,hi.permutation,hi.index,hi.table j,digit,j]
  have t3:step program n x (tableLoaded s digit)=.running (sourceAddress s digit):=by
    simp [step,program,sourceAddress,tableLoaded,tableAddress,writeNat,next,evalNat]
  have t4:step program n x (sourceAddress s digit)=.running (scalarLoaded s digit v):=by
    simp [step,program,scalarLoaded,sourceAddress,tableLoaded,tableAddress,writeNat,next,hi.source,hi.index,hload]
  have t5:step program n x (scalarLoaded s digit v)=.running (destinationAddress s digit v):=by
    simp [step,program,destinationAddress,scalarLoaded,sourceAddress,tableLoaded,tableAddress,
      writeNat,writeScalar,next,evalNat]
  have t6:step program n x (destinationAddress s digit v)=.running (stored s digit v):=by
    simp [step,program,stored,destinationAddress,scalarLoaded,sourceAddress,tableLoaded,
      tableAddress,writeNat,writeScalar,next]
  have t7:step program n x (stored s digit v)=.running (advanced s digit v):=by
    simp [step,program,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next,hi.one,evalNat]
  have t8:step program n x (advanced s digit v)=.running (iterationEnd s digit v):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,scalarLoaded,sourceAddress,
      tableLoaded,tableAddress,writeNat,writeScalar,next]
  exact ⟨iterationEnd s digit v,.next hs t0 (.next he t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.next h6 t7 (.next h7 t8 (.refl h8))))))))),
    iteration_invariant L a d b k phi heap s v hi hk hv,rfl,iteration_frame s digit v⟩


/-- The entire loop runs actual instructions, including the final failed test. -/
theorem loop (n : ℕ) (x : Fin n→ℂ) (L a d b k fuel B : ℕ) (phi : Fin L≃Fin L)
    (heap : ℕ→Option Scalar) (s : State) (hi:Invariant L a d b k phi heap s)
    (hsrc:Source L a heap) (hk:k+fuel=L) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (9*fuel) u ∧ Invariant L a d b L phi heap u ∧
    u.pc=2 ∧ Frame s u := by
  induction fuel generalizing k s with
  | zero =>
    have he:k=L:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hframe⟩:=iteration n x L a d b k B phi heap s hi hsrc (by omega)
      hd haB hdB hbB hcode hpc hs
    obtain ⟨v,hv,hiv,hpv,hfr⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨v,?_,hiv,hpv,hframe.trans hfr⟩
    convert hu.trans hv using 1;omega

def zeroState (s : State) : State := writeNat s 1510 0
def initialized (s : State) : State := writeNat (zeroState s) 1511 1

theorem initialize_invariant (L a d b : ℕ) (phi : Fin L≃Fin L) (s : State)
    (h70:s.natReg 1506=L) (h71:s.natReg 1507=a) (h72:s.natReg 1508=d) (h73:s.natReg 1509=b)
    (hTable:PermutationBank L b s.natHeap phi) : Invariant L a d b 0 phi s.scalarHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h70,h71,h72,h73,Outside,hTable]

theorem initialize_frame (s : State) : Frame s (initialized s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr
  simp [initialized,zeroState,writeNat,next,show r≠1510 by omega,show r≠1511 by omega]

/-- Inverse scatter into a disjoint possibly dirty destination using the actually read
Nat permutation table. The actual loop reads packed[i] and stores destination[phi(i)], never a forward gather. No action or runtime certificate is assumed. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (L a d b B : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L b s.natHeap phi) (hsrc:Source L a s.scalarHeap) (hd:Disjoint a d L)
    (haB:a+L≤B) (hdB:d+L≤B) (hbB:b+L≤B) (hcode:11≤B)
    (hpc:s.pc=0) (h70:s.natReg 1506=L) (h71:s.natReg 1507=a) (h72:s.natReg 1508=d) (h73:s.natReg 1509=b)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*L+4) u ∧
    (∀j:Fin L,u.scalarHeap (d+(phi j).val)=s.scalarHeap (a+j.val)) ∧
    (∀j:Fin L,u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d L s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧ u.natReg 1510=L := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 1510 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 1511 1 hz
    (by change s.pc+1+1≤B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=.next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hframe⟩:=loop n x L a d b 0 L B phi s.scalarHeap (initialized s)
    (initialize_invariant L a d b phi s h70 h71 h72 h73 hTable) hsrc (by omega)
    hd haB hdB hbB hcode hp hi
  let v:State:={u with pc:=11}
  have hv:WordBound B v:=changePC_bound B u 11 hu.final_bound hcode
  have hh:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ hh
    simp [step,program,hpu,hiu.index,hiu.length,v]
  refine ⟨v,?_,fun j=>hiu.copied j j.isLt,?_,hiu.outside,(initialize_frame s).trans hframe,rfl,hiu.index⟩
  · convert hb.executes (hu.executes he) using 1;omega
  · intro j
    exact hiu.outside _ (disjoint_source a d L hd j)

theorem runtime_bound (L : ℕ) : 9*L+4≤13*(L+1) := by omega

/-- One unchanged word bound includes every table/scalar address and private
instruction value. All other initialized banks must fit the same ambient bound. -/
def wordBudget (L a d b : ℕ) : ℕ := max (max (a+L) (d+L)) (max (b+L) 1517)

theorem wordBudget_polynomial (L a d b : ℕ) : wordBudget L a d b≤1517*(a+d+b+L+1) := by
  unfold wordBudget;omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (L a d b : ℕ) (phi : Fin L≃Fin L) (s : State)
    (hTable:PermutationBank L b s.natHeap phi) (hsrc:Source L a s.scalarHeap) (hd:Disjoint a d L)
    (hpc:s.pc=0) (h70:s.natReg 1506=L) (h71:s.natReg 1507=a) (h72:s.natReg 1508=d) (h73:s.natReg 1509=b)
    (hs:WordBound (wordBudget L a d b) s) : ∃u,
    BoundedExecution program n x (wordBudget L a d b) s (9*L+4) u ∧
    (∀j:Fin L,u.scalarHeap (d+(phi j).val)=s.scalarHeap (a+j.val)) ∧
    (∀j:Fin L,u.scalarHeap (a+j.val)=s.scalarHeap (a+j.val)) ∧
    Outside d L s.scalarHeap u ∧ Frame s u ∧ u.pc=11 ∧ u.natReg 1510=L :=
  execution n x L a d b _ phi s hTable hsrc hd (by unfold wordBudget;omega)
    (by unfold wordBudget;omega) (by unfold wordBudget;omega) (by unfold wordBudget;omega)
    hpc h70 h71 h72 h73 hs


/-- In ordinary coordinates, scatter uses the inverse lookup only on the
right-hand specification; the machine actually writes destination[phi(i)]. -/
theorem scatter_coordinates {L a d:ℕ} {phi:Fin L≃Fin L} {s u:State}
 (h:∀i:Fin L,u.scalarHeap (d+(phi i).val)=s.scalarHeap (a+i.val)) (j:Fin L) :
 u.scalarHeap (d+j.val)=s.scalarHeap (a+(phi.symm j).val) := by
 simpa only [phi.apply_symm_apply] using h (phi.symm j)

/-- A derived physical packing inverse table is sufficient to execute the
actual inverse scatter. Every original tagged entry is restored exactly,
including dirty/data flags; no forward-gather substitution is made. -/
theorem unpack_execution (n:ℕ) (x:Fin n→ℂ) (L:UniformSectorPackingMachine.Layout)
 (phi:Fin L.total≃Fin L.total) (v:Fin L.total→Scalar) (s:State)
 (table:UniformSectorPackingMachine.InverseReady L phi s)
 (packed:∀i:Fin L.total,s.scalarHeap (L.destination+i.val)=some (v (phi i)))
 (pc:s.pc=0) (hL:s.natReg 1506=L.total) (ha:s.natReg 1507=L.destination)
 (hd:s.natReg 1508=L.source) (hb:s.natReg 1509=L.inverse)
 (bound:WordBound L.B s) : ∃u,
 BoundedExecution program n x L.B s (9*L.total+4) u ∧
 (∀j:Fin L.total,u.scalarHeap (L.source+j.val)=some (v j)) ∧
 (∀j:Fin L.total,u.scalarHeap (L.destination+j.val)=s.scalarHeap (L.destination+j.val)) ∧
 Outside L.source L.total s.scalarHeap u ∧ Frame s u ∧ u.pc=11 := by
 obtain ⟨u,run,values,source,out,frame,up,_⟩:=execution n x L.total L.destination L.source L.inverse L.B
  phi s table (fun i=>⟨v (phi i),packed i⟩) (Or.inr L.sourceBelow)
  L.destinationBound (L.sourceBelow.trans (by have:=L.destinationBound;omega)) L.inverseBound
  (by have:=L.code;omega) pc hL ha hd hb bound
 refine ⟨u,run,?_,source,out,frame,up⟩
 intro j
 rw [scatter_coordinates values j,packed,phi.apply_symm_apply]

/-- Independent exact copy semantics require no prepared scalar assumption. -/
theorem unpack_tag {L:ℕ} {v:Fin L→Scalar} {u:State} {d:ℕ}
 (h:∀j:Fin L,u.scalarHeap (d+j.val)=some (v j)) (j:Fin L) :
 ∃z,u.scalarHeap (d+j.val)=some z ∧ z.value=(v j).value ∧ z.dependent=(v j).dependent :=
 ⟨v j,h j,rfl,rfl⟩

end
end ExactFourierCircuits.UniformScalarScatterMachine
