import UniformIntegerScalarMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDAGLiteralBankMachine
open UniformMachine UniformAssembly
open scoped BigOperators

/-- Nat230=number of chronological leaf slots, 231=triple table base,
232=leaf base, 238=prepared-zero cell. Scratch233..237; scalar scratch0..3,30.
The signed helper is literally relocated, including its charged return jump. -/
def program : Program :=
  [.scalarLiteral 30 0,.storeScalar 238 30,
   .natLiteral 233 0,.natLiteral 234 1,.natLiteral 235 3,
   .branchLT 233 230 6 48,
   .natBinary .mul 236 235 233,.natBinary .add 236 231 236,
   .loadNat 0 236,.natBinary .add 236 236 234,.loadNat 5 236,
   .natBinary .add 236 236 234,.loadNat 6 236] ++
  UniformIntegerScalarMachine.signedProgram.map (relocate 13 44) ++
  [.natBinary .add 237 232 233,.storeScalar 237 2,
   .natBinary .add 233 233 234,.jump 5,.halt]

theorem program_length : program.length=49 := rfl

theorem signed_code : CodeAt UniformIntegerScalarMachine.signedProgram program 13 44 := by
  intro i hi
  have hlen : UniformIntegerScalarMachine.signedProgram.length=31 := rfl
  rw [hlen] at hi
  interval_cases i <;> rfl

inductive Op where
  | lit (d v : ℕ)
  | add (d l r : ℕ)
  | mul (d l r : ℕ)
  | get (d a : ℕ)
  | scalar (d : ℕ) (q : ℚ)
  | put (a r : ℕ)
  deriving DecidableEq

def Op.code : Op→Instruction
  | .lit d v => .natLiteral d v
  | .add d l r => .natBinary .add d l r
  | .mul d l r => .natBinary .mul d l r
  | .get d a => .loadNat d a
  | .scalar d q => .scalarLiteral d q
  | .put a r => .storeScalar a r

noncomputable section

def Op.apply (o : Op) (s : State) : State := match o with
  | .lit d v => writeNat s d v
  | .add d l r => writeNat s d (s.natReg l+s.natReg r)
  | .mul d l r => writeNat s d (s.natReg l*s.natReg r)
  | .get d a => writeNat s d ((s.natHeap (s.natReg a)).getD 0)
  | .scalar d q => writeScalar s d ⟨q,false⟩
  | .put a r => {next s with scalarHeap:=(Function.update s.scalarHeap
      (s.natReg a) (some (s.scalarReg r)))}

def Op.readable : Op→State→Prop
  | .get _ a,s => (s.natHeap (s.natReg a)).isSome=true
  | _,_ => True

def Op.peak : Op→State→ℕ
  | .lit _ v,_ => v
  | .add _ l r,s => s.natReg l+s.natReg r
  | .mul _ l r,s => s.natReg l*s.natReg r
  | .get _ a,s => (s.natHeap (s.natReg a)).getD 0
  | .put a _,s => s.natReg a
  | _,_ => 0

def applyBlock : List Op→State→State
  | [],s => s
  | o::os,s => applyBlock os (o.apply s)
def readable : List Op→State→Prop
  | [],_ => True
  | o::os,s => o.readable s ∧ readable os (o.apply s)
def peak : List Op→State→ℕ
  | [],_ => 0
  | o::os,s => max (o.peak s) (peak os (o.apply s))
def BlockAt (os : List Op) (base : ℕ) : Prop :=
  ∀i,(hi:i < os.length)→program[base+i]?=some (os[i]'hi).code

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl
theorem applyBlock_pc (os : List Op) (s : State) :
    (applyBlock os s).pc=s.pc+os.length := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp only [applyBlock,ih,Op.apply_pc,List.length_cons];omega

theorem Op.step (o : Op) (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:program[s.pc]?=some o.code) (hr:o.readable s) :
    step program n x s=.running (o.apply s) := by
  cases o <;> simp [UniformMachine.step,hc,Op.code,Op.apply,evalNat]
  case get d a =>
    cases hh:s.natHeap (s.natReg a) with
    | none => simp [Op.readable,hh] at hr
    | some v => simp

theorem Op.bound (o : Op) (B : ℕ) (s : State) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (hv:o.peak s ≤ B) : WordBound B (o.apply s) := by
  cases o with
  | lit d v => exact writeNat_bound B s d v hs hp hv
  | add d l r => exact writeNat_bound B s d _ hs hp hv
  | mul d l r => exact writeNat_bound B s d _ hs hp hv
  | get d a => exact writeNat_bound B s d _ hs hp hv
  | scalar d q => exact writeScalar_bound B s d _ hs hp
  | put a r =>
    refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
    intro i v hi
    by_cases he:i=s.natReg a
    · simpa [he,Op.peak] using hv
    · exact hs.2.2.2.1 i v (by simpa [Op.apply,next,he] using hi)

theorem block_runs (os : List Op) (base n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:BlockAt os base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+os.length ≤ B) (hr:readable os s) (hv:peak os s ≤ B) :
    BoundedRuns program n x B s os.length (applyBlock os s) := by
  induction os generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have hh:s.pc+1 ≤ B := by simp only [List.length_cons] at hb;omega
    have hu:=o.bound B s hs hh ((le_max_left _ _).trans hv)
    have ht:BlockAt os (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change program[base+(i+1)]?=some (os[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have tail:=ih (base+1) (o.apply s) ht (by rw [Op.apply_pc,hp]) hu
      (by simp only [List.length_cons] at hb;omega) hr.2 ((le_max_right _ _).trans hv)
    have hfirst:=hc 0 (by simp)
    change program[base]?=some o.code at hfirst
    exact .next hs (o.step n x s (by simpa [hp] using hfirst) hr.1) tail

def initOps : List Op := [.scalar 30 0,.put 238 30,.lit 233 0,.lit 234 1,.lit 235 3]
def loadOps : List Op := [.mul 236 235 233,.add 236 231 236,.get 0 236,
  .add 236 236 234,.get 5 236,.add 236 236 234,.get 6 236]
def storeOps : List Op := [.add 237 232 233,.put 237 2,.add 233 233 234]
theorem init_code : BlockAt initOps 0 := by intro i hi; change i < 5 at hi; interval_cases i <;> rfl
theorem load_code : BlockAt loadOps 6 := by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem store_code : BlockAt storeOps 44 := by intro i hi;change i < 3 at hi;interval_cases i <;> rfl

def Protected (i : ℕ) : Prop := 7 ≤ i ∧ (i < 233 ∨ 238 ≤ i)
instance protectedDecidable (i : ℕ) : Decidable (Protected i) := inferInstanceAs (Decidable (7 ≤ i ∧ (i < 233 ∨ 238 ≤ i)))
def NatFrame (s u : State) : Prop := ∀i,Protected i→u.natReg i=s.natReg i
def Outside (b l m : ℕ) (s u : State) : Prop :=
  ∀i,i≠b→(i < l ∨ l+m ≤ i)→u.scalarHeap i=s.scalarHeap i
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ NatFrame s u
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   fun i hi=>(h'.2.2.2 i hi).trans (h.2.2.2 i hi)⟩
theorem Outside.trans {b l m : ℕ} {s u v : State}
    (h:Outside b l m s u) (h':Outside b l m u v) : Outside b l m s v :=
  fun i hb hi=>(h' i hb hi).trans (h i hb hi)
theorem Frame.withPC {s u : State} {pc : ℕ} (h:Frame s u) : Frame s {u with pc:=pc} := h
theorem Outside.withPC {s u : State} {b l m pc : ℕ}
    (h:Outside b l m s u) : Outside b l m s {u with pc:=pc} := h

def Source (m d : ℕ) (a den flag : ℕ→ℕ) (s : State) : Prop :=
  ∀j,j < m→s.natHeap (d+3*j)=some (a j) ∧
    s.natHeap (d+3*j+1)=some (den j) ∧ s.natHeap (d+3*j+2)=some (flag j) ∧ 0 < den j
def leaf (a den flag : ℕ) : Scalar :=
  ⟨UniformIntegerScalarMachine.signedValue a den flag,false⟩
def helperCost (a den flag : ℕ) : ℕ := 13+UniformPowerMachine.loopCost a+
  UniformPowerMachine.loopCost den+UniformIntegerScalarMachine.signCost flag
def runtime (m : ℕ) (a den flag : ℕ→ℕ) : ℕ :=
  7 + ∑ j ∈ Finset.range m, (12 + helperCost (a j) (den j) (flag j))

structure Invariant (m d l b k : ℕ) (a den flag : ℕ→ℕ) (s : State) : Prop where
  length : s.natReg 230=m
  table : s.natReg 231=d
  destination : s.natReg 232=l
  zeroAddress : s.natReg 238=b
  index : s.natReg 233=k
  one : s.natReg 234=1
  three : s.natReg 235=3
  zero : s.scalarHeap b=some ⟨0,false⟩
  leaves : ∀j,j < k→s.scalarHeap (l+j)=some (leaf (a j) (den j) (flag j))


theorem load_state (m d l b k : ℕ) (a den flag : ℕ→ℕ) (s : State)
    (hi:Invariant m d l b k a den flag s) (hs:Source m d a den flag s) (hk:k < m) :
    (applyBlock loadOps s).natReg 0=a k ∧ (applyBlock loadOps s).natReg 5=den k ∧
    (applyBlock loadOps s).natReg 6=flag k ∧
    (applyBlock loadOps s).scalarHeap=s.scalarHeap ∧ Frame s (applyBlock loadOps s) := by
  obtain ⟨ha,hd,hf,_⟩:=hs k hk
  constructor
  · simp [applyBlock,loadOps,Op.apply,writeNat,next,hi.three,hi.index,hi.table,hi.one,ha,hd,hf]
  constructor
  · simp [applyBlock,loadOps,Op.apply,writeNat,next,hi.three,hi.index,hi.table,hi.one,ha,hd,hf]
  constructor
  · simp [applyBlock,loadOps,Op.apply,writeNat,next,hi.three,hi.index,hi.table,hi.one,ha,hd,hf]
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i h
  have h0:i≠0:=by unfold Protected at h;omega
  have h5:i≠5:=by unfold Protected at h;omega
  have h6:i≠6:=by unfold Protected at h;omega
  have h236:i≠236:=by unfold Protected at h;omega
  simp [applyBlock,loadOps,Op.apply,writeNat,next,h0,h5,h6,h236]

theorem load_run (n : ℕ) (x : Fin n→ℂ) (m d l b k B : ℕ) (a den flag : ℕ→ℕ)
    (s : State) (hi:Invariant m d l b k a den flag s) (hsrc:Source m d a den flag s)
    (hk:k < m) (hB:d+3*m ≤ B) (hcode:49 ≤ B) (hp:s.pc=6) (hs:WordBound B s) :
    BoundedRuns program n x B s 7 (applyBlock loadOps s) := by
  obtain ⟨ha,hd,hf,_⟩:=hsrc k hk
  have haB: a k ≤ B :=(hs.2.2.1 _ _ ha).2
  have hdB: den k ≤ B :=(hs.2.2.1 _ _ hd).2
  have hfB: flag k ≤ B :=(hs.2.2.1 _ _ hf).2
  apply block_runs loadOps 6 n B x s load_code hp hs (by change 6+7 ≤ B;omega)
  · simp [readable,loadOps,Op.readable,Op.apply,writeNat,next,
      hi.three,hi.index,hi.table,hi.one,ha,hd,hf]
  · simp [peak,loadOps,Op.peak,Op.apply,writeNat,next,hi.three,hi.index,
      hi.table,hi.one,ha,hd,hf]
    omega

theorem store_frame (s : State) : Frame s (applyBlock storeOps s) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro i hi
  have h233:i≠233:=by unfold Protected at hi;omega
  have h237:i≠237:=by unfold Protected at hi;omega
  simp [applyBlock,storeOps,Op.apply,writeNat,next,h233,h237]

theorem store_heap (s : State) : (applyBlock storeOps s).scalarHeap=
    Function.update s.scalarHeap (s.natReg 232+s.natReg 233) (some (s.scalarReg 2)) := rfl

theorem iteration (n : ℕ) (x : Fin n→ℂ) (m d l b k B : ℕ) (a den flag : ℕ→ℕ)
    (s : State) (hi:Invariant m d l b k a den flag s) (hsrc:Source m d a den flag s)
    (hk:k < m) (hb:b < l) (hd:d+3*m ≤ B) (hl:l+m ≤ B) (hcode:49 ≤ B)
    (hp:s.pc=5) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (12+helperCost (a k) (den k) (flag k)) u ∧
    Invariant m d l b (k+1) a den flag u ∧ u.pc=5 ∧ Frame s u ∧ Outside b l m s u := by
  let entered : State := {s with pc:=6}
  have he:WordBound B entered:=changePC_bound B s 6 hs (by omega)
  have first:BoundedRuns program n x B s 1 entered:=.next hs
    (by simp [UniformMachine.step,program,hp,hi.index,hi.length,hk,entered]) (.refl he)
  have hie:Invariant m d l b k a den flag entered:=by cases hi;constructor <;> assumption
  have hsre:Source m d a den flag entered:=hsrc
  have hload:=load_run n x m d l b k B a den flag entered hie hsre hk hd hcode rfl he
  let loaded:=applyBlock loadOps entered
  obtain ⟨h0,h5,h6,hheap,hframe⟩:=load_state m d l b k a den flag entered hie hsre hk
  change loaded.natReg 0=a k at h0
  change loaded.natReg 5=den k at h5
  change loaded.natReg 6=flag k at h6
  have hlpc:loaded.pc=13:=by rw [applyBlock_pc];rfl
  have hlocal:WordBound B {loaded with pc:=0}:=changePC_bound B _ 0 hload.final_bound (by omega)
  obtain ⟨v,hv,hval,htag,hvf⟩:=UniformIntegerScalarMachine.bounded_signed_correct B
    (by omega) {loaded with pc:=0} hlocal rfl (by simpa [h5] using (hsrc k hk).2.2.2) n x
  have hpv:=UniformBoundedAssembly.boundedExecution_placed signed_code
    (by change 13+31 ≤ B;omega) (by omega) hv
  have hplaced:placed 13 {loaded with pc:=0}=loaded:=by
    cases heq:loaded with
    | mk pc nr sr nh sh out roots =>
      have hpc:pc=13:=by simpa only [heq] using hlpc
      simp [placed,hpc]
  rw [hplaced] at hpv
  let returned:State:={v with pc:=44}
  have hrFrame:Frame loaded returned:=by
    exact ⟨hvf.1,hvf.2.2.1,hvf.2.2.2.1,fun i hi=>hvf.2.2.2.2.1 i (by unfold Protected at hi;omega)⟩
  have hrHeap:returned.scalarHeap=loaded.scalarHeap:=hvf.2.1
  have hri:Invariant m d l b k a den flag returned:=by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hrFrame.2.2.2 230 (by decide)).trans ((hframe.2.2.2 230 (by decide)).trans hi.length)
    · exact (hrFrame.2.2.2 231 (by decide)).trans ((hframe.2.2.2 231 (by decide)).trans hi.table)
    · exact (hrFrame.2.2.2 232 (by decide)).trans ((hframe.2.2.2 232 (by decide)).trans hi.destination)
    · exact (hrFrame.2.2.2 238 (by decide)).trans ((hframe.2.2.2 238 (by decide)).trans hi.zeroAddress)
    · simpa [loaded,entered,applyBlock,loadOps,Op.apply,writeNat,next] using
        (hvf.2.2.2.2.1 233 (by decide)).trans hi.index
    · simpa [loaded,entered,applyBlock,loadOps,Op.apply,writeNat,next] using
        (hvf.2.2.2.2.1 234 (by decide)).trans hi.one
    · simpa [loaded,entered,applyBlock,loadOps,Op.apply,writeNat,next] using
        (hvf.2.2.2.2.1 235 (by decide)).trans hi.three
    · rw [hrHeap,hheap];exact hi.zero
    · intro j hj;rw [hrHeap,hheap];exact hi.leaves j hj
  have hscalar:returned.scalarReg 2=leaf (a k) (den k) (flag k):=by
    cases hq:v.scalarReg 2 with
    | mk value dependent =>
      have hval':value=UniformIntegerScalarMachine.signedValue (a k) (den k) (flag k):=by
        simpa [h0,h5,h6,hq] using hval
      have htag':dependent=false:=by simpa [hq] using htag
      simp [leaf,hval',htag']
  have hstore:BoundedRuns program n x B returned 3 (applyBlock storeOps returned):=by
    apply block_runs storeOps 44 n B x returned store_code rfl hpv.final_bound (by change 44+3 ≤ B;omega)
    · simp [readable,storeOps,Op.readable]
    · simp [peak,storeOps,Op.peak,Op.apply,writeNat,next,hri.destination,hri.index,hri.one];omega
  let u:State:={applyBlock storeOps returned with pc:=5}
  have huB:WordBound B u:=changePC_bound B _ 5 hstore.final_bound (by omega)
  have hpcStore:(applyBlock storeOps returned).pc=47:=by rw [applyBlock_pc];rfl
  have htail:BoundedRuns program n x B (applyBlock storeOps returned) 1 u:=.next hstore.final_bound
    (by rw [UniformMachine.step,hpcStore];rfl) (.refl huB)
  have huf:Frame returned u:=(store_frame returned).withPC
  refine ⟨u,?_,?_,rfl,hframe.trans (hrFrame.trans huf),?_⟩
  · have hall:=((first.trans hload).trans hpv).trans (hstore.trans htail)
    convert hall using 1
    simp only [helperCost,h0,h5,h6]
    omega
  · refine ⟨huf.2.2.2 230 (by decide) |>.trans hri.length,
      huf.2.2.2 231 (by decide) |>.trans hri.table,
      huf.2.2.2 232 (by decide) |>.trans hri.destination,
      huf.2.2.2 238 (by decide) |>.trans hri.zeroAddress,?_,?_,?_,?_,?_⟩
    · simp [u,applyBlock,storeOps,Op.apply,writeNat,next,hri.index,hri.one]
    · simp [u,applyBlock,storeOps,Op.apply,writeNat,next,hri.one]
    · simp [u,applyBlock,storeOps,Op.apply,writeNat,next,hri.three]
    · change (applyBlock storeOps returned).scalarHeap b=_
      rw [store_heap,hri.destination,hri.index,Function.update_of_ne (by omega)]
      exact hri.zero
    · intro j hj
      change (applyBlock storeOps returned).scalarHeap (l+j)=_
      rw [store_heap,hri.destination,hri.index,hscalar]
      by_cases hjk:j=k
      · subst j;simp
      · rw [Function.update_of_ne (by omega)];exact hri.leaves j (by omega)
  · intro i hib hil
    change (applyBlock storeOps returned).scalarHeap i=s.scalarHeap i
    rw [store_heap,hri.destination,hri.index,Function.update_of_ne (by omega),hrHeap,hheap]



def costFrom (a den flag : ℕ→ℕ) : ℕ→ℕ→ℕ
  | _,0 => 0
  | k,fuel+1 => 12+helperCost (a k) (den k) (flag k)+costFrom a den flag (k+1) fuel

theorem costFrom_sum (a den flag : ℕ→ℕ) (k fuel : ℕ) :
    costFrom a den flag k fuel=∑j∈Finset.range fuel,
      (12+helperCost (a (k+j)) (den (k+j)) (flag (k+j))) := by
  induction fuel generalizing k with
  | zero => simp [costFrom]
  | succ fuel ih =>
    rw [costFrom,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he:(∑j∈Finset.range fuel,(12+helperCost (a (k+1+j)) (den (k+1+j)) (flag (k+1+j))))=
        ∑j∈Finset.range fuel,(12+helperCost (a (k+(j+1))) (den (k+(j+1))) (flag (k+(j+1)))):=by
      apply Finset.sum_congr rfl
      intro j _; congr 3 <;> omega
    rw [he,Nat.add_comm]

theorem loop (n : ℕ) (x : Fin n→ℂ) (m d l b k fuel B : ℕ) (a den flag : ℕ→ℕ)
    (s : State) (hi:Invariant m d l b k a den flag s) (hsrc:Source m d a den flag s)
    (hk:k+fuel=m) (hb:b < l) (hd:d+3*m ≤ B) (hl:l+m ≤ B) (hcode:49 ≤ B)
    (hp:s.pc=5) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (costFrom a den flag k fuel) u ∧
    Invariant m d l b m a den flag u ∧ u.pc=5 ∧ Frame s u ∧ Outside b l m s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hp,⟨rfl,rfl,rfl,fun _ _=>rfl⟩,fun _ _ _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hou⟩:=iteration n x m d l b k B a den flag s hi hsrc
      (by omega) hb hd hl hcode hp hs
    have hsrcu:Source m d a den flag u:=by simpa [Source,hfu.1] using hsrc
    obtain ⟨v,hv,hiv,hpv,hfv,hov⟩:=ih (k+1) u hiu hsrcu (by omega) hpu hu.final_bound
    exact ⟨v,hu.trans hv,hiv,hpv,hfu.trans hfv,hou.trans hov⟩

/-- Whole literal producer. Source rows and positive denominators are physical
entry premises; scalar leaves and the prepared-zero cell are constructed. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (m d l b B : ℕ) (a den flag : ℕ→ℕ)
    (s : State) (hsrc:Source m d a den flag s) (hb:b < l)
    (hd:d+3*m ≤ B) (hl:l+m ≤ B) (hcode:49 ≤ B)
    (hp:s.pc=0) (hm:s.natReg 230=m) (ht:s.natReg 231=d)
    (hdst:s.natReg 232=l) (hz:s.natReg 238=b) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime m a den flag) u ∧
    u.scalarHeap b=some ⟨0,false⟩ ∧
    (∀j,j < m→u.scalarHeap (l+j)=some (leaf (a j) (den j) (flag j))) ∧
    Frame s u ∧ Outside b l m s u ∧ u.pc=48 := by
  have hinit:BoundedRuns program n x B s 5 (applyBlock initOps s):=by
    apply block_runs initOps 0 n B x s init_code hp hs (by change 0+5 ≤ B;omega)
    · simp [readable,initOps,Op.readable]
    · simp [peak,initOps,Op.peak,Op.apply,writeScalar,next,hz];omega
  let initialized:=applyBlock initOps s
  have hpi:initialized.pc=5:=by rw [applyBlock_pc,hp];rfl
  have hii:Invariant m d l b 0 a den flag initialized:=by
    constructor <;> simp [initialized,applyBlock,initOps,Op.apply,writeNat,writeScalar,next,
      hm,ht,hdst,hz]
  have hfi:Frame s initialized:=by
    refine ⟨rfl,rfl,rfl,?_⟩
    intro i hi
    have h233:i≠233:=by unfold Protected at hi;omega
    have h234:i≠234:=by unfold Protected at hi;omega
    have h235:i≠235:=by unfold Protected at hi;omega
    simp [initialized,applyBlock,initOps,Op.apply,writeNat,writeScalar,next,h233,h234,h235]
  have hoi:Outside b l m s initialized:=by
    intro i hib _
    simp [initialized,applyBlock,initOps,Op.apply,writeNat,writeScalar,next,hz,hib]
  have hsri:Source m d a den flag initialized:=hsrc
  obtain ⟨u,hu,hiu,hpu,hfu,hou⟩:=loop n x m d l b 0 m B a den flag initialized
    hii hsri (by omega) hb hd hl hcode hpi hinit.final_bound
  let v:State:={u with pc:=48}
  have hv:WordBound B v:=changePC_bound B u 48 hu.final_bound (by omega)
  have hfinish:BoundedExecution program n x B u 2 v:=.next hu.final_bound
    (by simp [UniformMachine.step,program,hpu,hiu.index,hiu.length,v])
    (.halt hv (by rw [UniformMachine.step];rfl))
  refine ⟨v,?_,hiu.zero,hiu.leaves,(hfi.trans hfu).withPC,(hoi.trans hou).withPC,rfl⟩
  have hall:=hinit.executes (hu.executes hfinish)
  convert hall using 1
  simp only [runtime,costFrom_sum,Nat.zero_add]
  omega

/-- Logarithmic scalar construction is charged separately for every actual row. -/
theorem runtime_log_bound (m B : ℕ) (a den flag : ℕ→ℕ)
    (ha:∀j,j < m→a j ≤ B) (hd:∀j,j < m→den j ≤ B) :
    runtime m a den flag ≤ 7+m*(14*(Nat.log2 (B+1)+1)+31) := by
  have hsum:(∑j∈Finset.range m,(12+helperCost (a j) (den j) (flag j))) ≤
      ∑j∈Finset.range m,(14*(Nat.log2 (B+1)+1)+31):=by
    apply Finset.sum_le_sum
    intro j hj
    have hjm:j < m:=Finset.mem_range.mp hj
    have haj:=ha j hjm
    have hdj:=hd j hjm
    have hc:=UniformIntegerScalarMachine.signed_cost_bound (a j) (den j) (flag j)
    have hla:Nat.log2 (a j+1) ≤ Nat.log2 (B+1):=by
      simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) (by omega : a j+1 ≤ B+1))
    have hld:Nat.log2 (den j+1) ≤ Nat.log2 (B+1):=by
      simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b:=2) (by omega : den j+1 ≤ B+1))
    change 12+helperCost (a j) (den j) (flag j) ≤ _
    unfold helperCost
    omega
  simpa [runtime] using Nat.add_le_add_left hsum 7

/-- In particular the existing master root at heap zero is untouched. -/
theorem master_preserved (b l m : ℕ) (s u : State) (h:Outside b l m s u)
    (hb:0 < b) (hl:0 < l) : u.scalarHeap 0=s.scalarHeap 0 :=
  h 0 (by omega) (Or.inl hl)



theorem runtime_log_of_source (m d B : ℕ) (a den flag : ℕ→ℕ) (s : State)
    (hsrc:Source m d a den flag s) (hs:WordBound B s) :
    runtime m a den flag ≤ 7+m*(14*(Nat.log2 (B+1)+1)+31) := by
  apply runtime_log_bound m B a den flag
  · intro j hj;exact (hs.2.2.1 _ _ (hsrc j hj).1).2
  · intro j hj;exact (hs.2.2.1 _ _ (hsrc j hj).2.1).2

theorem saved_preserved {s u : State} (h:Frame s u) (i : ℕ)
    (hi:100 ≤ i ∧ i ≤ 106) : u.natReg i=s.natReg i :=
  h.2.2.2 i (by unfold Protected;omega)

/-- The Nat source words encode rational numerators, denominators and signs;
the scalar value is proved from this encoding, not supplied at entry. -/
def RationalSource (m d : ℕ) (q : ℕ→ℚ) (s : State) : Prop :=
  Source m d (fun j=>(q j).num.natAbs) (fun j=>(q j).den)
    (fun j=>if (q j).num < 0 then 1 else 0) s

theorem leaf_rational (q : ℚ) :
    leaf q.num.natAbs q.den (if q.num < 0 then 1 else 0)=⟨q,false⟩ := by
  unfold leaf UniformIntegerScalarMachine.signedValue
  by_cases hq:q.num < 0
  · simp only [hq,ite_true,one_ne_zero,ite_false]
    have hc:(q.num:ℂ)= -((q.num.natAbs:ℕ):ℂ):=by
      exact_mod_cast (Int.eq_neg_natAbs_of_nonpos (by omega : q.num ≤ 0))
    rw [Rat.cast_def,hc,neg_div]
  · simp only [hq,ite_false]
    have hc:((q.num.natAbs:ℕ):ℂ)=(q.num:ℂ):=by
      have hInt:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (by omega : 0 ≤ q.num)
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ=>(z:ℂ)) hInt
    rw [hc,←Rat.cast_def];simp

theorem rational_execution (n : ℕ) (x : Fin n→ℂ) (m d l b B : ℕ) (q : ℕ→ℚ)
    (s : State) (hsrc:RationalSource m d q s) (hb:b < l)
    (hd:d+3*m ≤ B) (hl:l+m ≤ B) (hcode:49 ≤ B)
    (hp:s.pc=0) (hm:s.natReg 230=m) (ht:s.natReg 231=d)
    (hdst:s.natReg 232=l) (hz:s.natReg 238=b) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s
      (runtime m (fun j=>(q j).num.natAbs) (fun j=>(q j).den)
        (fun j=>if (q j).num < 0 then 1 else 0)) u ∧
    u.scalarHeap b=some ⟨0,false⟩ ∧
    (∀j,j < m→u.scalarHeap (l+j)=some ⟨q j,false⟩) ∧
    Frame s u ∧ Outside b l m s u ∧ u.pc=48 := by
  obtain ⟨u,hu,hzero,hleaves,hframe,houtside,hpc⟩:=execution n x m d l b B
    (fun j=>(q j).num.natAbs) (fun j=>(q j).den)
    (fun j=>if (q j).num < 0 then 1 else 0) s hsrc hb hd hl hcode hp hm ht hdst hz hs
  exact ⟨u,hu,hzero,fun j hj=>by simpa only [leaf_rational] using hleaves j hj,hframe,houtside,hpc⟩

example : leaf 0 1 0=⟨0,false⟩ := by norm_num [leaf,UniformIntegerScalarMachine.signedValue]
example : leaf 1 2 1=⟨-(1/2:ℂ),false⟩ := by norm_num [leaf,UniformIntegerScalarMachine.signedValue]



/-- Fresh positive zero address gives the master-root preservation contract. -/
theorem preserving_execution (n : ℕ) (x : Fin n→ℂ) (m d l b B : ℕ) (a den flag : ℕ→ℕ)
    (s : State) (hsrc:Source m d a den flag s) (hb0:0 < b) (hb:b < l)
    (hd:d+3*m ≤ B) (hl:l+m ≤ B) (hcode:49 ≤ B)
    (hp:s.pc=0) (hm:s.natReg 230=m) (ht:s.natReg 231=d)
    (hdst:s.natReg 232=l) (hz:s.natReg 238=b) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime m a den flag) u ∧
    u.scalarHeap b=some ⟨0,false⟩ ∧
    (∀j,j < m→u.scalarHeap (l+j)=some (leaf (a j) (den j) (flag j))) ∧
    u.scalarHeap 0=s.scalarHeap 0 ∧ Frame s u ∧ Outside b l m s u ∧ u.pc=48 := by
  obtain ⟨u,hu,hzero,hleaves,hframe,houtside,hpc⟩:=execution n x m d l b B a den flag s
    hsrc hb hd hl hcode hp hm ht hdst hz hs
  exact ⟨u,hu,hzero,hleaves,master_preserved b l m s u houtside hb0 (by omega),hframe,houtside,hpc⟩


end
end ExactFourierCircuits.UniformDAGLiteralBankMachine
