import UniformTensorAddressMachine
import UniformPairMachine
import UniformBoundedAssembly
import UniformTensorMonomialMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformBinaryCStageMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformPairMachine (prepared combine)
open OAI.ExactFourier

/- One actual ordinary binary-axis stage. Nat2800=P (lower-axis stride),
   2801=A (data base), 2802=Q (upper-axis count). Scratch2803..2811 and
   Nat0..2 are local. Constants1/2 hold a/b. Every butterfly, load, index
   operation and loop instruction is charged; no root or child is requested. -/
def boot : List Op := [.literal 2810 1,.literal 2811 2,
 .mul 2803 2800 2802,.literal 2804 0]
def loads : List Op := [.mul 2806 2805 2800,.mul 2806 2806 2811,
 .add 0 2801 2806,.add 0 0 2,.add 1 0 2800,
 .literal 2 1,.getScalar 0 2,.literal 2 2,.getScalar 1 2]
def program : Program := boot.map Op.code ++
 [.branchLT 2804 2803 5 29,.natBinary .div 2805 2804 2800,
  .natBinary .mod 2 2804 2800] ++ loads.map Op.code ++
 UniformPairMachine.program.map (relocate 16 27) ++
 [.natBinary .add 2804 2804 2810,.jump 4,.halt]
theorem boot_length : boot.length=4 := rfl
theorem loads_length : loads.length=9 := rfl
theorem program_length : program.length=30 := rfl
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem loads_code : BlockAt loads program 7 := by
 intro i hi;change i<9 at hi;interval_cases i <;> rfl
theorem pair_code : CodeAt UniformPairMachine.program program 16 27 := by
 intro i hi;change i<11 at hi;interval_cases i <;> rfl
theorem halt_at : program[29]?=some .halt := rfl
theorem increment_at : program[27]?=some (.natBinary .add 2804 2804 2810) := rfl
theorem loop_jump_at : program[28]?=some (.jump 4) := rfl
theorem branch_at : program[4]?=some (.branchLT 2804 2803 5 29) := rfl

noncomputable section

def setPC (s : State) (pc : ℕ) : State := {s with pc:=pc}
def Constants (s : State) : Prop :=
 s.scalarHeap 1=some (prepared a) ∧ s.scalarHeap 2=some (prepared b)
def Present (A L : ℕ) (s : State) : Prop :=
 ∀j,j<L→(s.scalarHeap (A+j)).isSome=true
def Header (P A Q i : ℕ) (s : State) : Prop :=
 s.pc=4 ∧ s.natReg 2800=P ∧ s.natReg 2801=A ∧ s.natReg 2802=Q ∧
 s.natReg 2803=P*Q ∧ s.natReg 2804=i ∧ s.natReg 2810=1 ∧ s.natReg 2811=2
def left (P A i : ℕ) : ℕ := A+UniformTensorAddressMachine.address P 2 i 0
def right (P A i : ℕ) : ℕ := A+UniformTensorAddressMachine.address P 2 i 1

theorem left_formula (P A i : ℕ) : left P A i=A+(i/P)*P*2+i%P := by
 unfold left UniformTensorAddressMachine.address;ring
theorem right_formula (P A i : ℕ) : right P A i=left P A i+P := by
 unfold right left UniformTensorAddressMachine.address;ring
theorem pair_distinct (P A i : ℕ) (hp : 0<P) : left P A i≠right P A i := by
 rw [right_formula];omega
theorem pair_range (P A Q i : ℕ) (hi : i<P*Q) :
 A≤left P A i ∧ left P A i<A+P*2*Q ∧
 A≤right P A i ∧ right P A i<A+P*2*Q := by
 have hl:=UniformTensorAddressMachine.address_lt P 2 Q i 0 hi (by omega)
 have hr:=UniformTensorAddressMachine.address_lt P 2 Q i 1 hi (by omega)
 unfold left right;omega

def quotient (s : State) : State :=
 writeNat (setPC s 5) 2805 (s.natReg 2804/s.natReg 2800)
def remainder (s : State) : State :=
 writeNat (quotient s) 2 (s.natReg 2804%s.natReg 2800)
def ready (s : State) : State := applyBlock loads (remainder s)

theorem ready_fields (P A Q i : ℕ) (s : State) (h : Header P A Q i s)
 (hc : Constants s) :
 (ready s).pc=16 ∧ (ready s).natReg 0=left P A i ∧
 (ready s).natReg 1=right P A i ∧
 (ready s).scalarReg 0=prepared a ∧ (ready s).scalarReg 1=prepared b := by
 rcases h with ⟨hpc,hp,ha,hq,hm,hi,h1,h2⟩
 rcases hc with ⟨hc,hd⟩
 simp [ready,remainder,quotient,loads,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,
  hp,ha,hi,h2,hc,hd,left_formula,right_formula]

theorem ready_heap (s : State) : (ready s).scalarHeap=s.scalarHeap := rfl

theorem index_runs (n : ℕ) (x : Fin n→ℂ) (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (hi : i<P*Q) :
 Runs program n x s 3 (remainder s) := by
 rcases h with ⟨hpc,hp',ha,hq,hm,hi',h1,h2⟩
 refine .next (u:=setPC s 5) ?_ (.next (u:=quotient s) ?_
  (.next (u:=remainder s) ?_ (.refl _)))
 all_goals simp [step,program,boot,quotient,remainder,setPC,writeNat,next,
  evalNat,hpc,hp',hm,hi',hi,hp.ne']

theorem index_bounded (n B : ℕ) (x : Fin n→ℂ) (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (hi : i<P*Q)
 (hs : WordBound B s) (hcode : 30≤B) :
 BoundedRuns program n x B s 3 (remainder s) := by
 have hb:=changePC_bound B s 5 hs (by omega)
 have hv:i/P≤B:=(Nat.div_le_self i P).trans (by rw [←h.2.2.2.2.2.1];exact hs.2.1 _)
 have hq:=writeNat_bound B (setPC s 5) 2805 (i/P) hb (by simp [setPC];omega) hv
 have hv':i%P≤B:=(Nat.mod_le i P).trans (by rw [←h.2.2.2.2.2.1];exact hs.2.1 _)
 have hr:=writeNat_bound B (quotient s) 2 (i%P)
  (by simpa [quotient,h.2.1,h.2.2.2.2.2.1] using hq)
  (by simp [quotient,setPC,writeNat,next];omega) hv'
 have hq':WordBound B (quotient s):=by
  simpa [quotient,h.2.1,h.2.2.2.2.2.1] using hq
 have hr':WordBound B (remainder s):=by
  simpa [remainder,h.2.1,h.2.2.2.2.2.1] using hr
 rcases h with ⟨hpc,hp',ha,hq,hm,hi',h1,h2⟩
 refine .next hs (u:=setPC s 5) ?_ (.next hb (u:=quotient s) ?_
  (.next hq' (u:=remainder s) ?_ (.refl hr')))
 all_goals simp [step,program,boot,quotient,remainder,setPC,writeNat,next,
  evalNat,hpc,hp',hm,hi',hi,hp.ne']

theorem loads_readable (s : State) (hc : Constants s) : readable loads s := by
 rcases hc with ⟨hc,hd⟩
 simp [loads,readable,Op.readable,Op.apply,writeNat,writeScalar,next,hc,hd]

theorem ready_bounded (n B : ℕ) (x : Fin n→ℂ) (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (hi : i<P*Q)
 (hc : Constants s) (hs : WordBound B s) (hcode : 30≤B) (extent : A+P*2*Q≤B) :
 BoundedRuns program n x B s 12 (ready s) := by
 have ind:=index_bounded n B x P A Q i s h hp hi hs hcode
 have range:=pair_range P A Q i hi
 have hm:(i/P)*P*2≤B:=by
  have he:=left_formula P A i
  omega
 have hab:A+(i/P)*P*2≤B:=by
  have he:=left_formula P A i
  omega
 have hl:left P A i≤B:=by omega
 have hr:right P A i≤B:=by omega
 have hmul:(i/P)*P≤B:=by omega
 have hright:A+i/P*P*2+i%P+P≤B:=by
  simpa only [right_formula,left_formula] using hr
 have cap:peak loads (remainder s)≤B:=by
  rcases h with ⟨hpc,hp',ha,hq,hcount,hi',h1,h2⟩
  simp [loads,peak,Op.peak,Op.apply,remainder,quotient,setPC,writeNat,
   next,hp',ha,hi',h2,hab,hmul,hright,show 2≤B by omega]
 have run:=block_runs loads program 7 n B x (remainder s) loads_code
  (by simp [remainder,quotient,setPC,writeNat,next]) ind.final_bound (by simp only [loads_length];omega)
  (loads_readable _ (by simpa [Constants,remainder,quotient,setPC,writeNat,next] using hc)) cap
 exact ind.trans run

theorem present_value (o : Option Scalar) (h : o.isSome=true) :
 o=some (o.getD Scalar.zero) := by cases o <;> simp_all

def pairFinal (P A i : ℕ) (s : State) : State :=
 UniformPairMachine.finalState (setPC (ready s) 0) a b
  ((s.scalarHeap (left P A i)).getD Scalar.zero)
  ((s.scalarHeap (right P A i)).getD Scalar.zero)

theorem pair_final_heap (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hc : Constants s) :
 (pairFinal P A i s).scalarHeap=Function.update
  (Function.update s.scalarHeap (left P A i) (some (combine a b
   ((s.scalarHeap (left P A i)).getD Scalar.zero)
   ((s.scalarHeap (right P A i)).getD Scalar.zero))))
  (right P A i) (some (combine b a
   ((s.scalarHeap (left P A i)).getD Scalar.zero)
   ((s.scalarHeap (right P A i)).getD Scalar.zero))) := by
 have f:=ready_fields P A Q i s h hc
 simp only [pairFinal,UniformPairMachine.final_heap,setPC,ready_heap,f.2.1,f.2.2.1]

theorem placed_reset (s : State) (hp : s.pc=16) : placed 16 (setPC s 0)=s := by
 cases s with
 | mk pc nr sr nh sh out roots=>
  change pc=16 at hp
  subst pc
  rfl

theorem pair_bounded (n B : ℕ) (x : Fin n→ℂ) (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (hi : i<P*Q)
 (hc : Constants s) (present : Present A (P*2*Q) s)
 (hs : WordBound B s) (hcode : 30≤B) (extent : A+P*2*Q≤B) :
 BoundedRuns program n x B s 23 (setPC (pairFinal P A i s) 27) := by
 have headRun:=ready_bounded n B x P A Q i s h hp hi hc hs hcode extent
 have fields:=ready_fields P A Q i s h hc
 have range:=pair_range P A Q i hi
 have lhs:s.scalarHeap (left P A i)=some ((s.scalarHeap (left P A i)).getD Scalar.zero):=by
  apply present_value
  have hleft:left P A i=A+UniformTensorAddressMachine.address P 2 i 0:=rfl
  rw [hleft];exact present _ (UniformTensorAddressMachine.address_lt P 2 Q i 0 hi (by omega))
 have rhs:s.scalarHeap (right P A i)=some ((s.scalarHeap (right P A i)).getD Scalar.zero):=by
  apply present_value
  exact present _ (UniformTensorAddressMachine.address_lt P 2 Q i 1 hi (by omega))
 have localRun:=UniformPairMachine.bounded_execution n x B (setPC (ready s) 0) a b
  ((s.scalarHeap (left P A i)).getD Scalar.zero)
  ((s.scalarHeap (right P A i)).getD Scalar.zero)
  ⟨rfl,by simpa only [setPC,ready_heap,fields.2.1] using lhs,
   by simpa only [setPC,ready_heap,fields.2.2.1] using rhs,
   fields.2.2.2.1,fields.2.2.2.2⟩ (by omega)
  (changePC_bound B _ 0 headRun.final_bound (by omega))
 have call:=UniformBoundedAssembly.boundedExecution_placed pair_code (by simp [UniformPairMachine.program_length];omega)
  (by omega) localRun
 rw [placed_reset _ fields.1] at call
 exact headRun.trans call

theorem ready_nat (s : State) (r : ℕ) (h0 : r≠0) (h1 : r≠1)
 (h2 : r≠2) (h5 : r≠2805) (h6 : r≠2806) :
 (ready s).natReg r=s.natReg r := by
 simp [ready,remainder,quotient,loads,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,
  h0,h1,h2,h5,h6]

theorem pair_final_nat (P A i : ℕ) (s : State) :
 (pairFinal P A i s).natReg=(ready s).natReg :=
 (UniformPairMachine.final_frame (setPC (ready s) 0) a b _ _).1

def round (P A i : ℕ) (s : State) : State :=
 setPC (writeNat (setPC (pairFinal P A i s) 27) 2804 (i+1)) 4

theorem round_header (P A Q i : ℕ) (s : State) (h : Header P A Q i s) :
 Header P A Q (i+1) (round P A i s) := by
 have keep (r : ℕ) (hr0 : r≠0) (hr1 : r≠1) (hr2 : r≠2)
  (hr4 : r≠2804) (hr5 : r≠2805) (hr6 : r≠2806) :
  (round P A i s).natReg r=s.natReg r:=by
   simp only [round,setPC,writeNat,next,pair_final_nat]
   rw [Function.update_of_ne hr4]
   exact ready_nat s r hr0 hr1 hr2 hr5 hr6
 rcases h with ⟨hpc,hp,ha,hq,hcount,hi,h1,h2⟩
 refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (keep 2800 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp
 · exact (keep 2801 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha
 · exact (keep 2802 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq
 · exact (keep 2803 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount
 · simp [round,setPC,writeNat,next]
 · exact (keep 2810 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1
 · exact (keep 2811 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2

theorem round_heap (P A i : ℕ) (s : State) :
 (round P A i s).scalarHeap=(pairFinal P A i s).scalarHeap := rfl

theorem round_constants (P A Q i : ℕ) (s : State) (h : Header P A Q i s)
 (hc : Constants s) (ha : 3≤A) : Constants (round P A i s) := by
 have hl:A≤left P A i:=by unfold left;omega
 have hr:A≤right P A i:=by unfold right;omega
 have eq:=pair_final_heap P A Q i s h hc
 unfold Constants
 rw [round_heap,eq]
 simpa [Constants,show 1≠left P A i by omega,show 1≠right P A i by omega,
  show 2≠left P A i by omega,show 2≠right P A i by omega] using hc

theorem round_present (P A Q i : ℕ) (s : State) (h : Header P A Q i s)
 (hc : Constants s) (present : Present A (P*2*Q) s) :
 Present A (P*2*Q) (round P A i s) := by
 intro j hj
 rw [round_heap,pair_final_heap P A Q i s h hc]
 by_cases hr:A+j=right P A i
 · simp [hr]
 · by_cases hl:A+j=left P A i
   · rw [Function.update_of_ne hr,hl];simp
   · simpa [hr,hl] using present j hj

theorem round_bounded (n B : ℕ) (x : Fin n→ℂ) (P A Q i : ℕ) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (hi : i<P*Q)
 (hc : Constants s) (present : Present A (P*2*Q) s)
 (hs : WordBound B s) (hcode : 30≤B) (extent : A+P*2*Q≤B) :
 BoundedRuns program n x B s 25 (round P A i s) := by
 have run:=pair_bounded n B x P A Q i s h hp hi hc present hs hcode extent
 have hv:i+1≤B:=by have hb:=hs.2.1 2803;rw [h.2.2.2.2.1] at hb;omega
 have hb:=writeNat_bound B (setPC (pairFinal P A i s) 27) 2804 (i+1)
  run.final_bound (by simp [setPC];omega) hv
 have finalBound:=changePC_bound B _ 4 hb (by omega)
 have endRun:BoundedRuns program n x B (setPC (pairFinal P A i s) 27) 2 (round P A i s):=by
  refine .next run.final_bound (u:=writeNat (setPC (pairFinal P A i s) 27) 2804 (i+1)) ?_
   (.next hb ?_ (.refl finalBound))
  · simp [step,increment_at,setPC,writeNat,next,evalNat,pair_final_nat,
    ready_nat s 2804 (by decide) (by decide) (by decide) (by decide) (by decide),
    ready_nat s 2810 (by decide) (by decide) (by decide) (by decide) (by decide),
    h.2.2.2.2.2.1,h.2.2.2.2.2.2.1]
  · simp [step,loop_jump_at,setPC,writeNat,next,round]
 exact run.trans endRun

def Kept (r : ℕ) : Prop :=
 r≠0 ∧ r≠1 ∧ r≠2 ∧ (r<2803 ∨ 2806<r) ∧ r≠2810 ∧ r≠2811
structure Frame (A L : ℕ) (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,Kept r→u.natReg r=s.natReg r
 scalarReg : ∀r,8≤r→u.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,z<A∨A+L≤z→u.scalarHeap z=s.scalarHeap z
theorem Frame.pc (A L : ℕ) (s : State) (pc : ℕ) : Frame A L s (setPC s pc) :=
 ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {A L : ℕ} {s u v : State} (f : Frame A L s u) (g : Frame A L u v) :
 Frame A L s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
  fun r h=>(g.natReg r h).trans (f.natReg r h),
  fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
  fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩

theorem frame_boot (A L : ℕ) (s : State) : Frame A L s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,?_,fun _ _=>rfl⟩
 · intro r hr
   dsimp only [Kept] at hr
   simp [boot,applyBlock,Op.apply,writeNat,next,hr.2.2.2.2.1,hr.2.2.2.2.2,
    show r≠2803 by omega,show r≠2804 by omega]
 · intro r hr;rfl

theorem frame_round (P A Q i : ℕ) (s : State) (h : Header P A Q i s)
 (hc : Constants s) (hi : i<P*Q) : Frame A (P*2*Q) s (round P A i s) := by
 have f:=UniformPairMachine.final_frame (setPC (ready s) 0) a b
  ((s.scalarHeap (left P A i)).getD Scalar.zero)
  ((s.scalarHeap (right P A i)).getD Scalar.zero)
 refine ⟨f.2.1,f.2.2.1,f.2.2.2.1,?_,?_,?_⟩
 · intro r hr
   dsimp only [Kept] at hr
   simp only [round,setPC,writeNat,next,pair_final_nat]
   rw [Function.update_of_ne (show r≠2804 by omega)]
   exact ready_nat s r hr.1 hr.2.1 hr.2.2.1 (by omega) (by omega)
 · intro r hr
   have h0:r≠0:=by omega
   have h1:r≠1:=by omega
   have eq:(pairFinal P A i s).scalarReg r=(ready s).scalarReg r:=f.2.2.2.2 r (Or.inr hr)
   change (pairFinal P A i s).scalarReg r=s.scalarReg r
   rw [eq]
   simp [ready,remainder,quotient,loads,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,h0,h1]
 · intro z hz
   rw [round_heap,pair_final_heap P A Q i s h hc]
   have range:=pair_range P A Q i hi
   simp [show z≠left P A i by omega,show z≠right P A i by omega]

def coordinate (P A Q : ℕ) (j : Fin (P*Q)) (t : Fin 2) : ℕ :=
 A+UniformTensorAddressMachine.address P 2 j.val t.val
def transformed {P Q : ℕ} (v : Fin (P*Q)→Fin 2→Scalar)
 (j : Fin (P*Q)) (t : Fin 2) : Scalar :=
 if t=0 then combine a b (v j 0) (v j 1) else combine b a (v j 0) (v j 1)
def Seen (P A Q i : ℕ) (v : Fin (P*Q)→Fin 2→Scalar) (s : State) : Prop :=
 ∀j t,s.scalarHeap (coordinate P A Q j t)=
  some (if j.val < i then transformed v j t else v j t)

theorem coordinate_injective (P A Q : ℕ) (j k : Fin (P*Q)) (t u : Fin 2)
 (h : coordinate P A Q j t=coordinate P A Q k u) : j=k ∧ t=u := by
 have he:(UniformTensorAddressMachine.fiberEquiv P 2 Q (j,t)).val=
  (UniformTensorAddressMachine.fiberEquiv P 2 Q (k,u)).val:=Nat.add_left_cancel h
 have eq: (j,t)=(k,u):=
  (UniformTensorAddressMachine.fiberEquiv P 2 Q).injective (Fin.ext he)
 exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩

theorem seen_present (P A Q i : ℕ) (v : Fin (P*Q)→Fin 2→Scalar) (s : State)
 (h : Seen P A Q i v s) : Present A (P*2*Q) s := by
 intro z hz
 obtain ⟨⟨j,t⟩,eq,_⟩:=UniformTensorAddressMachine.address_coverage P 2 Q ⟨z,hz⟩
 have hv:=h j t
 dsimp only [coordinate] at hv
 rw [eq] at hv
 simp [hv]

theorem seen_round (P A Q i : ℕ) (v : Fin (P*Q)→Fin 2→Scalar) (s : State)
 (h : Header P A Q i s) (hi : i<P*Q)
 (hc : Constants s) (seen : Seen P A Q i v s) :
 Seen P A Q (i+1) v (round P A i s) := by
 let current:Fin (P*Q):=⟨i,hi⟩
 have hv0:s.scalarHeap (left P A i)=some (v current 0):=by
  simpa [Seen,coordinate,left,current] using seen current 0
 have hv1:s.scalarHeap (right P A i)=some (v current 1):=by
  simpa [Seen,coordinate,right,current] using seen current 1
 have heaps:(round P A i s).scalarHeap=Function.update
  (Function.update s.scalarHeap (coordinate P A Q current 0) (some (transformed v current 0)))
  (coordinate P A Q current 1) (some (transformed v current 1)):=by
  rw [round_heap,pair_final_heap P A Q i s h hc,hv0,hv1]
  simp [coordinate,left,right,current,transformed]
 intro j t
 rw [heaps]
 by_cases hj:j=current
 · subst j
   have neq:coordinate P A Q current 0≠coordinate P A Q current 1:=by
    intro eq
    have hh:((0:Fin 2))=1:=(coordinate_injective P A Q current current 0 1 eq).2
    norm_num at hh
   fin_cases t
   · simp [neq,current]
   · simp [current]
 · have hn:j.val≠i:=by intro eq;apply hj;exact Fin.ext eq
   have hn0:coordinate P A Q j t≠coordinate P A Q current 0:=by
    intro eq;exact hj (coordinate_injective P A Q j current t 0 eq).1
   have hn1:coordinate P A Q j t≠coordinate P A Q current 1:=by
    intro eq;exact hj (coordinate_injective P A Q j current t 1 eq).1
   rw [Function.update_of_ne hn1,Function.update_of_ne hn0,seen j t]
   have same:j.val < i + 1↔j.val < i:=by omega
   simp only [same]

theorem loop_execution (n B : ℕ) (x : Fin n→ℂ) (P A Q i count : ℕ)
 (v : Fin (P*Q)→Fin 2→Scalar) (s : State)
 (h : Header P A Q i s) (hp : 0<P) (he : i+count=P*Q)
 (hc : Constants s) (seen : Seen P A Q i v s) (ha : 3≤A)
 (hs : WordBound B s) (hcode : 30≤B) (extent : A+P*2*Q≤B) :
 ∃u,BoundedExecution program n x B s (25*count+2) u ∧ Seen P A Q (P*Q) v u ∧
  Frame A (P*2*Q) s u := by
 induction count generalizing i s with
 | zero=>
  have hi:i=P*Q:=by omega
  have hb:=changePC_bound B s 29 hs (by omega)
  refine ⟨setPC s 29,.next hs (u:=setPC s 29) ?_ (.halt hb ?_),?_,Frame.pc _ _ _ _⟩
  · simp [step,branch_at,h.1,h.2.2.2.2.1,h.2.2.2.2.2.1,hi,setPC]
  · simp [step,setPC,halt_at]
  · simpa only [Seen,setPC,hi] using seen
 | succ count ih=>
  have hi:i<P*Q:=by omega
  have run:=round_bounded n B x P A Q i s h hp hi hc
   (seen_present P A Q i v s seen) hs hcode extent
  have header:=round_header P A Q i s h
  have constants:=round_constants P A Q i s h hc ha
  have done:=seen_round P A Q i v s h hi hc seen
  obtain ⟨u,rest,result,frame⟩:=ih (i+1) (round P A i s) header (by omega) constants done run.final_bound
  refine ⟨u,?_,result,(frame_round P A Q i s h hc hi).trans frame⟩
  have all:=run.executes rest
  convert all using 1
  omega

theorem boot_header (P A Q : ℕ) (s : State) (hpc : s.pc=0)
 (hp : s.natReg 2800=P) (ha : s.natReg 2801=A) (hq : s.natReg 2802=Q) :
 Header P A Q 0 (applyBlock boot s) := by
 simp [Header,boot,applyBlock,Op.apply,writeNat,next,hpc,hp,ha,hq]

/-- Complete actual stage. The input bank consists of arbitrary complete
    Scalars; no transformed data or intermediate execution is supplied. -/
theorem execution (n B : ℕ) (x : Fin n→ℂ) (P A Q : ℕ)
 (v : Fin (P*Q)→Fin 2→Scalar) (s : State)
 (hpc : s.pc=0) (hp : s.natReg 2800=P) (ha : s.natReg 2801=A)
 (hq : s.natReg 2802=Q) (hP : 0<P) (hA : 3≤A) (hc : Constants s)
 (data : ∀j t,s.scalarHeap (coordinate P A Q j t)=some (v j t))
 (hs : WordBound B s) (hcode : 30≤B) (extent : A+P*2*Q≤B) :
 ∃u,BoundedExecution program n x B s (25*(P*Q)+6) u ∧
  (∀j t,u.scalarHeap (coordinate P A Q j t)=some (transformed v j t)) ∧
  Frame A (P*2*Q) s u := by
 have hb:P*Q≤B:=by
  have eq:P*2*Q=2*(P*Q):=by ring
  rw [eq] at extent
  omega
 have read:readable boot s:=by simp [boot,readable,Op.readable]
 have cap:peak boot s≤B:=by
  simp [boot,peak,Op.peak,Op.apply,writeNat,next,hp,hq,hb,show 2≤B by omega ]
 have run:=block_runs boot program 0 n B x s boot_code hpc hs (by simp [boot];omega) read cap
 have header:=boot_header P A Q s hpc hp ha hq
 have constants:Constants (applyBlock boot s):=hc
 have seen:Seen P A Q 0 v (applyBlock boot s):=by
  intro j t;simpa [Seen,boot,applyBlock,Op.apply,writeNat,next] using data j t
 obtain ⟨u,rest,result,frame⟩:=loop_execution n B x P A Q 0 (P*Q) v (applyBlock boot s)
  header hP (by omega) constants seen hA run.final_bound hcode extent
 refine ⟨u,?_,?_,(frame_boot _ _ s).trans frame⟩
 · convert run.executes rest using 1
   simp only [boot_length]
   omega
 · intro j t;simpa only [Seen,ite_eq_left j.isLt] using result j t

theorem transformed_C {P Q : ℕ} (v : Fin (P*Q)→Fin 2→Scalar)
 (j : Fin (P*Q)) (t : Fin 2) :
 transformed v j t=⟨C.mulVec (fun d=>(v j d).value) t,
  (v j 0).dependent || (v j 1).dependent⟩ := by
 fin_cases t <;> simp [transformed,combine,C,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem runtime_volume (P Q : ℕ) : 25*(P*Q)+6≤13*(P*2*Q)+6 := by
 have he:P*2*Q=2*(P*Q):=by ring
 rw [he];omega

theorem Frame.constants {A L : ℕ} {s u : State} (h : Frame A L s u)
 (ha : 3≤A) (hc : Constants s) : Constants u := by
 rcases hc with ⟨hc,hd⟩
 exact ⟨(h.scalarHeap 1 (Or.inl (by omega))).trans hc,
  (h.scalarHeap 2 (Or.inl (by omega))).trans hd⟩

theorem canonical_code (n : ℕ) (hn : 0<n) : 30≤(n+2)^19 := by
 have small:30≤3^19:=by norm_num
 exact small.trans (Nat.pow_le_pow_left (by omega) 19)

theorem canonical_execution (n : ℕ) (hn : 0<n) (x : Fin n→ℂ) (P A Q : ℕ)
 (v : Fin (P*Q)→Fin 2→Scalar) (s : State)
 (hpc : s.pc=0) (hp : s.natReg 2800=P) (ha : s.natReg 2801=A)
 (hq : s.natReg 2802=Q) (hP : 0<P) (hA : 3≤A) (hc : Constants s)
 (data : ∀j t,s.scalarHeap (coordinate P A Q j t)=some (v j t))
 (hs : WordBound ((n+2)^19) s) (extent : A+P*2*Q≤(n+2)^19) :
 ∃u,BoundedExecution program n x ((n+2)^19) s (25*(P*Q)+6) u ∧
  (∀j t,u.scalarHeap (coordinate P A Q j t)=
   some ⟨C.mulVec (fun d=>(v j d).value) t,(v j 0).dependent || (v j 1).dependent⟩) ∧
  Frame A (P*2*Q) s u ∧ Constants u := by
 obtain ⟨u,run,result,frame⟩:=execution n _ x P A Q v s hpc hp ha hq hP hA hc data hs
  (canonical_code n hn) extent
 exact ⟨u,run,fun j t=>by rw [result j t,transformed_C],frame,frame.constants hA hc⟩

end
end ExactFourierCircuits.UniformBinaryCStageMachine
