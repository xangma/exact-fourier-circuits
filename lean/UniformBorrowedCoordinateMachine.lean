import UniformReciprocalMachine
import UniformWorkspacePlanner
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Nodup

set_option autoImplicit false
namespace ExactFourierCircuits.UniformBorrowedCoordinateMachine
open UniformMachine
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)

/-- Scan the local coordinates in increasing order, excluding two contiguous
blocks. Nat261=source offset,262=source width,263=target offset,264=target width,
265=borrowed count,266=output table. Nat267..272 are scratch. -/
def program : Program := [
  .natLiteral 267 0,.natLiteral 268 0,.natLiteral 269 1,
  .natBinary .add 270 261 262,.natBinary .add 271 263 264,
  .branchLT 268 265 6 16,
  .branchLT 267 270 7 8,.branchLT 267 261 8 14,
  .branchLT 267 271 9 10,.branchLT 267 263 10 14,
  .natBinary .add 272 266 268,.storeNat 272 267,
  .natBinary .add 268 268 269,.jump 14,
  .natBinary .add 267 267 269,.jump 5,.halt]

theorem program_length : program.length=17 := rfl

def Eligible (s e t a i : ℕ) : Prop :=
  (i < s ∨ s+e ≤ i) ∧ (i < t ∨ t+a ≤ i)
instance (s e t a i : ℕ) : Decidable (Eligible s e t a i) :=
  inferInstanceAs (Decidable ((i < s ∨ s+e ≤ i) ∧ (i < t ∨ t+a ≤ i)))

def available (v s e t a : ℕ) : List ℕ :=
  (List.range v).filter (fun i=>decide (Eligible s e t a i))

theorem available_mem {v s e t a i : ℕ} :
    i ∈ available v s e t a ↔ i < v ∧ Eligible s e t a i := by
  simp [available]

theorem available_nodup (v s e t a : ℕ) : (available v s e t a).Nodup :=
  List.nodup_range.filter _

theorem available_succ (v s e t a : ℕ) :
    available (v+1) s e t a=available v s e t a ++
      (if Eligible s e t a v then [v] else []) := by
  by_cases h:Eligible s e t a v <;>
    simp [available,List.range_succ,List.filter_append,h]

/-- The measured fit condition supplies enough distinct physical coordinates.
Overlapping excluded blocks are permitted; no complex-data test is used. -/
theorem available_capacity (v s e t a g : ℕ) (hfit:g+e+a ≤ v) :
    g ≤ (available v s e t a).length := by
  let good := (Finset.range v).filter (Eligible s e t a)
  let bad := Finset.Ico s (s+e) ∪ Finset.Ico t (t+a)
  have cover : Finset.range v ⊆ good ∪ bad := by
    intro i hi
    by_cases h:Eligible s e t a i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,h⟩)
    · apply Finset.mem_union_right
      simp only [bad,Finset.mem_union,Finset.mem_Ico]
      unfold Eligible at h
      omega
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le good bad
  have hb := Finset.card_union_le (Finset.Ico s (s+e)) (Finset.Ico t (t+a))
  have hgood : good.card=(available v s e t a).length := by
    rw [←List.toFinset_card_of_nodup (available_nodup v s e t a)]
    simp [good,available,List.toFinset_filter,List.toFinset_range]
  simp only [Finset.card_range] at hc
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at hb
  change bad.card ≤ e+a at hb
  rw [hgood] at hu
  omega

noncomputable section

def Headers (s e t a g d : ℕ) (u : State) : Prop :=
  u.natReg 261=s ∧ u.natReg 262=e ∧ u.natReg 263=t ∧
  u.natReg 264=a ∧ u.natReg 265=g ∧ u.natReg 266=d

structure Cursor (s e t a g d i j : ℕ) (u : State) : Prop where
  headers : Headers s e t a g d u
  index : u.natReg 267=i
  count : u.natReg 268=j
  one : u.natReg 269=1
  sourceEnd : u.natReg 270=s+e
  targetEnd : u.natReg 271=t+a

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀r,(r < 267 ∨ 273 ≤ r)→u.natReg r=s.natReg r

def Outside (d g : ℕ) (s u : State) : Prop :=
  ∀i,(i < d ∨ d+g ≤ i)→u.natHeap i=s.natHeap i

def initOps : List Op := [.literal 267 0,.literal 268 0,.literal 269 1,
  .add 270 261 262,.add 271 263 264]
theorem init_code : BlockAt initOps program 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl

theorem initialized (n : ℕ) (x : Fin n→ℂ) (s e t a g d B : ℕ) (u : State)
    (hh:Headers s e t a g d u) (hp:u.pc=0) (hs:WordBound B u)
    (hB:17 ≤ B) (he:s+e ≤ B) (ha:t+a ≤ B) :
    BoundedRuns program n x B u 5 (applyBlock initOps u) ∧
    Cursor s e t a g d 0 0 (applyBlock initOps u) ∧
    (applyBlock initOps u).pc=5 ∧ Frame u (applyBlock initOps u) ∧
    (applyBlock initOps u).natHeap=u.natHeap := by
  rcases hh with ⟨h261,h262,h263,h264,h265,h266⟩
  refine ⟨?_,?_,?_,?_,rfl⟩
  · apply block_runs initOps program 0 n B x u init_code hp hs (by change 0+5 ≤ B;omega)
    · simp [readable,initOps,Op.readable]
    · simp [peak,initOps,Op.peak,Op.apply,writeNat,next,h261,h262,h263,h264];omega
  · constructor <;> simp [initOps,applyBlock,Op.apply,writeNat,next,
      Headers,h261,h262,h263,h264,h265,h266]
  · simp [applyBlock,initOps,Op.apply,writeNat,next,hp]
  · refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro r hr
    simp (disch:=omega) [applyBlock,initOps,Op.apply,writeNat,next]

theorem pc_run (n : ℕ) (x : Fin n→ℂ) (B : ℕ) (u : State) (pc : ℕ)
    (hs:WordBound B u) (hp:pc ≤ B)
    (hc:step program n x u=.running {u with pc:=pc}) :
    BoundedRuns program n x B u 1 {u with pc:=pc} :=
  .next hs hc (.refl (changePC_bound B u pc hs hp))

theorem Cursor.withPC {s e t a g d i j pc : ℕ} {u : State}
    (h:Cursor s e t a g d i j u) : Cursor s e t a g d i j {u with pc:=pc} := by
  cases h;constructor <;> assumption

theorem target_branch (n : ℕ) (x : Fin n→ℂ) (B i t a : ℕ) (u : State)
    (hs:WordBound B u) (hB:17 ≤ B) (hp:u.pc=8)
    (hi:u.natReg 267=i) (ht:u.natReg 263=t) (he:u.natReg 271=t+a) :
    ∃c,c ≤ 2 ∧ BoundedRuns program n x B u c
      {u with pc:=if i < t ∨ t+a ≤ i then 10 else 14} := by
  by_cases hend:i < t+a
  · have h1:=pc_run n x B u 9 hs (by omega) (by
      simp [UniformMachine.step,program,hp,hi,he,hend])
    by_cases hleft:i < t
    · have h2:=pc_run n x B {u with pc:=9} 10 h1.final_bound (by omega) (by
        simp [UniformMachine.step,program,hi,ht,hleft])
      refine ⟨2,by omega,?_⟩
      simpa [hleft] using h1.trans h2
    · have h2:=pc_run n x B {u with pc:=9} 14 h1.final_bound (by omega) (by
        simp [UniformMachine.step,program,hi,ht,hleft])
      refine ⟨2,by omega,?_⟩
      simpa [hleft,show ¬t+a ≤ i by omega] using h1.trans h2
  · have h1:=pc_run n x B u 10 hs (by omega) (by
      simp [UniformMachine.step,program,hp,hi,he,hend])
    exact ⟨1,by omega,by simpa [show t+a ≤ i by omega] using h1⟩

theorem branch_prefix (n : ℕ) (x : Fin n→ℂ) (s e t a g d i j B : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hs:WordBound B u) (hB:17 ≤ B)
    (hp:u.pc=5) (hj:j < g) : ∃c,c ≤ 5 ∧ BoundedRuns program n x B u c
      {u with pc:=if Eligible s e t a i then 10 else 14} := by
  have h1:=pc_run n x B u 6 hs (by omega) (by
    simp [UniformMachine.step,program,hp,hc.count,hc.headers.2.2.2.2.1,hj])
  by_cases hend:i < s+e
  · have h2:=pc_run n x B {u with pc:=6} 7 h1.final_bound (by omega) (by
      simp [UniformMachine.step,program,hc.index,hc.sourceEnd,hend])
    by_cases hleft:i < s
    · have h3:=pc_run n x B {u with pc:=7} 8 h2.final_bound (by omega) (by
        simp [UniformMachine.step,program,hc.index,hc.headers.1,hleft])
      obtain ⟨c,cb,hr⟩:=target_branch n x B i t a {u with pc:=8} h3.final_bound
        hB rfl hc.index hc.headers.2.2.1 hc.targetEnd
      refine ⟨1+1+1+c,by omega,?_⟩
      simpa [Eligible,hleft] using ((h1.trans h2).trans h3).trans hr
    · have h3:=pc_run n x B {u with pc:=7} 14 h2.final_bound (by omega) (by
        simp [UniformMachine.step,program,hc.index,hc.headers.1,hleft])
      refine ⟨3,by omega,?_⟩
      simpa [Eligible,hleft,show ¬s+e ≤ i by omega] using (h1.trans h2).trans h3
  · have h2:=pc_run n x B {u with pc:=6} 8 h1.final_bound (by omega) (by
      simp [UniformMachine.step,program,hc.index,hc.sourceEnd,hend])
    obtain ⟨c,cb,hr⟩:=target_branch n x B i t a {u with pc:=8} h2.final_bound
      hB rfl hc.index hc.headers.2.2.1 hc.targetEnd
    refine ⟨1+1+c,by omega,?_⟩
    simpa [Eligible,show s+e ≤ i by omega] using (h1.trans h2).trans hr

def advanced (u : State) : State :=
  {writeNat {u with pc:=14} 267 (u.natReg 267+u.natReg 269) with pc:=5}

theorem advance_run (n : ℕ) (x : Fin n→ℂ) (B : ℕ) (u : State)
    (hs:WordBound B u) (hB:17 ≤ B) (hp:u.pc=14)
    (hi:u.natReg 267+u.natReg 269 ≤ B) :
    BoundedRuns program n x B u 2 (advanced u) := by
  have hw:=writeNat_bound B u 267 _ hs (by omega) hi
  have h2:=pc_run n x B (writeNat u 267 (u.natReg 267+u.natReg 269)) 5 hw (by omega) (by
    simp [UniformMachine.step,program,writeNat,next,hp])
  have h1:BoundedRuns program n x B u 1 (writeNat u 267 (u.natReg 267+u.natReg 269)):=
    .next hs (by simp [UniformMachine.step,program,hp,evalNat]) (.refl hw)
  simpa [advanced,writeNat,next] using h1.trans h2

def addressed (u : State) : State := writeNat {u with pc:=10} 272
  (u.natReg 266+u.natReg 268)
def stored (u : State) : State :=
  {next (addressed u) with natHeap:=(Function.update u.natHeap
    (u.natReg 266+u.natReg 268) (some (u.natReg 267)))}
def counted (u : State) : State := writeNat (stored u) 268
  (u.natReg 268+u.natReg 269)
def emitted (u : State) : State := advanced (counted u)

theorem store_bound (B : ℕ) (u : State) (address value : ℕ) (hs:WordBound B u)
    (hp:u.pc+1 ≤ B) (ha:address ≤ B) (hv:value ≤ B) :
    WordBound B {next u with natHeap:=Function.update u.natHeap address (some value)} := by
  refine ⟨hp,hs.2.1,?_,hs.2.2.2⟩
  intro i v hi
  by_cases h:i=address
  · subst i
    have he:v=value:=by simpa only [Function.update_self,Option.some.injEq] using hi.symm
    exact ⟨ha,he ▸ hv⟩
  · exact hs.2.2.1 i v (by simpa only [Function.update_of_ne h] using hi)

theorem emit_run (n : ℕ) (x : Fin n→ℂ) (s e t a g d i j v B : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hs:WordBound B u) (hB:17 ≤ B)
    (hp:u.pc=10) (hj:j < g) (hi:i < v) (hv:v ≤ B) (hd:d+g ≤ B) :
    BoundedRuns program n x B u 6 (emitted u) := by
  have haddr:WordBound B (addressed u):=writeNat_bound B {u with pc:=10} 272 _
    (changePC_bound B u 10 hs (by omega)) (by change 10+1 ≤ B;omega)
    (by rw [hc.headers.2.2.2.2.2,hc.count];omega)
  have h1:BoundedRuns program n x B u 1 (addressed u):=.next hs
    (by simp [UniformMachine.step,program,hp,addressed,evalNat,writeNat,next]) (.refl haddr)
  have hstore:WordBound B (stored u):=store_bound B (addressed u)
    (u.natReg 266+u.natReg 268) (u.natReg 267) haddr
    (by change 11+1 ≤ B;omega) (by rw [hc.headers.2.2.2.2.2,hc.count];omega)
    (by rw [hc.index];omega)
  have h2:BoundedRuns program n x B (addressed u) 1 (stored u):=.next haddr
    (by simp [UniformMachine.step,program,addressed,stored,writeNat,next]) (.refl hstore)
  have hcount:WordBound B (counted u):=writeNat_bound B (stored u) 268 _ hstore
    (by change 12+1 ≤ B;omega) (by rw [hc.count,hc.one];omega)
  have h3:BoundedRuns program n x B (stored u) 1 (counted u):=.next hstore
    (by simp [UniformMachine.step,program,stored,addressed,counted,writeNat,next,evalNat]) (.refl hcount)
  have h4:=pc_run n x B (counted u) 14 hcount (by omega) (by
    simp [UniformMachine.step,program,counted,stored,addressed,writeNat,next])
  have h5:=advance_run n x B {counted u with pc:=14} h4.final_bound hB rfl (by
    simp [counted,stored,addressed,writeNat,next,hc.index,hc.one];omega)
  simpa [emitted,advanced] using (((h1.trans h2).trans h3).trans h4).trans h5

def iteration (s e t a i : ℕ) (u : State) : State :=
  if Eligible s e t a i then emitted u else advanced u

theorem iteration_pc (s e t a i : ℕ) (u : State) : (iteration s e t a i u).pc=5 := by
  unfold iteration
  split_ifs <;> rfl

theorem iteration_cursor (s e t a g d i j : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) :
    Cursor s e t a g d (i+1) (if Eligible s e t a i then j+1 else j)
      (iteration s e t a i u) := by
  rcases hc with ⟨⟨h261,h262,h263,h264,h265,h266⟩,h267,h268,h269,h270,h271⟩
  by_cases h:Eligible s e t a i <;>
    constructor <;> simp [iteration,h,emitted,advanced,counted,stored,addressed,
      writeNat,next,Headers,h261,h262,h263,h264,h265,h266,h267,h268,h269,h270,h271]

theorem iteration_heap (s e t a g d i j : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) :
    (iteration s e t a i u).natHeap=
      if Eligible s e t a i then Function.update u.natHeap (d+j) (some i) else u.natHeap := by
  by_cases h:Eligible s e t a i <;>
    simp [iteration,h,emitted,advanced,counted,stored,addressed,writeNat,next,
      hc.index,hc.count,hc.headers.2.2.2.2.2]

theorem iteration_frame (s e t a i : ℕ) (u : State) : Frame u (iteration s e t a i u) := by
  by_cases h:Eligible s e t a i <;> simp only [iteration,h,ite_true,ite_false]
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals
    intro r hr
    simp (disch:=omega) [emitted,advanced,counted,stored,addressed,writeNat,next]

theorem iteration_outside (s e t a g d i j : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hj:j < g) : Outside d g u (iteration s e t a i u) := by
  intro z hz
  rw [iteration_heap s e t a g d i j u hc]
  by_cases h:Eligible s e t a i
  · simp only [h,ite_true,Function.update_of_ne (by omega : z≠d+j)]
  · simp [h]

theorem iteration_run (n : ℕ) (x : Fin n→ℂ) (s e t a g d i j v B : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hs:WordBound B u) (hB:17 ≤ B)
    (hp:u.pc=5) (hj:j < g) (hi:i < v) (hv:v ≤ B) (hd:d+g ≤ B) :
    ∃c,c ≤ 11 ∧ BoundedRuns program n x B u c (iteration s e t a i u) := by
  obtain ⟨c,hcBound,hr⟩:=branch_prefix n x s e t a g d i j B u hc hs hB hp hj
  by_cases h:Eligible s e t a i
  · have hr':BoundedRuns program n x B u c {u with pc:=10}:=by simpa only [h,ite_true] using hr
    have he:=emit_run n x s e t a g d i j v B {u with pc:=10} hc.withPC
      hr'.final_bound hB rfl hj hi hv hd
    refine ⟨c+6,by omega,?_⟩
    simpa [iteration,h,emitted,advanced,counted,stored,addressed,writeNat,next] using hr'.trans he
  · have hr':BoundedRuns program n x B u c {u with pc:=14}:=by simpa only [h,ite_false] using hr
    have he:=advance_run n x B {u with pc:=14} hr'.final_bound hB rfl (by
      simp only [hc.index,hc.one];omega)
    refine ⟨c+2,by omega,?_⟩
    simpa [iteration,h,advanced,writeNat,next] using hr'.trans he

def Filled (d : ℕ) (xs : List ℕ) (u : State) : Prop :=
  ∀j,(hj:j < xs.length)→u.natHeap (d+j)=some (xs[j]'hj)

theorem iteration_filled (s e t a g d i j : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hj:j=(available i s e t a).length)
    (hf:Filled d (available i s e t a) u) :
    Filled d (available (i+1) s e t a) (iteration s e t a i u) := by
  intro k hk
  rw [iteration_heap s e t a g d i j u hc]
  by_cases h:Eligible s e t a i
  · simp only [h,ite_true]
    have hav:available (i+1) s e t a=available i s e t a++[i]:=by
      simp only [available_succ,h,ite_true]
    by_cases hkj:k < j
    · rw [Function.update_of_ne (by omega : d+k≠d+j)]
      have he:(available (i+1) s e t a)[k]'hk=(available i s e t a)[k]'(by omega):=by
        simp only [hav,List.getElem_append_left (by omega : k < (available i s e t a).length)]
      rw [he];exact hf k (by omega)
    · have hklen:k < j+1:=by simpa only [hav,List.length_append,List.length_cons,List.length_nil,hj] using hk
      have he:k=j:=by omega
      subst k
      simp only [Function.update_self,Option.some.injEq]
      simp [hav,hj]
  · simp only [h,ite_false]
    have hav:available (i+1) s e t a=available i s e t a:=by simp only [available_succ,h,ite_false,List.append_nil]
    simpa only [hav] using hf k (by simpa only [hav] using hk)

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
theorem Outside.trans {d g : ℕ} {s u v : State} (h:Outside d g s u) (h':Outside d g u v) :
    Outside d g s v := fun i hi=>(h' i hi).trans (h i hi)

structure Outcome (s e t a g d start v k : ℕ) (u w : State) : Prop where
  start_le : start ≤ k
  end_le : k ≤ v
  cursor : Cursor s e t a g d k g w
  halt : w.pc=16
  length : g=(available k s e t a).length
  filled : Filled d (available k s e t a) w
  frame : Frame u w
  outside : Outside d g u w

theorem finish (n : ℕ) (x : Fin n→ℂ) (s e t a g d i v B : ℕ) (u : State)
    (hc:Cursor s e t a g d i g u) (hs:WordBound B u) (hB:17 ≤ B)
    (hp:u.pc=5) (hi:i ≤ v) (hl:g=(available i s e t a).length)
    (hf:Filled d (available i s e t a) u) :
    ∃w,BoundedExecution program n x B u 2 w ∧ Outcome s e t a g d i v i u w := by
  let w:State:={u with pc:=16}
  have hw:WordBound B w:=changePC_bound B u 16 hs (by omega)
  have halt:BoundedExecution program n x B w 1 w:=.halt hw
    (by simp [UniformMachine.step,program,w])
  refine ⟨w,.next hs ?_ halt,?_,⟩
  · simp [UniformMachine.step,program,hp,hc.count,hc.headers.2.2.2.2.1,w]
  · exact ⟨le_refl _,hi,hc.withPC,rfl,hl,hf,⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩,fun _ _=>rfl⟩

/-- Fuel is the remaining local coordinate interval, not a supplied execution
certificate. The capacity inequality rules out exhausting it before filling. -/
theorem loop (n : ℕ) (x : Fin n→ℂ) (s e t a g d i j v fuel B : ℕ) (u : State)
    (hc:Cursor s e t a g d i j u) (hs:WordBound B u) (hB:17 ≤ B)
    (hp:u.pc=5) (hend:i+fuel=v) (hv:v ≤ B) (hd:d+g ≤ B)
    (hj:j ≤ g) (hl:j=(available i s e t a).length)
    (hcap:g ≤ (available v s e t a).length) (hf:Filled d (available i s e t a) u) :
    ∃c k w,BoundedExecution program n x B u c w ∧ c ≤ 11*fuel+2 ∧
      Outcome s e t a g d i v k u w := by
  induction fuel generalizing i j u with
  | zero =>
    have he:i=v:=by omega
    have hstop:j=g:=by rw [←he,←hl] at hcap;omega
    have hcStop:Cursor s e t a g d i g u:=by simpa only [hstop] using hc
    have hlStop:g=(available i s e t a).length:=hstop.symm.trans hl
    obtain ⟨w,hr,ho⟩:=finish n x s e t a g d i v B u hcStop hs hB hp (by omega) hlStop hf
    exact ⟨2,i,w,hr,by omega,ho⟩
  | succ fuel ih =>
    by_cases hstop:j=g
    · have hcStop:Cursor s e t a g d i g u:=by simpa only [hstop] using hc
      have hlStop:g=(available i s e t a).length:=hstop.symm.trans hl
      obtain ⟨w,hr,ho⟩:=finish n x s e t a g d i v B u hcStop hs hB hp (by omega) hlStop hf
      exact ⟨2,i,w,hr,by omega,ho⟩
    · have hjg:j < g:=by omega
      obtain ⟨c,hcb,hr⟩:=iteration_run n x s e t a g d i j v B u hc hs hB hp hjg
        (by omega) hv hd
      have hc':=iteration_cursor s e t a g d i j u hc
      have hl':(if Eligible s e t a i then j+1 else j)=(available (i+1) s e t a).length:=by
        by_cases h:Eligible s e t a i <;> simp [available_succ,h,hl]
      have hj':(if Eligible s e t a i then j+1 else j) ≤ g:=by split_ifs <;> omega
      obtain ⟨c',k,w,hr',hcb',ho⟩:=ih (i+1) (if Eligible s e t a i then j+1 else j)
        (iteration s e t a i u) hc' hr.final_bound (iteration_pc s e t a i u)
        (by omega) hj' hl' (iteration_filled s e t a g d i j u hc hl hf)
      refine ⟨c+c',k,w,hr.executes hr',by omega,?_,⟩
      exact ⟨by have h:=ho.start_le;omega,ho.end_le,ho.cursor,ho.halt,ho.length,ho.filled,
        (iteration_frame s e t a i u).trans ho.frame,
        (iteration_outside s e t a g d i j u hc hjg).trans ho.outside⟩

theorem available_prefix (i v s e t a : ℕ) (hi:i ≤ v) :
    ∃tail,available v s e t a=available i s e t a++tail := by
  obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le hi
  subst v
  induction q with
  | zero => exact ⟨[],by simp⟩
  | succ q ih =>
    obtain ⟨tail,ht⟩:=ih (by omega)
    refine ⟨tail++(if Eligible s e t a (i+q) then [i+q] else []),?_⟩
    rw [show i+(q+1)=i+q+1 by omega,available_succ,ht,List.append_assoc]

def borrowed (v s e t a g : ℕ) : List ℕ := (available v s e t a).take g

/-- Full execution from dirty workspace. The only capacity premise is the
paper's measured integer fit. The resulting physical table is the first g
available local coordinates; all scalar data and protected state survive. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (v s e t a g d B : ℕ) (u : State)
    (hh:Headers s e t a g d u) (hp:u.pc=0) (hs:WordBound B u)
    (hB:17 ≤ B) (hv:v ≤ B) (he:s+e ≤ B) (ha:t+a ≤ B) (hd:d+g ≤ B)
    (hfit:g+e+a ≤ v) : ∃c w,
    BoundedExecution program n x B u c w ∧ c ≤ 11*v+7 ∧
    w.pc=16 ∧ w.natReg 268=g ∧ Filled d (borrowed v s e t a g) w ∧
    Frame u w ∧ Outside d g u w := by
  obtain ⟨hinit,hcursor,hipc,hframe,hheap⟩:=initialized n x s e t a g d B u hh hp hs hB he ha
  have hlen:0=(available 0 s e t a).length:=by simp [available]
  have hfilled:Filled d (available 0 s e t a) (applyBlock initOps u):=by
    intro j hj;simp [available] at hj
  obtain ⟨c,k,w,hr,hcost,ho⟩:=loop n x s e t a g d 0 0 v v B (applyBlock initOps u)
    hcursor hinit.final_bound hB hipc (by omega) hv hd (by omega) hlen
    (available_capacity v s e t a g hfit) hfilled
  obtain ⟨tail,ht⟩:=available_prefix k v s e t a ho.end_le
  have hborrow:borrowed v s e t a g=available k s e t a:=by
    rw [borrowed,ht,ho.length,List.take_left]
  refine ⟨5+c,w,hinit.executes hr,by omega,ho.halt,ho.cursor.count,?_,hframe.trans ho.frame,?_⟩
  · simpa only [hborrow] using ho.filled
  · intro i hi
    exact (ho.outside i hi).trans (congrFun hheap i)

theorem borrowed_length (v s e t a g : ℕ) (hfit:g+e+a ≤ v) :
    (borrowed v s e t a g).length=g := by
  rw [borrowed,List.length_take,min_eq_left (available_capacity v s e t a g hfit)]

theorem borrowed_nodup (v s e t a g : ℕ) : (borrowed v s e t a g).Nodup :=
  (available_nodup v s e t a).take

theorem borrowed_mem {v s e t a g z : ℕ} (hz:z∈borrowed v s e t a g) :
    z < v ∧ Eligible s e t a z := by
  exact available_mem.mp (List.mem_of_mem_take hz)

/-- Explicit finite coordinates of the emitted physical table, without a
choice of a labeling for the available set. -/
def embedding (v s e t a g : ℕ) (hfit:g+e+a ≤ v) : Fin g ↪ Fin v where
  toFun j:=⟨(borrowed v s e t a g)[j.val]'(by rw [borrowed_length v s e t a g hfit];exact j.isLt),
    (borrowed_mem (List.getElem_mem (by rw [borrowed_length v s e t a g hfit];exact j.isLt))).1⟩
  inj' i j h:=by
    apply Fin.ext
    have hv:=congrArg Fin.val h
    exact (borrowed_nodup v s e t a g).getElem_inj_iff.mp hv

theorem embedding_eligible (v s e t a g : ℕ) (hfit:g+e+a ≤ v) (j : Fin g) :
    Eligible s e t a (embedding v s e t a g hfit j).val :=
  (borrowed_mem (List.getElem_mem (by rw [borrowed_length v s e t a g hfit];exact j.isLt))).2

theorem embedding_excludes (v s e t a g : ℕ) (hfit:g+e+a ≤ v) (j : Fin g) :
    ¬(s ≤ (embedding v s e t a g hfit j).val ∧ (embedding v s e t a g hfit j).val < s+e) ∧
    ¬(t ≤ (embedding v s e t a g hfit j).val ∧ (embedding v s e t a g hfit j).val < t+a) := by
  have h:=embedding_eligible v s e t a g hfit j
  unfold Eligible at h
  omega

theorem physical_embedding (n : ℕ) (x : Fin n→ℂ) (v s e t a g d B : ℕ) (u : State)
    (hh:Headers s e t a g d u) (hp:u.pc=0) (hs:WordBound B u)
    (hB:17 ≤ B) (hv:v ≤ B) (he:s+e ≤ B) (ha:t+a ≤ B) (hd:d+g ≤ B)
    (hfit:g+e+a ≤ v) : ∃c w,
    BoundedExecution program n x B u c w ∧ c ≤ 11*v+7 ∧
    (∀j:Fin g,w.natHeap (d+j.val)=some (embedding v s e t a g hfit j).val) ∧
    Frame u w ∧ Outside d g u w := by
  obtain ⟨c,w,hr,hcost,_hpc,_hcount,hfilled,hframe,houtside⟩:=execution n x
    v s e t a g d B u hh hp hs hB hv he ha hd hfit
  exact ⟨c,w,hr,hcost,fun j=>hfilled j.val (by rw [borrowed_length v s e t a g hfit];exact j.isLt),
    hframe,houtside⟩

/-- The measured selected-chunk theorem supplies the capacity condition for
the actual printed graph size; no additional workspace certificate is needed. -/
theorem selected_execution (n : ℕ) (x : Fin n→ℂ) (v s e t a d B : ℕ) (u : State)
    (hselected:0 < UniformWorkspacePlanner.selected v)
    (htarget:a∈UniformWorkspacePlanner.chunkSizes (v-v/2) (UniformWorkspacePlanner.selected v))
    (hsource:e∈UniformWorkspacePlanner.chunkSizes (v/2) (UniformWorkspacePlanner.selected v))
    (hh:Headers s e t a (UniformWorkspacePlanner.gateCount a e) d u)
    (hp:u.pc=0) (hs:WordBound B u) (hB:17 ≤ B) (hv:v ≤ B)
    (he:s+e ≤ B) (ha:t+a ≤ B) (hd:d+UniformWorkspacePlanner.gateCount a e ≤ B) :
    ∃c w,BoundedExecution program n x B u c w ∧ c ≤ 11*v+7 ∧
      Filled d (borrowed v s e t a (UniformWorkspacePlanner.gateCount a e)) w ∧
      Frame u w ∧ Outside d (UniformWorkspacePlanner.gateCount a e) u w := by
  have hfit:UniformWorkspacePlanner.gateCount a e+e+a ≤ v:=by
    have h:=UniformWorkspacePlanner.selected_fit hselected htarget hsource
    omega
  obtain ⟨c,w,hr,hcost,_hpc,_hcount,hfilled,hframe,houtside⟩:=execution n x v s e t a
    (UniformWorkspacePlanner.gateCount a e) d B u hh hp hs hB hv he ha hd hfit
  exact ⟨c,w,hr,hcost,hfilled,hframe,houtside⟩

end
end ExactFourierCircuits.UniformBorrowedCoordinateMachine
