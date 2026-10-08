import UniformTensorMonomialMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformContiguousPowerBankMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)

/-- Nat550=length,551=actual prepared root address,552=destination.
Only Nat553..555 and Scalar60..61 are scratch. -/
def boot : List Op := [.literal 553 0,.literal 554 1,.literalScalar 60 1,.getScalar 61 551]
def body : List Op := [.add 555 552 553,.putScalar 555 60,
  .scalarMul 60 60 61,.add 553 553 554]
def program : Program := boot.map Op.code ++ [.branchLT 553 550 5 10] ++
  body.map Op.code ++ [.jump 4,.halt]
theorem program_length : program.length=11 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi; change i<4 at hi; interval_cases i <;> rfl
theorem body_code : BlockAt body program 5 := by
  intro i hi; change i<4 at hi; interval_cases i <;> rfl
theorem branch_at : program[4]?=some (.branchLT 553 550 5 10) := rfl
theorem jump_at : program[9]?=some (.jump 4) := rfl
theorem halt_at : program[10]?=some .halt := rfl

noncomputable section
structure Header (N Q P : ℕ) (s : State) : Prop where
  length : s.natReg 550=N
  source : s.natReg 551=Q
  target : s.natReg 552=P

structure Cursor (N Q P i : ℕ) (omega : ℂ) (s : State) : Prop where
  header : Header N Q P s
  pc : s.pc=4
  index : s.natReg 553=i
  one : s.natReg 554=1
  power : s.scalarReg 60=prepared (omega^i)
  root : s.scalarReg 61=prepared omega

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,(r<553 ∨ 556≤r)→u.natReg r=s.natReg r) ∧
  (∀r,(r<60 ∨ 62≤r)→u.scalarReg r=s.scalarReg r)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

def iteration (s : State) := setPC (applyBlock body (setPC s 5)) 4
def Outside (P N : ℕ) (s u : State) :=
  ∀j,(j<P ∨ P+N≤j)→u.scalarHeap j=s.scalarHeap j

theorem iteration_heap {N Q P i : ℕ} {omega : ℂ} {s : State}
    (h:Cursor N Q P i omega s) :
    (iteration s).scalarHeap=Function.update s.scalarHeap (P+i) (some (prepared (omega^i))) := by
  simp [iteration,body,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,
    h.header.target,h.index,h.power]

theorem iteration_cursor {N Q P i : ℕ} {omega : ℂ} {s : State}
    (h:Cursor N Q P i omega s) : Cursor N Q P (i+1) omega (iteration s) := by
  refine ⟨⟨?_,?_,?_⟩,rfl,?_,?_,?_,?_⟩
  all_goals simp [iteration,body,applyBlock,Op.apply,setPC,writeNat,writeScalar,next,
    h.header.length,h.header.source,h.header.target,h.index,h.one,h.power,h.root,
    prepared,evalField,pow_succ]

theorem iteration_frame (s : State) : Frame s (iteration s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [iteration,body,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next]

theorem iteration_bounded {N Q P i : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (omega : ℂ) (s : State) (h:Cursor N Q P i omega s) (hi:i<N)
    (hB:11≤B) (hP:P+N≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 6 (iteration s) := by
  let e:=setPC s 5
  have he:WordBound B e:=changePC_bound B s 5 hs (by omega)
  have hr:readable body e:=by
    simp [readable,body,Op.readable,Op.apply,setPC,e,writeNat,next,
      h.power,h.root,prepared,evalField]
  have hb:peak body e≤B:=by
    simp [peak,body,Op.peak,Op.apply,setPC,e,writeNat,writeScalar,next,
      h.header.target,h.index,h.one]
    omega
  have run:=block_runs body program 5 n B x e body_code rfl he (by change 5+4≤B;omega) hr hb
  have hp:(applyBlock body e).pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have enter:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [step,h.pc,branch_at,h.index,h.header.length,hi,e,setPC]) (.refl he)
  have jump:BoundedRuns program n x B (applyBlock body e) 1 (iteration s):=
    .next run.final_bound (by rw [step,hp,jump_at];rfl)
      (.refl (changePC_bound B _ 4 run.final_bound (by omega)))
  simpa [body] using enter.trans (run.trans jump)

theorem loop {N Q P i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (omega : ℂ) (s : State) (h:Cursor N Q P i omega s) (hi:i+remaining=N)
    (hB:11≤B) (hP:P+N≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (6*remaining) u ∧ Cursor N Q P N omega u ∧
    (∀j,i≤j→j<N→u.scalarHeap (P+j)=some (prepared (omega^j))) ∧
    Outside (P+i) remaining s u ∧ Frame s u := by
  induction remaining generalizing i s with
  | zero =>
    have he:i=N:=by omega
    subst i
    exact ⟨s,.refl hs,h,by intro j hj hlt;omega,fun _ _=>rfl,frame_refl s⟩
  | succ r ih =>
    have ilt:i<N:=by omega
    have run:=iteration_bounded B n x omega s h ilt hB hP hs
    obtain ⟨u,hu,hc,hw,ho,hf⟩:=ih (i:=i+1) (iteration s) (iteration_cursor h) (by omega)
      run.final_bound
    refine ⟨u,?_,hc,?_,?_,frame_trans (iteration_frame s) hf⟩
    · convert run.trans hu using 1;omega
    · intro j hji hj
      by_cases he:j=i
      · subst j
        rw [ho (P+i) (Or.inl (by omega)),iteration_heap h]
        simp
      · exact hw j (by omega) hj
    · intro j hj
      rw [ho j (by omega),iteration_heap h]
      apply Function.update_of_ne
      omega

/-- Every source load, power multiplication, store and loop branch is charged.
The root is an actual prepared heap value; no power bank enters the theorem. -/
theorem execution (N Q P B n : ℕ) (x : Fin n→ℂ) (omega : ℂ) (s : State)
    (hh:Header N Q P s) (hp:s.pc=0) (hroot:s.scalarHeap Q=some (prepared omega))
    (hB:11≤B) (hP:P+N≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (6*N+6) u ∧
    (∀j,j<N→u.scalarHeap (P+j)=some (prepared (omega^j))) ∧
    Outside P N s u ∧ Frame s u ∧ Header N Q P u ∧ u.pc=10 := by
  have rb:readable boot s:=by
    simp [readable,boot,Op.readable,Op.apply,writeNat,writeScalar,next,hh.source,hroot]
  have pk:peak boot s≤B:=by simp [peak,boot,Op.peak];omega
  have start:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+4≤B;omega) rb pk
  let v:=applyBlock boot s
  have cur:Cursor N Q P 0 omega v:=by
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_⟩
    all_goals simp [v,boot,applyBlock,Op.apply,writeNat,writeScalar,next,
      hp,hh.length,hh.source,hh.target,hroot,prepared]
  have bf:Frame s v:=by
    refine ⟨rfl,rfl,rfl,?_,?_⟩
    all_goals intro r hr
    all_goals simp (disch:=omega) [v,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
  obtain ⟨u,run,uc,uw,uo,uf⟩:=loop N B n x omega v cur (by omega) hB hP start.final_bound
  let z:=setPC u 10
  have bz:WordBound B z:=changePC_bound B u 10 run.final_bound (by omega)
  have leave:BoundedRuns program n x B u 1 z:=.next run.final_bound
    (by simp [step,uc.pc,branch_at,uc.index,uc.header.length,z,setPC]) (.refl bz)
  have stop:BoundedExecution program n x B z 1 z:=.halt bz (by simp [step,z,setPC,halt_at])
  refine ⟨z,?_,?_,?_,frame_trans bf uf,⟨uc.header.length,uc.header.source,uc.header.target⟩,rfl⟩
  · convert start.executes (run.executes (leave.executes stop)) using 1
    simp only [boot,List.length_cons,List.length_nil];omega
  · intro j hj;exact uw j (by omega) hj
  · intro j hj
    have h:=uo j (by simpa only [Nat.add_zero] using hj)
    exact h

theorem source_retained (N Q P : ℕ) (s u : State) (h:Outside P N s u)
    (hQ:P+N≤Q) : u.scalarHeap Q=s.scalarHeap Q := h Q (Or.inr hQ)

end
end ExactFourierCircuits.UniformContiguousPowerBankMachine
