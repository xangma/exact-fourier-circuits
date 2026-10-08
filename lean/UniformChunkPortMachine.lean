import UniformBorrowedCoordinateMachine
import UniformToeplitzChunkWord
import UniformRadixInstructionMachine
import UniformTensorMonomialMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformChunkPortMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Nat1020=actual zero-hole-free replay port,1021=input count,1022=gate count,
1023=source offset,1024=target offset,1025=actual Borrowed17 table base.
Nat1030 returns the mapped tensor coordinate; scratch1031..1034.
No scalar bank or row coefficient is inspected or changed. -/
def boot : List Op := [.literal 1031 1,.add 1032 1021 1031,.add 1033 1032 1022]
def source : List Op := [.add 1030 1023 1020]
def gate : List Op := [.sub 1034 1020 1032,.add 1034 1025 1034,.getNat 1030 1034]
def target : List Op := [.sub 1034 1020 1033,.add 1030 1024 1034]
def program : Program := boot.map Op.code ++ [.branchLT 1020 1021 4 6] ++
  source.map Op.code ++ [.halt,.branchLT 1020 1033 7 11] ++
  gate.map Op.code ++ [.halt] ++ target.map Op.code ++ [.halt]
theorem program_length : program.length=14 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem source_code : BlockAt source program 4 := by
  intro i hi;change i<1 at hi;interval_cases i;rfl
theorem gate_code : BlockAt gate program 7 := by
  intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem target_code : BlockAt target program 11 := by
  intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem source_branch : program[3]?=some (.branchLT 1020 1021 4 6) := rfl
theorem gate_branch : program[6]?=some (.branchLT 1020 1033 7 11) := rfl
theorem source_halt : program[5]?=some .halt := rfl
theorem gate_halt : program[10]?=some .halt := rfl
theorem target_halt : program[13]?=some .halt := rfl
def Domain (e g a p : ℕ) : Prop := p < e ∨ (e+1 ≤ p ∧ p < e+1+g+a)
def mapped (e g s t : ℕ) (borrowed : ℕ→ℕ) (p : ℕ) :=
  if p<e then s+p else if p<e+1+g then borrowed (p-(e+1)) else t+(p-(e+1+g))
def runtime (e g p : ℕ) := if p<e then 6 else if p<e+1+g then 9 else 8
theorem runtime_bound (e g p : ℕ) : runtime e g p≤9 := by
  unfold runtime;split_ifs <;> omega
theorem mapped_source (e g s t i : ℕ) (borrowed : ℕ→ℕ) (hi:i < e) :
    mapped e g s t borrowed i=s+i := by simp [mapped,hi]
theorem mapped_gate (e g s t i : ℕ) (borrowed : ℕ→ℕ) (hi:i < g) :
    mapped e g s t borrowed (e+1+i)=borrowed i := by
  simp [mapped,show ¬e+1+i<e by omega,show e+1+i<e+1+g by omega]
theorem mapped_target (e g s t i : ℕ) (borrowed : ℕ→ℕ) :
    mapped e g s t borrowed (e+1+g+i)=t+i := by
  simp [mapped,show ¬e+1+g+i<e by omega,show ¬e+1+g+i<e+1+g by omega]

noncomputable section
structure Header (p e g s t Q : ℕ) (u : State) : Prop where
  port : u.natReg 1020=p
  inputs : u.natReg 1021=e
  gates : u.natReg 1022=g
  source : u.natReg 1023=s
  target : u.natReg 1024=t
  borrowed : u.natReg 1025=Q
structure Fixed (p e g s t Q : ℕ) (u : State) : Prop where
  header : Header p e g s t Q u
  one : u.natReg 1031=1
  inputEnd : u.natReg 1032=e+1
  gateEnd : u.natReg 1033=e+1+g
def Bank (Q g : ℕ) (borrowed : ℕ→ℕ) (u : State) : Prop :=
  ∀ (i : ℕ), i < g → u.natHeap (Q+i)=some (borrowed i)
def Frame (u w : State) : Prop := w.scalarHeap=u.scalarHeap ∧
  w.scalarReg=u.scalarReg ∧ w.natHeap=u.natHeap ∧ w.outputs=u.outputs ∧
  w.rootOrders=u.rootOrders ∧
  (∀q,(q<1030 ∨ 1035≤q)→w.natReg q=u.natReg q)
theorem frame_refl (u : State) : Frame u u := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {u w z : State} (h:Frame u w) (h':Frame w z) : Frame u z :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.1.trans h.2.2.2.2.1,
    fun q hq=>(h'.2.2.2.2.2 q hq).trans (h.2.2.2.2.2 q hq)⟩
theorem boot_fixed {p e g s t Q : ℕ} {u : State} (h:Header p e g s t Q u) :
    Fixed p e g s t Q (applyBlock boot u) := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next,h.port,h.inputs,
    h.gates,h.source,h.target,h.borrowed,Nat.add_assoc]
theorem boot_frame (u : State) : Frame u (applyBlock boot u) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q hq;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]


/-- Ordinary address/width bounds. No mapped-coordinate certificate enters. -/
structure Bounds (e g a s t Q B : ℕ) : Prop where
 code : 14 ≤ B
 inputGateEnd : e+1+g ≤ B
 sourceEnd : s+e ≤ B
 targetEnd : t+a ≤ B
 borrowedEnd : Q+g ≤ B

theorem Header.withPC {p e g s t Q : ℕ} {u : State}
 (h:Header p e g s t Q u) (pc : ℕ) : Header p e g s t Q (setPC u pc) :=
 ⟨h.port,h.inputs,h.gates,h.source,h.target,h.borrowed⟩
theorem Fixed.withPC {p e g s t Q : ℕ} {u : State}
 (h:Fixed p e g s t Q u) (pc : ℕ) : Fixed p e g s t Q (setPC u pc) :=
 ⟨h.header.withPC pc,h.one,h.inputEnd,h.gateEnd⟩
theorem Frame.withPC {s u : State} (f:Frame s u) (pc : ℕ) : Frame s (setPC u pc) := f

theorem block_frame (b : List Op) (u : State) (hb:b=boot ∨ b=source ∨ b=gate ∨ b=target) :
 Frame u (applyBlock b u) := by
 rcases hb with rfl|rfl|rfl|rfl
 all_goals refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 all_goals intro q hq
 all_goals simp (disch:=omega) [boot,source,gate,target,applyBlock,Op.apply,writeNat,next]

theorem pc_run (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (u : State) (pc : ℕ)
 (hs:WordBound B u) (hp:pc ≤ B) (hc:step program n x u=.running (setPC u pc)) :
 BoundedRuns program n x B u 1 (setPC u pc) :=
 .next hs hc (.refl (changePC_bound B u pc hs hp))

/-- Exact 6/9/8 charged steps for source/gate/target, with all other state
preserved. The physical borrowed table is loaded only in the gate branch. -/
theorem execution (n B p e g a s t Q : ℕ) (borrowed : ℕ → ℕ) (x : Fin n → ℂ) (u : State)
 (h:Header p e g s t Q u) (domain:Domain e g a p) (bank:Bank Q g borrowed u)
 (bounds:Bounds e g a s t Q B) (hp:u.pc=0) (hs:WordBound B u) : ∃w,
 BoundedExecution program n x B u (runtime e g p) w ∧
 w.natReg 1030=mapped e g s t borrowed p ∧ Frame u w := by
 have b:=bounds.code
 have pr:u.natReg 1020 ≤ B:=hs.2.1 1020
 have bootRun:=block_runs boot program 0 n B x u boot_code hp hs
  (by change 0+3 ≤ B;omega)
  (by simp [readable,boot,Op.readable])
  (by simp [peak,boot,Op.peak,Op.apply,writeNat,next,h.inputs,h.gates];have :=bounds.inputGateEnd;omega)
 let v:=applyBlock boot u
 have vf:Fixed p e g s t Q v:=boot_fixed h
 have vp:v.pc=3:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 have frameV:Frame u v:=boot_frame u
 by_cases sourceCase:p < e
 · let entry:=setPC v 4
   have enter:BoundedRuns program n x B v 1 entry:=pc_run n x B v 4 bootRun.final_bound (by omega) (by
    simp [step,vp,source_branch,vf.header.port,vf.header.inputs,sourceCase,setPC])
   have f:Fixed p e g s t Q entry:=vf.withPC 4
   have opRun:=block_runs source program 4 n B x entry source_code rfl enter.final_bound
    (by change 4+1 ≤ B;omega) (by simp [readable,source,Op.readable])
    (by simp [peak,source,Op.peak,f.header.source,f.header.port];have :=bounds.sourceEnd;omega)
   let w:=applyBlock source entry
   have wp:w.pc=5:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
   have halted:BoundedExecution program n x B w 1 w:=.halt opRun.final_bound (by simp [step,wp,source_halt])
   refine ⟨w,?_,?_,frame_trans (frameV.withPC 4) (block_frame source entry (Or.inr (Or.inl rfl)))⟩
   · simpa [runtime,sourceCase,boot,source] using (bootRun.trans (enter.trans opRun)).executes halted
   · simp [w,source,applyBlock,Op.apply,writeNat,next,f.header.source,f.header.port,mapped,sourceCase]
 · let middle:=setPC v 6
   have enter:BoundedRuns program n x B v 1 middle:=pc_run n x B v 6 bootRun.final_bound (by omega) (by
    simp [step,vp,source_branch,vf.header.port,vf.header.inputs,sourceCase,setPC])
   have mf:Fixed p e g s t Q middle:=vf.withPC 6
   by_cases gateCase:p < e+1+g
   · have lower:e+1 ≤ p:=by unfold Domain at domain;omega
     have idx:p-(e+1) < g:=by omega
     have value:=bank (p-(e+1)) idx
     have vb:borrowed (p-(e+1)) ≤ B:=(hs.2.2.1 _ _ value).2
     let entry:=setPC middle 7
     have nextRun:BoundedRuns program n x B middle 1 entry:=pc_run n x B middle 7 enter.final_bound (by omega) (by
      simp [step,middle,setPC,gate_branch,vf.header.port,vf.gateEnd,gateCase])
     have f:Fixed p e g s t Q entry:=mf.withPC 7
     have eh:entry.natHeap=u.natHeap:=frameV.2.2.1
     have value':entry.natHeap (Q+(p-(e+1)))=some (borrowed (p-(e+1))):=by rw [eh];exact value
     have opRun:=block_runs gate program 7 n B x entry gate_code rfl nextRun.final_bound
      (by change 7+3 ≤ B;omega)
      (by simp [readable,gate,Op.readable,Op.apply,writeNat,next,f.header.port,f.inputEnd,f.header.borrowed,value'])
      (by simp [peak,gate,Op.peak,Op.apply,writeNat,next,f.header.port,f.inputEnd,f.header.borrowed,value'];
          have :=bounds.borrowedEnd;have pb:=hs.2.1 1020;rw [h.port] at pb;omega)
     let w:=applyBlock gate entry
     have wp:w.pc=10:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
     have halted:BoundedExecution program n x B w 1 w:=.halt opRun.final_bound (by simp [step,wp,gate_halt])
     refine ⟨w,?_,?_,frame_trans (frameV.withPC 7) (block_frame gate entry (Or.inr (Or.inr (Or.inl rfl))))⟩
     · simpa [runtime,sourceCase,gateCase,boot,gate] using (bootRun.trans (enter.trans (nextRun.trans opRun))).executes halted
     · simp [w,gate,applyBlock,Op.apply,writeNat,next,f.header.port,f.inputEnd,f.header.borrowed,value',mapped,sourceCase,gateCase]
   · have idx:p-(e+1+g) < a:=by unfold Domain at domain;omega
     let entry:=setPC middle 11
     have nextRun:BoundedRuns program n x B middle 1 entry:=pc_run n x B middle 11 enter.final_bound (by omega) (by
      simp [step,middle,setPC,gate_branch,vf.header.port,vf.gateEnd,gateCase])
     have f:Fixed p e g s t Q entry:=mf.withPC 11
     have opRun:=block_runs target program 11 n B x entry target_code rfl nextRun.final_bound
      (by change 11+2 ≤ B;omega) (by simp [readable,target,Op.readable])
      (by simp [peak,target,Op.peak,Op.apply,writeNat,next,f.header.port,f.gateEnd,f.header.target];
          have :=bounds.targetEnd;have pb:=hs.2.1 1020;rw [h.port] at pb;omega)
     let w:=applyBlock target entry
     have wp:w.pc=13:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
     have halted:BoundedExecution program n x B w 1 w:=.halt opRun.final_bound (by simp [step,wp,target_halt])
     refine ⟨w,?_,?_,frame_trans (frameV.withPC 11) (block_frame target entry (Or.inr (Or.inr (Or.inr rfl))))⟩
     · simpa [runtime,sourceCase,gateCase,boot,target] using (bootRun.trans (enter.trans (nextRun.trans opRun))).executes halted
     · simp [w,target,applyBlock,Op.apply,writeNat,next,f.header.port,f.gateEnd,f.header.target,mapped,sourceCase,gateCase]


def intervalEmbedding (v start length : ℕ) (h:start+length ≤ v) : Fin length ↪ Fin v where
 toFun i:=⟨start+i.val,by have :=i.isLt;omega⟩
 inj' i j eqn:=by
  apply Fin.ext
  have hv:=congrArg Fin.val eqn
  dsimp at hv
  omega

/-- Source/target intervals and the actual printed first-available embedding
supply the complete exact-width chunk placement, without choice. -/
def placement (v s e t a g : ℕ) (he:s+e ≤ v) (ha:t+a ≤ v)
 (separated:s+e ≤ t ∨ t+a ≤ s) (fit:g+e+a ≤ v) :
 UniformToeplitzChunkWord.Placement e g a v where
 source:=intervalEmbedding v s e he
 gates:=UniformBorrowedCoordinateMachine.embedding v s e t a g fit
 target:=intervalEmbedding v t a ha
 source_gates i j eqn:=by
  have hv:=congrArg Fin.val eqn
  have hj:=UniformBorrowedCoordinateMachine.embedding_eligible v s e t a g fit j
  have hi:=i.isLt
  change s+i.val=(UniformBorrowedCoordinateMachine.embedding v s e t a g fit j).val at hv
  unfold UniformBorrowedCoordinateMachine.Eligible at hj
  omega
 source_target i j eqn:=by
  have hv:=congrArg Fin.val eqn
  have hi:=i.isLt
  have hj:=j.isLt
  change s+i.val=t+j.val at hv
  omega
 gates_target i j eqn:=by
  have hv:=congrArg Fin.val eqn
  have hi:=UniformBorrowedCoordinateMachine.embedding_eligible v s e t a g fit i
  have hj:=j.isLt
  change (UniformBorrowedCoordinateMachine.embedding v s e t a g fit i).val=t+j.val at hv
  unfold UniformBorrowedCoordinateMachine.Eligible at hi
  omega

def borrowedCoordinate (v s e t a g : ℕ) (fit:g+e+a ≤ v) (i : ℕ) : ℕ :=
 if hi:i < g then (UniformBorrowedCoordinateMachine.embedding v s e t a g fit ⟨i,hi⟩).val else 0

theorem bank_of_physical {v s e t a g Q : ℕ} (fit:g+e+a ≤ v) (u : State)
 (bank:∀j:Fin g,u.natHeap (Q+j.val)=some (UniformBorrowedCoordinateMachine.embedding v s e t a g fit j).val) :
 Bank Q g (borrowedCoordinate v s e t a g fit) u := by
 intro i hi
 simpa only [borrowedCoordinate,dite_eq_left hi] using bank ⟨i,hi⟩

theorem natPorts_domain (e g a : ℕ) (i : Fin (e+g+a)) :
 Domain e g a (UniformToeplitzChunkWord.natPorts e g a i) := by
 obtain ⟨q,rfl⟩:= (UniformToeplitzChunkWord.flatten e g a).surjective i
 simp only [UniformToeplitzChunkWord.natPorts,Function.Embedding.trans_apply,
  Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
 rcases q with (q|q)|q
 · exact Or.inl q.isLt
 · right;change e+1 ≤ e+1+q.val ∧ e+1+q.val < e+1+g+a
   have :=q.isLt;omega
 · right;change e+1 ≤ e+1+g+q.val ∧ e+1+g+q.val < e+1+g+a
   have :=q.isLt;omega

theorem domain_range (e g a p : ℕ) :
 Domain e g a p ↔ p ∈ Set.range (UniformToeplitzChunkWord.natPorts e g a) := by
 constructor
 · intro hp
   by_cases hi:p < e
   · refine ⟨UniformToeplitzChunkWord.flatten e g a (Sum.inl (Sum.inl ⟨p,hi⟩)),?_⟩
     simp only [UniformToeplitzChunkWord.natPorts,Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
     rfl
   · have lower:e+1 ≤ p:=by unfold Domain at hp;omega
     by_cases hg:p < e+1+g
     · have idx:p-(e+1) < g:=by omega
       refine ⟨UniformToeplitzChunkWord.flatten e g a (Sum.inl (Sum.inr ⟨p-(e+1),idx⟩)),?_⟩
       simp only [UniformToeplitzChunkWord.natPorts,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
       change e+1+(p-(e+1))=p
       omega
     · have idx:p-(e+1+g) < a:=by unfold Domain at hp;omega
       refine ⟨UniformToeplitzChunkWord.flatten e g a (Sum.inr ⟨p-(e+1+g),idx⟩),?_⟩
       simp only [UniformToeplitzChunkWord.natPorts,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
       change e+1+g+(p-(e+1+g))=p
       omega
 · rintro ⟨i,rfl⟩
   exact natPorts_domain e g a i

theorem mapped_natPorts (v s e t a g : ℕ) (he:s+e ≤ v) (ha:t+a ≤ v)
 (separated:s+e ≤ t ∨ t+a ≤ s) (fit:g+e+a ≤ v) (i : Fin (e+g+a)) :
 mapped e g s t (borrowedCoordinate v s e t a g fit) (UniformToeplitzChunkWord.natPorts e g a i)=
 ((placement v s e t a g he ha separated fit).embedding i).val := by
 obtain ⟨q,rfl⟩:=(UniformToeplitzChunkWord.flatten e g a).surjective i
 simp only [UniformToeplitzChunkWord.natPorts,UniformToeplitzChunkWord.Placement.embedding,
  Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
 rcases q with (q|q)|q
 · change mapped e g s t _ q.val=s+q.val
   exact mapped_source _ _ _ _ _ _ q.isLt
 · change mapped e g s t _ (e+1+q.val)=(UniformBorrowedCoordinateMachine.embedding v s e t a g fit q).val
   rw [mapped_gate _ _ _ _ _ _ q.isLt]
   simp only [borrowedCoordinate,dite_eq_left q.isLt]
 · change mapped e g s t _ (e+1+g+q.val)=t+q.val
   exact mapped_target _ _ _ _ _ _

theorem mapped_inRange (v s e t a g p : ℕ) (he:s+e ≤ v) (ha:t+a ≤ v)
 (separated:s+e ≤ t ∨ t+a ≤ s) (fit:g+e+a ≤ v) (domain:Domain e g a p) :
 mapped e g s t (borrowedCoordinate v s e t a g fit) p < v := by
 obtain ⟨i,rfl⟩:=(domain_range e g a p).mp domain
 rw [mapped_natPorts v s e t a g he ha separated fit i]
 exact ((placement v s e t a g he ha separated fit).embedding i).isLt

theorem mapped_injective (v s e t a g : ℕ) (he:s+e ≤ v) (ha:t+a ≤ v)
 (separated:s+e ≤ t ∨ t+a ≤ s) (fit:g+e+a ≤ v) {p q : ℕ}
 (hp:Domain e g a p) (hq:Domain e g a q)
 (eqn:mapped e g s t (borrowedCoordinate v s e t a g fit) p=
  mapped e g s t (borrowedCoordinate v s e t a g fit) q) : p=q := by
 obtain ⟨i,rfl⟩:=(domain_range e g a p).mp hp
 obtain ⟨j,rfl⟩:=(domain_range e g a q).mp hq
 rw [mapped_natPorts v s e t a g he ha separated fit i,
  mapped_natPorts v s e t a g he ha separated fit j] at eqn
 have h:=((placement v s e t a g he ha separated fit).embedding).injective (Fin.ext eqn)
 subst j
 rfl

/-- The actual Borrowed17 table supplies the gate branch's physical input. -/
theorem physical_execution (n B v p e g a s t Q : ℕ) (x : Fin n → ℂ) (u : State)
 (he:s+e ≤ v) (ha:t+a ≤ v) (separated:s+e ≤ t ∨ t+a ≤ s) (fit:g+e+a ≤ v)
 (h:Header p e g s t Q u) (domain:Domain e g a p)
 (bank:∀j:Fin g,u.natHeap (Q+j.val)=some (UniformBorrowedCoordinateMachine.embedding v s e t a g fit j).val)
 (bounds:Bounds e g a s t Q B) (hp:u.pc=0) (hs:WordBound B u) : ∃w,
 BoundedExecution program n x B u (runtime e g p) w ∧
 w.natReg 1030=mapped e g s t (borrowedCoordinate v s e t a g fit) p ∧
 w.natReg 1030 < v ∧ Frame u w := by
 obtain ⟨w,run,result,frame⟩:=execution n B p e g a s t Q (borrowedCoordinate v s e t a g fit) x u h domain
  (bank_of_physical fit u bank) bounds hp hs
 exact ⟨w,run,result,by rw [result];exact mapped_inRange v s e t a g p he ha separated fit domain,frame⟩

end
end ExactFourierCircuits.UniformChunkPortMachine
