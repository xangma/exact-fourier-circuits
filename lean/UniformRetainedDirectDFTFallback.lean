import UniformEmptyStartupMatchingPreparation
import UniformRootExtractionMachine
import UniformDirectBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRetainedDirectDFTFallback
open UniformMachine UniformAssembly UniformDirectMachine
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section

/-- The existing direct loop, with its root request replaced by a physical
load of the already produced canonical root. -/
def body : Program:=UniformDirectMachine.program.set 2 (.loadScalar 0 140)
lemma body_length :body.length=21:=rfl
lemma body_lookup (i:ℕ) (h:i≠2) :body[i]?=UniformDirectMachine.program[i]? := by
 exact List.getElem?_set_ne (Ne.symm h)

/-- A proof-level state map. It is never a runtime instruction or free starting
state: later simulation transports a proved execution from the physical boot. -/
def rootMask (orders:List ℕ) (s:State):State:={s with rootOrders:=orders}
def resultMask (orders:List ℕ):StepResult→StepResult
 | .failed => .failed
 | .running s => .running (rootMask orders s)
 | .halted s => .halted (rootMask orders s)
def rootFree : Instruction→Bool
 | .root _ _ => false
 | _ => true
def NoRoots (p:Program):Prop:=p.all rootFree=true
lemma body_noRoots :NoRoots body:=by
 change body.all rootFree=true
 decide
lemma step_mask (p:Program) (nr:NoRoots p) (n:ℕ) (x:Fin n→ℂ) (s:State) (orders:List ℕ) :
 step p n x (rootMask orders s)=resultMask orders (step p n x s) := by
 cases hg:p[s.pc]? with
 | none=>simp [step,rootMask,resultMask,hg]
 | some ins=>
  have hn:rootFree ins=true :=List.all_eq_true.mp nr ins (List.mem_of_getElem? hg)
  cases ins with
  | natBinary op dst left right=>
   cases he:evalNat op (s.natReg left) (s.natReg right) <;>
    simp [step,rootMask,hg,he,resultMask,writeNat,next]
  | fieldBinary op dst left right=>
   cases he:evalField op (s.scalarReg left) (s.scalarReg right) <;>
    simp [step,rootMask,hg,he,resultMask,writeScalar,next]
  | input dst index=>
   by_cases hi:s.natReg index<n <;>
    simp [step,rootMask,hg,hi,resultMask,writeScalar,next]
  | loadNat dst address=>
   cases he:s.natHeap (s.natReg address) <;>
    simp [step,rootMask,hg,he,resultMask,writeNat,next]
  | loadScalar dst address=>
   cases he:s.scalarHeap (s.natReg address) <;>
    simp [step,rootMask,hg,he,resultMask,writeScalar,next]
  | output index src=>
   by_cases hi:s.natReg index<n <;>simp [step,rootMask,hg,hi,resultMask,next]
  | branchLT left right yes no=>
   by_cases hi:s.natReg left<s.natReg right <;>simp [step,rootMask,hg,hi,resultMask]
  | root dst order=>simp [rootFree] at hn
  | _=>simp [step,rootMask,hg,resultMask,writeNat,writeScalar,next]
lemma mask_bound (B:ℕ) (s:State) (hb:WordBound B s) (orders:List ℕ) (ho:∀r∈orders,r≤B) :
 WordBound B (rootMask orders s):=⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,ho⟩
def Interior (n B:ℕ) (s:State):Prop:=WordBound B s ∧ UniformDirectBounds.Counters n s
theorem step_interior (n B : ℕ) (hB:n+21≤B) (x : Fin n → ℂ) (s u : State)
    (hs : Interior n B s) (h : step program n x s = .running u) : Interior n B u := by
  obtain ⟨hb, hlo, hhi, hn, hone, hk, hj, hkstrict, hjstrict⟩ := hs
  have hpnext : s.pc + 1 ≤ B := by omega
  have hscalar (dst : ℕ) (v : Scalar) : WordBound B (writeScalar s dst v) :=
    writeScalar_bound _ s dst v hb hpnext
  interval_cases hpc : s.pc
  · by_cases hkn : s.natReg 1 < n
    · simp [step, program, hpc, hn, hkn] at h
      subst u
      refine ⟨changePC_bound _ s 6 hb (by omega), ?_⟩
      simp only [UniformDirectBounds.Counters]; omega
    · simp [step, program, hpc, hn, hkn] at h
      subst u
      refine ⟨changePC_bound _ s 20 hb (by omega), ?_⟩
      simp only [UniformDirectBounds.Counters]; omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨writeNat_bound _ s 2 0 hb (by omega) (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 2), Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 2)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨hscalar 2 _, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨hscalar 3 _, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · by_cases hjn : s.natReg 2 < n
    · simp [step, program, hpc, hn, hjn] at h
      subst u
      refine ⟨changePC_bound _ s 10 hb (by omega), ?_⟩
      simp only [UniformDirectBounds.Counters]; omega
    · simp [step, program, hpc, hn, hjn] at h
      subst u
      refine ⟨changePC_bound _ s 16 hb (by omega), ?_⟩
      simp only [UniformDirectBounds.Counters]; omega
  · have hjn : s.natReg 2 < n := hjstrict (by omega) (by omega)
    simp [step, program, hpc, hjn] at h
    subst u
    refine ⟨hscalar 4 _, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 5) (left := 2) (right := 4) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 5 v, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 3) (left := 3) (right := 5) (op := .add) (by simp [program, hpc]) h
    refine ⟨hscalar 3 v, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 2) (left := 2) (right := 1) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · have hjn : s.natReg 2 < n := hjstrict (by omega) (by omega)
    simp [step, program, hpc, evalNat, hone] at h
    subst u
    refine ⟨writeNat_bound _ s 2 (s.natReg 2 + 1) hb (by omega) (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 2), Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 2)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨changePC_bound _ s 9 hb (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters]; omega
  · have hkn : s.natReg 1 < n := hkstrict (by omega) (by omega)
    simp [step, program, hpc, hkn] at h
    subst u
    refine ⟨emit_bound _ s (s.natReg 1) _ (s.pc + 1) hb (by omega) (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 1) (left := 1) (right := 0) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 1 v, ?_⟩
    simp only [UniformDirectBounds.Counters, writeScalar, next]; omega
  · have hkn : s.natReg 1 < n := hkstrict (by omega) (by omega)
    simp [step, program, hpc, evalNat, hone] at h
    subst u
    refine ⟨writeNat_bound _ s 1 (s.natReg 1 + 1) hb (by omega) (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 1), Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 1)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨changePC_bound _ s 5 hb (by omega), ?_⟩
    simp only [UniformDirectBounds.Counters]; omega
  · simp [step, program, hpc] at h


lemma body_step {n:ℕ} (x:Fin n→ℂ) (s:State) (hpc:5 ≤ s.pc) :
 step body n x s=step UniformDirectMachine.program n x s := by
 unfold step
 rw [body_lookup s.pc (by omega)]
lemma reflected_execution {n B t:ℕ} {x:Fin n→ℂ} {s u:State} (hB:n+21≤B)
 (h:BoundedExecution UniformDirectMachine.program n x B s t u)
 (hc:UniformDirectBounds.Counters n s) (orders:List ℕ) (ho:∀r∈orders,r≤B) :
 BoundedExecution body n x B (rootMask orders s) t (rootMask orders u) := by
 revert hc
 induction h with
 | halt hb hh=>
  intro hc
  refine .halt (mask_bound B _ hb orders ho) ?_
  rw [step_mask body body_noRoots,body_step x _ hc.1,hh]
  rfl
 | next hb hh tail ih=>
  intro hc
  refine .next (mask_bound B _ hb orders ho) ?_ (ih (step_interior n B hB x _ _ ⟨hb,hc⟩ hh).2)
  rw [step_mask body body_noRoots,body_step x _ hc.1,hh]
  rfl

/-- This actual boot loads the physically produced root; the five instructions
cost exactly as much as the old root-request boot. -/
def boot0 (n:ℕ) (s:State):State:=writeNat s 0 n
def boot1 (n:ℕ) (s:State):State:=writeNat (boot0 n s) 3 1
def boot2 (n:ℕ) (s:State):State:=writeScalar (boot1 n s) 0 (prepared (OAI.ExactFourier.zeta n))
def boot3 (n:ℕ) (s:State):State:=writeNat (boot2 n s) 1 0
def boot (n:ℕ) (s:State):State:=writeScalar (boot3 n s) 1 (prepared 1)
lemma boot_bounded {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=0) (hn:n+21≤B)
 (root:s.scalarHeap (s.natReg 140)=some (prepared (OAI.ExactFourier.zeta n))) (bound:WordBound B s) :
 BoundedRuns body n x B s 5 (boot n s) := by
 have b0:=writeNat_bound B s 0 n bound (by omega) (by omega)
 have b1:=writeNat_bound B (boot0 n s) 3 1 b0 (by change s.pc+2≤B;omega) (by omega)
 have b2:=writeScalar_bound B (boot1 n s) 0 (prepared (OAI.ExactFourier.zeta n)) b1 (by change s.pc+3≤B;omega)
 have b3:=writeNat_bound B (boot2 n s) 1 0 b2 (by change s.pc+4≤B;omega) (by omega)
 have b4:=writeScalar_bound B (boot3 n s) 1 (prepared 1) b3 (by change s.pc+5≤B;omega)
 refine .next bound ?_ (.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.next b3 ?_ (.refl b4)))))
 all_goals simp [step,body,UniformDirectMachine.program,boot,boot0,boot1,boot2,boot3,writeNat,writeScalar,next,pc,root,prepared]
lemma boot_counters {n:ℕ} (s:State) (pc:s.pc=0) (zero:s.natReg 2=0) :
 UniformDirectBounds.Counters n (rootMask [n] (boot n s)) := by
 simp [UniformDirectBounds.Counters,rootMask,boot,boot0,boot1,boot2,boot3,writeNat,writeScalar,next,pc,zero]
lemma boot_invariant {n:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=0) :
 outerInvariant x 0 (rootMask [n] (boot n s)) := by
 simp [outerInvariant,context,rootMask,boot,boot0,boot1,boot2,boot3,prepared,writeNat,writeScalar,next,pc]
lemma mask_restore (s:State) (orders:List ℕ) :rootMask s.rootOrders (rootMask orders s)=s:=by
 cases s;rfl

/-- Universal actual loaded-root direct DFT, on arbitrary dirty surrounding
banks and output cells. No second root request occurs in the stored body. -/
theorem body_execution {n B:ℕ} (_hn:0<n) (x:Fin n→ℂ) (s:State) (pc:s.pc=0)
 (zero:s.natReg 2=0) (hB:n+21≤B)
 (root:s.scalarHeap (s.natReg 140)=some (prepared (OAI.ExactFourier.zeta n))) (bound:WordBound B s) :∃u,
 BoundedExecution body n x B s (7*n^2+9*n+7) u ∧ ComputesDFT n x u ∧u.rootOrders=s.rootOrders :=by
 have bootrun:=boot_bounded x s pc hB root bound
 let shadow:=rootMask [n] (boot n s)
 have shbound:WordBound B shadow:=mask_bound B _ bootrun.final_bound [n] (by simp;omega)
 obtain ⟨v,run,inv⟩:=outer_loop x n 0 shadow (by omega) (boot_invariant x s pc)
 have ex:=run.executes (halt_executes x v inv)
 have bx:=ex.bounded_of_invariant (Interior n B) ⟨shbound,boot_counters s pc zero⟩
  (fun _ h=>h.1) (fun a b h=>step_interior n B hB x a b h)
 have real:=reflected_execution hB bx (boot_counters s pc zero) s.rootOrders bound.2.2.2.2.2
 have restore:rootMask s.rootOrders shadow=boot n s:=by
  change rootMask s.rootOrders (rootMask [n] (boot n s))=boot n s
  cases s;rfl
 rw [restore] at real
 refine ⟨rootMask s.rootOrders {v with pc:=20},?_,?_,rfl⟩
 · convert bootrun.executes real using 1;ring
 · intro j;exact inv.2.2 j j.isLt


def heapsFree : Instruction → Bool
 | .storeNat _ _ | .storeScalar _ _ => false
 | _ => true
lemma heaps_step (p:Program) (free:p.all heapsFree=true) (n:ℕ) (x:Fin n→ℂ) (s u:State)
 (h:step p n x s=.running u):u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap := by
 cases hg:p[s.pc]? with
 | none=>simp [step,hg] at h
 | some ins=>
  have hn:heapsFree ins=true:=List.all_eq_true.mp free ins (List.mem_of_getElem? hg)
  cases ins with
  | natBinary op dst left right=>
   cases he:evalNat op (s.natReg left) (s.natReg right) <;> simp [step,hg,he] at h
   subst u;exact ⟨rfl,rfl⟩
  | fieldBinary op dst left right=>
   cases he:evalField op (s.scalarReg left) (s.scalarReg right) <;> simp [step,hg,he] at h
   subst u;exact ⟨rfl,rfl⟩
  | input dst index=>
   by_cases hi:s.natReg index<n <;> simp [step,hg,hi] at h
   subst u;exact ⟨rfl,rfl⟩
  | root dst order=>
   by_cases hi:s.natReg order=0 <;> simp [step,hg,hi] at h
   subst u;exact ⟨rfl,rfl⟩
  | loadNat dst address=>
   cases he:s.natHeap (s.natReg address) <;> simp [step,hg,he] at h
   subst u;exact ⟨rfl,rfl⟩
  | loadScalar dst address=>
   cases he:s.scalarHeap (s.natReg address) <;> simp [step,hg,he] at h
   subst u;exact ⟨rfl,rfl⟩
  | output index src=>
   by_cases hi:s.natReg index<n <;> simp [step,hg,hi] at h
   subst u;exact ⟨rfl,rfl⟩
  | storeNat address src=>simp [heapsFree] at hn
  | storeScalar address src=>simp [heapsFree] at hn
  | halt=>simp [step,hg] at h
  | branchLT left right yes no=>simp [step,hg] at h;subst u;exact ⟨rfl,rfl⟩
  | jump target=>simp [step,hg] at h;subst u;exact ⟨rfl,rfl⟩
  | _=>simp [step,hg] at h;subst u;exact ⟨rfl,rfl⟩
lemma heaps_execution {p:Program} (free:p.all heapsFree=true) {n t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:Executes p n x s t u):u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap :=by
 induction h with
 | halt _=>exact ⟨rfl,rfl⟩
 | next hs _ ih=>
  have f:=heaps_step p free n x _ _ hs
  exact ⟨ih.1.trans f.1,ih.2.trans f.2⟩
lemma body_heaps {n B t:ℕ} {x:Fin n→ℂ} {s u:State} (h:BoundedExecution body n x B s t u):
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap:=heaps_execution (by decide) h.executes

/-- Ordinary caller/root headers are installed physically. -/
def rootSetup:List Op := [.add 140 3203 3200,.add 141 101 3200]
def prep:List Op:=UniformEmptyStartupMatchingPreparation.sizeBoot++rootSetup
def reset:List Op:=[.literal 2 0]
def head:Program:=prep.map Op.code++UniformRootExtractionMachine.program.map (relocate 9 26)++reset.map Op.code
def program:Program:=head++body.map (relocate 27 48)++[.halt]
lemma prep_length:prep.length=9:=rfl
lemma reset_length:reset.length=1:=rfl
lemma head_length:head.length=27:=by
 simp only [head,List.length_append,List.length_map,prep_length,UniformRootExtractionMachine.program_length,reset_length]
lemma program_length:program.length=49:=by
 simp only [program,List.length_append,List.length_map,head_length,body_length];rfl
lemma prep_code:BlockAt prep program 0:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment [] (prep.map Op.code)
  (UniformRootExtractionMachine.program.map (relocate 9 26)++reset.map Op.code++body.map (relocate 27 48)++[.halt]) i (by simpa using hi)
 simpa only [program,head,List.nil_append,List.append_assoc,List.length_nil,Nat.zero_add,
  List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma root_code:CodeAt UniformRootExtractionMachine.program program 9 26:=by
 have eq:program=prep.map Op.code++UniformRootExtractionMachine.program.map (relocate 9 26)++
  (reset.map Op.code++body.map (relocate 27 48)++[.halt]):=by simp only [program,head,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code _ _ _ _ _ (by simp only [List.length_map,prep_length])
lemma reset_code:BlockAt reset program 26:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (prep.map Op.code++UniformRootExtractionMachine.program.map (relocate 9 26)) (reset.map Op.code)
  (body.map (relocate 27 48)++[.halt]) i (by simpa using hi)
 simpa only [program,head,List.append_assoc,List.length_append,List.length_map,prep_length,
  UniformRootExtractionMachine.program_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma body_code:CodeAt body program 27 48:=
 UniformRankCrossPreparationMachine.segment_code head [.halt] _ _ _ head_length
lemma halt_at:program[48]?=some .halt:=by
 have h:=UniformAllAxisSeedPreparation.lookup_segment (head++body.map (relocate 27 48)) [.halt] [] 0 (by decide)
 simpa only [program,List.append_nil,List.append_assoc,List.length_append,List.length_map,head_length,
  body_length,List.getElem?_cons_zero] using h
lemma prep_frame (s:State):(applyBlock prep s).natHeap=s.natHeap ∧(applyBlock prep s).scalarHeap=s.scalarHeap ∧
 (applyBlock prep s).scalarReg=s.scalarReg ∧(applyBlock prep s).outputs=s.outputs ∧(applyBlock prep s).rootOrders=s.rootOrders:=
 UniformEmptyStartupMatchingPreparation.natOnly_frame prep (by decide) s
lemma prep_headers {n:ℕ} (s:State) (m:UniformPermutationInversePreparation.Metadata n s):
 (applyBlock prep s).natReg 140=UniformEmptyStartupMatchingPreparation.arena n ∧(applyBlock prep s).natReg 141=n ∧
 (applyBlock prep s).natReg 104=UniformMasterRootMachine.order n:=by
 constructor
 · simp [prep,rootSetup,UniformEmptyStartupMatchingPreparation.sizeBoot,applyBlock,Op.apply,writeNat,next,m.saved.inputLength,UniformEmptyStartupMatchingPreparation.arena,pow_two,Nat.mul_comm]
 constructor
 · simp [prep,rootSetup,UniformEmptyStartupMatchingPreparation.sizeBoot,applyBlock,Op.apply,writeNat,next,m.saved.inputLength]
 · have eq:(applyBlock prep s).natReg 104=s.natReg 104:=by
    apply UniformSeedRankCrossPreparation.block_register_keeps
    simp [prep,rootSetup,UniformEmptyStartupMatchingPreparation.sizeBoot,UniformSeedRankCrossPreparation.KeepsRegister]
   exact eq.trans m.saved.masterRoot
lemma prep_safe {n:ℕ} (hn:0<n) (s:State) (m:UniformPermutationInversePreparation.Metadata n s):
 readable prep s ∧peak prep s≤UniformEmptyStartupMatchingPreparation.budget n:=by
 have boot:=UniformEmptyStartupMatchingPreparation.sizeBoot_safe hn s m.saved.inputLength
 have q:=UniformEmptyStartupMatchingPreparation.sizeBoot_root m.saved.inputLength
 have frame101:(applyBlock UniformEmptyStartupMatchingPreparation.sizeBoot s).natReg 101=n:=by
  simp [UniformEmptyStartupMatchingPreparation.sizeBoot,applyBlock,Op.apply,writeNat,next,m.saved.inputLength]
 have zero:(applyBlock UniformEmptyStartupMatchingPreparation.sizeBoot s).natReg 3200=0:=by
  simp [UniformEmptyStartupMatchingPreparation.sizeBoot,applyBlock,Op.apply,writeNat,next]
 have fits:=UniformEmptyStartupMatchingPreparation.arena_bounds hn
 have hq:UniformEmptyStartupMatchingPreparation.arena n≤UniformEmptyStartupMatchingPreparation.budget n:=by omega
 have small:n≤UniformEmptyStartupMatchingPreparation.budget n:=by omega
 have tail:readable rootSetup (applyBlock UniformEmptyStartupMatchingPreparation.sizeBoot s) ∧peak rootSetup (applyBlock UniformEmptyStartupMatchingPreparation.sizeBoot s)≤UniformEmptyStartupMatchingPreparation.budget n:=by
  constructor
  · simp [rootSetup,readable,Op.readable]
  · simp [rootSetup,peak,Op.peak,Op.apply,writeNat,next,q,zero,frame101,hq,small]
 rw [prep,UniformEmptyStartupMatchingPreparation.readable_append,UniformEmptyStartupMatchingPreparation.peak_append]
 exact ⟨⟨boot.1,tail.1⟩,max_le boot.2 tail.2⟩
lemma code_bound {n:ℕ} (hn:0<n):n+21≤UniformEmptyStartupMatchingPreparation.budget n ∧49≤UniformEmptyStartupMatchingPreparation.budget n:=by
 have h5:=UniformDirectBounds.linear_le_polynomial hn
 have h19:(n+2)^5≤(n+2)^19:=Nat.pow_le_pow_right (by omega :1≤n+2) (by decide)
 have h3:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
 norm_num at h3
 unfold UniformEmptyStartupMatchingPreparation.budget;omega

/-- Charged canonical root extraction followed by the actual direct loop.
The entry is real Metadata/Operands, never a freely conjugated/rooted state. -/
theorem execution {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (s:State)
 (m:UniformPermutationInversePreparation.Metadata n s) (ops:UniformInitialPreparation.Operands n x s)
 (pc:s.pc=0) (bound:WordBound (UniformEmptyStartupMatchingPreparation.budget n) s) :∃u,
 BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) s
  (7*n^2+9*n+27+UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/n)) u ∧
 ComputesDFT n x u ∧u.rootOrders=s.rootOrders ∧u.scalarHeap 0=s.scalarHeap 0 ∧u.pc=48 :=by
 have cb:=code_bound hn
 have safe:=prep_safe hn s m
 have first:=block_runs prep program 0 n (UniformEmptyStartupMatchingPreparation.budget n) x s prep_code pc bound
  (by rw [prep_length];omega) safe.1 safe.2
 let e:=setPC (applyBlock prep s) 0
 have eb:=changePC_bound (UniformEmptyStartupMatchingPreparation.budget n) (applyBlock prep s) 0 first.final_bound (by omega)
 have headers:=prep_headers s m
 have master:e.scalarHeap 0=some (prepared (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))):=
  (congrFun (prep_frame s).2.1 0).trans (UniformSeedRankCrossPreparation.operands_master ops)
 have ndvd:n∣UniformMasterRootMachine.order n:=
  (Nat.dvd_mul_left n 2).trans (UniformMasterRootMachine.divisor_orders n).1
 obtain ⟨v,rootRun,rootVal,rootOutside,rootFrame,vp⟩:=UniformRootExtractionMachine.execution
  n (UniformMasterRootMachine.order n) n (UniformEmptyStartupMatchingPreparation.arena n) (UniformEmptyStartupMatchingPreparation.budget n) x e rfl headers.2.2 headers.2.1 headers.1
  (UniformMasterRootMachine.order_bounds hn).1 hn ndvd master (by omega) eb
 have rp:=UniformBoundedAssembly.boundedExecution_placed root_code
  (by rw [UniformRootExtractionMachine.program_length];omega :9+UniformRootExtractionMachine.program.length≤UniformEmptyStartupMatchingPreparation.budget n)
  (by omega :26≤UniformEmptyStartupMatchingPreparation.budget n) rootRun
 have pp:(applyBlock prep s).pc=9:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,prep_length]
 rw [show placed 9 e=applyBlock prep s from UniformSeedRankCrossPreparation.placed_zero _ _ pp] at rp
 let w:=setPC v 26
 have resetRun:=block_runs reset program 26 n (UniformEmptyStartupMatchingPreparation.budget n) x w reset_code rfl rp.final_bound
  (by rw [reset_length];omega) (by simp [reset,readable,Op.readable]) (by simp [reset,peak,Op.peak])
 let d:=setPC (applyBlock reset w) 0
 have db:=changePC_bound (UniformEmptyStartupMatchingPreparation.budget n) (applyBlock reset w) 0 resetRun.final_bound (by omega)
 have address:d.natReg 140=UniformEmptyStartupMatchingPreparation.arena n:=by
  have kept:=rootFrame.2.2.2.2 140 (by omega) (by omega)
  simpa [d,w,reset,applyBlock,Op.apply,writeNat,next,setPC,e] using kept.trans headers.1
 have val:d.scalarHeap (d.natReg 140)=some (prepared (OAI.ExactFourier.zeta n)):=by
  rw [address];exact rootVal
 obtain ⟨z,last,DFT,roots⟩:=body_execution hn x d rfl
  (by simp [d,w,reset,applyBlock,Op.apply,writeNat,next,setPC]) cb.1 val db
 have bp:=UniformBoundedAssembly.boundedExecution_placed body_code
  (by rw [body_length];omega :27+body.length≤UniformEmptyStartupMatchingPreparation.budget n) (by omega :48≤UniformEmptyStartupMatchingPreparation.budget n) last
 have dp:(applyBlock reset w).pc=27:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,reset_length]
  rfl
 rw [show placed 27 d=applyBlock reset w from UniformSeedRankCrossPreparation.placed_zero _ _ dp] at bp
 let u:=setPC z 48
 have stop:BoundedExecution program n x (UniformEmptyStartupMatchingPreparation.budget n) u 1 u:=.halt bp.final_bound (by simp [step,u,setPC,halt_at])
 refine ⟨u,?_,DFT,?_,?_,rfl⟩
 · convert first.executes (rp.executes (resetRun.executes (bp.executes stop))) using 1
   simp only [prep_length,reset_length];ring
 · exact roots.trans (rootFrame.2.2.1.trans (prep_frame s).2.2.2.2)
 · calc u.scalarHeap 0=z.scalarHeap 0:=rfl
        _=d.scalarHeap 0:=congrFun (body_heaps last).2 0
        _=v.scalarHeap 0:=rfl
        _=e.scalarHeap 0:=rootOutside 0 (by have q:=UniformEmptyStartupMatchingPreparation.arena_bounds hn;omega)
        _=s.scalarHeap 0:=congrFun (prep_frame s).2.1 0

end
end ExactFourierCircuits.UniformRetainedDirectDFTFallback
