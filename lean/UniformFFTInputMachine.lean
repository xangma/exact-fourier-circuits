import UniformPreparedFFTMachine
import UniformScalarCopyMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFFTInputMachine
open UniformMachine UniformRadixTwoDAG
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)

/-- Nat70=height,174=source count,175=source base,176=stride,122=target.
Only Nat177..183 and Scalar32 are overwritten. -/
def setup : List Op := [.literal 177 1,.literal 178 0,.literal 179 1,.literal 180 2]
def grow : List Op := [.mul 177 177 180,.add 178 178 179]
def copyBlock : List Op := [.mul 182 176 181,.add 182 175 182,.getScalar 32 182]
def tailBlock : List Op := [.add 183 122 181,.putScalar 183 32,.add 181 181 179]
def program : Program := setup.map Op.code ++ [.branchLT 178 70 5 8] ++ grow.map Op.code ++
  [.jump 4,.natLiteral 181 0,.branchLT 181 177 10 20,.branchLT 181 174 11 15] ++
  copyBlock.map Op.code ++ [.jump 16,.scalarLiteral 32 0] ++ tailBlock.map Op.code ++ [.jump 9,.halt]

theorem program_length : program.length=21 := rfl
theorem setup_at : BlockAt setup program 0 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem grow_at : BlockAt grow program 5 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem copy_at : BlockAt copyBlock program 11 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem tail_at : BlockAt tailBlock program 16 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl

def iterationCost (M k : ℕ) : ℕ := if k<M then 10 else 7
def loopCost (M k : ℕ) : ℕ→ℕ
 | 0=>0
 | f+1=>iterationCost M k+loopCost M (k+1) f

theorem loopCost_formula (M k f : ℕ) : loopCost M k f=7*f+3*min f (M-k) := by
  induction f generalizing k with
  | zero=>simp [loopCost]
  | succ f ih=>
    simp only [loopCost,ih,iterationCost]
    split_ifs <;> omega

noncomputable section

def paddedAt (M : ℕ) (input : Fin M→Scalar) (k : ℕ) : Scalar :=
  if h:k<M then input ⟨k,h⟩ else Scalar.zero

def padded (K M : ℕ) (input : Fin M→Scalar) : Fin (width K)→Scalar :=
  fun i=>paddedAt M input i.val

def Source (M S q : ℕ) (input : Fin M→Scalar) (s : State) : Prop :=
  ∀j,s.scalarHeap (S+q*j.val)=some (input j)
def Outside (A N : ℕ) (heap : ℕ→Option Scalar) (s : State) : Prop :=
  ∀i,(i < A ∨ A + N ≤ i)→s.scalarHeap i=heap i

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,r≠32→u.scalarReg r=s.scalarReg r) ∧ (∀r,(r<177 ∨ 183<r)→u.natReg r=s.natReg r)

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

structure Initializing (K t : ℕ) (s : State) : Prop where
  height:s.natReg 70=K
  size:s.natReg 177=width t
  index:s.natReg 178=t
  one:s.natReg 179=1
  two:s.natReg 180=2

theorem Initializing.withPC {K t pc : ℕ} {s : State} (h:Initializing K t s) : Initializing K t {s with pc:=pc} := by cases h;constructor <;> assumption

theorem setup_spec (K : ℕ) (s : State) (h:s.natReg 70=K) : Initializing K 0 (applyBlock setup s) := by
  constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h,width]
theorem setup_frame (s : State) : Frame s (applyBlock setup s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr;simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
theorem grow_spec (K t : ℕ) (s : State) (h:Initializing K t s) : Initializing K (t+1) (applyBlock grow s) := by
  constructor <;> simp [grow,applyBlock,Op.apply,writeNat,next,h.height,h.size,h.index,h.one,h.two,width,Nat.mul_comm,Nat.two_mul]
theorem grow_frame (s : State) : Frame s (applyBlock grow s) := by
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr;simp (disch:=omega) [grow,applyBlock,Op.apply,writeNat,next]
theorem setup_readable (s : State) : readable setup s := by simp [readable,setup,Op.readable]
theorem grow_readable (s : State) : readable grow s := by simp [readable,grow,Op.readable]

theorem initialize_loop (n K t f B : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Initializing K t s) (hf:t+f=K) (hp:s.pc=4) (hN:width K≤B) (hK:K≤B)
    (hc:20≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (4*f+1) u ∧ Initializing K K u ∧ u.pc=8 ∧
    u.scalarHeap=s.scalarHeap ∧ Frame s u := by
  induction f generalizing t s with
  | zero=>
    have he:t=K:=by omega
    subst t
    let u:State:={s with pc:=8}
    have hu:WordBound B u:=changePC_bound B s 8 hs (by omega)
    have st:step program n x s=.running u:=by simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,hp,h.index,h.height,u]
    exact ⟨u,.next hs st (.refl hu),h.withPC,rfl,rfl,Frame.refl s⟩
  | succ f ih=>
    have hlt:t<K:=by omega
    let e:State:={s with pc:=5}
    have he:WordBound B e:=changePC_bound B s 5 hs (by omega)
    have st:step program n x s=.running e:=by simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,hp,h.index,h.height,hlt,e]
    have hn:width (t+1)≤width K:=UniformRadixInstructionMachine.width_mono (by omega)
    have hg:peak grow e≤B:=by
      simp [peak,grow,Op.apply,Op.peak,writeNat,next,e,h.size,h.index,h.one,h.two]
      constructor
      · simpa only [width,Nat.mul_comm,Nat.two_mul] using hn.trans hN
      · omega
    have hr:=block_runs grow program 5 n B x e grow_at rfl he (by change 5+2≤B;omega) (grow_readable e) hg
    let u:State:={applyBlock grow e with pc:=4}
    have hu:WordBound B u:=changePC_bound B _ 4 hr.final_bound (by omega)
    have hj:step program n x (applyBlock grow e)=.running u:=by
      have hh:(applyBlock grow e).pc=7:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
      simp only [step,hh];rfl
    have hm:Initializing K (t+1) u:=by have hh:=grow_spec K t e h.withPC;exact hh.withPC
    obtain ⟨v,hv,hvi,hvp,hheap,hframe⟩:=ih (t+1) u hm (by omega) rfl hu
    refine ⟨v,?_,hvi,hvp,hheap.trans rfl,(grow_frame e).trans hframe⟩
    have hfirst:BoundedRuns program n x B s 1 e:=.next hs st (.refl he)
    have hlast:BoundedRuns program n x B (applyBlock grow e) 1 u:=.next hr.final_bound hj (.refl hu)
    have all:=hfirst.trans (hr.trans (hlast.trans hv))
    convert all using 1;simp only [show grow.length=2 by rfl];omega

structure Invariant (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State) : Prop where
  height:s.natReg 70=K
  size:s.natReg 177=width K
  length:s.natReg 174=M
  source:s.natReg 175=S
  stride:s.natReg 176=q
  target:s.natReg 122=A
  index:s.natReg 181=k
  one:s.natReg 179=1
  sourceBank:Source M S q input s
  written:∀j,j<k→s.scalarHeap (A+j)=some (paddedAt M input j)
  outside:Outside A (width K) heap s

theorem Invariant.withPC {K M S q A k pc : ℕ} {input : Fin M→Scalar} {heap : ℕ→Option Scalar} {s : State}
    (h:Invariant K M S q A k input heap s) : Invariant K M S q A k input heap {s with pc:=pc} := by
  cases h;constructor <;> assumption

/-- Zero stride may repeat a source cell. Even the boundary case S=A is safe:
its first store copies that same scalar, retaining its actual tag. -/
theorem source_after_store (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State)
    (h:Invariant K M S q A k input heap s) (_hk:k<width K) (hd:S+q*M≤A) :
    Source M S q input {s with scalarHeap:=Function.update s.scalarHeap (A+k) (some (paddedAt M input k))} := by
  intro j
  change Function.update s.scalarHeap (A+k) (some (paddedAt M input k)) (S+q*j.val)=some (input j)
  by_cases he:S+q*j.val=A+k
  · have hq:q=0:=by
      by_contra hn
      have hh:=Nat.mul_lt_mul_of_pos_left j.isLt (show 0<q by omega)
      omega
    have hk0:k=0:=by rw [hq] at he hd;simp only [Nat.zero_mul,Nat.add_zero] at he hd;omega
    have hM:0<M:=by have:=j.isLt;omega
    let z:Fin M:=⟨0,hM⟩
    have hsame:input z=input j:=by
      have hz:s.scalarHeap S=some (input z):=by simpa [hq] using h.sourceBank z
      have hj:s.scalarHeap S=some (input j):=by simpa [hq] using h.sourceBank j
      exact Option.some.inj (hz.symm.trans hj)
    rw [he]
    simpa [paddedAt,hk0,hM,z] using congrArg some hsame
  · rw [Function.update_of_ne he]
    exact h.sourceBank j


def picked (M : ℕ) (s : State) : State :=
  if s.natReg 181<M then {applyBlock copyBlock {s with pc:=11} with pc:=16}
  else writeScalar {s with pc:=15} 32 Scalar.zero

def iterationEnd (M : ℕ) (s : State) : State := {applyBlock tailBlock (picked M s) with pc:=9}

theorem picked_spec (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State)
    (h:Invariant K M S q A k input heap s) :
    Invariant K M S q A k input heap (picked M s) ∧
    (picked M s).scalarReg 32=paddedAt M input k ∧ (picked M s).pc=16 ∧
    (picked M s).scalarHeap=s.scalarHeap ∧ Frame s (picked M s) := by
  by_cases hk:k<M
  · have hv:=h.sourceBank ⟨k,hk⟩
    refine ⟨?_,?_,by simp [picked,h.index,hk],by simp [picked,h.index,hk,applyBlock,copyBlock,Op.apply,writeNat,writeScalar,next],?_⟩
    · constructor <;> simp [picked,h.index,hk,applyBlock,copyBlock,Op.apply,writeNat,writeScalar,next,
        h.height,h.size,h.length,h.source,h.stride,h.target,h.one]
      all_goals first | exact h.sourceBank | exact h.written | exact h.outside
    · simp [picked,h.index,hk,applyBlock,copyBlock,Op.apply,writeNat,writeScalar,next,h.stride,h.source,hv,paddedAt]
    · simp only [picked,h.index,ite_eq_left hk]
      refine ⟨rfl,rfl,rfl,?_,?_⟩
      · intro r hr;simp [h.index,applyBlock,copyBlock,Op.apply,writeNat,writeScalar,next,hr]
      · intro r hr;simp (disch:=omega) [h.index,applyBlock,copyBlock,Op.apply,writeNat,writeScalar,next]
  · refine ⟨?_,?_,by simp [picked,h.index,hk,writeScalar,next],by simp [picked,h.index,hk,writeScalar,next],?_⟩
    · constructor <;> simp [picked,h.index,hk,writeScalar,next,h.height,h.size,h.length,h.source,h.stride,h.target,h.one]
      all_goals first | exact h.sourceBank | exact h.written | exact h.outside
    · simp [picked,h.index,hk,writeScalar,next,paddedAt]
    · simp only [picked,h.index,ite_eq_right hk]
      refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
      intro r hr;simp [writeScalar,next,hr]

theorem iteration_heap (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State)
    (h:Invariant K M S q A k input heap s) : (iterationEnd M s).scalarHeap=
      Function.update s.scalarHeap (A+k) (some (paddedAt M input k)) := by
  have hp:=picked_spec K M S q A k input heap s h
  simp [iterationEnd,applyBlock,tailBlock,Op.apply,writeNat,next,hp.1.target,hp.1.index,hp.2.1,hp.2.2.2.1]

theorem iteration_frame (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State)
    (h:Invariant K M S q A k input heap s) : Frame s (iterationEnd M s) := by
  have hp:=picked_spec K M S q A k input heap s h
  apply hp.2.2.2.2.trans
  refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
  intro r hr;simp (disch:=omega) [iterationEnd,applyBlock,tailBlock,Op.apply,writeNat,next]

theorem iteration_invariant (K M S q A k : ℕ) (input : Fin M→Scalar) (heap : ℕ→Option Scalar) (s : State)
    (h:Invariant K M S q A k input heap s) (hk:k<width K) (hd:S+q*M≤A) :
    Invariant K M S q A (k+1) input heap (iterationEnd M s) := by
  have hp:=picked_spec K M S q A k input heap s h
  constructor
  all_goals simp [iterationEnd,applyBlock,tailBlock,Op.apply,writeNat,next,hp.1.height,hp.1.size,hp.1.length,hp.1.source,hp.1.stride,hp.1.target,hp.1.index,hp.1.one]
  · intro j
    change Function.update (picked M s).scalarHeap (A+k) (some ((picked M s).scalarReg 32)) (S+q*j.val)=_
    rw [hp.2.1,hp.2.2.2.1]
    exact source_after_store K M S q A k input heap s h hk hd j
  · intro j hj
    rw [hp.2.1,hp.2.2.2.1]
    by_cases he:j=k
    · subst j;simp
    · rw [Function.update_of_ne (by omega)]
      exact h.written j (by omega)
  · intro i hi
    change Function.update (picked M s).scalarHeap (A+k) (some ((picked M s).scalarReg 32)) i=_
    rw [hp.2.1,hp.2.2.2.1,Function.update_of_ne (by omega)]
    exact h.outside i hi

theorem iteration (n K M S q A k B : ℕ) (x : Fin n→ℂ) (input : Fin M→Scalar)
    (heap : ℕ→Option Scalar) (s : State) (h:Invariant K M S q A k input heap s)
    (hk:k<width K) (hd:S+q*M≤A) (hB:A+width K≤B) (hc:20≤B)
    (hp:s.pc=9) (hs:WordBound B s) :
    BoundedRuns program n x B s (iterationCost M k) (iterationEnd M s) := by
  let e:State:={s with pc:=10}
  have he:WordBound B e:=changePC_bound B s 10 hs (by omega)
  have st:step program n x s=.running e:=by
    simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,hp,h.index,h.size,hk,e]
  have hfirst:BoundedRuns program n x B s 1 e:=.next hs st (.refl he)
  have hpick:BoundedRuns program n x B e (if k<M then 5 else 2) (picked M s):=by
    by_cases hkm:k<M
    · let c:State:={s with pc:=11}
      have cb:WordBound B c:=changePC_bound B s 11 hs (by omega)
      have ct:step program n x e=.running c:=by
        simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,e,c,h.index,h.length,hkm]
      have hv:=h.sourceBank ⟨k,hkm⟩
      have cr:readable copyBlock c:=by
        simp [readable,copyBlock,Op.readable,Op.apply,writeNat,next,c,h.stride,h.index,h.source,hv]
      have hqk:q*k≤q*M:=Nat.mul_le_mul_left q (by omega)
      have cp:peak copyBlock c≤B:=by
        simp [peak,copyBlock,Op.peak,Op.apply,writeNat,next,c,h.stride,h.index,h.source]
        omega
      have hr:=block_runs copyBlock program 11 n B x c copy_at rfl cb (by change 11+3≤B;omega) cr cp
      have hb:WordBound B (picked M s):=by
        simp only [picked,h.index,ite_eq_left hkm]
        exact changePC_bound B _ 16 hr.final_bound (by omega)
      have hj:step program n x (applyBlock copyBlock c)=.running (picked M s):=by
        have hp':(applyBlock copyBlock c).pc=14:=by rw [UniformReciprocalMachine.applyBlock_pc];rfl
        simp only [step,hp']
        simp [program,setup,grow,copyBlock,tailBlock,Op.code,picked,h.index,hkm,c]
      have ht:BoundedRuns program n x B (applyBlock copyBlock c) 1 (picked M s):=.next hr.final_bound hj (.refl hb)
      simp only [ite_eq_left hkm]
      have hf:BoundedRuns program n x B e 1 c:=.next he ct (.refl cb)
      convert hf.trans (hr.trans ht) using 1
      rfl
    · let c:State:={s with pc:=15}
      have cb:WordBound B c:=changePC_bound B s 15 hs (by omega)
      have ct:step program n x e=.running c:=by
        simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,e,c,h.index,h.length,hkm]
      have hb:WordBound B (picked M s):=by
        simp only [picked,h.index,ite_eq_right hkm]
        exact writeScalar_bound B _ 32 Scalar.zero cb (by change 16≤B;omega)
      have hj:step program n x c=.running (picked M s):=by
        simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,picked,h.index,hkm,c,Scalar.zero]
      simp only [ite_eq_right hkm]
      exact .next he ct (.next cb hj (.refl hb))
  have hpi:=picked_spec K M S q A k input heap s h
  have htailp:peak tailBlock (picked M s)≤B:=by
    simp [peak,tailBlock,Op.peak,Op.apply,writeNat,next,hpi.1.target,hpi.1.index,hpi.1.one]
    omega
  have htailread:readable tailBlock (picked M s):=by simp [readable,tailBlock,Op.readable]
  have htail:=block_runs tailBlock program 16 n B x (picked M s) tail_at hpi.2.2.1 hpick.final_bound
    (by change 16+3≤B;omega) htailread htailp
  have hend:WordBound B (iterationEnd M s):=changePC_bound B _ 9 htail.final_bound (by omega)
  have hj:step program n x (applyBlock tailBlock (picked M s))=.running (iterationEnd M s):=by
    have hh:(applyBlock tailBlock (picked M s)).pc=19:=by rw [UniformReciprocalMachine.applyBlock_pc,hpi.2.2.1];rfl
    simp only [step,hh];rfl
  have hlast:BoundedRuns program n x B (applyBlock tailBlock (picked M s)) 1 (iterationEnd M s):=
    .next htail.final_bound hj (.refl hend)
  have hall:=hfirst.trans (hpick.trans (htail.trans hlast))
  convert hall using 1
  simp only [iterationCost,show tailBlock.length=3 by rfl]
  split_ifs <;> omega


theorem loop (n K M S q A k f B : ℕ) (x : Fin n→ℂ) (input : Fin M→Scalar)
    (heap : ℕ→Option Scalar) (s : State) (h:Invariant K M S q A k input heap s)
    (hf:k+f=width K) (hd:S+q*M≤A) (hB:A+width K≤B) (hc:20≤B)
    (hp:s.pc=9) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (loopCost M k f) u ∧ Invariant K M S q A (width K) input heap u ∧
    u.pc=9 ∧ Frame s u := by
  induction f generalizing k s with
  | zero=>
    have hk:k=width K:=by omega
    subst k
    exact ⟨s,.refl hs,h,hp,Frame.refl s⟩
  | succ f ih=>
    have hi:=iteration n K M S q A k B x input heap s h (by omega) hd hB hc hp hs
    have hinv:=iteration_invariant K M S q A k input heap s h (by omega) hd
    obtain ⟨u,hu,hui,hup,huf⟩:=ih (k+1) (iterationEnd M s) hinv (by omega) rfl hi.final_bound
    exact ⟨u,by simpa only [loopCost] using hi.trans hu,hui,hup,(iteration_frame K M S q A k input heap s h).trans huf⟩

/-- Fixed strided gather and zero padding. The source cells are physically
present, every read/store/branch/address operation is charged, and no tag changes. -/
theorem execution (n K M S q A B : ℕ) (x : Fin n→ℂ) (input : Fin M→Scalar) (s : State)
    (hsrc:Source M S q input s) (hM:M≤width K) (hd:S+q*M≤A)
    (hB:A+width K≤B) (hc:20≤B) (hp:s.pc=0)
    (h70:s.natReg 70=K) (h174:s.natReg 174=M) (h175:s.natReg 175=S)
    (h176:s.natReg 176=q) (h122:s.natReg 122=A) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (4*K+7*width K+3*M+8) u ∧
    (∀i:Fin (width K),u.scalarHeap (A+i.val)=some (padded K M input i)) ∧
    Source M S q input u ∧ Outside A (width K) s.scalarHeap u ∧ Frame s u ∧ u.pc=20 := by
  have hsetup:=block_runs setup program 0 n B x s setup_at hp hs (by change 4≤B;omega)
    (setup_readable s) (by simp [peak,setup,Op.peak];omega)
  have hsp:(applyBlock setup s).pc=4:=by rw [UniformReciprocalMachine.applyBlock_pc,hp];rfl
  have hK:K≤B:=by rw [←h70];exact hs.2.1 70
  obtain ⟨t,ht,hti,htp,hheap,htf⟩:=initialize_loop n K 0 K B x (applyBlock setup s) (setup_spec K s h70) (by omega) hsp
    (by omega) hK hc hsetup.final_bound
  have htf':Frame s t:=(setup_frame s).trans htf
  let e:=writeNat t 181 0
  have heb:WordBound B e:=writeNat_bound B t 181 0 ht.final_bound (by rw [htp];omega) (by omega)
  have hepc:e.pc=9:=by simp [e,writeNat,next,htp]
  have het:step program n x t=.running e:=by simp only [step,htp];rfl
  have hef:Frame t e:=by
    refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_⟩
    intro r hr;simp [e,writeNat,next,show r≠181 by omega]
  have heinv:Invariant K M S q A 0 input s.scalarHeap e:=by
    constructor
    · simpa [e,writeNat,next] using hti.height
    · simpa [e,writeNat,next] using hti.size
    · exact (hef.2.2.2.2 174 (Or.inl (by decide))).trans ((htf'.2.2.2.2 174 (Or.inl (by decide))).trans h174)
    · exact (hef.2.2.2.2 175 (Or.inl (by decide))).trans ((htf'.2.2.2.2 175 (Or.inl (by decide))).trans h175)
    · exact (hef.2.2.2.2 176 (Or.inl (by decide))).trans ((htf'.2.2.2.2 176 (Or.inl (by decide))).trans h176)
    · exact (hef.2.2.2.2 122 (Or.inl (by decide))).trans ((htf'.2.2.2.2 122 (Or.inl (by decide))).trans h122)
    · simp [e,writeNat]
    · simpa [e,writeNat,next] using hti.one
    · intro j;change t.scalarHeap _=_;rw [hheap];exact hsrc j
    · intro j hj;omega
    · intro i _;change t.scalarHeap i=_;rw [hheap];rfl
  obtain ⟨u,hu,hui,hup,huf⟩:=loop n K M S q A 0 (width K) B x input s.scalarHeap e heinv (by omega) hd hB hc hepc heb
  let v:State:={u with pc:=20}
  have hv:WordBound B v:=changePC_bound B u 20 hu.final_bound hc
  have hhalt:BoundedExecution program n x B v 1 v:=.halt hv (by simp only [step];rfl)
  have hend:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ hhalt
    simp [step,program,setup,grow,copyBlock,tailBlock,Op.code,hup,hui.index,hui.size,v]
  have heRun:BoundedRuns program n x B t 1 e:=.next ht.final_bound het (.refl heb)
  have hall:=hsetup.executes (ht.executes (heRun.executes (hu.executes hend)))
  refine ⟨v,?_,fun i=>hui.written i.val i.isLt,hui.sourceBank,hui.outside,htf'.trans (hef.trans huf),rfl⟩
  convert hall using 1
  simp only [loopCost_formula,Nat.sub_zero,Nat.min_eq_right hM]
  simp only [show setup.length=4 by rfl]
  omega

def wordBudget (K M S q A : ℕ) : ℕ := max (S+q*M) (max (A+width K) 184)

theorem wordBudget_bounds (K M S q A B : ℕ) (h:wordBudget K M S q A≤B) :
    S+q*M≤B ∧ A+width K≤B ∧ 184≤B := by unfold wordBudget at h;omega

theorem runtime_bound (K M : ℕ) (hM:M≤width K) : 4*K+7*width K+3*M+8≤4*K+10*width K+8 := by omega

/-- Padding is explicitly prepared false, and existing source tags are retained. -/
theorem padded_prepared (K M : ℕ) (input : Fin M→Scalar) (h:∀i,(input i).dependent=false) :
    ∀i,(padded K M input i).dependent=false := by
  intro i;unfold padded paddedAt;split_ifs
  · exact h _
  · rfl


open UniformAssembly OAI.ExactFourier

/-- A single literal program gathers/pads and then prepares and executes FFT.
There is no host initialization at the phase boundary. -/
def combinedProgram : Program := program.map (relocate 0 21) ++
  UniformPreparedFFTMachine.program.map (relocate 21 220) ++ [.halt]

theorem combinedProgram_length : combinedProgram.length=221 := by
  simp [combinedProgram,program_length,UniformPreparedFFTMachine.program_length]

theorem gather_code : CodeAt program combinedProgram 0 21 := by
  intro i hi
  simp only [combinedProgram,Nat.zero_add,List.getElem?_append,List.length_append,List.length_map,program_length,
    UniformPreparedFFTMachine.program_length,List.getElem?_map]
  have hb:i<21:=by simpa only [program_length] using hi
  split_ifs <;> first | omega | rfl

theorem prepared_code : CodeAt UniformPreparedFFTMachine.program combinedProgram 21 220 := by
  intro i hi
  simp only [combinedProgram,List.getElem?_append,List.length_append,List.length_map,program_length,
    UniformPreparedFFTMachine.program_length,List.getElem?_map]
  have hb:i<199:=by simpa only [UniformPreparedFFTMachine.program_length] using hi
  split_ifs <;> try omega
  all_goals simp only [show 21+i-21=i by omega]

def CombinedPersistent (r : ℕ) : Prop := UniformPreparedFFTMachine.Persistent r ∧ (r<177 ∨ 183<r)

/-- The physical FFT-input premise is discharged by the actual gather/padding
execution. Only the already prepared master root and original source bank enter. -/
theorem combined_execution (n K M S q A d D B : ℕ) (x : Fin n→ℂ) (input : Fin M→Scalar) (s : State)
    (hsrc:Source M S q input s) (hM:M≤width K) (hd:S+q*M≤A) (hA:0<A)
    (hc:221≤B) (hp:s.pc=0) (h70:s.natReg 70=K) (h174:s.natReg 174=M) (h175:s.natReg 175=S)
    (h176:s.natReg 176=q) (h122:s.natReg 122=A) (h107:s.natReg 107=d) (h104:s.natReg 104=D)
    (hroot:s.scalarHeap 0=some ⟨zeta D,false⟩) (hD:0<D) (hdiv:width K∣D)
    (hbudget:UniformPreparedFFTMachine.wordBudget K A d≤B) (hs:WordBound B s) : ∃u t,
    BoundedExecution combinedProgram n x B s t u ∧
    t≤4*K+7*width K+3*M+9+UniformPreparedFFTMachine.runtime D K ∧
    (∀i,u.scalarHeap (A+count K+i.val)=some
      ⟨(fourierMatrix (width K)).mulVec (fun i=>(padded K M input i).value) i,
        UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun i=>(padded K M input i).dependent) (count K+i.val)⟩) ∧
    Source M S q input u ∧ UniformRadixRowTableMachine.Outside d (3*count K) s.natHeap u ∧
    (∀i,(i < A ∨ UniformPreparedFFTMachine.rootAddress K A + 1 ≤ i)→u.scalarHeap i=s.scalarHeap i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,CombinedPersistent r→u.natReg r=s.natReg r) ∧ u.pc=220 := by
  have hb:=UniformPreparedFFTMachine.wordBudget_bounds K A d B hbudget
  obtain ⟨v,hv,hpad,hvs,hvo,hvf,hvp⟩:=execution n K M S q A B x input s hsrc hM hd (by omega) (by omega) hp h70 h174 h175 h176 h122 hs
  have placedv:=UniformBoundedAssembly.boundedExecution_placed gather_code (by simpa only [program_length,Nat.zero_add] using (show 21≤B by omega)) (by omega) hv
  have he0:placed 0 s=s:=by cases s;simp [placed]
  rw [he0] at placedv
  let vs:State:={v with pc:=21}
  let ve:State:={vs with pc:=0}
  have hve:WordBound B ve:=changePC_bound B _ 0 placedv.final_bound (by omega)
  have hentry:UniformPreparedFFTMachine.Entry K A d D (padded K M input) ve:=by
    refine ⟨rfl,?_,?_,?_,?_,?_,hpad⟩
    · exact (hvf.2.2.2.2 70 (Or.inl (by decide))).trans h70
    · exact (hvf.2.2.2.2 122 (Or.inl (by decide))).trans h122
    · exact (hvf.2.2.2.2 107 (Or.inl (by decide))).trans h107
    · exact (hvf.2.2.2.2 104 (Or.inl (by decide))).trans h104
    · exact (hvo 0 (Or.inl hA)).trans hroot
  obtain ⟨u,tu,hu,htu,hout,hNat,hScalar,hOutputs,hRoots,hRegs,hpc⟩:=UniformPreparedFFTMachine.execution n K A d D B x (padded K M input) ve hentry hD hdiv hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hve
  have placedu:=UniformBoundedAssembly.boundedExecution_placed prepared_code (by simpa only [UniformPreparedFFTMachine.program_length] using (show 220≤B by omega)) (by omega) hu
  have he1:placed 21 ve=vs:=UniformPreparedFFTMachine.reset_placed vs 21 rfl
  rw [he1] at placedu
  let z:State:={u with pc:=220}
  have halt:BoundedExecution combinedProgram n x B z 1 z:=.halt placedu.final_bound (by simp only [step];rfl)
  have all:=placedv.executes (placedu.executes halt)
  refine ⟨z,_,all,by omega,hout,?_,?_,?_,hOutputs.trans hvf.2.1,hRoots.trans hvf.2.2.1,?_,rfl⟩
  · intro j
    have hj:=j.isLt
    have hqs:q*j.val≤q*M:=Nat.mul_le_mul_left q (by omega)
    have hN:=width_pos K
    exact (hScalar (S+q*j.val) (Or.inl (by omega))).trans (hvs j)
  · intro i hi
    exact (hNat i hi).trans (congrFun hvf.1 i)
  · intro i hi
    have hin:i < A+width K ∨ UniformPreparedFFTMachine.rootAddress K A + 1 ≤ i:=by omega
    exact (hScalar i hin).trans (hvo i (by
      dsimp only [UniformPreparedFFTMachine.rootAddress,UniformPreparedFFTMachine.powerBase] at hi
      omega))
  · intro r hr
    exact (hRegs r hr.1).trans (hvf.2.2.2.2 r hr.2)

/-- Closed selected-root variant: the master bank/order/divisor are obtained from
actual startup metadata and operands, rather than additional local root requests. -/
theorem selected_combined_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (r K M S q A d : ℕ)
    (input : Fin M→Scalar) (s : State) (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) (hr:r≤UniformWorkingLength.workingLength n) (hk:2^K≤8*r)
    (hsrc:Source M S q input s) (hM:M≤width K) (hd:S+q*M≤A)
    (hp:s.pc=0) (h70:s.natReg 70=K) (h174:s.natReg 174=M) (h175:s.natReg 175=S)
    (h176:s.natReg 176=q) (h122:s.natReg 122=A) (h107:s.natReg 107=d)
    (hA:UniformGlobalLocalPreparation.globalEnd n≤A)
    (hdglobal:UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n≤d)
    (hbudget:UniformPreparedFFTMachine.wordBudget K A d≤(n+2)^19) (hs:WordBound ((n+2)^19) s) : ∃u t,
    BoundedExecution combinedProgram n x ((n+2)^19) s t u ∧
    t≤4*K+7*width K+3*M+9+UniformPreparedFFTMachine.runtime (UniformMasterRootMachine.order n) K ∧
    (∀i,u.scalarHeap (A+count K+i.val)=some
      ⟨(fourierMatrix (width K)).mulVec (fun i=>(padded K M input i).value) i,
        UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun i=>(padded K M input i).dependent) (count K+i.val)⟩) ∧
    Source M S q input u ∧ UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    (∀i,i<UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n→u.natHeap i=s.natHeap i) ∧
    (∀i,(i < A ∨ UniformPreparedFFTMachine.rootAddress K A + 1 ≤ i)→u.scalarHeap i=s.scalarHeap i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    (∀r,CombinedPersistent r→u.natReg r=s.natReg r) ∧ u.pc=220 := by
  have hroot:s.scalarHeap 0=some ⟨zeta (UniformMasterRootMachine.order n),false⟩:=by
    simpa [UniformCConstantsMachine.bank,UniformPairMachine.prepared] using ho.constants 0
  have hdiv:width K∣UniformMasterRootMachine.order n:=by
    simpa only [width_eq] using UniformMasterRootMachine.localPowerOrder_dvd hr hk
  have hpositive:0<A:=by have hg:=UniformGlobalLocalPreparation.globalEnd_formula n;omega
  have hc:221≤(n+2)^19:=by have hb:=UniformPermutationInversePreparation.word_setup hn;omega
  obtain ⟨u,t,he,ht,hout,hsu,hNat,hScalar,hOutputs,hRoots,hRegs,hpc⟩:=combined_execution n K M S q A d (UniformMasterRootMachine.order n) ((n+2)^19) x input s
    hsrc hM hd hpositive hc hp h70 h174 h175 h176 h122 h107 hm.saved.masterRoot hroot (UniformMasterRootMachine.order_bounds hn).1 hdiv hbudget hs
  have hprefix:∀i,i<UniformPermutationInversePreparation.inverseBase n+UniformInitialPreparation.len n→u.natHeap i=s.natHeap i:=by
    intro i hi;exact hNat i (Or.inl (by omega))
  have hsaved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
      (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) u:=by
    constructor
    · exact (hRegs 100 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.nextPrime
    · exact (hRegs 101 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.inputLength
    · exact (hRegs 102 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.count
    · exact (hRegs 103 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.workingLength
    · exact (hRegs 104 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.masterRoot
    · exact (hRegs 105 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.copyAddress
    · exact (hRegs 106 (by simp [CombinedPersistent,UniformPreparedFFTMachine.Persistent])).trans hm.saved.copyLength
  have hmu:=hm.transport_saved hsaved (by intro a ha;apply hprefix;unfold UniformPermutationInversePreparation.inverseBase;omega)
  have hou:=UniformGlobalLocalPreparation.operands_transport_below ho (by intro i hi;exact hScalar i (Or.inl (by omega)))
  exact ⟨u,t,he,ht,hout,hsu,hmu,hou,hprefix,hScalar,hOutputs,hRoots,hRegs,hpc⟩

/-- Prepared source coefficients and prepared-zero padding remain prepared
through every instruction of the combined program. -/
theorem combined_output_prepared (K M A : ℕ) (input : Fin M→Scalar) (u : State)
    (hp:∀i,(input i).dependent=false)
    (h:∀i,u.scalarHeap (A+count K+i.val)=some
      ⟨(fourierMatrix (width K)).mulVec (fun i=>(padded K M input i).value) i,
        UniformOffsetLinearMachine.TaggedFFT.dependencyValue K (fun i=>(padded K M input i).dependent) (count K+i.val)⟩) :
    ∀i,u.scalarHeap (A+count K+i.val)=some (UniformRadixTwoMachine.preparedScalar
      ((fourierMatrix (width K)).mulVec (fun i=>(padded K M input i).value) i)) := by
  intro i
  rw [h i,UniformOffsetLinearMachine.TaggedFFT.dependencyValue_prepared K _ (padded_prepared K M input hp)]
  rfl

end
end ExactFourierCircuits.UniformFFTInputMachine
