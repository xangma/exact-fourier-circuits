import UniformAllAxisSeedPreparation
import UniformTensorDiagonalBankMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisDiagonalPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
namespace D
abbrev Header := UniformTensorDiagonalBankMachine.Header
abbrev Coefficients := UniformTensorDiagonalBankMachine.Coefficients
abbrev Result := UniformTensorDiagonalBankMachine.Result
end D
open UniformAllAxisSeedPreparation (axisCount radix radixAt prefixSum axisBase directoryBase Retained)

/-- Caller Nat330=count,331=directory,332=lane,333=rowBase,334=permutationPool,
335=coefficientPool. The loop carries index336 and prefix337. -/
def boot : List Op := [.literal 336 0,.literal 337 0,.literal 338 1,
  .literal 339 2,.literal 343 0]
def prepare : List Op := [.mul 340 336 339,.add 340 331 340,.getNat 341 340,
  .add 340 340 338,.getNat 170 340,.mul 342 332 170,.add 171 341 342,
  .add 172 334 337,.add 173 335 337,.add 174 333 343,.add 175 336 343]
def advance : List Op := [.add 337 337 170,.add 336 336 338]
def head : Program := boot.map Op.code++[.branchLT 336 330 6 40]++prepare.map Op.code
def program : Program := embed head UniformTensorDiagonalBankMachine.program
  (advance.map Op.code++[.jump 5,.halt]) 37
theorem boot_length : boot.length=5 := rfl
theorem prepare_length : prepare.length=11 := rfl
theorem advance_length : advance.length=2 := rfl
theorem head_length : head.length=17 := rfl
theorem program_length : program.length=41 := rfl
theorem branch_at : program[5]?=some (.branchLT 336 330 6 40) := rfl
theorem jump_at : program[39]?=some (.jump 5) := rfl
theorem halt_at : program[40]?=some .halt := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem prepare_code : BlockAt prepare program 6 := by
  intro i hi;change i < 11 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advance program 37 := by
  intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem diagonal_code : CodeAt UniformTensorDiagonalBankMachine.program program 17 37 := by
  simpa only [program,head_length] using embed_code head UniformTensorDiagonalBankMachine.program
    (advance.map Op.code++[.jump 5,.halt]) 37

noncomputable section
structure Header (n row p c : ℕ) (q : Fin 5) (s : State) : Prop where
  count : s.natReg 330=axisCount n
  directory : s.natReg 331=directoryBase n
  lane : s.natReg 332=q.val
  row : s.natReg 333=row
  permutation : s.natReg 334=p
  coefficient : s.natReg 335=c
structure Cursor (n k : ℕ) (s : State) : Prop where
  index : s.natReg 336=k
  offset : s.natReg 337=prefixSum n k
  one : s.natReg 338=1
  two : s.natReg 339=2
  zero : s.natReg 343=0

def value (n : ℕ) (q : Fin 5) (j : Fin (axisCount n)) (i : Fin (radix n j)) : ℂ :=
  UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta (radix n j)) q i.val
def sourceLane (n : ℕ) (q : Fin 5) (j : Fin (axisCount n)) : ℕ :=
  axisBase n j.val+q.val*radix n j
def axis (n : ℕ) (q : Fin 5) (p c : ℕ) (j : Fin (axisCount n)) : UniformTensorMonomialMachine.Axis :=
  UniformTensorDiagonalBankMachine.identityAxis (radix n j)
    (UniformGlobalLocalPreparation.radix_pos n j) (p+prefixSum n j.val) (c+prefixSum n j.val) (value n q j)
def axes (n : ℕ) (q : Fin 5) (p c : ℕ) : List UniformTensorMonomialMachine.Axis :=
  List.ofFn (axis n q p c)
theorem axes_length (n : ℕ) (q : Fin 5) (p c : ℕ) : (axes n q p c).length=axisCount n := by
  exact List.length_ofFn

structure Limits (n row p c B : ℕ) : Prop where
  code : 41 ≤ B
  directory : directoryBase n+2*axisCount n ≤ row
  rows : row+3*axisCount n ≤ p
  permutation : p+prefixSum n (axisCount n) ≤ B
  source : axisBase n (axisCount n) ≤ c
  coefficient : c+prefixSum n (axisCount n) ≤ B

theorem sourceLane_bound (n : ℕ) (q : Fin 5) (j : Fin (axisCount n)) :
    sourceLane n q j+radix n j ≤ axisBase n (axisCount n) := by
  have hq:=q.isLt
  have hnext:=UniformAllAxisSeedPreparation.axisBase_next n j
  have hmono:=UniformAllAxisSeedPreparation.axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
  have hm: q.val*radix n j+radix n j ≤ 5*radix n j := by nlinarith
  unfold sourceLane;omega

theorem retained_coefficients {n : ℕ} (q : Fin 5) {s : State}
    (h:Retained n (axisCount n) s) (j : Fin (axisCount n)) :
    D.Coefficients (radix n j) (sourceLane n q j) (value n q j) s := by
  intro i
  exact h.coefficients j j.isLt q i

def Frame (n row p c : ℕ) (s t : State) : Prop :=
  t.rootOrders=s.rootOrders ∧ t.outputs=s.outputs ∧
  (∀i,(i < 170 ∨ 180 < i) → (i < 336 ∨ 343 < i) → t.natReg i=s.natReg i) ∧
  (∀i,i ≠ 9 → t.scalarReg i=s.scalarReg i) ∧
  (∀i,(i < row ∨ row+3*axisCount n ≤ i) → (i < p ∨ p+prefixSum n (axisCount n) ≤ i) →
    t.natHeap i=s.natHeap i) ∧
  (∀i,i < c ∨ c+prefixSum n (axisCount n) ≤ i → t.scalarHeap i=s.scalarHeap i)
theorem frame_refl (n row p c : ℕ) (s : State) : Frame n row p c s s :=
  ⟨rfl,rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _=>rfl⟩
theorem frame_trans {n row p c : ℕ} {s t u : State}
    (h:Frame n row p c s t) (h':Frame n row p c t u) : Frame n row p c s u :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,fun i hi hj=>(h'.2.2.1 i hi hj).trans (h.2.2.1 i hi hj),
    fun i hi=>(h'.2.2.2.1 i hi).trans (h.2.2.2.1 i hi),
    fun i hi hj=>(h'.2.2.2.2.1 i hi hj).trans (h.2.2.2.2.1 i hi hj),
    fun i hi=>(h'.2.2.2.2.2 i hi).trans (h.2.2.2.2.2 i hi)⟩

theorem retained_transfer {n row p c B : ℕ} {s t : State} (h:Retained n (axisCount n) s)
    (l:Limits n row p c B) (f:Frame n row p c s t) : Retained n (axisCount n) t := by
  constructor
  · intro j hj q i
    rw [f.2.2.2.2.2 _ (Or.inl ?_)]
    · exact h.coefficients j hj q i
    · have hb:=sourceLane_bound n q j;have hi:=i.isLt
      unfold sourceLane at hb;have hc:=l.source;omega
  · intro j hj
    rw [f.2.2.2.2.1 _ (Or.inl ?_) (Or.inl ?_)]
    · exact h.address j hj
    · have hdir:=l.directory;omega
    · have hdir:=l.directory;have hr:=l.rows;omega
  · intro j hj
    rw [f.2.2.2.2.1 _ (Or.inl ?_) (Or.inl ?_)]
    · exact h.width j hj
    · have hdir:=l.directory;omega
    · have hdir:=l.directory;have hr:=l.rows;omega

theorem blocks_frame (n row p c : ℕ) (s : State) :
    Frame n row p c s (applyBlock boot s) ∧ Frame n row p c s (applyBlock prepare s) ∧
    Frame n row p c s (applyBlock advance s) := by
  refine ⟨?_,?_,?_⟩
  all_goals simp (disch:=omega) [Frame,boot,prepare,advance,applyBlock,Op.apply,writeNat,next]
  all_goals intro i hi hj;simp (disch:=omega)

theorem boot_properties (n row p c : ℕ) (q : Fin 5) (s : State) (h:Header n row p c q s) :
    Header n row p c q (applyBlock boot s) ∧ Cursor n 0 (applyBlock boot s) := by
  rcases h with ⟨hm,hd,hq,hr,hp,hc⟩
  constructor
  · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,hm,hd,hq,hr,hp,hc]
  · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,UniformAllAxisSeedPreparation.prefix_zero]

theorem prepare_properties (n row p c k : ℕ) (q : Fin 5) (s : State)
    (h:Header n row p c q s) (v:Cursor n k s) (hk:k < axisCount n)
    (hr:Retained n (axisCount n) s) :
    Header n row p c q (applyBlock prepare s) ∧ Cursor n k (applyBlock prepare s) ∧
    D.Header (radix n ⟨k,hk⟩) (sourceLane n q ⟨k,hk⟩) (p+prefixSum n k)
      (c+prefixSum n k) row k (applyBlock prepare s) := by
  have a:=hr.address ⟨k,hk⟩ hk
  have r:=hr.width ⟨k,hk⟩ hk
  have a':s.natHeap (directoryBase n+k*2)=some (axisBase n k):=by
    simpa only [Nat.mul_comm] using a
  have r':s.natHeap (directoryBase n+k*2+1)=some (radix n ⟨k,hk⟩):=by
    simpa only [Nat.mul_comm] using r
  rcases h with ⟨hm,hd,hq,hrow,hp,hc⟩;rcases v with ⟨hi,ho,h1,h2,h0⟩
  refine ⟨?_,?_,?_⟩
  all_goals constructor <;> simp [prepare,applyBlock,Op.apply,writeNat,next,hm,hd,hq,hrow,hp,hc,
    hi,ho,h1,h2,h0,sourceLane,a',r']

theorem advance_properties (n row p c k : ℕ) (q : Fin 5) (s : State)
    (h:Header n row p c q s) (v:Cursor n k s) (hk:k < axisCount n)
    (hr:s.natReg 170=radix n ⟨k,hk⟩) :
    Header n row p c q (applyBlock advance s) ∧ Cursor n (k+1) (applyBlock advance s) := by
  rcases h with ⟨hm,hd,hq,hrow,hp,hc⟩;rcases v with ⟨hi,ho,h1,h2,h0⟩
  constructor
  · constructor <;> simp [advance,applyBlock,Op.apply,writeNat,next,hm,hd,hq,hrow,hp,hc]
  · constructor <;> simp [advance,applyBlock,Op.apply,writeNat,next,hi,ho,h1,h2,h0,hr,
      UniformAllAxisSeedPreparation.prefix_succ,radixAt,hk]

theorem header_withPC {n row p c pc : ℕ} {q : Fin 5} {s : State}
    (h:Header n row p c q s) : Header n row p c q (setPC s pc) :=
  ⟨h.count,h.directory,h.lane,h.row,h.permutation,h.coefficient⟩
theorem cursor_withPC {n k pc : ℕ} {s : State} (h:Cursor n k s) : Cursor n k (setPC s pc) :=
  ⟨h.index,h.offset,h.one,h.two,h.zero⟩
theorem setPC_same (s : State) (pc : ℕ) (hp:s.pc=pc) : setPC s pc=s := by
  cases s;simp_all [setPC]
theorem header_frame {n row p c : ℕ} {q : Fin 5} {s t : State}
    (h:Header n row p c q s) (f:UniformTensorDiagonalBankMachine.Frame s t) : Header n row p c q t := by
  constructor
  · exact (f.2.2.1 330 (by omega)).trans h.count
  · exact (f.2.2.1 331 (by omega)).trans h.directory
  · exact (f.2.2.1 332 (by omega)).trans h.lane
  · exact (f.2.2.1 333 (by omega)).trans h.row
  · exact (f.2.2.1 334 (by omega)).trans h.permutation
  · exact (f.2.2.1 335 (by omega)).trans h.coefficient
theorem cursor_frame {n k : ℕ} {s t : State}
    (h:Cursor n k s) (f:UniformTensorDiagonalBankMachine.Frame s t) : Cursor n k t := by
  constructor
  · exact (f.2.2.1 336 (by omega)).trans h.index
  · exact (f.2.2.1 337 (by omega)).trans h.offset
  · exact (f.2.2.1 338 (by omega)).trans h.one
  · exact (f.2.2.1 339 (by omega)).trans h.two
  · exact (f.2.2.1 343 (by omega)).trans h.zero

theorem boot_bounded (n row p c B : ℕ) (x : Fin n → ℂ) (s : State)
    (l:Limits n row p c B) (hpc:s.pc=0) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (applyBlock boot s) := by
  apply block_runs boot program 0 n B x s boot_code hpc hs (by rw [boot_length];have h:=l.code;omega)
  · simp [readable,boot,Op.readable]
  · simp [peak,boot,Op.peak];have h:=l.code;omega

theorem prepare_bounded (n row p c B k : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State)
    (h:Header n row p c q s) (v:Cursor n k s) (hk:k < axisCount n)
    (hr:Retained n (axisCount n) s) (l:Limits n row p c B) (hpc:s.pc=6) (hs:WordBound B s) :
    BoundedRuns program n x B s 11 (applyBlock prepare s) := by
  have a:s.natHeap (directoryBase n+k*2)=some (axisBase n k):=by
    simpa only [Nat.mul_comm] using hr.address ⟨k,hk⟩ hk
  have r:s.natHeap (directoryBase n+k*2+1)=some (radix n ⟨k,hk⟩):=by
    simpa only [Nat.mul_comm] using hr.width ⟨k,hk⟩ hk
  have hp:=UniformAllAxisSeedPreparation.prefix_mono n (show k ≤ axisCount n by omega)
  have hb:=sourceLane_bound n q ⟨k,hk⟩
  have hdir:=l.directory;have hrow:=l.rows;have hperm:=l.permutation
  have hsource:=l.source;have hcoef:=l.coefficient;have hcode:=l.code
  apply block_runs prepare program 6 n B x s prepare_code hpc hs (by rw [prepare_length];omega)
  · simp [readable,prepare,Op.readable,Op.apply,writeNat,next,h.directory,v.index,v.one,v.two,a,r]
  · simp [peak,prepare,Op.peak,Op.apply,writeNat,next,h.directory,h.lane,h.row,h.permutation,
      h.coefficient,v.index,v.offset,v.one,v.two,v.zero,a,r]
    change axisBase n k+q.val*radix n ⟨k,hk⟩+radix n ⟨k,hk⟩ ≤ axisBase n (axisCount n) at hb
    omega

theorem advance_bounded (n row p c B k : ℕ) (x : Fin n → ℂ) (s : State)
    (v:Cursor n k s) (hk:k < axisCount n) (hr:s.natReg 170=radix n ⟨k,hk⟩)
    (l:Limits n row p c B) (hpc:s.pc=37) (hs:WordBound B s) :
    BoundedRuns program n x B s 2 (applyBlock advance s) := by
  have hp:=UniformAllAxisSeedPreparation.prefix_mono n (show k+1 ≤ axisCount n by omega)
  have hnext:=UniformAllAxisSeedPreparation.prefix_succ n k
  rw [UniformAllAxisSeedPreparation.radixAt_eq n ⟨k,hk⟩] at hnext
  have hdir:=l.directory;have hrow:=l.rows;have hperm:=l.permutation;have hcode:=l.code
  apply block_runs advance program 37 n B x s advance_code hpc hs (by rw [advance_length];omega)
  · simp [readable,advance,Op.readable]
  · simp [peak,advance,Op.peak,Op.apply,writeNat,next,v.index,v.offset,v.one,hr];omega

structure Produced (n row p c : ℕ) (q : Fin 5) (j : Fin (axisCount n)) (s : State) : Prop where
  width : s.natHeap (row+j.val*3)=some (radix n j)
  permutationBase : s.natHeap (row+j.val*3+1)=some (p+prefixSum n j.val)
  coefficientBase : s.natHeap (row+j.val*3+2)=some (c+prefixSum n j.val)
  permutation : ∀i:Fin (radix n j),s.natHeap (p+prefixSum n j.val+i.val)=some i.val
  coefficient : ∀i:Fin (radix n j),s.scalarHeap (c+prefixSum n j.val+i.val)=some (UniformPairMachine.prepared (value n q j i))
structure AxisEffect (n row p c : ℕ) (q : Fin 5) (j : Fin (axisCount n)) (s t : State) : Prop where
  produced : Produced n row p c q j t
  natFrame : ∀a,(a < row+j.val*3 ∨ row+j.val*3+3 ≤ a) →
    (a < p+prefixSum n j.val ∨ p+prefixSum n j.val+radix n j ≤ a) → t.natHeap a=s.natHeap a
  scalarFrame : ∀a,a < c+prefixSum n j.val ∨ c+prefixSum n j.val+radix n j ≤ a → t.scalarHeap a=s.scalarHeap a

theorem helper_global_frame {n row p c : ℕ} (q : Fin 5) (j : Fin (axisCount n)) {s t : State}
    (h:D.Result (radix n j) (sourceLane n q j)
      (p+prefixSum n j.val) (c+prefixSum n j.val) row j.val (value n q j) s t) : Frame n row p c s t := by
  have hp:=UniformAllAxisSeedPreparation.prefix_mono n (show j.val+1 ≤ axisCount n by have h:=j.isLt;omega)
  have he:=UniformAllAxisSeedPreparation.prefix_succ n j.val
  rw [UniformAllAxisSeedPreparation.radixAt_eq n j] at he
  refine ⟨h.frame.1,h.frame.2.1,?_,h.frame.2.2.2,?_,?_⟩
  · intro i hi _;apply h.frame.2.2.1;rcases hi with hi|hi <;> omega
  · intro a ha hb
    apply h.natFrame
    · have h:=j.isLt;rcases ha with ha|ha <;> omega
    · rcases hb with hb|hb <;> omega
  · intro a ha;apply h.scalarFrame;rcases ha with ha|ha <;> omega

/-- One directory read and actual compact-lane copy, with every call setup,
index update and relocated continuation charged in the literal driver. -/
theorem iteration_execution (n row p c B k : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State)
    (h:Header n row p c q s) (v:Cursor n k s) (hk:k < axisCount n)
    (hr:Retained n (axisCount n) s) (l:Limits n row p c B) (hpc:s.pc=5) (hs:WordBound B s) : ∃t,
    BoundedRuns program n x B s (9*radix n ⟨k,hk⟩+27) t ∧ t.pc=5 ∧
    Header n row p c q t ∧ Cursor n (k+1) t ∧ Retained n (axisCount n) t ∧
    Frame n row p c s t ∧ AxisEffect n row p c q ⟨k,hk⟩ s t := by
  let a:=setPC s 6
  have hab:WordBound B a:=changePC_bound B s 6 hs (by have h:=l.code;omega)
  have branch:BoundedRuns program n x B s 1 a:=.next hs
    (by simp [step,hpc,branch_at,h.count,v.index,hk,a,setPC]) (.refl hab)
  have ah:=header_withPC (pc:=6) h
  have av:=cursor_withPC (pc:=6) v
  have ar:Retained n (axisCount n) a:=⟨hr.coefficients,hr.address,hr.width⟩
  have prep:=prepare_bounded n row p c B k q x a ah av hk ar l rfl hab
  let b:=applyBlock prepare a
  have bp:b.pc=17:=by rw [UniformTensorMonomialMachine.applyBlock_pc,prepare_length];rfl
  have bprops:=prepare_properties n row p c k q a ah av hk ar
  let entry:=setPC b 0
  have eb:WordBound B entry:=changePC_bound B b 0 prep.final_bound (by omega)
  have ready:D.Coefficients (radix n ⟨k,hk⟩) (sourceLane n q ⟨k,hk⟩) (value n q ⟨k,hk⟩) entry:=by
    intro i;exact (retained_coefficients q hr ⟨k,hk⟩) i
  have eheader:D.Header (radix n ⟨k,hk⟩) (sourceLane n q ⟨k,hk⟩) (p+prefixSum n k)
      (c+prefixSum n k) row k entry:=by
    exact ⟨bprops.2.2.width,bprops.2.2.source,bprops.2.2.permutation,bprops.2.2.coefficient,
      bprops.2.2.row,bprops.2.2.depth⟩
  have hsum:=UniformAllAxisSeedPreparation.prefix_mono n (show k+1 ≤ axisCount n by omega)
  have hnext:=UniformAllAxisSeedPreparation.prefix_succ n k
  rw [UniformAllAxisSeedPreparation.radixAt_eq n ⟨k,hk⟩] at hnext
  have hsource:=sourceLane_bound n q ⟨k,hk⟩
  have hd:=l.directory;have hr':=l.rows;have hp:=l.permutation;have hc:=l.coefficient
  have hsrc:=l.source;have hcode:=l.code
  obtain ⟨call,e⟩:=UniformTensorDiagonalBankMachine.complete_execution B n (radix n ⟨k,hk⟩)
    (sourceLane n q ⟨k,hk⟩) (p+prefixSum n k) (c+prefixSum n k) row k x (value n q ⟨k,hk⟩)
    entry eheader rfl ready (Or.inl (by omega)) (Or.inl (by omega))
    (by omega) (by omega) (by omega) (by omega) eb
  let d:=setPC (UniformTensorDiagonalBankMachine.finalState (radix n ⟨k,hk⟩) entry) 37
  have called:BoundedRuns program n x B b (9*radix n ⟨k,hk⟩+12) d:=by
    have rr:=UniformBoundedAssembly.boundedExecution_placed diagonal_code (by rw [UniformTensorDiagonalBankMachine.program_length];omega)
      (by omega) call
    have he:placed 17 entry=b:=setPC_same b 17 bp
    simpa only [he,d,setPC] using rr
  have dh:=header_withPC (pc:=37) (header_frame (header_withPC (pc:=0) bprops.1) e.frame)
  have dv:=cursor_withPC (pc:=37) (cursor_frame (cursor_withPC (pc:=0) bprops.2.1) e.frame)
  have dr:d.natReg 170=radix n ⟨k,hk⟩:=e.header.width
  have post:=advance_bounded n row p c B k x d dv hk dr l rfl called.final_bound
  let t:=setPC (applyBlock advance d) 5
  have postpc:(applyBlock advance d).pc=39:=by rw [UniformTensorMonomialMachine.applyBlock_pc,advance_length];rfl
  have tb:WordBound B t:=changePC_bound B _ 5 post.final_bound (by omega)
  have jump:BoundedRuns program n x B (applyBlock advance d) 1 t:=.next post.final_bound
    (by rw [step,postpc,jump_at];rfl) (.refl tb)
  have tp:=advance_properties n row p c k q d dh dv hk dr
  have fg:=helper_global_frame q ⟨k,hk⟩ e
  have fb:= (blocks_frame n row p c a).2.1
  have fd:= (blocks_frame n row p c d).2.2
  have all:Frame n row p c s t:=frame_trans fb (frame_trans fg fd)
  refine ⟨t,?_,rfl,header_withPC tp.1,cursor_withPC tp.2,retained_transfer hr l all,all,?_,⟩
  · convert branch.trans (prep.trans (called.trans (post.trans jump))) using 1
    omega
  · refine ⟨⟨e.rowWidth,e.rowPermutation,e.rowCoefficient,e.permutation,e.coefficient⟩,?_,?_⟩
    · intro addr hrow hperm;exact e.natFrame addr hrow hperm
    · intro addr haddr;exact e.scalarFrame addr haddr

def Written (n row p c k : ℕ) (q : Fin 5) (s : State) : Prop :=
  ∀j:Fin (axisCount n),j.val < k → Produced n row p c q j s

theorem previous_transfer {n row p c B : ℕ} (q : Fin 5) (j k : Fin (axisCount n))
    (hjk:j.val < k.val) {s t : State} (l:Limits n row p c B)
    (e:AxisEffect n row p c q k s t) (h:Produced n row p c q j s) : Produced n row p c q j t := by
  have hp:=UniformAllAxisSeedPreparation.prefix_mono n (show j.val+1 ≤ k.val by omega)
  have he:=UniformAllAxisSeedPreparation.prefix_succ n j.val
  rw [UniformAllAxisSeedPreparation.radixAt_eq n j] at he
  have hrows:=l.rows;have hj:=j.isLt;have hk:=k.isLt
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [e.natFrame _ (Or.inl (by omega)) (Or.inl (by omega))];exact h.width
  · rw [e.natFrame _ (Or.inl (by omega)) (Or.inl (by omega))];exact h.permutationBase
  · rw [e.natFrame _ (Or.inl (by omega)) (Or.inl (by omega))];exact h.coefficientBase
  · intro i;have hi:=i.isLt
    rw [e.natFrame _ (Or.inr (by omega)) (Or.inl (by omega))];exact h.permutation i
  · intro i;have hi:=i.isLt
    rw [e.scalarFrame _ (Or.inl (by omega))];exact h.coefficient i

theorem written_advance {n row p c B k : ℕ} (q : Fin 5) (hk:k < axisCount n) {s t : State}
    (l:Limits n row p c B) (e:AxisEffect n row p c q ⟨k,hk⟩ s t)
    (h:Written n row p c k q s) : Written n row p c (k+1) q t := by
  intro j hj
  by_cases he:j.val=k
  · have je:j=⟨k,hk⟩:=Fin.ext he;subst j;exact e.produced
  · exact previous_transfer q j ⟨k,hk⟩ (by change j.val < k;omega) l e (h j (by omega))

def loopCost (n : ℕ) : ℕ → ℕ → ℕ
  | _,0=>0
  | k,f+1=>9*radixAt n k+27+loopCost n (k+1) f
theorem loopCost_formula (n k f : ℕ) (hf:k+f ≤ axisCount n) :
    loopCost n k f+9*prefixSum n k=9*prefixSum n (k+f)+27*f := by
  induction f generalizing k with
  | zero=>simp [loopCost]
  | succ f ih=>
    have hk:k < axisCount n:=by omega
    have h:=ih (k+1) (by omega)
    have he:=UniformAllAxisSeedPreparation.prefix_succ n k
    rw [loopCost]
    have ha:k+1+f=k+(f+1):=by omega
    rw [ha] at h
    omega

theorem loop (n row p c B k f : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State)
    (h:Header n row p c q s) (v:Cursor n k s) (hf:k+f ≤ axisCount n)
    (hr:Retained n (axisCount n) s) (hw:Written n row p c k q s)
    (l:Limits n row p c B) (hpc:s.pc=5) (hs:WordBound B s) : ∃t,
    BoundedRuns program n x B s (loopCost n k f) t ∧ t.pc=5 ∧
    Header n row p c q t ∧ Cursor n (k+f) t ∧ Retained n (axisCount n) t ∧
    Written n row p c (k+f) q t ∧ Frame n row p c s t := by
  induction f generalizing k s with
  | zero=>exact ⟨s,.refl hs,hpc,h,v,hr,hw,frame_refl n row p c s⟩
  | succ f ih=>
    have hk:k < axisCount n:=by omega
    obtain ⟨t,run,tp,th,tv,tr,tf,te⟩:=iteration_execution n row p c B k q x s h v hk hr l hpc hs
    have tw:=written_advance q hk l te hw
    obtain ⟨u,rest,up,uh,uv,ur,uw,uf⟩:=ih (k+1) t th tv (by omega) tr tw tp run.final_bound
    refine ⟨u,?_,up,uh,?_,ur,?_,frame_trans tf uf⟩
    · convert run.trans rest using 1
      rw [loopCost,UniformAllAxisSeedPreparation.radixAt_eq n ⟨k,hk⟩]
    · simpa only [show k+1+f=k+(f+1) by omega] using uv
    · simpa only [show k+1+f=k+(f+1) by omega] using uw

/-- Complete actual directory traversal. All five compact source lanes and
the directory remain present while the new banks are emitted. -/
theorem execution (n row p c B : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State)
    (h:Header n row p c q s) (hr:Retained n (axisCount n) s)
    (l:Limits n row p c B) (hpc:s.pc=0) (hs:WordBound B s) : ∃t,
    BoundedExecution program n x B s (9*prefixSum n (axisCount n)+27*axisCount n+7) t ∧
    t.pc=40 ∧ Header n row p c q t ∧ Cursor n (axisCount n) t ∧
    Retained n (axisCount n) t ∧ Written n row p c (axisCount n) q t ∧ Frame n row p c s t := by
  have start:=boot_bounded n row p c B x s l hpc hs
  let a:=applyBlock boot s
  have ap:a.pc=5:=by rw [UniformTensorMonomialMachine.applyBlock_pc,boot_length,hpc]
  have av:=boot_properties n row p c q s h
  have af:Frame n row p c s a:=(blocks_frame n row p c s).1
  obtain ⟨u,run,up,uh,uv,ur,uw,uf⟩:=loop n row p c B 0 (axisCount n) q x a av.1 av.2
    (by omega) (retained_transfer hr l af) (by intro j hj;omega) l ap start.final_bound
  let t:=setPC u 40
  have tb:WordBound B t:=changePC_bound B u 40 run.final_bound (by have h:=l.code;omega)
  have tail:BoundedExecution program n x B u 2 t:=by
    refine .next run.final_bound ?_ (.halt tb ?_)
    · simp [step,up,branch_at,uh.count,uv.index,t,setPC]
    · simp [step,t,setPC,halt_at]
  have hcost:=loopCost_formula n 0 (axisCount n) (by omega)
  rw [UniformAllAxisSeedPreparation.prefix_zero] at hcost
  simp only [Nat.zero_add] at uv uw hcost
  refine ⟨t,?_,rfl,header_withPC uh,cursor_withPC uv,?_,?_,frame_trans af uf⟩
  · convert start.executes (run.executes tail) using 1
    omega
  · exact ⟨ur.coefficients,ur.address,ur.width⟩
  · intro j hj
    have z:=uw j hj
    exact ⟨z.width,z.permutationBase,z.coefficientBase,z.permutation,z.coefficient⟩

theorem rows_of_lookup (as : List UniformTensorMonomialMachine.Axis) (d row : ℕ) (s : State)
    (h:∀k a,as[k]?=some a → s.natHeap (row+(d+k)*3)=some a.radix ∧
      s.natHeap (row+(d+k)*3+1)=some a.permutationBase ∧
      s.natHeap (row+(d+k)*3+2)=some a.coefficientBase) :
    UniformTensorMonomialMachine.Rows as d row s := by
  induction as generalizing d with
  | nil=>trivial
  | cons a as ih=>
    have head:=h 0 a rfl
    refine ⟨by simpa using head.1,by simpa using head.2.1,by simpa using head.2.2,ih (d+1) ?_⟩
    intro k b hb
    have next:=h (k+1) b (by simpa using hb)
    simpa only [show d+1+k=d+(k+1) by omega] using next

theorem written_banks (n p c : ℕ) (q : Fin 5) (L : UniformTensorMonomialMachine.Layout) (s : State)
    (h:Written n L.row p c (axisCount n) q s)
    (hp:p+prefixSum n (axisCount n) ≤ L.natStack) (hc:c+prefixSum n (axisCount n) ≤ L.scalarStack) :
    UniformTensorMonomialMachine.Banks (axes n q p c) 0 L s := by
  constructor
  · apply rows_of_lookup
    intro k a ha
    obtain ⟨hk,hka⟩:=List.getElem?_eq_some_iff.mp ha
    have hk':k < axisCount n:=by simpa only [axes_length] using hk
    have ae:a=axis n q p c ⟨k,hk'⟩:=by
      simpa only [axes,List.getElem_ofFn] using hka.symm
    have z:=h ⟨k,hk'⟩ hk'
    rw [ae]
    simp only [Nat.zero_add]
    change s.natHeap (L.row+k*3)=some (radix n ⟨k,hk'⟩) ∧
      s.natHeap (L.row+k*3+1)=some (p+prefixSum n k) ∧
      s.natHeap (L.row+k*3+2)=some (c+prefixSum n k)
    exact ⟨z.width,z.permutationBase,z.coefficientBase⟩
  · intro a ha i
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    exact (h j j.isLt).permutation i
  · intro a ha i
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    exact (h j j.isLt).coefficient i
  · intro a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    have he:=UniformAllAxisSeedPreparation.prefix_succ n j.val
    rw [UniformAllAxisSeedPreparation.radixAt_eq n j] at he
    have hm:=UniformAllAxisSeedPreparation.prefix_mono n (show j.val+1 ≤ axisCount n by have h:=j.isLt;omega)
    change p+prefixSum n j.val+radix n j ≤ L.natStack
    omega
  · intro a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    have he:=UniformAllAxisSeedPreparation.prefix_succ n j.val
    rw [UniformAllAxisSeedPreparation.radixAt_eq n j] at he
    have hm:=UniformAllAxisSeedPreparation.prefix_mono n (show j.val+1 ≤ axisCount n by have h:=j.isLt;omega)
    change c+prefixSum n j.val+radix n j ≤ L.scalarStack
    omega

theorem prefix_count (n k : ℕ) (hk:k ≤ axisCount n) : k ≤ prefixSum n k := by
  induction k with
  | zero=>omega
  | succ k ih=>
    have h:=ih (by omega)
    have hk':k < axisCount n:=by omega
    have hp:0 < radix n ⟨k,hk'⟩:=UniformGlobalLocalPreparation.radix_pos n ⟨k,hk'⟩
    have he:=UniformAllAxisSeedPreparation.prefix_succ n k
    rw [UniformAllAxisSeedPreparation.radixAt_eq n ⟨k,hk'⟩] at he
    omega
theorem linear_cost (n : ℕ) : 9*prefixSum n (axisCount n)+27*axisCount n+7 ≤ 36*prefixSum n (axisCount n)+7 := by
  have h:=prefix_count n (axisCount n) (le_refl _);omega

theorem protected_frame {n row p c B : ℕ} {s t : State} (l:Limits n row p c B)
    (f:Frame n row p c s t) : UniformAllAxisSeedPreparation.ProtectedFrame n s t := by
  have hd:=l.directory;have hr:=l.rows;have hc:=l.source
  have hpool:UniformGlobalLocalPreparation.globalEnd n ≤ axisBase n (axisCount n):=by
    unfold axisBase UniformLocalSeedTableMachine.poolBase;omega
  refine ⟨?_,?_,?_,f.2.1,f.1⟩
  · intro i _ hi;apply f.2.2.2.2.1 <;> exact Or.inl (by omega)
  · intro i hi;exact f.2.2.2.2.2 i (Or.inl (by omega))
  · intro i hi hj;exact f.2.2.1 i (Or.inl (by omega)) (Or.inl (by omega))

/-- Actual complete tensor banks, from the retained physical compact source,
with the selected protected metadata and operand banks preserved. -/
theorem execution_banks (n p c : ℕ) (q : Fin 5) (x : Fin n → ℂ)
    (L : UniformTensorMonomialMachine.Layout) (s : State)
    (h:Header n L.row p c q s) (hr:Retained n (axisCount n) s)
    (l:Limits n L.row p c L.B) (hp:p+prefixSum n (axisCount n) ≤ L.natStack)
    (hc:c+prefixSum n (axisCount n) ≤ L.scalarStack)
    (hm:UniformPermutationInversePreparation.Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hpc:s.pc=0) (hs:WordBound L.B s) : ∃t,
    BoundedExecution program n x L.B s (9*prefixSum n (axisCount n)+27*axisCount n+7) t ∧
    UniformTensorMonomialMachine.Banks (axes n q p c) 0 L t ∧ Retained n (axisCount n) t ∧
    UniformPermutationInversePreparation.Metadata n t ∧ UniformInitialPreparation.Operands n x t ∧
    Frame n L.row p c s t ∧ t.pc=40 := by
  obtain ⟨t,run,tp,_,_,tr,tw,tf⟩:=execution n L.row p c L.B q x s h hr l hpc hs
  have pf:=protected_frame l tf
  exact ⟨t,run,written_banks n p c q L t tw hp hc,tr,pf.metadata hm,pf.operands ho,tf,tp⟩

def rowPool (n : ℕ) : ℕ := directoryBase n+2*axisCount n
def permutationPool (n : ℕ) : ℕ := rowPool n+3*axisCount n
def coefficientPool (n : ℕ) : ℕ := axisBase n (axisCount n)
/-- Explicit fresh pool envelopes fit the selected ambient word bound. The
entry registers are still physical caller arguments, not free table rows. -/
theorem selected_pools_fit {n : ℕ} (hn:0 < n) :
    Limits n (rowPool n) (permutationPool n) (coefficientPool n) ((n+2)^19) := by
  have he:UniformInitialPreparation.ell n ≤ 2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold UniformInitialPreparation.ell UniformWorkingLength.axisCount;omega
  have hL:UniformInitialPreparation.len n < 4*n:=UniformWorkingLength.workingLength_upper hn
  have hT:=UniformAllAxisSeedPreparation.prefix_bound n (axisCount n) (le_refl _)
  have hprod:(UniformInitialPreparation.ell n+1)*UniformInitialPreparation.len n ≤ (2*n+1)*(4*n):=
    Nat.mul_le_mul (by omega) (by omega)
  have hT':prefixSum n (axisCount n) ≤ (2*n+1)*(4*n):=hT.trans hprod
  have hs:300 ≤ (n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 17;norm_num at h;omega
  have hb:300*(n+2)^2 ≤ (n+2)^19:=by
    rw [show 19=17+2 by decide,pow_add];exact Nat.mul_le_mul_right ((n+2)^2) hs
  have hp:permutationPool n+prefixSum n (axisCount n) ≤ 300*(n+2)^2:=by
    unfold permutationPool rowPool axisCount
    rw [UniformAllAxisSeedPreparation.directory_formula]
    nlinarith
  have hc:coefficientPool n+prefixSum n (axisCount n) ≤ 300*(n+2)^2:=by
    unfold coefficientPool axisBase UniformLocalSeedTableMachine.poolBase
    rw [UniformGlobalLocalPreparation.globalEnd_formula]
    nlinarith
  exact ⟨by nlinarith,le_refl _,le_refl _,hp.trans hb,le_refl _,hc.trans hb⟩

theorem axes_radices (n p c : ℕ) (q : Fin 5) :
    UniformTensorMonomialMachine.radices (axes n q p c)=UniformSelectedDFSMachine.selectedRadices n := by
  simp [UniformTensorMonomialMachine.radices,axes,axis,UniformTensorDiagonalBankMachine.identityAxis,
    UniformSelectedDFSMachine.selectedRadices]
  funext i;rfl
theorem axes_volume (n p c : ℕ) (q : Fin 5) :
    (UniformTensorMonomialMachine.radices (axes n q p c)).prod=UniformInitialPreparation.len n := by
  rw [axes_radices,UniformSelectedDFSMachine.selectedRadices_product]

/-- Producer halt and consumer halt are charged jumps; one final halt closes
the single literal108-instruction composition. -/
def fullProgram : Program := embed [] program
  (UniformTensorMonomialMachine.program.map (relocate 41 107)++[.halt]) 41
theorem fullProgram_length : fullProgram.length=108 := rfl
theorem producer_code : CodeAt program fullProgram 0 41 :=
  by simpa only [fullProgram,List.length_nil] using embed_code ([]:Program) program
      (UniformTensorMonomialMachine.program.map (relocate 41 107)++[.halt]) 41
theorem tensor_code : CodeAt UniformTensorMonomialMachine.program fullProgram 41 107 := by
  intro i hi
  have hi':i < 66:=by simpa only [UniformTensorMonomialMachine.program_length] using hi
  simp only [fullProgram,embed,List.nil_append]
  rw [List.getElem?_append_right (by simp only [List.length_map,program_length];omega)]
  simp only [List.length_map,program_length,show 41+i-41=i by omega]
  rw [List.getElem?_append_left (by simp only [List.length_map,UniformTensorMonomialMachine.program_length];omega)]
  simp only [List.getElem?_map]
theorem full_halt : fullProgram[107]?=some .halt := rfl

/-- Actual producer-to-tensor execution. The complete output banks are
derived inside the proof. Caller data and disjoint physical placements are
the remaining entry premises, with no tensor action/table certificate. -/
theorem full_execution (n p c : ℕ) (q : Fin 5) (x : Fin n → ℂ)
    (L : UniformTensorMonomialMachine.Layout) (s : State)
    (h:Header n L.row p c q s) (hr:Retained n (axisCount n) s)
    (l:Limits n L.row p c L.B) (hp:p+prefixSum n (axisCount n) ≤ L.natStack)
    (hc:c+prefixSum n (axisCount n) ≤ L.scalarStack)
    (hinput:L.source+L.volume ≤ c) (hell:L.ell=axisCount n) (hvolume:L.volume=UniformInitialPreparation.len n)
    (hcall:UniformTensorMonomialMachine.Call L s) (hsrc:UniformTensorMonomialMachine.SourceAt L s)
    (hcode:108 ≤ L.B) (hpc:s.pc=0) (hs:WordBound L.B s) : ∃u,
    BoundedExecution fullProgram n x L.B s
      (9*prefixSum n (axisCount n)+27*axisCount n+
        UniformTensorMonomialMachine.treeCost (UniformSelectedDFSMachine.selectedRadices n)+18) u ∧
    u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
    ∀j:Fin (UniformTensorMonomialMachine.radices (axes n q p c)).prod,∀v,
      s.scalarHeap (L.source+j.val)=some v →
      u.scalarHeap (L.destination+(UniformTensorMonomialMachine.tensorPermutation (axes n q p c) j).val)=
        some (UniformPairMachine.product (UniformTensorMonomialMachine.tensorCoefficient (axes n q p c) j) v) := by
  obtain ⟨t,run,tp,_,_,_,tw,tf⟩:=execution n L.row p c L.B q x s h hr l hpc hs
  have banks:=written_banks n p c q L t tw hp hc
  let entry:=setPC t 0
  have eb:WordBound L.B entry:=changePC_bound L.B t 0 run.final_bound (by omega)
  have ec:UniformTensorMonomialMachine.Call L entry:=by
    constructor
    · exact (tf.2.2.1 1 (by omega) (by omega)).trans hcall.axes
    · exact (tf.2.2.1 5 (by omega) (by omega)).trans hcall.row
    · exact (tf.2.2.1 6 (by omega) (by omega)).trans hcall.natStack
    · exact (tf.2.2.1 7 (by omega) (by omega)).trans hcall.source
    · exact (tf.2.2.1 15 (by omega) (by omega)).trans hcall.destination
    · exact (tf.2.2.1 16 (by omega) (by omega)).trans hcall.scalarStack
  have es:UniformTensorMonomialMachine.SourceAt L entry:=by
    intro j hj
    have hf:=tf.2.2.2.2.2 (L.source+j) (Or.inl (by omega))
    obtain ⟨v,hv⟩:=hsrc j hj
    exact ⟨v,hf.trans hv⟩
  have be:=UniformTensorMonomialMachine.banks_transfer (axes n q p c) 0 L t entry
    (by rw [axes_length,hell];omega) banks (fun _ _=>rfl) (fun _ _=>rfl)
  obtain ⟨consumer,ce,action⟩:=UniformTensorMonomialMachine.tensor_execution (axes n q p c) L n x entry rfl
    (hell.trans (axes_length n q p c).symm) (hvolume.trans (axes_volume n p c q).symm) ec be es eb
  have producer:=UniformBoundedAssembly.boundedExecution_placed producer_code
    (by rw [program_length];omega) (by omega) run
  let final:=setPC (UniformTensorMonomialMachine.finalState (axes n q p c) entry) 107
  have tensor:=UniformBoundedAssembly.boundedExecution_placed tensor_code
    (by rw [UniformTensorMonomialMachine.program_length];omega) (by omega) consumer
  have tensorStart:placed 41 entry=setPC t 41:=rfl
  have initialEq:placed 0 s=s:=by change setPC s (0+s.pc)=s;simpa using setPC_same s s.pc rfl
  rw [initialEq] at producer
  rw [tensorStart] at tensor
  have halt:BoundedExecution fullProgram n x L.B final 1 final:=.halt tensor.final_bound
    (by simp [step,final,setPC,full_halt])
  refine ⟨final,?_,ce.frame.1.trans tf.1,ce.frame.2.1.trans tf.2.1,?_,⟩
  · convert producer.executes (tensor.executes halt) using 1
    rw [axes_radices];omega
  · intro j v hv
    apply action j v
    have hj:j.val < L.volume:=by rw [hvolume,←axes_volume n p c q];exact j.isLt
    exact (tf.2.2.2.2.2 _ (Or.inl (by omega))).trans hv

end
end ExactFourierCircuits.UniformAllAxisDiagonalPreparation
