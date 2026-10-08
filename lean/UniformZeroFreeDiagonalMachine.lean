import UniformReciprocalMachine
import UniformDiagonal

set_option autoImplicit false
namespace ExactFourierCircuits.UniformZeroFreeDiagonalMachine
open UniformMachine
open UniformReciprocalMachine (Op applyBlock readable peak BlockAt block_runs prepared)
open scoped BigOperators

/-- Width370, original371, conjugates372, shift373, differences374,
    inverse differences375. Scratch Nat376..379 and Scalar10..15. -/
def boot : List Op := [.literal 376 0,.literal 377 1,
  .literalScalar 10 1,.literalScalar 15 1]
def sumBody : List Op := [.add 378 371 376,.getScalar 11 378,
  .add 379 372 376,.getScalar 12 379,.field .mul 13 11 12,
  .field .add 10 10 13,.add 376 376 377]
def between : List Op := [.putScalar 373 10,.field .div 14 15 10,
  .add 378 373 377,.putScalar 378 14,.literal 376 0]
def inverseBody : List Op := [.add 378 371 376,.getScalar 11 378,
  .field .sub 11 11 10,.field .div 14 15 11,.add 378 374 376,
  .putScalar 378 11,.add 378 375 376,.putScalar 378 14,.add 376 376 377]
def program : Program := boot.map Op.code ++ [.branchLT 376 370 5 13] ++
  sumBody.map Op.code ++ [.jump 4] ++ between.map Op.code ++
  [.branchLT 376 370 19 29] ++ inverseBody.map Op.code ++ [.jump 18,.halt]
theorem program_length : program.length=30 := rfl
theorem sum_branch : program[4]?=some (.branchLT 376 370 5 13) := rfl
theorem sum_jump : program[12]?=some (.jump 4) := rfl
theorem inverse_branch : program[18]?=some (.branchLT 376 370 19 29) := rfl
theorem inverse_jump : program[28]?=some (.jump 18) := rfl
theorem halt_at : program[29]?=some .halt := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem sum_code : BlockAt sumBody program 5 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl
theorem between_code : BlockAt between program 13 := by
  intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem inverse_code : BlockAt inverseBody program 19 := by
  intro i hi;change i<9 at hi;interval_cases i <;> rfl

noncomputable section
structure Header (k a b d e f : ℕ) (s : State) : Prop where
  width : s.natReg 370=k
  original : s.natReg 371=a
  conjugates : s.natReg 372=b
  shift : s.natReg 373=d
  differences : s.natReg 374=e
  inverseDifferences : s.natReg 375=f

def Sources {k : ℕ} (a b : ℕ) (c : Fin k→ℂ) (s : State) : Prop :=
  ∀j:Fin k,s.scalarHeap (a+j.val)=some (prepared (c j)) ∧
    s.scalarHeap (b+j.val)=some (prepared (starRingEnd ℂ (c j)))
def partialSum {k : ℕ} (c : Fin k→ℂ) (i : ℕ) : ℂ :=
  1+∑j∈Finset.range i,if h:j<k then c ⟨j,h⟩*starRingEnd ℂ (c ⟨j,h⟩) else 0

theorem partial_zero {k : ℕ} (c : Fin k→ℂ) : partialSum c 0=1 := by simp [partialSum]
theorem partial_succ {k : ℕ} (c : Fin k→ℂ) (i : ℕ) (hi:i<k) :
    partialSum c (i+1)=partialSum c i+c ⟨i,hi⟩*starRingEnd ℂ (c ⟨i,hi⟩) := by
  simp only [partialSum,Finset.sum_range_succ,dite_eq_left hi];ring
theorem partial_full {k : ℕ} (c : Fin k→ℂ) : partialSum c k=UniformDiagonal.shift c := by
  unfold partialSum UniformDiagonal.shift
  congr 1
  rw [←Fin.sum_univ_eq_sum_range]
  simp

def setPC (s : State) (pc : ℕ) : State := {s with pc:=pc}
def sumIteration (s : State) : State := setPC (applyBlock sumBody (setPC s 5)) 4

def Frame (s t : State) : Prop := t.natHeap=s.natHeap ∧ t.rootOrders=s.rootOrders ∧
  t.outputs=s.outputs ∧ (∀r,(r<376 ∨ 380≤r)→t.natReg r=s.natReg r) ∧
  (∀r,(r<10 ∨ 16≤r)→t.scalarReg r=s.scalarReg r)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem frame_trans {s t u : State} (h:Frame s t) (h':Frame t u) : Frame s u := by
  refine ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,?_,?_⟩
  · intro r hr;exact (h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr)
  · intro r hr;exact (h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)

theorem sum_properties {k : ℕ} (a b d e f i : ℕ) (c : Fin k→ℂ) (s : State)
    (h:Header k a b d e f s) (hi:s.natReg 376=i) (h1:s.natReg 377=1)
    (hc:s.scalarReg 10=prepared (partialSum c i)) (hir:i<k) (hs:Sources a b c s) :
    Header k a b d e f (sumIteration s) ∧ (sumIteration s).natReg 376=i+1 ∧
    (sumIteration s).natReg 377=1 ∧
    (sumIteration s).scalarReg 10=prepared (partialSum c (i+1)) ∧
    (sumIteration s).scalarReg 15=s.scalarReg 15 ∧
    (sumIteration s).scalarHeap=s.scalarHeap ∧ (sumIteration s).pc=4 ∧
    Frame s (sumIteration s) := by
  obtain ⟨ha,hb⟩:=hs ⟨i,hir⟩
  rcases h with ⟨h370,h371,h372,h373,h374,h375⟩
  constructor
  · constructor <;> simp [sumIteration,setPC,applyBlock,sumBody,Op.apply,
      writeNat,writeScalar,next,h370,h371,h372,h373,h374,h375]
  · simp (disch:=omega) [sumIteration,setPC,applyBlock,sumBody,Op.apply,writeNat,
      writeScalar,next,hi,h1,h371,h372,ha,hb,hc,prepared,evalField,partial_succ c i hir,Frame]
    constructor <;> intro r hr <;> simp (disch:=omega)

structure SumCursor (k a b d e f i : ℕ) (c : Fin k→ℂ) (s : State) : Prop where
  header : Header k a b d e f s
  pc : s.pc=4
  index : s.natReg 376=i
  one : s.natReg 377=1
  accumulator : s.scalarReg 10=prepared (partialSum c i)
  unit : s.scalarReg 15=prepared 1

theorem sum_bounded {k : ℕ} (B n a b d e f i : ℕ) (x : Fin n→ℂ)
    (c : Fin k→ℂ) (s : State) (h:SumCursor k a b d e f i c s)
    (hi:i<k) (hsrc:Sources a b c s) (hB:30≤B) (ha:a+k≤B) (hb:b+k≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 9 (sumIteration s) := by
  let t:=setPC s 5
  have ht:WordBound B t:=changePC_bound B s 5 hs (by omega)
  obtain ⟨sa,sb⟩:=hsrc ⟨i,hi⟩
  have hr:readable sumBody t:=by
    simp [readable,sumBody,Op.readable,Op.apply,t,setPC,writeNat,writeScalar,next,
      h.header.original,h.header.conjugates,h.index,sa,sb,h.accumulator,prepared,evalField]
  have hk:peak sumBody t≤B:=by
    simp [peak,sumBody,Op.peak,Op.apply,t,setPC,writeNat,writeScalar,next,
      h.header.original,h.header.conjugates,h.index,h.one]
    omega
  have bodyRun:=block_runs sumBody program 5 n B x t sum_code rfl ht (by change 5+7≤B;omega) hr hk
  have ep:(applyBlock sumBody t).pc=12:=by
    rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock sumBody t) 1 (sumIteration s):=
    .next bodyRun.final_bound (by rw [step,ep,sum_jump];rfl)
      (.refl (changePC_bound B _ 4 bodyRun.final_bound (by omega)))
  have enter:BoundedRuns program n x B s 1 t:=.next hs
    (by simp [step,h.pc,sum_branch,h.header.width,h.index,hi,t,setPC]) (.refl ht)
  simpa [sumBody] using enter.trans (bodyRun.trans jump)

theorem sum_loop {k : ℕ} (B n a b d e f i fuel : ℕ) (x : Fin n→ℂ)
    (c : Fin k→ℂ) (s : State) (h:SumCursor k a b d e f i c s)
    (hsrc:Sources a b c s) (hcount:i+fuel=k) (hB:30≤B) (ha:a+k≤B) (hb:b+k≤B)
    (hs:WordBound B s) : ∃t,BoundedRuns program n x B s (9*fuel) t ∧
      SumCursor k a b d e f k c t ∧ t.scalarHeap=s.scalarHeap ∧ Frame s t := by
  induction fuel generalizing i s with
  | zero =>
    have hik:i=k:=by omega
    subst i
    exact ⟨s,.refl hs,h,rfl,frame_refl s⟩
  | succ fuel ih =>
    have hi:i<k:=by omega
    have run:=sum_bounded B n a b d e f i x c s h hi hsrc hB ha hb hs
    have z:=sum_properties a b d e f i c s h.header h.index h.one h.accumulator hi hsrc
    have cursor:SumCursor k a b d e f (i+1) c (sumIteration s):=
      ⟨z.1,z.2.2.2.2.2.2.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1.trans h.unit⟩
    have src:Sources a b c (sumIteration s):=by
      simpa only [Sources,z.2.2.2.2.2.1] using hsrc
    obtain ⟨t,rest,ht,heap,frame⟩:=ih (i+1) (sumIteration s) cursor src (by omega) run.final_bound
    exact ⟨t,by convert run.trans rest using 1;omega,ht,
      heap.trans z.2.2.2.2.2.1,frame_trans z.2.2.2.2.2.2.2 frame⟩

theorem boot_properties {k : ℕ} (a b d e f : ℕ) (c : Fin k→ℂ) (s : State)
    (h:Header k a b d e f s) (hp:s.pc=0) :
    SumCursor k a b d e f 0 c (applyBlock boot s) ∧
      (applyBlock boot s).scalarHeap=s.scalarHeap ∧ Frame s (applyBlock boot s) := by
  rcases h with ⟨h370,h371,h372,h373,h374,h375⟩
  constructor
  · constructor
    · constructor <;> simp [applyBlock,boot,Op.apply,writeNat,writeScalar,next,
        h370,h371,h372,h373,h374,h375]
    all_goals simp [applyBlock,boot,Op.apply,writeNat,writeScalar,next,hp,prepared,partial_zero]
  · constructor
    · rfl
    · simp [Frame,applyBlock,boot,Op.apply,writeNat,writeScalar,next]
      constructor <;> intro r hr <;> simp (disch:=omega)

structure InvCursor (k a b d e f i : ℕ) (c : Fin k→ℂ) (s : State) : Prop where
  header : Header k a b d e f s
  pc : s.pc=18
  index : s.natReg 376=i
  one : s.natReg 377=1
  shift : s.scalarReg 10=prepared (UniformDiagonal.shift c)
  unit : s.scalarReg 15=prepared 1

def inverseIteration (s : State) : State := setPC (applyBlock inverseBody (setPC s 19)) 18

theorem between_properties {k : ℕ} (a b d e f : ℕ) (c : Fin k→ℂ) (s : State)
    (h:SumCursor k a b d e f k c s) :
    InvCursor k a b d e f 0 c (applyBlock between (setPC s 13)) ∧
      (applyBlock between (setPC s 13)).scalarHeap=Function.update
        (Function.update s.scalarHeap d (some (prepared (UniformDiagonal.shift c))))
        (d+1) (some (prepared ((UniformDiagonal.shift c)⁻¹))) ∧
      Frame s (applyBlock between (setPC s 13)) := by
  have acc:s.scalarReg 10=prepared (UniformDiagonal.shift c):=by
    simpa only [partial_full] using h.accumulator
  have hz:=UniformDiagonal.shift_ne_zero c
  constructor
  · constructor
    · rcases h.header with ⟨h370,h371,h372,h373,h374,h375⟩
      constructor <;> simp [applyBlock,between,Op.apply,writeNat,writeScalar,next,setPC,
        h370,h371,h372,h373,h374,h375]
    all_goals simp [applyBlock,between,Op.apply,writeNat,writeScalar,next,setPC,acc,h.unit,h.one]
  · simp [applyBlock,between,Op.apply,writeNat,writeScalar,next,setPC,acc,h.unit,h.one,
      h.header.shift,prepared,evalField,hz,one_div,Frame]
    constructor <;> intro r hr <;> simp (disch:=omega)

theorem between_bounded {k : ℕ} (B n a b d e f : ℕ) (x : Fin n→ℂ)
    (c : Fin k→ℂ) (s : State) (h:SumCursor k a b d e f k c s)
    (hB:30≤B) (hd:d+1≤B) (hs:WordBound B s) :
    BoundedRuns program n x B (setPC s 13) 5 (applyBlock between (setPC s 13)) := by
  have acc:s.scalarReg 10=prepared (UniformDiagonal.shift c):=by
    simpa only [partial_full] using h.accumulator
  have hz:=UniformDiagonal.shift_ne_zero c
  apply block_runs between program 13 n B x (setPC s 13) between_code rfl
    (changePC_bound B s 13 hs (by omega)) (by change 13+5≤B;omega)
  · simp [readable,between,Op.readable,Op.apply,setPC,next,acc,h.unit,prepared,evalField,hz]
  · simp [peak,between,Op.peak,Op.apply,setPC,writeNat,writeScalar,next,h.header.shift,h.one]
    omega

theorem inverse_properties {k : ℕ} (a b d e f i : ℕ) (c : Fin k→ℂ) (s : State)
    (h:InvCursor k a b d e f i c s) (hi:i<k)
    (hc:s.scalarHeap (a+i)=some (prepared (c ⟨i,hi⟩))) :
    InvCursor k a b d e f (i+1) c (inverseIteration s) ∧
      (inverseIteration s).scalarHeap=Function.update
        (Function.update s.scalarHeap (e+i) (some (prepared (c ⟨i,hi⟩-UniformDiagonal.shift c))))
        (f+i) (some (prepared ((c ⟨i,hi⟩-UniformDiagonal.shift c)⁻¹))) ∧
      Frame s (inverseIteration s) := by
  have hz:=UniformDiagonal.coefficient_sub_shift_ne_zero c ⟨i,hi⟩
  constructor
  · constructor
    · rcases h.header with ⟨h370,h371,h372,h373,h374,h375⟩
      constructor <;> simp [inverseIteration,setPC,applyBlock,inverseBody,Op.apply,writeNat,
        writeScalar,next,h370,h371,h372,h373,h374,h375]
    all_goals simp [inverseIteration,setPC,applyBlock,inverseBody,Op.apply,writeNat,
      writeScalar,next,h.shift,h.unit,h.index,h.one]
  · simp [inverseIteration,setPC,applyBlock,inverseBody,Op.apply,writeNat,writeScalar,next,
      h.header.original,h.header.differences,h.header.inverseDifferences,h.index,hc,
      h.shift,h.unit,h.one,prepared,evalField,hz,one_div,Frame]
    constructor <;> intro r hr <;> simp (disch:=omega)

theorem inverse_bounded {k : ℕ} (B n a b d e f i : ℕ) (x : Fin n→ℂ)
    (c : Fin k→ℂ) (s : State) (h:InvCursor k a b d e f i c s) (hi:i<k)
    (hc:s.scalarHeap (a+i)=some (prepared (c ⟨i,hi⟩)))
    (hB:30≤B) (ha:a+k≤B) (he:e+k≤B) (hf:f+k≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 11 (inverseIteration s) := by
  let t:=setPC s 19
  have ht:WordBound B t:=changePC_bound B s 19 hs (by omega)
  have hz:=UniformDiagonal.coefficient_sub_shift_ne_zero c ⟨i,hi⟩
  have hr:readable inverseBody t:=by
    simp [readable,inverseBody,Op.readable,Op.apply,t,setPC,writeNat,writeScalar,next,
      h.header.original,h.index,hc,h.shift,h.unit,prepared,evalField,hz]
  have hk:peak inverseBody t≤B:=by
    simp [peak,inverseBody,Op.peak,Op.apply,t,setPC,writeNat,writeScalar,next,
      h.header.original,h.header.differences,h.header.inverseDifferences,h.index,h.one]
    omega
  have bodyRun:=block_runs inverseBody program 19 n B x t inverse_code rfl ht (by change 19+9≤B;omega) hr hk
  have ep:(applyBlock inverseBody t).pc=28:=by
    rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock inverseBody t) 1 (inverseIteration s):=
    .next bodyRun.final_bound (by rw [step,ep,inverse_jump];rfl)
      (.refl (changePC_bound B _ 18 bodyRun.final_bound (by omega)))
  have enter:BoundedRuns program n x B s 1 t:=.next hs
    (by simp [step,h.pc,inverse_branch,h.header.width,h.index,hi,t,setPC]) (.refl ht)
  simpa [inverseBody] using enter.trans (bodyRun.trans jump)

def Written {k : ℕ} (e f i : ℕ) (c : Fin k→ℂ) (s : State) : Prop :=
  ∀j : Fin k, j.val < i → s.scalarHeap (e+j.val)=some (prepared (c j-UniformDiagonal.shift c)) ∧
    s.scalarHeap (f+j.val)=some (prepared ((c j-UniformDiagonal.shift c)⁻¹))
def Outside (e f i fuel : ℕ) (s t : State) : Prop := ∀r,
  (r<e+i ∨ e+i+fuel≤r)→(r<f+i ∨ f+i+fuel≤r)→t.scalarHeap r=s.scalarHeap r

theorem inverse_loop {k : ℕ} (B n a b d e f i fuel : ℕ) (x : Fin n→ℂ)
    (c : Fin k→ℂ) (s : State) (h:InvCursor k a b d e f i c s)
    (hsrc:Sources a b c s) (hw:Written e f i c s) (hcount:i+fuel=k)
    (hB:30≤B) (ha:a+k≤e) (hb:b+k≤e) (hef:e+k≤f) (hf:f+k≤B)
    (hs:WordBound B s) : ∃t,BoundedRuns program n x B s (11*fuel) t ∧
      InvCursor k a b d e f k c t ∧ Sources a b c t ∧ Written e f k c t ∧
      Outside e f i fuel s t ∧ Frame s t := by
  induction fuel generalizing i s with
  | zero =>
    have hik:i=k:=by omega
    subst i
    exact ⟨s,.refl hs,h,hsrc,hw,fun _ _ _=>rfl,frame_refl s⟩
  | succ fuel ih =>
    have hi:i<k:=by omega
    have hc: s.scalarHeap (a+i)=some (prepared (c ⟨i,hi⟩)):=(hsrc ⟨i,hi⟩).1
    have run:=inverse_bounded B n a b d e f i x c s h hi hc hB (by omega) (by omega) hf hs
    have z:=inverse_properties a b d e f i c s h hi hc
    have src:Sources a b c (inverseIteration s):=by
      intro j
      have hj:=j.isLt
      have old:=hsrc j
      simpa (disch:=omega) [z.2.1] using old
    have written:Written e f (i+1) c (inverseIteration s):=by
      intro j hj
      have hlt:=j.isLt
      by_cases he:j.val=i
      · have je:j=⟨i,hi⟩:=Fin.ext he
        subst j
        simp (disch:=omega) [z.2.1]
      · have old:=hw j (by omega)
        simpa (disch:=omega) [z.2.1] using old
    obtain ⟨t,rest,cursor,src',written',outside,frame⟩:=ih (i+1) (inverseIteration s)
      z.1 src written (by omega) run.final_bound
    refine ⟨t,?_,cursor,src',written',?_,frame_trans z.2.2 frame⟩
    · convert run.trans rest using 1;omega
    · intro r he hf'
      rw [outside r (by omega) (by omega),z.2.1]
      simp (disch:=omega)

theorem frame_pc (s : State) (pc : ℕ) : Frame s (setPC s pc) :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩

def Result {k : ℕ} (d e f : ℕ) (c : Fin k→ℂ) (s : State) : Prop :=
  s.scalarHeap d=some (prepared (UniformDiagonal.shift c)) ∧
    s.scalarHeap (d+1)=some (prepared ((UniformDiagonal.shift c)⁻¹)) ∧ Written e f k c s

def OutsideResult (d e f k : ℕ) (s t : State) : Prop := ∀r,
  (r<d ∨ d+2≤r)→(r<e ∨ e+k≤r)→(r<f ∨ f+k≤r)→t.scalarHeap r=s.scalarHeap r

/-- Every guard follows from the actual prepared original/conjugate banks.
No scalar zero test, free phase write, or supplied nonzero certificate occurs. -/
theorem execution {k : ℕ} (B n a b d e f : ℕ) (x : Fin n→ℂ) (c : Fin k→ℂ)
    (s : State) (hh:Header k a b d e f s) (hp:s.pc=0) (hsrc:Sources a b c s)
    (hB:30≤B) (ha:a+k≤d) (hb:b+k≤d) (hd:d+2≤e) (he:e+k≤f) (hf:f+k≤B)
    (hs:WordBound B s) : ∃t,BoundedExecution program n x B s (20*k+12) t ∧
      t.pc=29 ∧ Result d e f c t ∧ Sources a b c t ∧ OutsideResult d e f k s t ∧ Frame s t := by
  have bootRun:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+4≤B;omega)
    (by simp [readable,boot,Op.readable]) (by simp [peak,boot,Op.peak];omega)
  have z:=boot_properties a b d e f c s hh hp
  have src:Sources a b c (applyBlock boot s):=by simpa only [Sources,z.2.1] using hsrc
  obtain ⟨u,sumRun,hu,heapU,frameU⟩:=sum_loop B n a b d e f 0 k x c (applyBlock boot s)
    z.1 src (by omega) hB (by omega) (by omega) bootRun.final_bound
  have exitSum:BoundedRuns program n x B u 1 (setPC u 13):=.next sumRun.final_bound
    (by simp [step,hu.pc,sum_branch,hu.header.width,hu.index,setPC])
    (.refl (changePC_bound B u 13 sumRun.final_bound (by omega)))
  have betweenRun:=between_bounded B n a b d e f x c u hu hB (by omega) sumRun.final_bound
  let v:=applyBlock between (setPC u 13)
  have hv:=between_properties a b d e f c u hu
  have srcV:Sources a b c v:=by
    intro j
    have hj:=j.isLt
    have old:=hsrc j
    simpa (disch:=omega) [v,hv.2.1,heapU,z.2.1] using old
  have empty:Written e f 0 c v:=by intro j hj;omega
  obtain ⟨w,inverseRun,hw,srcW,writtenW,outsideW,frameW⟩:=inverse_loop B n a b d e f 0 k
    x c v hv.1 srcV empty (by omega) hB (by omega) (by omega) he hf betweenRun.final_bound
  have exitInv:BoundedRuns program n x B w 1 (setPC w 29):=.next inverseRun.final_bound
    (by simp [step,hw.pc,inverse_branch,hw.header.width,hw.index,setPC])
    (.refl (changePC_bound B w 29 inverseRun.final_bound (by omega)))
  have halt:BoundedExecution program n x B (setPC w 29) 1 (setPC w 29):=
    .halt exitInv.final_bound (by simp [step,setPC,halt_at])
  refine ⟨setPC w 29,?_,rfl,?_,?_,?_,?_,⟩
  · convert (bootRun.trans (sumRun.trans (exitSum.trans (betweenRun.trans
      (inverseRun.trans exitInv))))).executes halt using 1
    simp only [show boot.length=4 from rfl]
    omega
  · refine ⟨?_,?_,?_⟩
    · change w.scalarHeap d=some (prepared (UniformDiagonal.shift c))
      rw [outsideW d (by omega) (by omega),hv.2.1]
      simp
    · change w.scalarHeap (d+1)=some (prepared ((UniformDiagonal.shift c)⁻¹))
      rw [outsideW (d+1) (by omega) (by omega),hv.2.1]
      simp
    · simpa only [Written,setPC] using writtenW
  · simpa only [Sources,setPC] using srcW
  · intro r hrd hre hrf
    change w.scalarHeap r=s.scalarHeap r
    rw [outsideW r (by omega) (by omega),hv.2.1,heapU,z.2.1]
    simp (disch:=omega)
  · exact frame_trans z.2.2 (frame_trans frameU (frame_trans hv.2.2
      (frame_trans frameW (frame_pc w 29))))

theorem produced_nonzero {k : ℕ} (d e f : ℕ) (c : Fin k→ℂ) (s : State)
    (h:Result d e f c s) :
    (∃v,s.scalarHeap d=some v ∧ v.dependent=false ∧ v.value≠0) ∧
      ∀j:Fin k,∃v,s.scalarHeap (e+j.val)=some v ∧ v.dependent=false ∧ v.value≠0 := by
  refine ⟨⟨prepared (UniformDiagonal.shift c),h.1,rfl,UniformDiagonal.shift_ne_zero c⟩,?_⟩
  intro j
  exact ⟨prepared (c j-UniformDiagonal.shift c),(h.2.2 j j.isLt).1,rfl,
    UniformDiagonal.coefficient_sub_shift_ne_zero c j⟩

theorem prefix_retained {d e f k : ℕ} {s t : State} (h:OutsideResult d e f k s t)
    (hd:d≤e) (he:e≤f) : ∀r,r<d→t.scalarHeap r=s.scalarHeap r := by
  intro r hr
  exact h r (by omega) (by omega) (by omega)

theorem master_retained {d e f k : ℕ} {s t : State} (h:OutsideResult d e f k s t)
    (hd:0<d) (he:d≤e) (hf:e≤f) : t.scalarHeap 0=s.scalarHeap 0 :=
  prefix_retained h he hf 0 hd

end
end ExactFourierCircuits.UniformZeroFreeDiagonalMachine
