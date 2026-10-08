import UniformTensorMonomialMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTensorDiagonalBankMachine
open UniformMachine
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Six incoming headers: width170, source171, permutation172, coefficient173,
    rowBase174, depth175. Scratch176..180 and Scalar9 only. -/
def setup : List Op := [.literal 176 0,.literal 177 1,.literal 178 3,.mul 180 175 178,
  .add 180 174 180,.putNat 180 170,.add 180 180 177,.putNat 180 172,
  .add 180 180 177,.putNat 180 173]
def body : List Op := [.add 179 172 176,.putNat 179 176,.add 179 171 176,
  .getScalar 9 179,.add 179 173 176,.putScalar 179 9,.add 176 176 177]
def program : Program := setup.map Op.code ++ [.branchLT 176 170 11 19] ++
  body.map Op.code ++ [.jump 10,.halt]
theorem setup_length : setup.length=10 := rfl
theorem body_length : body.length=7 := rfl
theorem program_length : program.length=20 := rfl
theorem branch_at : program[10]?=some (.branchLT 176 170 11 19) := rfl
theorem jump_at : program[18]?=some (.jump 10) := rfl
theorem halt_at : program[19]?=some .halt := rfl
theorem setup_code : BlockAt setup program 0 := by
  intro i hi;change i<10 at hi;interval_cases i <;> rfl
theorem body_code : BlockAt body program 11 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl

noncomputable section
structure Header (r src p c b d : ℕ) (s : State) : Prop where
  width : s.natReg 170=r
  source : s.natReg 171=src
  permutation : s.natReg 172=p
  coefficient : s.natReg 173=c
  row : s.natReg 174=b
  depth : s.natReg 175=d

def initialized (s : State) : State := applyBlock setup s
def iteration (s : State) : State := setPC (applyBlock body (setPC s 11)) 10
def copied : ℕ→State→State
  | 0,s=> s
  | k+1,s=> copied k (iteration s)
def finalState (r : ℕ) (s : State) : State := setPC (copied r (initialized s)) 19

def Coefficients (r src : ℕ) (f : Fin r→ℂ) (s : State) : Prop :=
  ∀j:Fin r,s.scalarHeap (src+j.val)=some (prepared (f j))
def Written (r p c i : ℕ) (f : Fin r→ℂ) (s : State) : Prop :=
  ∀j:Fin r,j.val < i →s.natHeap (p+j.val)=some j.val ∧
    s.scalarHeap (c+j.val)=some (prepared (f j))
def Frame (s t : State) : Prop :=
  t.rootOrders=s.rootOrders ∧ t.outputs=s.outputs ∧
  (∀j,j<176 ∨ 180< j→t.natReg j=s.natReg j) ∧
  (∀j,j≠9→t.scalarReg j=s.scalarReg j)

theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,fun _ _=> rfl,fun _ _=> rfl⟩
theorem frame_trans {s t u : State} (h:Frame s t) (h':Frame t u) : Frame s u := by
  refine ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,?_,?_⟩
  · intro j hj;exact (h'.2.2.1 j hj).trans (h.2.2.1 j hj)
  · intro j hj;exact (h'.2.2.2 j hj).trans (h.2.2.2 j hj)

theorem setup_properties (r src p c b d : ℕ) (s : State) (h:Header r src p c b d s) :
    Header r src p c b d (initialized s) ∧ (initialized s).natReg 176=0 ∧
    (initialized s).natReg 177=1 ∧ (initialized s).natReg 178=3 ∧
    (initialized s).natHeap=Function.update
      (Function.update (Function.update s.natHeap (b+d*3) (some r)) (b+d*3+1) (some p))
      (b+d*3+2) (some c) ∧ (initialized s).scalarHeap=s.scalarHeap ∧ Frame s (initialized s) := by
  rcases h with ⟨hr,hs,hp,hc,hb,hd⟩
  constructor
  · constructor <;> simp [initialized,applyBlock,setup,Op.apply,writeNat,next,hr,hs,hp,hc,hb,hd]
  · simp (disch:=omega) [initialized,applyBlock,setup,Op.apply,writeNat,next,hr,hp,hc,hb,hd,
      Frame,Nat.add_assoc]
    intro j hj;simp (disch:=omega)

theorem setup_bounded (B n r src p c b d : ℕ) (x : Fin n→ℂ) (s : State)
    (h:Header r src p c b d s) (hpc:s.pc=0) (hB:20≤ B) (hrow:b+d*3+2≤ B)
    (hs:WordBound B s) : BoundedRuns program n x B s 10 (initialized s) := by
  have hr:r≤ B:=by simpa only [h.width] using hs.2.1 170
  have hp:p≤ B:=by simpa only [h.permutation] using hs.2.1 172
  have hc:c≤ B:=by simpa only [h.coefficient] using hs.2.1 173
  apply block_runs setup program 0 n B x s setup_code hpc hs (by rw [setup_length];omega)
  · simp [readable,setup,Op.readable]
  · simp [peak,setup,Op.peak,Op.apply,writeNat,next,h.width,h.permutation,h.coefficient,h.row,h.depth,
      Nat.add_assoc]
    omega

theorem iteration_properties (r src p c b d i : ℕ) (f : Fin r→ℂ) (s : State)
    (h:Header r src p c b d s) (hi:s.natReg 176=i) (h1:s.natReg 177=1)
    (hir:i< r) (hcoef:s.scalarHeap (src+i)=some (prepared (f ⟨i,hir⟩))) :
    Header r src p c b d (iteration s) ∧ (iteration s).natReg 176=i+1 ∧
    (iteration s).natReg 177=1 ∧ (iteration s).natReg 178=s.natReg 178 ∧
    (iteration s).natHeap=Function.update s.natHeap (p+i) (some i) ∧
    (iteration s).scalarHeap=Function.update s.scalarHeap (c+i) (some (prepared (f ⟨i,hir⟩))) ∧
    (iteration s).pc=10 ∧ Frame s (iteration s) := by
  rcases h with ⟨hr,hs,hp,hc,hb,hd⟩
  constructor
  · constructor <;> simp [iteration,setPC,applyBlock,body,Op.apply,writeNat,writeScalar,next,
      hr,hs,hp,hc,hb,hd]
  · simp (disch:=omega) [iteration,setPC,applyBlock,body,Op.apply,writeNat,writeScalar,next,
      hs,hp,hc,hi,h1,hcoef,Frame]
    constructor <;> intro j hj <;> simp (disch:=omega)

theorem iteration_bounded (B n r src p c b d i : ℕ) (x : Fin n→ℂ) (f : Fin r→ℂ) (s : State)
    (h:Header r src p c b d s) (hpc:s.pc=10) (hi:s.natReg 176=i) (h1:s.natReg 177=1)
    (hir:i< r) (hcoef:s.scalarHeap (src+i)=some (prepared (f ⟨i,hir⟩)))
    (hB:20≤ B) (hp:p+r≤ B) (hc:c+r≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s 9 (iteration s) := by
  let e:=setPC s 11
  have he:WordBound B e:=changePC_bound B s 11 hs (by omega)
  have hsource:src+i≤ B:=hs.2.2.2.1 _ _ hcoef
  have hr:r≤ B:=by simpa only [h.width] using hs.2.1 170
  have readable':readable body e:=by
    simp [readable,body,Op.readable,Op.apply,e,setPC,writeNat,next,h.source,hi,hcoef]
  have peak':peak body e≤ B:=by
    simp [peak,body,Op.peak,Op.apply,e,setPC,writeNat,writeScalar,next,h.source,h.permutation,
      h.coefficient,hi,h1]
    omega
  have run:=block_runs body program 11 n B x e body_code rfl he
    (by rw [body_length];omega) readable' peak'
  have ep:(applyBlock body e).pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,body_length];rfl
  have jump:BoundedRuns program n x B (applyBlock body e) 1 (iteration s):=
    .next run.final_bound (by rw [UniformMachine.step,ep,jump_at];rfl)
      (.refl (changePC_bound B _ 10 run.final_bound (by omega)))
  have first:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [UniformMachine.step,hpc,branch_at,h.width,hi,hir,e,setPC]) (.refl he)
  simpa only [body_length] using first.trans (run.trans jump)


structure LoopEffect (r src p c b d i k : ℕ) (f : Fin r→ℂ) (s t : State) : Prop where
  pc : t.pc=10
  header : Header r src p c b d t
  index : t.natReg 176=i+k
  one : t.natReg 177=1
  coefficients : Coefficients r src f t
  written : Written r p c (i+k) f t
  frame : Frame s t
  natFrame : ∀a,a< p+i ∨ p+i+k≤ a→t.natHeap a=s.natHeap a
  scalarFrame : ∀a,a< c+i ∨ c+i+k≤ a→t.scalarHeap a=s.scalarHeap a

/-- All iteration reads are from the actual prepared scalar bank. Stores
    are charged even when the coefficient is zero or the destination dirty. -/
theorem copy_loop (B n r src p c b d i k : ℕ) (x : Fin n→ℂ) (f : Fin r→ℂ) (s : State)
    (h:Header r src p c b d s) (hpc:s.pc=10) (hi:s.natReg 176=i) (h1:s.natReg 177=1)
    (hik:i+k=r) (hcoef:Coefficients r src f s) (hw:Written r p c i f s)
    (hsep:src+r≤ c ∨ c+r≤ src) (hB:20≤ B) (hp:p+r≤ B) (hc:c+r≤ B) (hs:WordBound B s) :
    BoundedRuns program n x B s (9*k) (copied k s) ∧
      LoopEffect r src p c b d i k f s (copied k s) := by
  induction k generalizing s i with
  | zero =>
    refine ⟨.refl hs,⟨hpc,h,by simpa [copied] using hi,h1,hcoef,by simpa [copied] using hw,frame_refl s,?_,?_⟩⟩
    · intro a _;rfl
    · intro a _;rfl
  | succ k ih =>
    have hir:i< r:=by omega
    have ready:=hcoef ⟨i,hir⟩
    have run:=iteration_bounded B n r src p c b d i x f s h hpc hi h1 hir ready hB hp hc hs
    have e:=iteration_properties r src p c b d i f s h hi h1 hir ready
    have source:Coefficients r src f (iteration s):=by
      intro j
      rw [e.2.2.2.2.2.1,Function.update_of_ne]
      · exact hcoef j
      · have hj:=j.isLt;rcases hsep with h|h <;> omega
    have written:Written r p c (i+1) f (iteration s):=by
      intro j hj
      by_cases he:j.val=i
      · have je:j=⟨i,hir⟩:=Fin.ext he
        subst j
        rw [e.2.2.2.2.1,e.2.2.2.2.2.1]
        simp
      · have old:=hw j (by omega)
        rw [e.2.2.2.2.1,e.2.2.2.2.2.1,
          Function.update_of_ne (show p+j.val≠p+i by omega),
          Function.update_of_ne (show c+j.val≠c+i by omega)]
        exact old
    obtain ⟨rest,z⟩:=ih (i+1) (iteration s) e.1 e.2.2.2.2.2.2.1 e.2.1 e.2.2.1
      (by omega) source written run.final_bound
    refine ⟨by simpa only [copied,Nat.mul_succ,Nat.add_comm] using run.trans rest,?_,⟩
    change LoopEffect r src p c b d i (k+1) f s (copied k (iteration s))
    refine ⟨z.pc,z.header,?_,z.one,z.coefficients,?_,frame_trans e.2.2.2.2.2.2.2 z.frame,?_,?_⟩
    · rw [z.index];omega
    · simpa only [show i+1+k=i+(k+1) by omega] using z.written
    · intro a ha
      rw [z.natFrame a (by rcases ha with h|h;exact Or.inl (by omega);exact Or.inr (by omega)),
        e.2.2.2.2.1,Function.update_of_ne]
      rcases ha with h|h <;> omega
    · intro a ha
      rw [z.scalarFrame a (by rcases ha with h|h;exact Or.inl (by omega);exact Or.inr (by omega)),
        e.2.2.2.2.2.1,Function.update_of_ne]
      rcases ha with h|h <;> omega

structure Result (r src p c b d : ℕ) (f : Fin r→ℂ) (s t : State) : Prop where
  pc : t.pc=19
  header : Header r src p c b d t
  count : t.natReg 176=r
  coefficients : Coefficients r src f t
  permutation : ∀j:Fin r,t.natHeap (p+j.val)=some j.val
  coefficient : ∀j:Fin r,t.scalarHeap (c+j.val)=some (prepared (f j))
  rowWidth : t.natHeap (b+d*3)=some r
  rowPermutation : t.natHeap (b+d*3+1)=some p
  rowCoefficient : t.natHeap (b+d*3+2)=some c
  frame : Frame s t
  natFrame : ∀a,(a< b+d*3 ∨ b+d*3+3≤ a)→(a< p ∨ p+r≤ a)→t.natHeap a=s.natHeap a
  scalarFrame : ∀a,a< c ∨ c+r≤ a→t.scalarHeap a=s.scalarHeap a

/-- One fixed finite producer, with sizing/address arithmetic, row writes,
    every identity store/coefficient copy, branches, continuation and halt. -/
theorem complete_execution (B n r src p c b d : ℕ) (x : Fin n→ℂ) (f : Fin r→ℂ) (s : State)
    (h:Header r src p c b d s) (hpc:s.pc=0) (hcoef:Coefficients r src f s)
    (hsep:src+r≤ c ∨ c+r≤ src) (hrowSep:b+d*3+3≤ p ∨ p+r≤ b+d*3)
    (hB:20≤ B) (hrow:b+d*3+2≤ B) (hp:p+r≤ B) (hc:c+r≤ B) (hs:WordBound B s) :
    BoundedExecution program n x B s (9*r+12) (finalState r s) ∧
      Result r src p c b d f s (finalState r s) := by
  have start:=setup_bounded B n r src p c b d x s h hpc hB hrow hs
  have e:=setup_properties r src p c b d s h
  have source:Coefficients r src f (initialized s):=by
    intro j;rw [e.2.2.2.2.2.1];exact hcoef j
  obtain ⟨run,z⟩:=copy_loop B n r src p c b d 0 r x f (initialized s) e.1
    (by rw [initialized,UniformTensorMonomialMachine.applyBlock_pc,setup_length,hpc])
    e.2.1 e.2.2.1 (by omega) source (by intro j hj;omega) hsep hB hp hc start.final_bound
  let t:=copied r (initialized s)
  let u:=setPC t 19
  have ub:WordBound B u:=changePC_bound B t 19 run.final_bound (by omega)
  have tail:BoundedExecution program n x B t 2 u:=by
    refine .next run.final_bound ?_ (.halt ub ?_)
    · simp [UniformMachine.step,z.pc,branch_at,z.index,z.header.width,u,setPC,t]
    · simp [UniformMachine.step,u,setPC,halt_at]
  refine ⟨?_,?_,⟩
  · simpa only [finalState,t,u,show 10+(9*r+2)=9*r+12 by omega] using start.executes (run.executes tail)
  · have rowFrame (j : ℕ) (hj:j<3) : t.natHeap (b+d*3+j)=(initialized s).natHeap (b+d*3+j):=by
      apply z.natFrame
      rcases hrowSep with h|h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine ⟨rfl,?_,?_,z.coefficients,?_,?_,?_,?_,?_,frame_trans e.2.2.2.2.2.2 z.frame,?_,?_⟩
    · exact ⟨z.header.width,z.header.source,z.header.permutation,z.header.coefficient,z.header.row,z.header.depth⟩
    · simpa only [finalState,setPC,Nat.zero_add] using z.index
    · intro j;exact (z.written j (by have h:=j.isLt;omega)).1
    · intro j;exact (z.written j (by have h:=j.isLt;omega)).2
    · have h:=rowFrame 0 (by omega)
      rw [Nat.add_zero,e.2.2.2.2.1] at h
      simpa (disch:=omega) [finalState,setPC,t] using h
    · have h:=rowFrame 1 (by omega)
      rw [e.2.2.2.2.1] at h
      simpa (disch:=omega) [finalState,setPC,t] using h
    · have h:=rowFrame 2 (by omega)
      rw [e.2.2.2.2.1] at h
      simpa [finalState,setPC,t] using h
    · intro a hrow hp'
      rw [show (finalState r s).natHeap a=t.natHeap a from rfl,
        z.natFrame a (by simpa only [Nat.add_zero,Nat.zero_add] using hp'),e.2.2.2.2.1]
      simp (disch:=omega) [Function.update_of_ne]
    · intro a ha
      exact (z.scalarFrame a (by simpa only [Nat.add_zero,Nat.zero_add] using ha)).trans
        (congrFun e.2.2.2.2.2.1 a)


def identityAxis (r : ℕ) (hr:0< r) (p c : ℕ) (f : Fin r→ℂ) :
    UniformTensorMonomialMachine.Axis := ⟨r,hr,Equiv.refl _,f,p,c⟩

theorem identityAxis_permutation (r : ℕ) (hr:0< r) (p c : ℕ) (f : Fin r→ℂ) :
    (identityAxis r hr p c f).permutation=Equiv.refl (Fin r) := rfl

/-- The emitted row and two emitted banks directly satisfy the frozen
    TensorMonomial66 singleton interface at the requested caller depth. -/
theorem result_banks (r src p c d : ℕ) (f : Fin r→ℂ) (hr:0< r)
    (L : UniformTensorMonomialMachine.Layout) (s t : State)
    (h:Result r src p c L.row d f s t)
    (hp:p+r≤L.natStack) (hc:c+r≤L.scalarStack) :
    UniformTensorMonomialMachine.Banks [identityAxis r hr p c f] d L t := by
  constructor
  · exact ⟨h.rowWidth,h.rowPermutation,h.rowCoefficient,True.intro⟩
  · intro a ha i
    simp only [List.mem_singleton] at ha;subst a
    exact h.permutation i
  · intro a ha i
    simp only [List.mem_singleton] at ha;subst a
    exact h.coefficient i
  · intro a ha;simp only [List.mem_singleton] at ha;subst a;exact hp
  · intro a ha;simp only [List.mem_singleton] at ha;subst a;exact hc

/-- Same ambient word bound as the tensor caller. The source coefficients
    are honest physically present prepared scalars; no action/table premise
    is assumed for the newly produced identity axis. -/
theorem produce_singleton (n r src p c d : ℕ) (x : Fin n→ℂ) (f : Fin r→ℂ) (hr:0< r)
    (L : UniformTensorMonomialMachine.Layout) (s : State)
    (h:Header r src p c L.row d s) (hpc:s.pc=0) (hcoef:Coefficients r src f s)
    (hsep:src+r≤ c ∨ c+r≤ src)
    (hrowSep:L.row+d*3+3≤ p ∨ p+r≤L.row+d*3) (hd:d<L.ell)
    (hp:p+r≤L.natStack) (hc:c+r≤L.scalarStack) (hs:WordBound L.B s) :
    BoundedExecution program n x L.B s (9*r+12) (finalState r s) ∧
    Result r src p c L.row d f s (finalState r s) ∧
    UniformTensorMonomialMachine.Banks [identityAxis r hr p c f] d L (finalState r s) := by
  have hb:=L.codeBound
  have hn:=L.natStackBound
  have hs':=L.scalarStackBound
  have rows:=L.rowsBelow
  obtain ⟨run,e⟩:=complete_execution L.B n r src p c L.row d x f s h hpc hcoef hsep hrowSep
    (by omega) (by omega) (by omega) (by omega) hs
  exact ⟨run,e,result_banks r src p c d f hr L s (finalState r s) e hp hc⟩

theorem produced_prepared (r src p c b d : ℕ) (f : Fin r→ℂ) (s t : State)
    (h:Result r src p c b d f s t) (j : Fin r) :
    ∃v,t.scalarHeap (c+j.val)=some v ∧ v.dependent=false ∧ v.value=f j :=
  ⟨prepared (f j),h.coefficient j,rfl,rfl⟩

end
end ExactFourierCircuits.UniformTensorDiagonalBankMachine
