import UniformReciprocalMachine
import UniformPairMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3, pointwise multiplication by the transformed fixed operand,
PDF p.23 (`eq:chirp`).

Refines the paper's linear pointwise step with prepared coefficients.
Heap layouts, tags and frames are implementation bookkeeping; the coefficient
transform is supplied separately and is not assumed free.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformChirpPointwiseMachine
open UniformMachine UniformPairMachine
open UniformReciprocalMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def rowOps : List Op := [.add 63 26 62,.getScalar 0 63,.add 64 28 62,
  .getScalar 1 64,.field .mul 0 0 1,.putScalar 63 0,.add 62 62 61]
def program : Program := [.natLiteral 61 1,.natLiteral 62 0,.branchLT 62 17 3 11]++
  rowOps.map Op.code++[.jump 2,.halt]
theorem program_length : program.length=12 := rfl
theorem row_code : BlockAt rowOps program 3 := by
  intro i hi
  change i<7 at hi
  interval_cases i <;> rfl

def productScalar (v : Scalar) (k : ℂ) : Scalar := ⟨v.value*k,v.dependent⟩
def adjusted (j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (t : ℕ) : Scalar :=
  if t<j then productScalar (v t) (y t) else v t
def Bank (a L j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (s : State) : Prop :=
  ∀t,t<L → s.scalarHeap (a+t)=some (adjusted j v y t)
def Kernels (k L : ℕ) (y : ℕ→ℂ) (s : State) : Prop :=
  ∀t,t<L → s.scalarHeap (k+t)=some (prepared (y t))

structure Geometry (a k L j : ℕ) (s : State) : Prop where
  pc:s.pc=2
  width:s.natReg 17=L
  data:s.natReg 26=a
  kernel:s.natReg 28=k
  one:s.natReg 61=1
  index:s.natReg 62=j

def entered (s : State) : State := {s with pc:=3}
def rowEnd (s : State) : State := {applyBlock rowOps (entered s) with pc:=2}

theorem row_readable (a k L j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (s : State)
    (hg:Geometry a k L j s) (hj:j<L) (hb:Bank a L j v y s) (hk:Kernels k L y s) :
    readable rowOps (entered s) := by
  have hv:s.scalarHeap (a+j)=some (v j):=by simpa [adjusted] using hb j hj
  have hy:=hk j hj
  simp [readable,rowOps,Op.readable,Op.apply,entered,writeNat,writeScalar,next,
    hg.data,hg.kernel,hg.index,hv,hy,evalField,prepared]

theorem row_peak (a k L j B : ℕ) (s : State) (hg:Geometry a k L j s)
    (hj:j<L) (ha:a+L≤B) (hk:k+L≤B) : peak rowOps (entered s)≤B := by
  simp [peak,rowOps,Op.peak,Op.apply,entered,writeNat,writeScalar,next,
    hg.data,hg.kernel,hg.index,hg.one]
  omega

theorem row_runs {n : ℕ} (x : Fin n→ℂ) (a k L j B : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ)
    (s : State) (hg:Geometry a k L j s) (hj:j<L) (hb:Bank a L j v y s)
    (hk:Kernels k L y s) (hB:64≤B) (ha:a+L≤B) (hkB:k+L≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 9 (rowEnd s) := by
  have he:WordBound B (entered s):=changePC_bound B s 3 hs (by omega)
  have henter:BoundedRuns program n x B s 1 (entered s):=by
    refine .next hs ?_ (.refl he)
    simp [step,program,rowOps,hg.pc,hg.index,hg.width,hj,entered]
  have hbody:=block_runs rowOps program 3 n B x (entered s) row_code rfl he
    (by change 3+7≤B;omega) (row_readable a k L j v y s hg hj hb hk)
    (row_peak a k L j B s hg hj ha hkB)
  have hp:(applyBlock rowOps (entered s)).pc=10:=by
    rw [UniformReciprocalMachine.applyBlock_pc];rfl
  have hlast:BoundedRuns program n x B (applyBlock rowOps (entered s)) 1 (rowEnd s):=by
    refine .next hbody.final_bound ?_ (.refl (changePC_bound B _ 2 hbody.final_bound (by omega)))
    simp only [step,hp]
    rfl
  exact (henter.trans hbody).trans hlast

theorem row_geometry (a k L j : ℕ) (s : State) (hg:Geometry a k L j s) :
    Geometry a k L (j+1) (rowEnd s) := by
  constructor <;> simp [rowEnd,applyBlock,rowOps,Op.apply,entered,writeNat,writeScalar,next,
    hg.width,hg.data,hg.kernel,hg.one,hg.index]

theorem row_heap (a k L j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (s : State)
    (hg:Geometry a k L j s) (hj:j<L) (hb:Bank a L j v y s) (hk:Kernels k L y s) :
    (rowEnd s).scalarHeap=Function.update s.scalarHeap (a+j) (some (productScalar (v j) (y j))) := by
  have hv:s.scalarHeap (a+j)=some (v j):=by simpa [adjusted] using hb j hj
  have hy:=hk j hj
  simp [rowEnd,applyBlock,rowOps,Op.apply,entered,writeNat,writeScalar,next,
    hg.data,hg.kernel,hg.index,hv,hy,evalField,prepared,productScalar]

def Frame (a L : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀b,b<a ∨ a+L≤b → u.scalarHeap b=s.scalarHeap b) ∧
  (∀r,r<61 ∨ 65≤r → u.natReg r=s.natReg r) ∧
  ∀r,2≤r → u.scalarReg r=s.scalarReg r
theorem frame_refl (a L : ℕ) (s : State) : Frame a L s s :=
  ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {a L : ℕ} {s u w : State} (h:Frame a L s u) (h':Frame a L u w) :
    Frame a L s w :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun b hb=>(h'.2.2.2.1 b hb).trans (h.2.2.2.1 b hb),
    fun r hr=>(h'.2.2.2.2.1 r hr).trans (h.2.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩

theorem row_frame (a k L j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (s : State)
    (hg:Geometry a k L j s) (hj:j<L) (hb:Bank a L j v y s) (hk:Kernels k L y s) :
    Frame a L s (rowEnd s) := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · intro b h
    rw [row_heap a k L j v y s hg hj hb hk,Function.update_of_ne (by omega)]
  · intro r hr
    simp [rowEnd,applyBlock,rowOps,Op.apply,entered,writeNat,writeScalar,next,
      show r≠62 by omega,show r≠63 by omega,show r≠64 by omega]
  · intro r hr
    simp [rowEnd,applyBlock,rowOps,Op.apply,entered,writeNat,writeScalar,next,
      show r≠0 by omega,show r≠1 by omega]

theorem row_bank (a k L j : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ) (s : State)
    (hg:Geometry a k L j s) (hj:j<L) (hb:Bank a L j v y s) (hk:Kernels k L y s) :
    Bank a L (j+1) v y (rowEnd s) := by
  intro t ht
  rw [row_heap a k L j v y s hg hj hb hk]
  by_cases he:t=j
  · subst t;simp [adjusted]
  · rw [Function.update_of_ne (by omega),hb t ht]
    by_cases h:t<j <;> simp [adjusted,h,show (t<j+1)↔(t<j) by omega]

theorem kernels_frame {a k L : ℕ} {y : ℕ→ℂ} {s u : State} (hk:Kernels k L y s)
    (hsep:a+L≤k ∨ k+L≤a) (hf:Frame a L s u) : Kernels k L y u := by
  intro j hj
  rw [hf.2.2.2.1 (k+j) (by rcases hsep with h|h;exact Or.inr (by omega);exact Or.inl (by omega))]
  exact hk j hj

theorem loop_execution {n : ℕ} (x : Fin n→ℂ) (a k L j fuel B : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ)
    (s : State) (hg:Geometry a k L j s) (hjl:j+fuel=L) (hb:Bank a L j v y s)
    (hk:Kernels k L y s) (hsep:a+L≤k ∨ k+L≤a) (hB:64≤B)
    (ha:a+L≤B) (hkB:k+L≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*fuel+2) u ∧ Bank a L L v y u ∧
    Kernels k L y u ∧ Frame a L s u ∧ u.pc=11 := by
  induction fuel generalizing j s with
  | zero =>
    have he:j=L:=by omega
    let u:State:={s with pc:=11}
    have hu:WordBound B u:=changePC_bound B s 11 hs (by omega)
    refine ⟨u,.next hs ?_ (.halt hu ?_),?_,hk,frame_refl a L s,rfl⟩
    · simp [step,program,rowOps,hg.pc,hg.width,hg.index,he,u]
    · simp [step,program,rowOps,u]
    · simpa only [Bank,u,he] using hb
  | succ fuel ih =>
    have hj:j<L:=by omega
    have hr:=row_runs x a k L j B v y s hg hj hb hk hB ha hkB hs
    have hf:=row_frame a k L j v y s hg hj hb hk
    obtain ⟨u,hu,hbu,hku,hfu,hpc⟩:=ih (j+1) (rowEnd s) (row_geometry a k L j s hg)
      (by omega) (row_bank a k L j v y s hg hj hb hk) (kernels_frame hk hsep hf) hr.final_bound
    refine ⟨u,?_,hbu,hku,hf.trans hfu,hpc⟩
    convert hr.executes hu using 1;omega

def one (s : State) : State := writeNat s 61 1
def initialized (s : State) : State := writeNat (one s) 62 0

theorem pointwise_execution {n : ℕ} (x : Fin n→ℂ) (a k L B : ℕ) (v : ℕ→Scalar) (y : ℕ→ℂ)
    (s : State) (hp:s.pc=0) (h17:s.natReg 17=L) (h26:s.natReg 26=a) (h28:s.natReg 28=k)
    (hb:Bank a L 0 v y s) (hk:Kernels k L y s) (hsep:a+L≤k ∨ k+L≤a)
    (hB:64≤B) (ha:a+L≤B) (hkB:k+L≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (9*L+4) u ∧
    (∀j,j<L → u.scalarHeap (a+j)=some (productScalar (v j) (y j))) ∧
    Kernels k L y u ∧ Frame a L s u ∧ u.pc=11 := by
  have ho:=writeNat_bound B s 61 1 hs (by omega) (by omega)
  have hi:=writeNat_bound B (one s) 62 0 ho (by simp [one,writeNat,next,hp];omega) (by omega)
  have hstart:BoundedRuns program n x B s 2 (initialized s):=by
    refine .next hs (u:=one s) ?_ (.next ho (u:=initialized s) ?_ (.refl hi))
    all_goals simp [step,program,rowOps,initialized,one,writeNat,next,hp]
  have hg:Geometry a k L 0 (initialized s):=by
    constructor <;> simp [initialized,one,writeNat,next,hp,h17,h26,h28]
  have hf:Frame a L s (initialized s):=by
    refine ⟨rfl,rfl,rfl,fun _ _=>rfl,?_,fun _ _=>rfl⟩
    intro r hr
    simp [initialized,one,writeNat,next,show r≠61 by omega,show r≠62 by omega]
  obtain ⟨u,hu,hbu,hku,hfu,hpc⟩:=loop_execution x a k L 0 L B v y (initialized s) hg (by omega) hb hk
    hsep hB ha hkB hi
  refine ⟨u,?_,?_,hku,hf.trans hfu,hpc⟩
  · convert hstart.executes hu using 1;omega
  · intro j hj;simpa [adjusted,hj] using hbu j hj

theorem pointwise_cost_linear (L : ℕ) : 9*L+4≤13*(L+1) := by omega

end
end ExactFourierCircuits.UniformChirpPointwiseMachine
