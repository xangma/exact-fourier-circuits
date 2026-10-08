import UniformGlobalLocalPreparation
import UniformScalarCopyMachine

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ExactFourierCircuits.UniformLocalSeedTableMachine
namespace Strided
open UniformMachine

/-- Arguments Nat146=stride,147=count,148=source,149=destination.
All reads/stores and arithmetic are literal charged machine instructions. -/
def program : Program := [
  .natLiteral 150 0,.natLiteral 151 1,.branchLT 150 147 3 10,
  .natBinary .mul 154 150 146,.natBinary .add 152 148 154,
  .loadScalar 32 152,.natBinary .add 153 149 150,.storeScalar 153 32,
  .natBinary .add 150 150 151,.jump 2,.halt]

theorem program_length : program.length=11 := rfl

noncomputable section

def Source (m a stride : ℕ) (heap : ℕ → Option Scalar) : Prop :=
  ∀j,j < m → ∃v,heap (a+stride*j)=some v

def Outside (d m : ℕ) (heap : ℕ → Option Scalar) (s : State) : Prop :=
  ∀i,(i < d ∨ d+m  ≤  i) → s.scalarHeap i=heap i

structure Invariant (m a d stride k : ℕ) (heap : ℕ → Option Scalar) (s : State) : Prop where
  step : s.natReg 146=stride
  length : s.natReg 147=m
  source : s.natReg 148=a
  destination : s.natReg 149=d
  index : s.natReg 150=k
  one : s.natReg 151=1
  copied : ∀j,j < k → s.scalarHeap (d+j)=heap (a+stride*j)
  outside : Outside d m heap s

/-- Metadata, outputs, root requests and all other scalar registers are retained. -/
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ ∀r,r ≠ 32  →  u.scalarReg r=s.scalarReg r

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2 r hr).trans (h.2.2.2 r hr)⟩

theorem Invariant.withPC {m a d stride k pc : ℕ} {heap : ℕ → Option Scalar} {s : State}
    (h:Invariant m a d stride k heap s) : Invariant m a d stride k heap {s with pc:=pc} := by
  cases h;constructor <;> assumption

def scaled (s : State) : State := writeNat {s with pc:=3} 154 (s.natReg 150*s.natReg 146)
def sourceAddress (s : State) : State :=
  writeNat (scaled s) 152 (s.natReg 148+s.natReg 150*s.natReg 146)
def loaded (s : State) (v : Scalar) : State := writeScalar (sourceAddress s) 32 v
def destinationAddress (s : State) (v : Scalar) : State :=
  writeNat (loaded s v) 153 (s.natReg 149+s.natReg 150)
def stored (s : State) (v : Scalar) : State :=
  {next (destinationAddress s v) with scalarHeap:=(Function.update s.scalarHeap
    (s.natReg 149+s.natReg 150) (some v))}
def advanced (s : State) (v : Scalar) : State := writeNat (stored s v) 150 (s.natReg 150+1)
def iterationEnd (s : State) (v : Scalar) : State := {advanced s v with pc:=2}

theorem store_bound (B : ℕ) (s : State) (address : ℕ) (value : Scalar) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (ha:address ≤ B) :
    WordBound B {next s with scalarHeap:=Function.update s.scalarHeap address (some value)} := by
  refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro j v hj
  by_cases he:j=address
  · subst j;exact ha
  · exact hs.2.2.2.1 j v (by simpa [he] using hj)

theorem iteration_heap (s : State) (v : Scalar) :
    (iterationEnd s v).scalarHeap=Function.update s.scalarHeap
      (s.natReg 149+s.natReg 150) (some v) := rfl

theorem iteration_frame (s : State) (v : Scalar) : Frame s (iterationEnd s v) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro r hr
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,writeNat,writeScalar,next,hr]

theorem iteration_invariant (m a d stride k : ℕ) (heap : ℕ → Option Scalar) (s : State) (v : Scalar)
    (hi:Invariant m a d stride k heap s) (hk:k < m) (hv:heap (a+stride*k)=some v) :
    Invariant m a d stride (k+1) heap (iterationEnd s v) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next] using hi.step
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next] using hi.length
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next] using hi.source
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next] using hi.destination
  · simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next,hi.index]
  · simpa [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next] using hi.one
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index]
    by_cases he:j=k
    · subst j;simp [hv]
    · rw [Function.update_of_ne (by omega)]
      exact hi.copied j (by omega)
  · intro j hj
    rw [iteration_heap,hi.destination,hi.index,Function.update_of_ne (by omega)]
    exact hi.outside j hj

def NatFrame (s u : State) : Prop := ∀i,(i < 147 ∨ 155  ≤  i) → u.natReg i=s.natReg i

theorem NatFrame.trans {s u v : State} (h:NatFrame s u) (h':NatFrame u v) : NatFrame s v :=
  fun i hi=>(h' i hi).trans (h i hi)

theorem iteration_nat (s : State) (v : Scalar) : NatFrame s (iterationEnd s v) := by
  intro i hi
  simp [iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,writeNat,writeScalar,next,
    show i ≠ 150 by omega,show i ≠ 152 by omega,show i ≠ 153 by omega,show i ≠ 154 by omega]


/-- Eight real instructions copy one present source scalar and advance the loop. -/
theorem iteration (n : ℕ) (x : Fin n → ℂ) (m a d stride k B : ℕ) (heap : ℕ → Option Scalar)
    (s : State) (hi:Invariant m a d stride k heap s) (hsrc:Source m a stride heap)
    (hk:k < m) (hstride:0<stride) (hd:a+stride*m  ≤  d) (hB:d+m  ≤  B) (hcode:10  ≤  B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s 8 u ∧ Invariant m a d stride (k+1) heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  obtain ⟨v,hv⟩:=hsrc k hk
  have hkm:stride*k<stride*m:=Nat.mul_lt_mul_of_pos_left hk hstride
  have hload:s.scalarHeap (a+stride*k)=some v:=(hi.outside _ (Or.inl (by omega))).trans hv
  have he:WordBound B {s with pc:=3}:=changePC_bound B s 3 hs (by omega)
  have hm:WordBound B (scaled s):=writeNat_bound B {s with pc:=3} 154 _ he
    (by change 4 ≤ B;omega) (by rw [hi.index,hi.step,Nat.mul_comm];omega)
  have h1:WordBound B (sourceAddress s):=writeNat_bound B (scaled s) 152 _ hm
    (by change 5 ≤ B;omega) (by rw [hi.source,hi.index,hi.step,Nat.mul_comm];omega)
  have h2:WordBound B (loaded s v):=writeScalar_bound B (sourceAddress s) 32 v h1
    (by change 6 ≤ B;omega)
  have h3:WordBound B (destinationAddress s v):=writeNat_bound B (loaded s v) 153 _ h2
    (by change 7 ≤ B;omega) (by rw [hi.destination,hi.index];omega)
  have h4:WordBound B (stored s v):=UniformScalarCopyMachine.store_bound B (destinationAddress s v)
    (s.natReg 149+s.natReg 150) v h3 (by change 8 ≤ B;omega) (by rw [hi.destination,hi.index];omega)
  have h5:WordBound B (advanced s v):=writeNat_bound B (stored s v) 150 _ h4
    (by change 9 ≤ B;omega) (by rw [hi.index];omega)
  have h6:WordBound B (iterationEnd s v):=changePC_bound B _ 2 h5 (by omega)
  have t0:step program n x s=.running {s with pc:=3}:=by
    simp [step,program,hpc,hi.index,hi.length,hk]
  have tm:step program n x {s with pc:=3}=.running (scaled s):=by
    simp [step,program,scaled,evalNat]
  have t1:step program n x (scaled s)=.running (sourceAddress s):=by
    simp [step,program,sourceAddress,scaled,writeNat,next,evalNat]
  have t2:step program n x (sourceAddress s)=.running (loaded s v):=by
    simp [step,program,loaded,sourceAddress,scaled,writeNat,writeScalar,next,
      hi.source,hi.index,hi.step,Nat.mul_comm,hload]
  have t3:step program n x (loaded s v)=.running (destinationAddress s v):=by
    simp [step,program,destinationAddress,loaded,sourceAddress,scaled,writeNat,writeScalar,next,evalNat]
  have t4:step program n x (destinationAddress s v)=.running (stored s v):=by
    simp [step,program,stored,destinationAddress,loaded,sourceAddress,scaled,writeNat,writeScalar,next]
  have t5:step program n x (stored s v)=.running (advanced s v):=by
    simp [step,program,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next,hi.one,evalNat]
  have t6:step program n x (advanced s v)=.running (iterationEnd s v):=by
    simp [step,program,iterationEnd,advanced,stored,destinationAddress,loaded,sourceAddress,scaled,
      writeNat,writeScalar,next]
  exact ⟨iterationEnd s v,.next hs t0 (.next he tm (.next hm t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.next h5 t6 (.refl h6)))))))),
    iteration_invariant m a d stride k heap s v hi hk hv,rfl,iteration_frame s v,iteration_nat s v⟩


/-- All loop iterations execute the literal program. A source value is never
selected by an uncharged copying primitive. -/
theorem loop (n : ℕ) (x : Fin n → ℂ) (m a d stride k fuel B : ℕ) (heap : ℕ → Option Scalar)
    (s : State) (hi:Invariant m a d stride k heap s) (hsrc:Source m a stride heap)
    (hk:k+fuel=m) (hstride:0<stride) (hd:a+stride*m  ≤  d) (hB:d+m  ≤  B) (hcode:10  ≤  B)
    (hpc:s.pc=2) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (8*fuel) u ∧ Invariant m a d stride m heap u ∧
    u.pc=2 ∧ Frame s u ∧ NatFrame s u := by
  induction fuel generalizing k s with
  | zero =>
    have hkm:k=m:=by omega
    subst k
    exact ⟨s,.refl hs,hi,hpc,⟨rfl,rfl,rfl,fun _ _=>rfl⟩,fun i _=>rfl⟩
  | succ fuel ih =>
    obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=iteration n x m a d stride k B heap s hi hsrc (by omega)
      hstride hd hB hcode hpc hs
    obtain ⟨w,hw,hiw,hpw,hfw,hnw⟩:=ih (k+1) u hiu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hiw,hpw,hfu.trans hfw,hnu.trans hnw⟩
    convert hu.trans hw using 1;omega


def zeroState (s : State) : State := writeNat s 150 0
def initialized (s : State) : State := writeNat (zeroState s) 151 1

theorem initialize_invariant (m a d stride : ℕ) (s : State) (h146:s.natReg 146=stride) (h147:s.natReg 147=m)
    (h148:s.natReg 148=a) (h149:s.natReg 149=d) :
    Invariant m a d stride 0 s.scalarHeap (initialized s) := by
  constructor <;> simp [initialized,zeroState,writeNat,next,h146,h147,h148,h149,Outside]

theorem initialize_frame (s : State) : Frame s (initialized s) := ⟨rfl,rfl,rfl,fun _ _=>rfl⟩
theorem initialize_nat (s : State) : NatFrame s (initialized s) := by
  intro i hi
  simp [initialized,zeroState,writeNat,next,show i ≠ 150 by omega,show i ≠ 151 by omega]

/-- Complete fixed RAM copy with the original source as its specification.
Every source scalar is explicitly present. The destination can be dirty. The word
budget is identical at every step, and both exact values and dependency flags are copied without arithmetic. -/
theorem execution (n : ℕ) (x : Fin n → ℂ) (m a d stride B : ℕ) (s : State)
    (hsrc:Source m a stride s.scalarHeap) (hstride:0<stride) (hd:a+stride*m  ≤  d) (hB:d+m  ≤  B) (hcode:10  ≤  B)
    (hpc:s.pc=0) (h146:s.natReg 146=stride) (h147:s.natReg 147=m) (h148:s.natReg 148=a) (h149:s.natReg 149=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (8*m+4) u ∧
    (∀j,j < m → u.scalarHeap (d+j)=s.scalarHeap (a+stride*j)) ∧
    (∀j,j < m → u.scalarHeap (a+stride*j)=s.scalarHeap (a+stride*j)) ∧
    Outside d m s.scalarHeap u ∧ Frame s u ∧ NatFrame s u := by
  have hz:WordBound B (zeroState s):=writeNat_bound B s 150 0 hs (by omega) (by omega)
  have hi:WordBound B (initialized s):=writeNat_bound B (zeroState s) 151 1 hz
    (by change s.pc+1+1  ≤  B;omega) (by omega)
  have t0:step program n x s=.running (zeroState s):=by rw [step,hpc];rfl
  have t1:step program n x (zeroState s)=.running (initialized s):=by
    simp [step,program,initialized,zeroState,writeNat,next,hpc]
  have hb:BoundedRuns program n x B s 2 (initialized s):=
    .next hs t0 (.next hz t1 (.refl hi))
  have hp:(initialized s).pc=2:=by simp [initialized,zeroState,writeNat,next,hpc]
  obtain ⟨u,hu,hiu,hpu,hfu,hnu⟩:=loop n x m a d stride 0 m B s.scalarHeap (initialized s)
    (initialize_invariant m a d stride s h146 h147 h148 h149) hsrc (by omega) hstride hd hB hcode hp hi
  let v:State:={u with pc:=10}
  have hv:WordBound B v:=changePC_bound B u 10 hu.final_bound hcode
  have halt:BoundedExecution program n x B v 1 v:=.halt hv (by rw [step];rfl)
  have he:BoundedExecution program n x B u 2 v:=by
    refine .next hu.final_bound ?_ halt
    simp [step,program,hpu,hiu.index,hiu.length,v]
  refine ⟨v,?_,hiu.copied,?_,hiu.outside,(initialize_frame s).trans hfu,
    (initialize_nat s).trans hnu⟩
  · convert hb.executes (hu.executes he) using 1;omega
  · intro j hj
    have hjs:stride*j<stride*m:=Nat.mul_lt_mul_of_pos_left hj hstride
    exact hiu.outside (a+stride*j) (Or.inl (by omega))


end
end Strided

open UniformPairMachine
open UniformInitialPreparation (ell len)
open UniformNewton.Preparation
noncomputable section

def poolBase (n : ℕ) : ℕ := UniformGlobalLocalPreparation.globalEnd n+17*len n+16

theorem all_workspaces_before_pool (n r : ℕ) (hr:r ≤ len n) :
    UniformGlobalLocalPreparation.rootSource n r+1+r<poolBase n := by
  dsimp [poolBase,UniformGlobalLocalPreparation.rootSource,UniformGlobalLocalPreparation.scratchBase,
    UniformGlobalLocalPreparation.resultBase]
  omega

theorem output_H_address (r : ℕ) (j : Fin r) :
    ((table r).output (finProdFinEquiv (j,(0:Fin 5)))).val=UniformNewtonTableMachine.HIndex j.val := by
  simp only [table,Equiv.symm_apply_apply,Fin.isValue,Fin.val_zero,ite_true]
  change (HRef j.val).val=UniformNewtonTableMachine.HIndex j.val
  exact UniformNewtonTableMachine.HRef_val _

theorem output_scale_address (r : ℕ) (j : Fin r) :
    ((table r).output (finProdFinEquiv (j,(1:Fin 5)))).val=UniformNewtonTableMachine.scaleIndex j.val := by
  simp only [table,Equiv.symm_apply_apply,Fin.isValue,Fin.val_one,ite_true]
  change (scaleRef j.val).val=UniformNewtonTableMachine.scaleIndex j.val
  exact UniformNewtonTableMachine.scaleRef_val _

theorem output_invD_address (r : ℕ) (j : Fin r) :
    ((table r).output (finProdFinEquiv (j,(4:Fin 5)))).val=5*r+3*j.val+5 := by
  simp [table,finalInvDiagonal,inverseLift,Fin.val_last,inverseCount_formula]

theorem output_invH_address (r : ℕ) (j : Fin r) :
    ((table r).output (finProdFinEquiv (j,(2:Fin 5)))).val=5*r+3*j.val+3 := by
  simp [table,finalInvH,inverseLift,Fin.val_last,inverseCount_formula]

def seedValue (omega : ℂ) (q : Fin 5) (j : ℕ) : ℂ :=
  if q.val=0 then OAI.ExactFourier.NewtonFourier.H omega j
  else if q.val=1 then OAI.ExactFourier.NewtonFourier.scale omega j
  else if q.val=2 then (UniformNewton.diagonalValue omega j)⁻¹
  else if q.val=3 then (OAI.ExactFourier.NewtonFourier.H omega j)⁻¹
  else PowerSeries.coeff j (OAI.ExactFourier.NewtonFourier.invH omega)⁻¹

def sourceAddress (r a g : ℕ) (q : Fin 5) (j : ℕ) : ℕ :=
  if q.val=0 then a+UniformNewtonTableMachine.HIndex j
  else if q.val=1 then a+UniformNewtonTableMachine.scaleIndex j
  else if q.val=2 then a+5*r+3*j+5
  else if q.val=3 then a+5*r+3*j+3
  else g+j

def Sources (r a g : ℕ) (omega : ℂ) (s : UniformMachine.State) : Prop :=
  ∀q:Fin 5,∀j:Fin r,s.scalarHeap (sourceAddress r a g q j.val)=some (prepared (seedValue omega q j.val))

/-- The actual already-produced local coefficient banks supply every source;
there is no ready compact destination-table premise. -/
theorem Sources.fromLocal {r a g : ℕ} {omega : ℂ} {s : UniformMachine.State}
    (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s)
    (hg:UniformReciprocalMachine.GPrefix r g (OAI.ExactFourier.NewtonFourier.invH omega) s) :
    Sources r a g omega s := by
  intro q j
  fin_cases q
  · have h:=hp j 0
    rw [output_H_address] at h
    simpa [sourceAddress,seedValue,expected,UniformPairMachine.prepared,UniformReciprocalMachine.prepared] using h
  · have h:=hp j 1
    rw [output_scale_address] at h
    simpa [sourceAddress,seedValue,expected,UniformPairMachine.prepared,UniformReciprocalMachine.prepared] using h
  · have h:=hp j 4
    rw [output_invD_address] at h
    simpa [sourceAddress,seedValue,expected,UniformPairMachine.prepared,UniformReciprocalMachine.prepared,Nat.add_assoc] using h
  · have h:=hp j 2
    rw [output_invH_address] at h
    simpa [sourceAddress,seedValue,expected,UniformPairMachine.prepared,UniformReciprocalMachine.prepared,Nat.add_assoc] using h
  · simpa [sourceAddress,seedValue,UniformPairMachine.prepared,UniformReciprocalMachine.prepared] using hg j.val j.isLt


open UniformMachine UniformAssembly
open UniformReciprocalMachine (Op applyBlock peak readable BlockAt block_runs)

/-- Seven charged strided passes: the exceptional zero entries of H/scale,
then their positive entries, inverse diagonal, inverse H, and reciprocal G. -/
def rowWidth (r : ℕ) (i : Fin 7) : ℕ := ![1,r-1,1,r-1,r,r,r] i
def rowSource (r a g : ℕ) (i : Fin 7) : ℕ :=
  ![a+1,a+5,a+1,a+7,a+5*r+5,a+5*r+3,g] i
def rowOffset (r : ℕ) (i : Fin 7) : ℕ := ![0,1,r,r+1,2*r,3*r,4*r] i
def rowStride (i : Fin 7) : ℕ := ![1,5,1,5,3,3,1] i
def rowBase (i : Fin 7) : ℕ := ![6,21,36,51,67,85,103] i
def childBase (i : Fin 7) : ℕ := ![10,25,40,56,74,92,108] i
def rowEnd (i : Fin 7) : ℕ := ![21,36,51,67,85,103,119] i

def constants : List Op := [.literal 121 0,.literal 122 1,.literal 123 5,
  .literal 124 7,.literal 125 3,.literal 126 4]
def rowSetup (i : Fin 7) : List Op := ![
  [.add 147 122 121,.add 148 118 122,.add 149 120 121,.literal 146 1],
  [.sub 147 117 122,.add 148 118 123,.add 149 120 122,.literal 146 5],
  [.add 147 122 121,.add 148 118 122,.add 149 120 117,.literal 146 1],
  [.sub 147 117 122,.add 148 118 124,.add 149 120 117,.add 149 149 122,.literal 146 5],
  [.add 147 117 121,.mul 148 117 123,.add 148 148 118,.add 148 148 123,
    .add 149 117 117,.add 149 149 120,.literal 146 3],
  [.add 147 117 121,.mul 148 117 123,.add 148 148 118,.add 148 148 125,
    .mul 149 117 125,.add 149 149 120,.literal 146 3],
  [.add 147 117 121,.add 148 119 121,.mul 149 117 126,.add 149 149 120,.literal 146 1]] i

def program : Program := constants.map Op.code ++
  (List.ofFn fun i:Fin 7=> (rowSetup i).map Op.code ++
    Strided.program.map (relocate (childBase i) (rowEnd i))).flatten ++ [.halt]

theorem program_length : program.length=120 := rfl
theorem constants_code : BlockAt constants program 0 := by
  intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem rowSetup_code (i : Fin 7) : BlockAt (rowSetup i) program (rowBase i) := by
  fin_cases i <;> intro j hj <;> simp [rowSetup] at hj
  all_goals interval_cases j <;> rfl

theorem child_code (i : Fin 7) : CodeAt Strided.program program (childBase i) (rowEnd i) := by
  fin_cases i <;> intro j hj <;> change j<11 at hj
  all_goals interval_cases j <;> rfl

theorem halt_code : program[119]?=some .halt := rfl

theorem setup_end (i : Fin 7) : rowBase i+(rowSetup i).length=childBase i := by fin_cases i <;> rfl
theorem row_end_next (k : ℕ) (hk:k+1<7) :
    rowEnd ⟨k,by omega⟩=rowBase ⟨k+1,hk⟩ := by
  have hk':k ≤ 5:=by omega
  interval_cases k <;> rfl

theorem row_stride_pos (i : Fin 7) : 0<rowStride i := by fin_cases i <;> decide

theorem row_within (r : ℕ) (hr:0<r) (i : Fin 7) : rowOffset r i+rowWidth r i ≤ 5*r := by
  fin_cases i <;> simp [rowOffset,rowWidth] <;> omega

theorem row_ordered (r : ℕ) (hr:0<r) (i j : Fin 7) (h:i<j) :
    rowOffset r i+rowWidth r i  ≤  rowOffset r j := by
  fin_cases i <;> fin_cases j <;> simp [rowOffset,rowWidth] at * <;> omega

theorem row_source_bound (r a g d : ℕ) (hr:0<r) (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d) (i : Fin 7) :
    rowSource r a g i+rowStride i*rowWidth r i ≤ d := by
  fin_cases i <;> simp [rowSource,rowStride,rowWidth] <;> omega

theorem row_present {r a g : ℕ} {omega : ℂ} {s : State} (hr:0<r) (h:Sources r a g omega s) (i : Fin 7) :
    Strided.Source (rowWidth r i) (rowSource r a g i) (rowStride i) s.scalarHeap := by
  fin_cases i
  · intro j hj
    have hz:j=0:=by simp [rowWidth] at hj;omega
    subst j
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.HIndex] using h 0 ⟨0,hr⟩⟩
  · intro j hj
    have hjr:j+1<r:=by simp [rowWidth] at hj;omega
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.HIndex,
      Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h 0 ⟨j+1,hjr⟩⟩
  · intro j hj
    have hz:j=0:=by simp [rowWidth] at hj;omega
    subst j
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.scaleIndex] using h 1 ⟨0,hr⟩⟩
  · intro j hj
    have hjr:j+1<r:=by simp [rowWidth] at hj;omega
    refine ⟨prepared (seedValue omega 1 (j+1)),?_⟩
    have he:rowSource r a g 3+rowStride 3*j=sourceAddress r a g 1 (j+1):=by
      simp [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.scaleIndex,Nat.mul_add];omega
    change s.scalarHeap (rowSource r a g 3+rowStride 3*j)=_
    rw [he];exact h 1 ⟨j+1,hjr⟩
  · intro j hj;have hjr:j<r:=by simpa [rowWidth] using hj
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress,Nat.mul_add,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm] using h 2 ⟨j,hjr⟩⟩
  · intro j hj;have hjr:j<r:=by simpa [rowWidth] using hj
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress,Nat.mul_add,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm] using h 3 ⟨j,hjr⟩⟩
  · intro j hj;have hjr:j<r:=by simpa [rowWidth] using hj
    exact ⟨_,by simpa [rowSource,rowStride,sourceAddress] using h 4 ⟨j,hjr⟩⟩

structure Header (r a g d : ℕ) (s : State) : Prop where
  count : s.natReg 117=r
  source : s.natReg 118=a
  reciprocal : s.natReg 119=g
  destination : s.natReg 120=d
  zero : s.natReg 121=0
  one : s.natReg 122=1
  five : s.natReg 123=5
  seven : s.natReg 124=7
  three : s.natReg 125=3
  four : s.natReg 126=4

theorem Header.withPC {r a g d pc : ℕ} {s : State} (h:Header r a g d s) :
    Header r a g d {s with pc:=pc} := by
  cases h;constructor <;> assumption

theorem Header.transport {r a g d : ℕ} {s u : State} (h:Header r a g d s)
    (hn:∀i,i<146 → u.natReg i=s.natReg i) : Header r a g d u := by
  exact ⟨(hn _ (by decide)).trans h.count,(hn _ (by decide)).trans h.source,
    (hn _ (by decide)).trans h.reciprocal,(hn _ (by decide)).trans h.destination,
    (hn _ (by decide)).trans h.zero,(hn _ (by decide)).trans h.one,
    (hn _ (by decide)).trans h.five,(hn _ (by decide)).trans h.seven,
    (hn _ (by decide)).trans h.three,(hn _ (by decide)).trans h.four⟩

/-- Apart from actual destination stores, only scratch Nat146..154 and scalar32 change. -/
def Frame (s u : State) : Prop := Strided.Frame s u ∧ ∀i,i<146 → u.natReg i=s.natReg i

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h.1.trans h'.1,fun i hi=>(h'.2 i hi).trans (h.2 i hi)⟩

theorem rowSetup_frame (i : Fin 7) (s : State) : Frame s (applyBlock (rowSetup i) s) := by
  fin_cases i <;> constructor
  all_goals first
    | exact ⟨rfl,rfl,rfl,fun _ _=>rfl⟩
    | intro j hj;simp (disch:=omega) [rowSetup,applyBlock,Op.apply,writeNat,next]

theorem rowSetup_heap (i : Fin 7) (s : State) : (applyBlock (rowSetup i) s).scalarHeap=s.scalarHeap := by
  fin_cases i <;> rfl

theorem rowSetup_readable (i : Fin 7) (s : State) : readable (rowSetup i) s := by
  fin_cases i <;> trivial

theorem rowSetup_registers {r a g d : ℕ} {s : State} (h:Header r a g d s) (i : Fin 7) :
    let u:=applyBlock (rowSetup i) s
    u.natReg 146=rowStride i ∧ u.natReg 147=rowWidth r i ∧
    u.natReg 148=rowSource r a g i ∧ u.natReg 149=d+rowOffset r i := by
  fin_cases i <;> simp [rowSetup,applyBlock,Op.apply,writeNat,next,rowStride,rowWidth,rowSource,rowOffset,
    h.count,h.source,h.reciprocal,h.destination,h.zero,h.one,h.five,h.seven,h.three,h.four,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,two_mul]

theorem rowSetup_peak {r a g d B : ℕ} {s : State} (h:Header r a g d s) (hr:0<r)
    (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d) (hB:d+5*r ≤ B) (i : Fin 7) : peak (rowSetup i) s ≤ B := by
  fin_cases i <;> simp [rowSetup,peak,Op.peak,Op.apply,writeNat,next,
    h.count,h.source,h.reciprocal,h.destination,h.zero,h.one,h.five,h.seven,h.three,h.four]
  all_goals omega


def RowCopies (r a g d k : ℕ) (heap : ℕ → Option Scalar) (s : State) : Prop :=
  ∀i:Fin 7,i.val<k → ∀j,j<rowWidth r i →
    s.scalarHeap (d+rowOffset r i+j)=heap (rowSource r a g i+rowStride i*j)

theorem row_execution (n : ℕ) (x : Fin n → ℂ) (r a g d B : ℕ) (i : Fin 7) (s : State)
    (hr:0<r) (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d) (hB:d+5*r ≤ B) (hcode:120 ≤ B)
    (hh:Header r a g d s) (hsrc:Strided.Source (rowWidth r i) (rowSource r a g i) (rowStride i) s.scalarHeap)
    (hpc:s.pc=rowBase i) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s ((rowSetup i).length+8*rowWidth r i+4) u ∧
    u.pc=rowEnd i ∧ Header r a g d u ∧
    (∀j,j<rowWidth r i → u.scalarHeap (d+rowOffset r i+j)=s.scalarHeap (rowSource r a g i+rowStride i*j)) ∧
    Strided.Outside (d+rowOffset r i) (rowWidth r i) s.scalarHeap u ∧ Frame s u := by
  have hset:=block_runs (rowSetup i) program (rowBase i) n B x s (rowSetup_code i) hpc hs
    (by fin_cases i <;> simp [rowBase,rowSetup] <;> omega) (rowSetup_readable i s)
    (rowSetup_peak hh hr ha hg hB i)
  let z:=applyBlock (rowSetup i) s
  let e:State:={z with pc:=0}
  obtain ⟨h146,h147,h148,h149⟩:=rowSetup_registers hh i
  have he:WordBound B e:=changePC_bound B z 0 hset.final_bound (by omega)
  have hed:d+rowOffset r i+rowWidth r i ≤ B:=by have hw:=row_within r hr i;omega
  obtain ⟨u,hu,hcopy,hsource,hout,hframe,hnat⟩:=Strided.execution n x (rowWidth r i)
    (rowSource r a g i) (d+rowOffset r i) (rowStride i) B e
    (by simpa only [e,z,rowSetup_heap] using hsrc) (row_stride_pos i)
    (by have hb:=row_source_bound r a g d hr ha hg i;omega) hed (by omega) rfl
    h146 h147 h148 h149 he
  have hruns:=UniformBoundedAssembly.boundedExecution_placed (child_code i)
    (by fin_cases i <;> simp [childBase,Strided.program_length] <;> omega)
    (by fin_cases i <;> simp [rowEnd] <;> omega) hu
  have hp:z.pc=childBase i:=(UniformReciprocalMachine.applyBlock_pc _ s).trans (by rw [hpc,setup_end])
  have hplace:placed (childBase i) e=z:=by change {z with pc:=childBase i}=z;rw [←hp]
  rw [hplace] at hruns
  have hfr:Frame s {u with pc:=rowEnd i}:=(rowSetup_frame i s).trans
    ⟨hframe,fun j hj=>hnat j (Or.inl (by omega))⟩
  refine ⟨{u with pc:=rowEnd i},?_,rfl,hh.transport hfr.2,?_,?_,hfr⟩
  · exact hset.trans hruns
  · simpa only [e,z,rowSetup_heap] using hcopy
  · intro j hj;exact (hout j hj).trans (congrFun (rowSetup_heap i s) j)

def suffixCost (r k : ℕ) : ℕ :=
  ((List.ofFn fun i:Fin 7=>(rowSetup i).length+8*rowWidth r i+4).drop k).sum

theorem suffixCost_end (r : ℕ) : suffixCost r 7=0 := rfl

theorem suffixCost_next (r k : ℕ) (hk:k<7) :
    suffixCost r k=(rowSetup ⟨k,hk⟩).length+8*rowWidth r ⟨k,hk⟩+4+suffixCost r (k+1) := by
  interval_cases k <;> simp [suffixCost,rowSetup,rowWidth,Nat.add_assoc]

theorem suffixCost_total (r : ℕ) (hr:0<r) : suffixCost r 0=40*r+64 := by
  simp [suffixCost,rowSetup,rowWidth];omega

def rowPC (k : ℕ) : ℕ := if h:k<7 then rowBase ⟨k,h⟩ else 119

theorem rows_execution (n : ℕ) (x : Fin n → ℂ) (r a g d k fuel B : ℕ)
    (heap : ℕ → Option Scalar) (s : State) (hr:0<r) (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d)
    (hB:d+5*r ≤ B) (hcode:120 ≤ B) (hk:k+fuel=7) (hh:Header r a g d s)
    (hsrc:∀i:Fin 7,Strided.Source (rowWidth r i) (rowSource r a g i) (rowStride i) heap)
    (hc:RowCopies r a g d k heap s) (hout:Strided.Outside d (5*r) heap s)
    (hpc:s.pc=rowPC k) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (suffixCost r k) u ∧ u.pc=119 ∧ Header r a g d u ∧
    RowCopies r a g d 7 heap u ∧ Strided.Outside d (5*r) heap u ∧ Frame s u := by
  induction fuel generalizing k s with
  | zero =>
    have he:k=7:=by omega
    subst k
    exact ⟨s,by rw [suffixCost_end];exact .refl hs,by simpa [rowPC] using hpc,hh,hc,hout,
      ⟨⟨rfl,rfl,rfl,fun _ _=>rfl⟩,fun _ _=>rfl⟩⟩
  | succ fuel ih =>
    have hki:k<7:=by omega
    let i:Fin 7:=⟨k,hki⟩
    have hsource:Strided.Source (rowWidth r i) (rowSource r a g i) (rowStride i) s.scalarHeap:=by
      intro j hj
      obtain ⟨v,hv⟩:=hsrc i j hj
      have hm:=Nat.mul_lt_mul_of_pos_left hj (row_stride_pos i)
      have hb:=row_source_bound r a g d hr ha hg i
      exact ⟨v,(hout _ (Or.inl (by omega))).trans hv⟩
    obtain ⟨u,hu,hpu,hhu,hcu,houtU,hfr⟩:=row_execution n x r a g d B i s hr ha hg hB hcode hh hsource
      (by simpa only [rowPC,dite_eq_left hki] using hpc) hs
    have hcopy:RowCopies r a g d (k+1) heap u:=by
      intro j hj l hl
      by_cases he:j.val=k
      · have heji:j=i:=Fin.ext he
        subst j
        rw [hcu l hl,hout _ (Or.inl ?_)]
        have hm:=Nat.mul_lt_mul_of_pos_left hl (row_stride_pos i)
        have hb:=row_source_bound r a g d hr ha hg i
        omega
      · have hjk:j.val<k:=by omega
        have horder:=row_ordered r hr j i (by exact hjk)
        exact (houtU _ (Or.inl (by omega))).trans (hc j hjk l hl)
    have houtside:Strided.Outside d (5*r) heap u:=by
      intro j hj
      have hw:=row_within r hr i
      exact (houtU j (by rcases hj with hj|hj;exact Or.inl (by omega);exact Or.inr (by omega))).trans
        (hout j hj)
    have hpnext:u.pc=rowPC (k+1):=by
      by_cases hnext:k+1<7
      · rw [rowPC,dite_eq_left hnext,←row_end_next k hnext];exact hpu
      · have hk6:k=6:=by omega
        subst k
        simpa [rowPC,rowEnd,i] using hpu
    obtain ⟨w,hw,hpw,hhw,hcw,how,hfw⟩:=ih (k+1) u (by omega) hhu hcopy houtside hpnext hu.final_bound
    refine ⟨w,?_,hpw,hhw,hcw,how,hfr.trans hfw⟩
    convert hu.trans hw using 1
    rw [suffixCost_next r k hki]


/-- The retained compact pool has five contiguous lanes, with no data retagging. -/
def Compact (r d : ℕ) (omega : ℂ) (s : State) : Prop :=
  ∀q:Fin 5,∀j:Fin r,s.scalarHeap (d+q.val*r+j.val)=some (prepared (seedValue omega q j.val))

theorem compact_of_rows {r a g d : ℕ} {omega : ℂ} {s u : State}
    (hc:RowCopies r a g d 7 s.scalarHeap u) (hsrc:Sources r a g omega s) : Compact r d omega u := by
  intro q j
  fin_cases q
  · by_cases hj:j.val=0
    · have h:=hc 0 (by decide) 0 (by simp [rowWidth])
      have hs:=hsrc 0 j
      simp [rowOffset,rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.HIndex,hj] at h hs ⊢
      exact h.trans hs
    · have hjp:0<j.val:=by omega
      have h:=hc 1 (by decide) (j.val-1) (by simp [rowWidth];omega)
      have he:rowSource r a g 1+rowStride 1*(j.val-1)=sourceAddress r a g 0 j.val:=by
        simp [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.HIndex,hj]
        omega
      rw [he] at h
      have hd:d+rowOffset r 1+(j.val-1)=d+j.val:=by simp [rowOffset];omega
      rw [hd] at h
      simpa using h.trans (hsrc 0 j)
  · by_cases hj:j.val=0
    · have h:=hc 2 (by decide) 0 (by simp [rowWidth])
      have hs:=hsrc 1 j
      simp [rowOffset,rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.scaleIndex,hj] at h hs ⊢
      exact h.trans hs
    · have hjp:0<j.val:=by omega
      have h:=hc 3 (by decide) (j.val-1) (by simp [rowWidth];omega)
      have he:rowSource r a g 3+rowStride 3*(j.val-1)=sourceAddress r a g 1 j.val:=by
        simp [rowSource,rowStride,sourceAddress,UniformNewtonTableMachine.scaleIndex,hj]
        omega
      rw [he] at h
      have hd:d+rowOffset r 3+(j.val-1)=d+r+j.val:=by simp [rowOffset];omega
      rw [hd] at h
      simpa using h.trans (hsrc 1 j)
  · have h:=hc 4 (by decide) j.val j.isLt
    have he:rowSource r a g 4+rowStride 4*j.val=sourceAddress r a g 2 j.val:=by
      simp [rowSource,rowStride,sourceAddress];omega
    rw [he] at h
    simpa [rowOffset,Nat.add_assoc] using h.trans (hsrc 2 j)
  · have h:=hc 5 (by decide) j.val j.isLt
    have he:rowSource r a g 5+rowStride 5*j.val=sourceAddress r a g 3 j.val:=by
      simp [rowSource,rowStride,sourceAddress];omega
    rw [he] at h
    simpa [rowOffset,Nat.add_assoc] using h.trans (hsrc 3 j)
  · have h:=hc 6 (by decide) j.val j.isLt
    have he:rowSource r a g 6+rowStride 6*j.val=sourceAddress r a g 4 j.val:=by
      simp [rowSource,rowStride,sourceAddress]
    rw [he] at h
    simpa [rowOffset,Nat.add_assoc] using h.trans (hsrc 4 j)

/-- Emitter constants are initialized by six charged literal instructions. -/
theorem constants_header {r a g d : ℕ} {s : State} (h117:s.natReg 117=r) (h118:s.natReg 118=a)
    (h119:s.natReg 119=g) (h120:s.natReg 120=d) : Header r a g d (applyBlock constants s) := by
  constructor <;> simp [constants,applyBlock,Op.apply,writeNat,next,h117,h118,h119,h120]

/-- The six constants may change Nat121..126. All saved global headers are retained. -/
def OuterFrame (s u : State) : Prop := Strided.Frame s u ∧
  ∀ (i : ℕ), (i < 121 ∨ 127  ≤  i)  →  i < 146  →  u.natReg i = s.natReg i

theorem constants_frame (s : State) : OuterFrame s (applyBlock constants s) := by
  refine ⟨⟨rfl,rfl,rfl,fun _ _=>rfl⟩,?_⟩
  intro i hi _
  simp (disch:=omega) [constants,applyBlock,Op.apply,writeNat,next]

/-- Actual fixed120-instruction emitter; count40*r+71 includes every pointer,
scalar load/store, branch, loop increment, setup and final halt. Source facts
come from the produced Newton/G banks, never from a preprinted compact table. -/
theorem execution (n : ℕ) (x : Fin n → ℂ) (r a g d B : ℕ) (omega : ℂ) (s : State)
    (hr:0<r) (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d) (hB:d+5*r ≤ B) (hcode:120 ≤ B)
    (hsrc:Sources r a g omega s) (hpc:s.pc=0)
    (h117:s.natReg 117=r) (h118:s.natReg 118=a) (h119:s.natReg 119=g) (h120:s.natReg 120=d)
    (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (40*r+71) u ∧ Compact r d omega u ∧
    Strided.Outside d (5*r) s.scalarHeap u ∧ OuterFrame s u ∧ u.pc=119 := by
  have hc:=block_runs constants program 0 n B x s constants_code hpc hs
    (by change 6 ≤ B;omega) (by trivial) (by simp [peak,constants,Op.peak];omega)
  let z:=applyBlock constants s
  have hzheap:z.scalarHeap=s.scalarHeap:=rfl
  have hzpc:z.pc=rowPC 0:=by rw [UniformReciprocalMachine.applyBlock_pc,hpc];rfl
  obtain ⟨u,hu,hpu,hhu,hcopies,houtside,hframe⟩:=rows_execution n x r a g d 0 7 B s.scalarHeap z hr ha hg
    hB hcode rfl (constants_header h117 h118 h119 h120) (row_present hr hsrc)
    (by intro i hi;omega) (by intro i hi;rfl) hzpc hc.final_bound
  have hh:WordBound B u:=hu.final_bound
  have halt:BoundedExecution program n x B u 1 u:=.halt hh (by simp [step,hpu,halt_code])
  refine ⟨u,?_,compact_of_rows hcopies hsrc,houtside,?_,hpu⟩
  · convert hc.executes (hu.executes halt) using 1
    rw [suffixCost_total r hr];change 40*r+71=6+(40*r+64+1);omega
  · exact ⟨(constants_frame s).1.trans hframe.1,
      fun i hi hib=>(hframe.2 i hib).trans ((constants_frame s).2 i hi hib)⟩

/-- Direct public bridge from the actual local RAM output postconditions. -/
theorem execution_from_local (n : ℕ) (x : Fin n → ℂ) (r a g d B : ℕ) (omega : ℂ) (s : State)
    (hr:0<r) (ha:a+8*r+5 ≤ d) (hg:g+r ≤ d) (hB:d+5*r ≤ B) (hcode:120 ≤ B)
    (hp:UniformNewtonTableMachine.PreparedOutputs r omega a s)
    (hgReady:UniformReciprocalMachine.GPrefix r g (OAI.ExactFourier.NewtonFourier.invH omega) s)
    (hpc:s.pc=0) (h117:s.natReg 117=r) (h118:s.natReg 118=a)
    (h119:s.natReg 119=g) (h120:s.natReg 120=d) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (40*r+71) u ∧ Compact r d omega u ∧
    Strided.Outside d (5*r) s.scalarHeap u ∧ OuterFrame s u ∧ u.pc=119 :=
  execution n x r a g d B omega s hr ha hg hB hcode (Sources.fromLocal hp hgReady) hpc h117 h118 h119 h120 hs


/-- Charged selected-axis header producer. The radix is loaded from the actual
protected CRT row; no caller-supplied local addresses or row length are used. -/
def globalPointer : List Op := [.literal 107 4,.mul 108 110 107,
  .add 108 102 108,.add 108 105 108]
def globalSetup : List Op := [
  .literal 107 7,.add 111 102 107,.literal 107 2,.mul 112 101 107,.add 111 111 112,
  .add 111 111 103,.add 111 111 103,.literal 107 1,.add 111 111 107,.add 111 111 103,
  .literal 107 8,.mul 112 117 107,.add 118 111 112,.literal 107 5,.add 118 118 107,
  .add 119 118 112,.literal 107 10,.add 119 119 107,
  .literal 107 17,.mul 112 103 107,.add 120 111 112,.literal 107 16,.add 120 120 107]
def globalHead : Program := globalPointer.map Op.code++[.loadNat 117 108]++globalSetup.map Op.code
def fullProgram : Program := embed globalHead program [.halt] 148

theorem globalPointer_length : globalPointer.length=4 := rfl
theorem globalSetup_length : globalSetup.length=23 := rfl
theorem globalHead_length : globalHead.length=28 := rfl
theorem fullProgram_length : fullProgram.length=149 := by rw [fullProgram,embed_length,globalHead_length,program_length];rfl

theorem globalPointer_code : BlockAt globalPointer fullProgram 0 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem globalLoad_code : fullProgram[4]?=some (.loadNat 117 108) := rfl
theorem globalSetup_code : BlockAt globalSetup fullProgram 5 := by
  intro i hi;change i<23 at hi;interval_cases i <;> rfl
theorem fullProgram_child : CodeAt program fullProgram 28 148 := by
  simpa only [fullProgram,globalHead_length] using embed_code globalHead program [.halt] 148
theorem fullProgram_halt : fullProgram[148]?=some .halt := by
  simp only [fullProgram,embed]
  rw [List.getElem?_append_right (by simp [globalHead_length,program_length])]
  simp [globalHead_length,program_length]

def globalLoaded (s : State) (r : ℕ) : State := writeNat (applyBlock globalPointer s) 117 r
def globalInitialized (s : State) (r : ℕ) : State := applyBlock globalSetup (globalLoaded s r)

theorem globalPointer_address {n : ℕ} (j : Fin (ell n+1)) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hj:s.natReg 110=j.val) :
    (applyBlock globalPointer s).natReg 108=UniformInitialPreparation.copyBase n+
      UniformCRTHeaderMachine.tableAddress (ell n) j.val 0 :=
  UniformGlobalLocalPreparation.pointer_address j s hm hj

theorem globalInitialized_registers {n : ℕ} (j : Fin (ell n+1)) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) :
    let r:=UniformGlobalLocalPreparation.radix n j
    (globalInitialized s r).natReg 117=r ∧
    (globalInitialized s r).natReg 118=UniformGlobalLocalPreparation.resultBase n r ∧
    (globalInitialized s r).natReg 119=UniformGlobalLocalPreparation.rootSource n r+1 ∧
    (globalInitialized s r).natReg 120=poolBase n := by
  simp [globalInitialized,globalLoaded,globalPointer,globalSetup,applyBlock,Op.apply,writeNat,next,
    hm.saved.count,hm.saved.inputLength,hm.saved.workingLength,poolBase,UniformGlobalLocalPreparation.resultBase,
    UniformGlobalLocalPreparation.rootSource,UniformGlobalLocalPreparation.scratchBase,
    UniformGlobalLocalPreparation.globalEnd_formula,Nat.mul_comm,Nat.add_assoc]
  omega

theorem globalInitialized_frame (s : State) (r : ℕ) :
    Strided.Frame s (globalInitialized s r) ∧
    (∀i,100 ≤ i → i ≤ 106 → (globalInitialized s r).natReg i=s.natReg i) ∧
    (globalInitialized s r).scalarHeap=s.scalarHeap := by
  refine ⟨⟨rfl,rfl,rfl,fun _ _=>rfl⟩,?_,rfl⟩
  intro i hi hiu
  simp (disch:=omega) [globalInitialized,globalLoaded,globalPointer,globalSetup,applyBlock,Op.apply,writeNat,next]

theorem globalPointer_peak {n : ℕ} (j : Fin (ell n+1)) (B : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hj:s.natReg 110=j.val)
    (hcopy:UniformInitialPreparation.copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ B)
    (hcode:149 ≤ B) : peak globalPointer s ≤ B := by
  have hjb:=j.isLt
  simp [peak,globalPointer,Op.peak,Op.apply,writeNat,next,hm.saved.count,hm.saved.copyAddress,hj]
  unfold UniformGlobalNatPreparation.amount at hcopy
  simp only [UniformInitialPreparation.copyBase] at hcopy
  omega

theorem globalSetup_peak {n : ℕ} (j : Fin (ell n+1)) (B : ℕ) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s)
    (hp:poolBase n+5*UniformGlobalLocalPreparation.radix n j ≤ B) (hcode:149 ≤ B) :
    peak globalSetup (globalLoaded s (UniformGlobalLocalPreparation.radix n j)) ≤ B := by
  have hr:=UniformGlobalLocalPreparation.radix_le_length n j
  have hr0:=UniformGlobalLocalPreparation.radix_pos n j
  simp [peak,globalSetup,globalLoaded,globalPointer,Op.peak,Op.apply,applyBlock,writeNat,next,
    hm.saved.count,hm.saved.inputLength,hm.saved.workingLength]
  unfold poolBase at hp
  rw [UniformGlobalLocalPreparation.globalEnd_formula] at hp
  omega

/-- Both Newton source regions and the G lane lie strictly below the retained pool. -/
theorem selected_source_bounds (n : ℕ) (j : Fin (ell n+1)) :
    UniformGlobalLocalPreparation.resultBase n (UniformGlobalLocalPreparation.radix n j)+
      8*UniformGlobalLocalPreparation.radix n j+5 ≤ poolBase n ∧
    UniformGlobalLocalPreparation.rootSource n (UniformGlobalLocalPreparation.radix n j)+1+
      UniformGlobalLocalPreparation.radix n j ≤ poolBase n := by
  have hr:=UniformGlobalLocalPreparation.radix_le_length n j
  dsimp only [poolBase,UniformGlobalLocalPreparation.rootSource,UniformGlobalLocalPreparation.scratchBase,
    UniformGlobalLocalPreparation.resultBase]
  omega

theorem pool_word_bound {n : ℕ} (hn:0<n) (j : Fin (ell n+1)) :
    149 ≤ (n+2)^19 ∧ poolBase n+5*UniformGlobalLocalPreparation.radix n j ≤ (n+2)^19 := by
  have he:ell n ≤ 2*n:=by have h:=UniformWorkingLength.firstExceed_bound n;unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hr:=UniformGlobalLocalPreparation.radix_le_length n j
  have hp:300 ≤ (n+2)^18:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 18;norm_num at h;omega
  have hb:300*(n+2) ≤ (n+2)^19:=by rw [pow_succ];exact Nat.mul_le_mul_right (n+2) hp
  unfold poolBase
  rw [UniformGlobalLocalPreparation.globalEnd_formula]
  omega

/-- Full charged selected-axis emitter. The only local-value premises are actual
postconditions of the preceding299-instruction producer. All header values,
source/destination addresses, loads, stores and loops are executed here. -/
theorem selected_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (ell n+1))
    (s : State) (hm:UniformPermutationInversePreparation.Metadata n s)
    (hp:UniformNewtonTableMachine.PreparedOutputs (UniformGlobalLocalPreparation.radix n j)
      (OAI.ExactFourier.zeta (UniformGlobalLocalPreparation.radix n j))
      (UniformGlobalLocalPreparation.resultBase n (UniformGlobalLocalPreparation.radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (UniformGlobalLocalPreparation.radix n j)
      (UniformGlobalLocalPreparation.rootSource n (UniformGlobalLocalPreparation.radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (UniformGlobalLocalPreparation.radix n j))) s)
    (hpc:s.pc=0) (hj:s.natReg 110=j.val) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution fullProgram n x ((n+2)^19) s (40*UniformGlobalLocalPreparation.radix n j+100) u ∧
    Compact (UniformGlobalLocalPreparation.radix n j) (poolBase n)
      (OAI.ExactFourier.zeta (UniformGlobalLocalPreparation.radix n j)) u ∧
    Strided.Outside (poolBase n) (5*UniformGlobalLocalPreparation.radix n j) s.scalarHeap u ∧
    UniformPermutationInversePreparation.Metadata n u ∧
    Strided.Frame s u ∧ (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.pc=148 := by
  let r:=UniformGlobalLocalPreparation.radix n j
  let B:=(n+2)^19
  obtain ⟨hcode,hpool⟩:=pool_word_bound hn j
  obtain ⟨_,hcopy,_⟩:=UniformGlobalLocalPreparation.word_setup hn j
  have hptr:=block_runs globalPointer fullProgram 0 n B x s globalPointer_code hpc hs
    (by change 4 ≤ B;omega) (by trivial) (globalPointer_peak j B s hm hj hcopy hcode)
  have h4:(applyBlock globalPointer s).pc=4:=by rw [UniformReciprocalMachine.applyBlock_pc,hpc];rfl
  have hl:(applyBlock globalPointer s).natHeap ((applyBlock globalPointer s).natReg 108)=some r:=by
    rw [globalPointer_address j s hm hj,UniformReciprocalMachine.applyBlock_natHeap]
    exact (hm.crt j).1
  have hbLoad:WordBound B (globalLoaded s r):=writeNat_bound B _ 117 r hptr.final_bound
    (by rw [h4];omega) (by have hr:=UniformGlobalLocalPreparation.radix_le_length n j;omega)
  have hload:BoundedRuns fullProgram n x B (applyBlock globalPointer s) 1 (globalLoaded s r):=
    .next hptr.final_bound (by simp [step,h4,globalLoad_code,hl,globalLoaded]) (.refl hbLoad)
  have hp5:(globalLoaded s r).pc=5:=by simp [globalLoaded,writeNat,next,h4]
  have hsetup:=block_runs globalSetup fullProgram 5 n B x (globalLoaded s r) globalSetup_code hp5 hbLoad
    (by change 28 ≤ B;omega) (by trivial) (globalSetup_peak j B s hm hpool hcode)
  let z:=globalInitialized s r
  let e:State:={z with pc:=0}
  have heB:WordBound B e:=changePC_bound B z 0 hsetup.final_bound (by omega)
  obtain ⟨h117,h118,h119,h120⟩:=globalInitialized_registers j s hm
  have heNat:e.natReg=(globalInitialized s r).natReg:=rfl
  have heHeap:e.scalarHeap=(globalInitialized s r).scalarHeap:=rfl
  have he117:e.natReg 117=r:=(congrFun heNat 117).trans h117
  have he118:e.natReg 118=UniformGlobalLocalPreparation.resultBase n r:=(congrFun heNat 118).trans h118
  have he119:e.natReg 119=UniformGlobalLocalPreparation.rootSource n r+1:=(congrFun heNat 119).trans h119
  have he120:e.natReg 120=poolBase n:=(congrFun heNat 120).trans h120
  have hn:e.scalarHeap=s.scalarHeap:=heHeap.trans (globalInitialized_frame s r).2.2
  have hpe:UniformNewtonTableMachine.PreparedOutputs r (OAI.ExactFourier.zeta r)
      (UniformGlobalLocalPreparation.resultBase n r) e:=by
    intro j q;exact (congrFun hn _).trans (hp j q)
  have hge:UniformReciprocalMachine.GPrefix r (UniformGlobalLocalPreparation.rootSource n r+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta r)) e:=by
    intro k hk;exact (congrFun hn _).trans (hg k hk)
  obtain ⟨ha,hgB⟩:=selected_source_bounds n j
  obtain ⟨u,hu,hcompact,houtside,hframe,hpu⟩:=execution_from_local n x r
    (UniformGlobalLocalPreparation.resultBase n r) (UniformGlobalLocalPreparation.rootSource n r+1)
    (poolBase n) B (OAI.ExactFourier.zeta r) e (UniformGlobalLocalPreparation.radix_pos n j)
    ha hgB hpool (by omega) hpe hge rfl he117 he118 he119 he120 heB
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed fullProgram_child
    (by rw [program_length];omega :28+program.length ≤ B) (by omega :148 ≤ B) hu
  have hzpc:z.pc=28:=(UniformReciprocalMachine.applyBlock_pc globalSetup (globalLoaded s r)).trans
    (by rw [hp5,globalSetup_length])
  have heq:placed 28 e=z:=by change {z with pc:=28}=z;rw [←hzpc]
  rw [heq] at hplaced
  let final:State:={u with pc:=148}
  have hhalt:BoundedExecution fullProgram n x B final 1 final:=.halt hplaced.final_bound
    (by simp [step,final,fullProgram_halt])
  have hsaved:∀i,100 ≤ i → i ≤ 106 → final.natReg i=s.natReg i:=by
    intro i hi hiu
    exact (hframe.2 i (Or.inl (by omega)) (by omega)).trans ((globalInitialized_frame s r).2.1 i hi hiu)
  have hmeta:UniformPermutationInversePreparation.Metadata n final:=by
    apply hm.transport_saved
    · constructor
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.nextPrime
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.inputLength
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.count
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.workingLength
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.masterRoot
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.copyAddress
      · exact (hsaved _ (by decide) (by decide)).trans hm.saved.copyLength
    · intro a ha
      exact congrFun (hframe.1.1.trans (globalInitialized_frame s r).1.1) _
  refine ⟨final,?_,hcompact,?_,hmeta,(globalInitialized_frame s r).1.trans hframe.1,hsaved,rfl⟩
  · convert (hptr.trans hload).trans hsetup |>.executes (hplaced.executes hhalt) using 1
    change 40*r+100=4+1+23+(40*r+71+1);omega
  · intro i hi;exact (houtside i hi).trans (congrFun hn i)


/-- A semantic high-frame theorem for the actual frozen299-instruction program.
It reconstructs its real root copy and Newton/reciprocal run, then uses execution
determinism; it does not infer retention from allocation alone. -/
theorem local_execution_high_pool {n B t : ℕ} (x : Fin n→ℂ) (j : Fin (ell n+1))
    (s u : State) (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) (hpc:s.pc=0) (hj:s.natReg 110=j.val)
    (hcopy:UniformInitialPreparation.copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ B)
    (hWord:UniformReciprocalMachine.completeWordBudget (UniformGlobalLocalPreparation.radix n j)
      (UniformGlobalLocalPreparation.resultBase n (UniformGlobalLocalPreparation.radix n j))
      (UniformGlobalLocalPreparation.rootSource n (UniformGlobalLocalPreparation.radix n j)) ≤ B)
    (hcode:299 ≤ B) (hs:WordBound B s)
    (he:BoundedExecution UniformGlobalLocalPreparation.program n x B s t u) :
    ∀i,poolBase n ≤ i → u.scalarHeap i=s.scalarHeap i := by
  let r:=UniformGlobalLocalPreparation.radix n j
  have hr:=UniformGlobalLocalPreparation.radix_pos n j
  have hrL:=UniformGlobalLocalPreparation.radix_le_length n j
  have hLB:len n ≤ B:=by rw [←hm.saved.workingLength];exact hs.2.1 103
  have hptr:=block_runs UniformGlobalLocalPreparation.pointer UniformGlobalLocalPreparation.program 0 n B x s
    UniformGlobalLocalPreparation.pointer_code hpc hs (by change 4 ≤ B;omega) (by trivial)
    (UniformGlobalLocalPreparation.pointer_peak j B s hm hj hcopy hcode)
  have hp4:(applyBlock UniformGlobalLocalPreparation.pointer s).pc=4:=by
    rw [UniformReciprocalMachine.applyBlock_pc,hpc];rfl
  have hload:(applyBlock UniformGlobalLocalPreparation.pointer s).natHeap
      ((applyBlock UniformGlobalLocalPreparation.pointer s).natReg 108)=some r:=by
    rw [UniformGlobalLocalPreparation.pointer_address j s hm hj,UniformReciprocalMachine.applyBlock_natHeap]
    exact (hm.crt j).1
  have hbLoad:WordBound B (UniformGlobalLocalPreparation.loaded s r):=writeNat_bound B _ 16 r hptr.final_bound
    (by rw [hp4];omega) (by omega)
  have hl:BoundedRuns UniformGlobalLocalPreparation.program n x B
      (applyBlock UniformGlobalLocalPreparation.pointer s) 1 (UniformGlobalLocalPreparation.loaded s r):=
    .next hptr.final_bound (by simp [step,hp4,UniformGlobalLocalPreparation.load_code,hload,
      UniformGlobalLocalPreparation.loaded]) (.refl hbLoad)
  have hp5:(UniformGlobalLocalPreparation.loaded s r).pc=5:=by
    simp [UniformGlobalLocalPreparation.loaded,writeNat,next,hp4]
  have hset:=block_runs UniformGlobalLocalPreparation.setup UniformGlobalLocalPreparation.program 5 n B x
    (UniformGlobalLocalPreparation.loaded s r) UniformGlobalLocalPreparation.setup_code hp5 hbLoad
    (by change 29 ≤ B;omega) (UniformGlobalLocalPreparation.setup_readable x j s hj ho)
    (UniformGlobalLocalPreparation.setup_peak j B s hm hj hWord)
  let z:=UniformGlobalLocalPreparation.initialized s r
  let e:State:={z with pc:=0}
  have heB:WordBound B e:=changePC_bound B z 0 hset.final_bound (by omega)
  obtain ⟨h16,h17,h18,h19⟩:=UniformGlobalLocalPreparation.initialized_registers j s hm hj
  have hn:e.natReg=(UniformGlobalLocalPreparation.initialized s r).natReg:=rfl
  have hh:e.scalarHeap=(UniformGlobalLocalPreparation.initialized s r).scalarHeap:=rfl
  have hbank:UniformNewtonTableMachine.Bank (UniformGlobalLocalPreparation.bank n) e:=by
    intro q
    exact (congrFun hh q.val).trans (UniformGlobalLocalPreparation.initialized_bank x j s hm hj ho q)
  have haxis:e.scalarHeap (UniformGlobalLocalPreparation.rootSource n r)=some (prepared (OAI.ExactFourier.zeta r)):=
    (congrFun hh _).trans (UniformGlobalLocalPreparation.initialized_axis x j s hm hj ho)
  obtain ⟨v,hv,hg,hp,hb,ha,hout,hroot,hrows,hother⟩:=UniformReciprocalMachine.complete_execution n x r
    (UniformGlobalLocalPreparation.resultBase n r) (UniformGlobalLocalPreparation.scratchBase n r)
    (UniformGlobalLocalPreparation.rootSource n r) B (OAI.ExactFourier.zeta r)
    (UniformGlobalLocalPreparation.bank n) e hr (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hr))
    (UniformGlobalLocalPreparation.layout n r) rfl ((congrFun hn 16).trans h16)
    ((congrFun hn 17).trans h17) ((congrFun hn 18).trans h18) ((congrFun hn 19).trans h19)
    hbank haxis hWord heB
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed UniformGlobalLocalPreparation.reciprocal_code
    (by rw [UniformReciprocalMachine.completeProgram_length];omega :
      29+UniformReciprocalMachine.completeProgram.length ≤ B) (by omega :298 ≤ B) hv
  have hpz:z.pc=29:=(UniformReciprocalMachine.applyBlock_pc UniformGlobalLocalPreparation.setup
    (UniformGlobalLocalPreparation.loaded s r)).trans (by rw [hp5,UniformGlobalLocalPreparation.setup_length])
  have heq:placed 29 e=z:=by change {z with pc:=29}=z;rw [←hpz]
  rw [heq] at hplaced
  have hhalt:BoundedExecution UniformGlobalLocalPreparation.program n x B {v with pc:=298} 1 {v with pc:=298}:=
    .halt hplaced.final_bound (by simp [step,UniformGlobalLocalPreparation.halt_at])
  have hbefore:BoundedRuns UniformGlobalLocalPreparation.program n x B s 29 z:=by
    convert (hptr.trans hl).trans hset using 1 <;> rfl
  have hall:=hbefore.executes (hplaced.executes hhalt)
  have heqFinal:u={v with pc:=298}:=(he.executes.deterministic hall.executes).2
  rw [heqFinal]
  intro i hi
  have hbound:UniformGlobalLocalPreparation.rootSource n r+1+r<poolBase n:=
    all_workspaces_before_pool n r hrL
  have h6:6 ≤ i:=by
    dsimp only [poolBase] at hi
    omega
  have hres:UniformGlobalLocalPreparation.resultBase n r+8*r+3 ≤ i:=by
    dsimp only [UniformGlobalLocalPreparation.rootSource,UniformGlobalLocalPreparation.scratchBase] at hbound
    omega
  have hscratch:UniformGlobalLocalPreparation.scratchBase n r+6 ≤ i:=by
    dsimp only [UniformGlobalLocalPreparation.rootSource] at hbound
    omega
  have hG:UniformGlobalLocalPreparation.rootSource n r+1+r ≤ i:=by omega
  have hzheap:e.scalarHeap i=s.scalarHeap i:=by
    change (UniformGlobalLocalPreparation.initialized s r).scalarHeap i=s.scalarHeap i
    have hneq:i ≠ UniformGlobalLocalPreparation.rootSource n r:=by omega
    rw [UniformGlobalLocalPreparation.initialized_heap x j s hm hj ho]
    exact Function.update_of_ne hneq _ _
  exact (hother i h6 (Or.inr hres) (Or.inr hscratch) (Or.inr hG)).trans hzheap

/-- Same polynomial ambient word bound as the actual local producer. -/
theorem local_execution_high_pool_budget {n t : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (ell n+1))
    (s u : State) (hm:UniformPermutationInversePreparation.Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) (hpc:s.pc=0) (hj:s.natReg 110=j.val)
    (hs:WordBound ((n+2)^19) s)
    (he:BoundedExecution UniformGlobalLocalPreparation.program n x ((n+2)^19) s t u) :
    ∀i,poolBase n ≤ i → u.scalarHeap i=s.scalarHeap i := by
  obtain ⟨hcode,hcopy,hWord⟩:=UniformGlobalLocalPreparation.word_setup hn j
  exact local_execution_high_pool x j s u hm ho hpc hj hcopy hWord hcode hs he

end
end ExactFourierCircuits.UniformLocalSeedTableMachine
