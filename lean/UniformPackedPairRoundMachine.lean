import UniformPairMachine
import UniformBoundedAssembly
import UniformCConstantsMachine

set_option autoImplicit false

/-! One physical C round over disjoint contiguous packed pairs. The entry
provides actual scalar cells and prepared coefficient cells; all coefficient
loads, pair addresses, kernel instructions and loop control are charged. -/
namespace ExactFourierCircuits.UniformPackedPairRoundMachine
open UniformMachine UniformAssembly OAI.ExactFourier

/-- Nat1280=base,1281=count,1282/1283=coefficient addresses. Scratch is
Nat0/1,1284..1287 and Scalar0..7. No Nat heap entry is written. -/
def boot : Program  :=  [.natLiteral 1284 0,.natLiteral 1285 1,
  .natLiteral 1286 2,.loadScalar 0 1282,.loadScalar 1 1283]
def head : Program  :=  boot ++ [.branchLT 1284 1281 6 22,
  .natBinary .mul 1287 1284 1286,.natBinary .add 0 1280 1287,
  .natBinary .add 1 0 1285]
def tail : Program  :=  [.natBinary .add 1284 1284 1285,.jump 5,.halt]
def program : Program  :=  embed head UniformPairMachine.program tail 20
theorem program_length : program.length=23  :=  rfl
theorem kernel_code : CodeAt UniformPairMachine.program program 9 20  :=
  embed_code head UniformPairMachine.program tail 20
theorem contextFree : UniformContext.ContextFree program  :=  by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program,
    embed,head,boot,tail,UniformPairMachine.program,relocate]

noncomputable section
abbrev diagonalCoefficient : ℂ  :=  ExactFourierCircuits.a
abbrev offDiagonalCoefficient : ℂ  :=  ExactFourierCircuits.b
abbrev Bank (m : ℕ)  :=  Fin m  →  Fin 2  →  Scalar
def address (a : ℕ) (i : ℕ) (t : Fin 2) : ℕ  :=  a+2*i+t.val
def transformed (v : Fin 2 → Scalar) (t : Fin 2) : Scalar  :=
  if t=0 then UniformPairMachine.combine diagonalCoefficient offDiagonalCoefficient (v 0) (v 1)
  else UniformPairMachine.combine offDiagonalCoefficient diagonalCoefficient (v 0) (v 1)
def Source (a m : ℕ) (v : Bank m) (s : State) : Prop  :=
  ∀ i t, s.scalarHeap (address a i.val t)=some (v i t)
def Constants (c d : ℕ) (s : State) : Prop  :=
  s.scalarHeap c=some (UniformPairMachine.prepared diagonalCoefficient)  ∧
  s.scalarHeap d=some (UniformPairMachine.prepared offDiagonalCoefficient)
structure Header (a m c d : ℕ) (s : State) : Prop where
  base : s.natReg 1280=a
  count : s.natReg 1281=m
  diagonal : s.natReg 1282=c
  offDiagonal : s.natReg 1283=d
def Outside (a m : ℕ) (s u : State) : Prop  :=
  ∀ j, j<a  ∨  a+2*m ≤ j → u.scalarHeap j=s.scalarHeap j
structure Frame (s u : State) : Prop where
  natHeap : u.natHeap=s.natHeap
  outputs : u.outputs=s.outputs
  rootOrders : u.rootOrders=s.rootOrders
  natReg : ∀ r, r ≠ 0 → r ≠ 1 → (r<1284  ∨ 1288 ≤ r) → u.natReg r=s.natReg r
  scalarReg : ∀ r, 8 ≤ r → u.scalarReg r=s.scalarReg r
theorem Frame.refl (s : State) : Frame s s  :=  ⟨rfl,rfl,rfl,fun _ _ _ _ => rfl,fun _ _ => rfl⟩
theorem Frame.trans {s u w : State} (h:Frame s u) (h':Frame u w) : Frame s w  :=
  ⟨h'.natHeap.trans h.natHeap,h'.outputs.trans h.outputs,
    h'.rootOrders.trans h.rootOrders,
    fun r h0 h1 hr => (h'.natReg r h0 h1 hr).trans (h.natReg r h0 h1 hr),
    fun r hr => (h'.scalarReg r hr).trans (h.scalarReg r hr)⟩
theorem Outside.trans {a m : ℕ} {s u w : State}
    (h:Outside a m s u) (h':Outside a m u w) : Outside a m s w  :=
  fun j hj => (h' j hj).trans (h j hj)

structure Cursor (a m c d k : ℕ) (v : Bank m) (origin s : State) : Prop where
  header : Header a m c d s
  index : s.natReg 1284=k
  one : s.natReg 1285=1
  two : s.natReg 1286=2
  diagonal : s.scalarReg 0=UniformPairMachine.prepared diagonalCoefficient
  offDiagonal : s.scalarReg 1=UniformPairMachine.prepared offDiagonalCoefficient
  bank : ∀ i t, s.scalarHeap (address a i.val t)=
    some (if i.val<k then transformed (v i) t else v i t)
  outside : Outside a m origin s
theorem Cursor.withPC {a m c d k pc : ℕ} {v : Bank m} {origin s : State}
    (h:Cursor a m c d k v origin s) : Cursor a m c d k v origin {s with pc := pc}  :=  by
  refine ⟨?_, h.index, h.one, h.two, h.diagonal, h.offDiagonal, h.bank, h.outside⟩
  exact ⟨h.header.base,h.header.count,h.header.diagonal,h.header.offDiagonal⟩

def offsetState (s : State)  :=  writeNat {s with pc := 6} 1287 (s.natReg 1284*s.natReg 1286)
def leftState (s : State)  :=  writeNat (offsetState s) 0 (s.natReg 1280+s.natReg 1284*s.natReg 1286)
def callState (s : State)  :=  writeNat (leftState s) 1 (s.natReg 1280+s.natReg 1284*s.natReg 1286+s.natReg 1285)
def kernelEnd (s : State) (u v : Scalar)  :=
  {UniformPairMachine.finalState {callState s with pc := 0} diagonalCoefficient offDiagonalCoefficient u v with pc := 20}
def advanced (s : State) (u v : Scalar)  :=  writeNat (kernelEnd s u v) 1284 (s.natReg 1284+1)
def iterationEnd (s : State) (u v : Scalar)  :=  {advanced s u v with pc := 5}

@[simp] theorem kernelEnd_nat (s : State) (u v : Scalar) :
    (kernelEnd s u v).natReg=(callState s).natReg := rfl
@[simp] theorem kernelEnd_pc (s : State) (u v : Scalar) :
    (kernelEnd s u v).pc=20 := rfl

theorem iteration_heap (s : State) (u v : Scalar) :
    (iterationEnd s u v).scalarHeap=Function.update
      (Function.update s.scalarHeap (s.natReg 1280+s.natReg 1284*s.natReg 1286)
        (some (UniformPairMachine.combine diagonalCoefficient offDiagonalCoefficient u v)))
      (s.natReg 1280+s.natReg 1284*s.natReg 1286+s.natReg 1285)
        (some (UniformPairMachine.combine offDiagonalCoefficient diagonalCoefficient u v))  :=  rfl
theorem iteration_frame (s : State) (u v : Scalar) : Frame s (iterationEnd s u v)  :=  by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r h0 h1 hr
    simp [iterationEnd,advanced,kernelEnd,callState,leftState,offsetState,
      UniformPairMachine.finalState,UniformPairMachine.storedLeft,
      UniformPairMachine.addedRight,UniformPairMachine.productOtherRight,
      UniformPairMachine.productOtherLeft,UniformPairMachine.addedLeft,
      UniformPairMachine.productRight,UniformPairMachine.productLeft,
      UniformPairMachine.loadedBoth,UniformPairMachine.loadedLeft,writeNat,writeScalar,next,
      h0,h1,show r ≠ 1284 by omega,show r ≠ 1287 by omega]
  · intro r hr
    simp [iterationEnd,advanced,kernelEnd,callState,leftState,offsetState,
      UniformPairMachine.finalState,UniformPairMachine.storedLeft,
      UniformPairMachine.addedRight,UniformPairMachine.productOtherRight,
      UniformPairMachine.productOtherLeft,UniformPairMachine.addedLeft,
      UniformPairMachine.productRight,UniformPairMachine.productLeft,
      UniformPairMachine.loadedBoth,UniformPairMachine.loadedLeft,writeNat,writeScalar,next,
      show r ≠ 2 by omega,show r ≠ 3 by omega,show r ≠ 4 by omega,
      show r ≠ 5 by omega,show r ≠ 6 by omega,show r ≠ 7 by omega]

theorem iteration_cursor {a m c d k : ℕ} {v : Bank m} {origin s : State}
    (h:Cursor a m c d k v origin s) (hk:k < m) :
    Cursor a m c d (k+1) v origin
      (iterationEnd s (v ⟨k,hk⟩ 0) (v ⟨k,hk⟩ 1))  :=  by
  have hf := iteration_frame s (v ⟨k,hk⟩ 0) (v ⟨k,hk⟩ 1)
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hf.natReg 1280 (by omega) (by omega) (by omega)).trans h.header.base
  · exact (hf.natReg 1281 (by omega) (by omega) (by omega)).trans h.header.count
  · exact (hf.natReg 1282 (by omega) (by omega) (by omega)).trans h.header.diagonal
  · exact (hf.natReg 1283 (by omega) (by omega) (by omega)).trans h.header.offDiagonal
  · simp [iterationEnd,advanced,writeNat,next,h.index]
  · simp [iterationEnd,advanced,callState,leftState,offsetState,writeNat,next,h.one]
  · simp [iterationEnd,advanced,callState,leftState,offsetState,writeNat,next,h.two]
  · simpa [iterationEnd,advanced,kernelEnd,callState,leftState,offsetState,writeNat,next]
      using ((UniformPairMachine.final_frame {callState s with pc := 0} diagonalCoefficient offDiagonalCoefficient
        (v ⟨k,hk⟩ 0) (v ⟨k,hk⟩ 1)).2.2.2.2 0 (by omega)).trans h.diagonal
  · simpa [iterationEnd,advanced,kernelEnd,callState,leftState,offsetState,writeNat,next]
      using ((UniformPairMachine.final_frame {callState s with pc := 0} diagonalCoefficient offDiagonalCoefficient
        (v ⟨k,hk⟩ 0) (v ⟨k,hk⟩ 1)).2.2.2.2 1 (by omega)).trans h.offDiagonal
  · intro i t
    rw [iteration_heap,h.header.base,h.index,h.two,h.one]
    by_cases he:i.val=k
    · have hi:i=⟨k,hk⟩ := Fin.ext he
      subst i
      fin_cases t <;> simp [address,transformed,Nat.mul_comm]
    · have h0:address a i.val t ≠ a+k*2 := by unfold address;omega
      have h1:address a i.val t ≠ a+k*2+1 := by unfold address;omega
      rw [Function.update_of_ne h1,Function.update_of_ne h0,h.bank]
      congr 2;apply propext;omega
  · intro j hj
    rw [iteration_heap,h.header.base,h.index,h.two,h.one,
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact h.outside j hj

/-- The loop derives every Ready state from the remaining contiguous bank. -/
theorem iteration (n : ℕ) (x : Fin n → ℂ) {a m c d k B : ℕ} {v : Bank m}
    {origin s : State} (h:Cursor a m c d k v origin s) (hk:k < m)
    (hcap:a+2*m ≤ B) (hcode:23 ≤ B) (hpc:s.pc=5) (hs:WordBound B s) :
    ∃ u, BoundedRuns program n x B s 17 u  ∧
      Cursor a m c d (k+1) v origin u  ∧ u.pc=5 ∧ Frame s u  :=  by
  let u := v ⟨k,hk⟩ 0
  let w := v ⟨k,hk⟩ 1
  have he:WordBound B {s with pc := 6} := changePC_bound B s 6 hs (by omega)
  have h1:WordBound B (offsetState s) := writeNat_bound B {s with pc := 6} 1287 _ he
    (by change 7 ≤ B;omega) (by rw [h.index,h.two];omega)
  have h2:WordBound B (leftState s) := writeNat_bound B (offsetState s) 0 _ h1
    (by change 8 ≤ B;omega) (by rw [h.header.base,h.index,h.two];omega)
  have h3:WordBound B (callState s) := writeNat_bound B (leftState s) 1 _ h2
    (by change 9 ≤ B;omega) (by rw [h.header.base,h.index,h.two,h.one];omega)
  have localBound:WordBound B {callState s with pc := 0} := changePC_bound B _ 0 h3 (by omega)
  have ready:UniformPairMachine.Ready diagonalCoefficient offDiagonalCoefficient u w {callState s with pc := 0} := by
    refine ⟨rfl,?_,?_,?_,?_⟩
    · simpa [callState,leftState,offsetState,writeNat,next,h.header.base,h.index,h.two,
        address,Nat.mul_comm,u] using h.bank ⟨k,hk⟩ 0
    · simpa [callState,leftState,offsetState,writeNat,next,h.header.base,h.index,h.two,h.one,
        address,Nat.mul_comm,w] using h.bank ⟨k,hk⟩ 1
    · simpa [callState,leftState,offsetState,writeNat,next] using h.diagonal
    · simpa [callState,leftState,offsetState,writeNat,next] using h.offDiagonal
  have kr := UniformPairMachine.bounded_execution n x B _ diagonalCoefficient offDiagonalCoefficient u w ready (by omega) localBound
  have kp := UniformBoundedAssembly.boundedExecution_placed kernel_code (by simp [UniformPairMachine.program_length];omega)
    (by omega) kr
  have krun:BoundedRuns program n x B (callState s) 11 (kernelEnd s u w) := by
    simpa [placed,kernelEnd,callState,leftState,offsetState,writeNat,next] using kp
  have h4 := krun.final_bound
  have h5:WordBound B (advanced s u w) := writeNat_bound B _ 1284 _ h4
    (by change 21 ≤ B;omega) (by rw [h.index];omega)
  have h6:WordBound B (iterationEnd s u w) := changePC_bound B _ 5 h5 (by omega)
  have preRun:BoundedRuns program n x B s 4 (callState s) := by
    refine .next hs ?_ (.next he ?_ (.next h1 ?_ (.next h2 ?_ (.refl h3))))
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,hpc,h.index,h.header.count,hk]
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,offsetState,evalNat]
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,leftState,offsetState,writeNat,next,evalNat]
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,callState,leftState,offsetState,writeNat,next,evalNat]
  have suffix:BoundedRuns program n x B (kernelEnd s u w) 2 (iterationEnd s u w) := by
    refine .next h4 ?_ (.next h5 ?_ (.refl h6))
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,
        callState,leftState,offsetState,writeNat,next,advanced,h.one,evalNat]
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,
        advanced,writeNat,next,iterationEnd]
  refine ⟨iterationEnd s u w,?_,iteration_cursor h hk,rfl,iteration_frame s u w⟩
  convert (preRun.trans krun).trans suffix using 1

theorem loop (n : ℕ) (x : Fin n → ℂ) {a m c d k B fuel : ℕ} {v : Bank m}
    {origin s : State} (h:Cursor a m c d k v origin s) (hk:k+fuel=m)
    (hcap:a+2*m ≤ B) (hcode:23 ≤ B) (hpc:s.pc=5) (hs:WordBound B s) :
    ∃ u, BoundedRuns program n x B s (17*fuel) u  ∧ Cursor a m c d m v origin u  ∧
      u.pc=5 ∧ Frame s u  :=  by
  induction fuel generalizing k s with
  | zero  =>
    have he:k=m := by omega
    subst k
    exact ⟨s,.refl hs,h,hpc,Frame.refl s⟩
  | succ fuel ih  =>
    obtain ⟨u,hu,hcu,hpu,hfu⟩ := iteration n x h (by omega) hcap hcode hpc hs
    obtain ⟨w,hw,hcw,hpw,hfw⟩ := ih hcu (by omega) hpu hu.final_bound
    refine ⟨w,?_,hcw,hpw,hfu.trans hfw⟩
    convert hu.trans hw using 1;omega

def zeroState (s : State)  :=  writeNat s 1284 0
def oneState (s : State)  :=  writeNat (zeroState s) 1285 1
def twoState (s : State)  :=  writeNat (oneState s) 1286 2
def diagonalState (s : State)  :=  writeScalar (twoState s) 0 (UniformPairMachine.prepared diagonalCoefficient)
def initialized (s : State)  :=  writeScalar (diagonalState s) 1 (UniformPairMachine.prepared offDiagonalCoefficient)
theorem initialize_frame (s : State) : Frame s (initialized s)  :=  by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r h0 h1 hr
    simp [initialized,diagonalState,twoState,oneState,zeroState,writeNat,writeScalar,next,
      show r ≠ 1284 by omega,show r ≠ 1285 by omega,show r ≠ 1286 by omega]
  · intro r hr
    simp [initialized,diagonalState,twoState,oneState,zeroState,writeNat,writeScalar,next,
      show r ≠ 0 by omega,show r ≠ 1 by omega]
theorem initialize_cursor {a m c d : ℕ} {v : Bank m} {s : State}
    (hh:Header a m c d s) (hv:Source a m v s) : Cursor a m c d 0 v s (initialized s)  :=  by
  constructor
  · cases hh;constructor <;> simp_all [initialized,diagonalState,twoState,oneState,zeroState,writeNat,writeScalar,next]
  all_goals simp_all [initialized,diagonalState,twoState,oneState,zeroState,
    writeNat,writeScalar,next,Source,Outside]

/-- Universal continuous execution; pair flags are the actual conservative OR.
Coefficient cells outside the pair interval and every unpaired scalar are retained. -/
theorem execution (n : ℕ) (x : Fin n → ℂ) (a m c d B : ℕ) (v : Bank m) (s : State)
    (hh:Header a m c d s) (hv:Source a m v s) (hc:Constants c d s)
    (hcap:a+2*m ≤ B) (hcode:23 ≤ B) (hp:s.pc=0) (hs:WordBound B s) :
    ∃ u, BoundedExecution program n x B s (17*m+7) u  ∧ u.pc=22 ∧
      (∀ i t, u.scalarHeap (address a i.val t)=some (transformed (v i) t))  ∧
      Outside a m s u  ∧ Frame s u  :=  by
  have h0 := writeNat_bound B s 1284 0 hs (by omega) (by omega)
  have h1 := writeNat_bound B (zeroState s) 1285 1 h0
    (by change s.pc+1+1 ≤ B;omega) (by omega)
  have h2 := writeNat_bound B (oneState s) 1286 2 h1
    (by change s.pc+1+1+1 ≤ B;omega) (by omega)
  have h3 := writeScalar_bound B (twoState s) 0 (UniformPairMachine.prepared diagonalCoefficient) h2
    (by change s.pc+1+1+1+1 ≤ B;omega)
  have h4 := writeScalar_bound B (diagonalState s) 1 (UniformPairMachine.prepared offDiagonalCoefficient) h3
    (by change s.pc+1+1+1+1+1 ≤ B;omega)
  have start:BoundedRuns program n x B s 5 (initialized s) := by
    refine .next hs ?_ (.next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_ (.refl h4)))))
    all_goals simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,
      initialized,diagonalState,twoState,oneState,zeroState,writeNat,writeScalar,next,hp,
      hh.diagonal,hh.offDiagonal,hc.1,hc.2]
  obtain ⟨u,hu,hcu,hpu,hfu⟩ := loop n x (initialize_cursor hh hv) (by omega : 0+m=m)
    hcap hcode (by simp [initialized,diagonalState,twoState,oneState,zeroState,writeNat,writeScalar,next,hp]) h4
  let w:State := {u with pc := 22}
  have hw := changePC_bound B u 22 hu.final_bound (by omega)
  have finish:BoundedExecution program n x B u 2 w := by
    refine .next hu.final_bound ?_ (.halt hw ?_)
    · simp [step,program,embed,head,boot,tail,UniformPairMachine.program,relocate,hpu,
        hcu.index,hcu.header.count,w]
    · change step program n x {u with pc := 22}=.halted {u with pc := 22}
      rfl
  refine ⟨w,?_,rfl,?_,hcu.outside,by
    have hf := (initialize_frame s).trans hfu
    exact ⟨hf.natHeap,hf.outputs,hf.rootOrders,hf.natReg,hf.scalarReg⟩⟩
  · convert start.executes (hu.executes finish) using 1;omega
  · intro i t
    simpa [w,i.isLt] using hcu.bank i t

theorem transformed_value (v : Fin 2 → Scalar) (t : Fin 2) :
    (transformed v t).value=C.mulVec (fun j =>  (v j).value) t  :=  by
  fin_cases t <;> simp [transformed,UniformPairMachine.combine,C,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
theorem transformed_flag (v : Fin 2 → Scalar) (t : Fin 2) :
    (transformed v t).dependent=((v 0).dependent || (v 1).dependent)  :=  by
  fin_cases t <;> rfl
theorem runtime_linear (m : ℕ) : 17*m+7 ≤ 24*(m+1)  :=  by omega
theorem constants_retained {a m c d : ℕ} {s u : State} (ho:Outside a m s u)
    (hc:Constants c d s) (hcd:c<a  ∨ a+2*m ≤ c) (hdd:d<a  ∨ a+2*m ≤ d) :
    Constants c d u  :=  ⟨(ho c hcd).trans hc.1,(ho d hdd).trans hc.2⟩

theorem Frame.header {a m c d : ℕ} {s u : State}
    (hf : Frame s u) (hh : Header a m c d s) : Header a m c d u := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (hf.natReg 1280 (by omega) (by omega) (by omega)).trans hh.base
  · exact (hf.natReg 1281 (by omega) (by omega) (by omega)).trans hh.count
  · exact (hf.natReg 1282 (by omega) (by omega) (by omega)).trans hh.diagonal
  · exact (hf.natReg 1283 (by omega) (by omega) (by omega)).trans hh.offDiagonal

theorem Frame.saved_header {s u : State} (hf : Frame s u) (r : ℕ)
    (hr : 100 ≤ r ∧ r ≤ 106) : u.natReg r=s.natReg r :=
  hf.natReg r (by omega) (by omega) (by omega)

theorem master_retained {a m : ℕ} {s u : State} (ho : Outside a m s u)
    (ha : 0<a) : u.scalarHeap 0=s.scalarHeap 0 := ho 0 (Or.inl ha)

/-- Startup's actual heap1/heap2 values are sufficient; no register readiness
or uncharged coefficient preparation is needed by the round. -/
theorem startup_constants (n : ℕ) (s : State)
    (h : ∀j : Fin 6,s.scalarHeap j.val=
      some (UniformPairMachine.prepared (UniformCConstantsMachine.bank n j))) :
    Constants 1 2 s := by
  exact ⟨h 1,h 2⟩

structure Result (a m c d : ℕ) (v : Bank m) (origin u : State) : Prop where
  pc : u.pc=22
  header : Header a m c d u
  bank : Source a m (fun i=>transformed (v i)) u
  constants : Constants c d u
  outside : Outside a m origin u
  frame : Frame origin u

/-- The retained-bank interface uses ordinary coefficient/data interval
separation. The same ambient B bounds every actual instruction. -/
theorem execution_result (n : ℕ) (x : Fin n→ℂ) (a m c d B : ℕ) (v : Bank m) (s : State)
    (hh : Header a m c d s) (hv : Source a m v s) (hc : Constants c d s)
    (hcd : c<a ∨ a+2*m≤c) (hdd : d<a ∨ a+2*m≤d)
    (hcap : a+2*m≤B) (hcode : 23≤B) (hp : s.pc=0) (hs : WordBound B s) :
    ∃u,BoundedExecution program n x B s (17*m+7) u ∧ Result a m c d v s u := by
  obtain ⟨u,hu,hpc,hbank,ho,hf⟩ := execution n x a m c d B v s hh hv hc hcap hcode hp hs
  exact ⟨u,hu,⟨hpc,hf.header hh,hbank,constants_retained ho hc hcd hdd,ho,hf⟩⟩

theorem Result.C_values {a m c d : ℕ} {v : Bank m} {s u : State}
    (h : Result a m c d v s u) (i : Fin m) (t : Fin 2) :
    u.scalarHeap (address a i.val t)=
      some ⟨C.mulVec (fun j=>(v i j).value) t,
        (v i 0).dependent || (v i 1).dependent⟩ := by
  rw [h.bank i t]
  congr 1
  change transformed (v i) t =
    ⟨C.mulVec (fun j=>(v i j).value) t,(v i 0).dependent || (v i 1).dependent⟩
  have eta : transformed (v i) t =
      ⟨(transformed (v i) t).value,(transformed (v i) t).dependent⟩ := rfl
  rw [eta,transformed_value,transformed_flag]

def wordBudget (a m c d : ℕ) : ℕ := max (a+2*m) (max (max c d) 23)
theorem wordBudget_polynomial (a m c d : ℕ) :
    wordBudget a m c d ≤ 24*(a+2*m+c+d+1) := by
  unfold wordBudget
  omega
end
end ExactFourierCircuits.UniformPackedPairRoundMachine
