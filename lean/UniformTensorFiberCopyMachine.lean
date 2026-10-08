import UniformTensorMonomialMachine
import UniformTensorAddressMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformTensorFiberCopyMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
/-- Headers1900..1904: length, source, destination, source/destination strides.
Only Nat1905..1908 and Scalar100 change. Every access/control step is charged. -/
def boot : List Op := [.literal 1905 0,.literal 1906 1]
def body : List Op := [.mul 1907 1905 1903,.add 1907 1901 1907,.getScalar 100 1907,
 .mul 1908 1905 1904,.add 1908 1902 1908,.putScalar 1908 100,.add 1905 1905 1906]
def program : Program := boot.map Op.code++[.branchLT 1905 1900 3 11]++body.map Op.code++[.jump 2,.halt]
theorem program_length : program.length=12 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
theorem body_code : BlockAt body program 3 := by intro i hi;change i < 7 at hi;interval_cases i <;> rfl
theorem branch_at : program[2]?=some (.branchLT 1905 1900 3 11) := rfl
theorem jump_at : program[10]?=some (.jump 2) := rfl
theorem halt_at : program[11]?=some .halt := rfl
noncomputable section
structure Header (m a d p q : ℕ) (s : State) : Prop where
 length : s.natReg 1900=m
 source : s.natReg 1901=a
 destination : s.natReg 1902=d
 sourceStride : s.natReg 1903=p
 destinationStride : s.natReg 1904=q

def Source (m a p : ℕ) (heap : ℕ → Option Scalar) : Prop := ∀ j, j < m → ∃v,heap (a+j*p)=some v
def Outside (d q m : ℕ) (heap : ℕ → Option Scalar) (s : State) : Prop :=
 ∀ z, (∀ j, j < m → z ≠ d+j*q) → s.scalarHeap z=heap z
structure Frame (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀ i, (i < 1905 ∨ 1909 ≤ i) → u.natReg i=s.natReg i
 scalarReg : ∀ i, i ≠ 100 → u.scalarReg i=s.scalarReg i

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (h:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.natHeap.trans h.natHeap,g.outputs.trans h.outputs,g.roots.trans h.roots,
 fun i hi=>(g.natReg i hi).trans (h.natReg i hi),fun i hi=>(g.scalarReg i hi).trans (h.scalarReg i hi)⟩
theorem Header.withPC {m a d p q pc:ℕ} {s:State} (h:Header m a d p q s) : Header m a d p q {s with pc:=pc} :=
 ⟨h.length,h.source,h.destination,h.sourceStride,h.destinationStride⟩
theorem Header.frame {m a d p q:ℕ} {s u:State} (h:Header m a d p q s) (f:Frame s u) : Header m a d p q u :=
 ⟨(f.natReg _ (by omega)).trans h.length,(f.natReg _ (by omega)).trans h.source,
 (f.natReg _ (by omega)).trans h.destination,(f.natReg _ (by omega)).trans h.sourceStride,
 (f.natReg _ (by omega)).trans h.destinationStride⟩
structure Cursor (m a d p q k : ℕ) (heap : ℕ → Option Scalar) (s : State) : Prop where
 header : Header m a d p q s
 index : s.natReg 1905=k
 one : s.natReg 1906=1
 copied : ∀ j, j < k → s.scalarHeap (d+j*q)=heap (a+j*p)
 outside : Outside d q m heap s

def iterationEnd (s:State) := {applyBlock body {s with pc:=3} with pc:=2}
theorem iteration_heap {m a d p q k:ℕ} {s:State} (h:Header m a d p q s) (hi:s.natReg 1905=k) :
 (iterationEnd s).scalarHeap=Function.update s.scalarHeap (d+k*q)
   (some ((s.scalarHeap (a+k*p)).getD Scalar.zero)) := by
 simp [iterationEnd,applyBlock,body,Op.apply,writeNat,writeScalar,next,h.source,h.destination,
   h.sourceStride,h.destinationStride,hi]
theorem iteration_frame (s:State) : Frame s (iterationEnd s) := by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · intro i hi
   simp (disch:=omega) [iterationEnd,applyBlock,body,Op.apply,writeNat,writeScalar,next]
 · intro i hi
   simp [iterationEnd,applyBlock,body,Op.apply,writeNat,writeScalar,next,hi]

theorem iteration_cursor {m a d p q k:ℕ} {heap:ℕ → Option Scalar} {s:State}
 (h:Cursor m a d p q k heap s) (hk:k < m) (hq:0 < q)
 (hv:∃v,heap (a+k*p)=some v) (separate:∀ i, i < m → ∀ j, j < m → a+i*p ≠ d+j*q) :
 Cursor m a d p q (k+1) heap (iterationEnd s) := by
 obtain ⟨v,hv⟩:=hv
 have load:s.scalarHeap (a+k*p)=some v := (h.outside _ (separate k hk)).trans hv
 refine ⟨h.header.frame (iteration_frame s),?_,?_,?_,?_⟩
 · simp [iterationEnd,applyBlock,body,Op.apply,writeNat,writeScalar,next,h.index,h.one]
 · simp [iterationEnd,applyBlock,body,Op.apply,writeNat,writeScalar,next,h.one]
 · intro j hj
   rw [iteration_heap h.header h.index,load]
   by_cases he:j=k
   · subst j;simp [hv]
   · rw [Function.update_of_ne (by intro hh;have :=Nat.eq_of_mul_eq_mul_right hq (Nat.add_left_cancel hh);omega)]
     exact h.copied j (by omega)
 · intro z hz
   rw [iteration_heap h.header h.index,Function.update_of_ne (hz k hk)]
   exact h.outside z hz

theorem iteration (n B m a d p q k:ℕ) (x:Fin n → ℂ) (heap:ℕ → Option Scalar) (s:State)
 (h:Cursor m a d p q k heap s) (hk:k < m) (hq:0 < q) (src:Source m a p heap)
 (separate:∀ i, i < m → ∀ j, j < m → a+i*p ≠ d+j*q)
 (ha:a+m*p ≤ B) (hd:d+m*q ≤ B) (hc:12 ≤ B) (hp:s.pc=2) (hs:WordBound B s) :
 ∃u,BoundedRuns program n x B s 9 u ∧ Cursor m a d p q (k+1) heap u ∧ u.pc=2 ∧ Frame s u := by
 obtain ⟨v,hv⟩:=src k hk
 have load:s.scalarHeap (a+k*p)=some v := (h.outside _ (separate k hk)).trans hv
 have kp:k*p ≤ m*p:=Nat.mul_le_mul_right p (by omega)
 have kq:k*q ≤ m*q:=Nat.mul_le_mul_right q (by omega)
 have mb:m ≤ B:=by have hm:=Nat.mul_le_mul_left m (show 1 ≤ q by omega);nlinarith
 let t:State:={s with pc:=3}
 have ht:WordBound B t:=changePC_bound B s 3 hs (by omega)
 have enter:BoundedRuns program n x B s 1 t:=.next hs
   (by simp [step,hp,branch_at,h.index,h.header.length,hk,t]) (.refl ht)
 have b:=block_runs body program 3 n B x t body_code rfl ht (by change 3+7 ≤ B;omega)
   (by simp [readable,body,Op.readable,Op.apply,t,writeNat,next,h.index,h.header.sourceStride,h.header.source,load])
   (by simp [peak,body,Op.peak,Op.apply,t,writeNat,writeScalar,next,h.index,h.one,
      h.header.source,h.header.destination,h.header.sourceStride,h.header.destinationStride];omega)
 have bp:(applyBlock body t).pc=10:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have jump:BoundedRuns program n x B (applyBlock body t) 1 (iterationEnd s):=.next b.final_bound
   (by simp [step,bp,jump_at,iterationEnd,t])
   (.refl (changePC_bound B _ 2 b.final_bound (by omega)))
 exact ⟨iterationEnd s,by convert enter.trans (b.trans jump) using 1; rfl,
   iteration_cursor h hk hq ⟨v,hv⟩ separate,rfl,iteration_frame s⟩

theorem loop (n B m a d p q k fuel:ℕ) (x:Fin n → ℂ) (heap:ℕ → Option Scalar) (s:State)
 (h:Cursor m a d p q k heap s) (count:k+fuel=m) (hq:0 < q) (src:Source m a p heap)
 (separate:∀ i, i < m → ∀ j, j < m → a+i*p ≠ d+j*q)
 (ha:a+m*p ≤ B) (hd:d+m*q ≤ B) (hc:12 ≤ B) (hp:s.pc=2) (hs:WordBound B s) :
 ∃u,BoundedRuns program n x B s (9*fuel) u ∧ Cursor m a d p q m heap u ∧ u.pc=2 ∧ Frame s u := by
 induction fuel generalizing k s with
 | zero =>
   have he:k=m:=by omega
   subst k
   exact ⟨s,.refl hs,h,hp,Frame.refl s⟩
 | succ fuel ih =>
   obtain ⟨u,run,cu,pc,fr⟩:=iteration n B m a d p q k x heap s h (by omega) hq src separate ha hd hc hp hs
   obtain ⟨v,rest,cv,pv,fv⟩:=ih (k+1) u cu (by omega) pc run.final_bound
   exact ⟨v,by convert run.trans rest using 1;omega,cv,pv,fr.trans fv⟩

theorem boot_frame (s:State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro i hi
 simp (disch:=omega) [applyBlock,boot,Op.apply,writeNat,next]
/-- Whole fixed bytecode copies full Scalar values/flags without field arithmetic. -/
theorem execution (n B m a d p q:ℕ) (x:Fin n → ℂ) (s:State)
 (header:Header m a d p q s) (hq:0 < q) (src:Source m a p s.scalarHeap)
 (separate:∀ i, i < m → ∀ j, j < m → a+i*p ≠ d+j*q)
 (ha:a+m*p ≤ B) (hd:d+m*q ≤ B) (hc:12 ≤ B) (hp:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (9*m+4) u ∧ u.pc=11 ∧
 (∀ j, j < m → u.scalarHeap (d+j*q)=s.scalarHeap (a+j*p)) ∧ Outside d q m s.scalarHeap u ∧ Frame s u := by
 have start:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+2 ≤ B;omega)
   (by simp [readable,boot,Op.readable]) (by simp [peak,boot,Op.peak];omega)
 have init:Cursor m a d p q 0 s.scalarHeap (applyBlock boot s):=by
   refine ⟨header.frame (boot_frame s),?_,?_,?_,?_⟩
   · simp [applyBlock,boot,Op.apply,writeNat,next]
   · simp [applyBlock,boot,Op.apply,writeNat,next]
   · intro j hj;omega
   · intro z _;rfl
 have pc:(applyBlock boot s).pc=2:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 obtain ⟨u,run,cu,pcu,fr⟩:=loop n B m a d p q 0 m x s.scalarHeap (applyBlock boot s)
   init (by omega) hq src separate ha hd hc pc start.final_bound
 let v:State:={u with pc:=11}
 have vb:=changePC_bound B u 11 run.final_bound (by omega)
 have stop:BoundedExecution program n x B u 2 v:=.next run.final_bound
   (by simp [step,pcu,branch_at,cu.index,cu.header.length,v])
   (.halt vb (by simp [step,v,halt_at]))
 have fv:Frame u v:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 exact ⟨v,by convert start.executes (run.executes stop) using 1;simp [boot];omega,rfl,cu.copied,cu.outside,(boot_frame s).trans (fr.trans fv)⟩
theorem runtime_linear (r:ℕ) : 9*r+4 ≤ 13*(r+1) := by omega
end
end ExactFourierCircuits.UniformTensorFiberCopyMachine
