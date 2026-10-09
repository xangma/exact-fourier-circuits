import UniformTensorMonomialMachine
import UniformScalarCopyMachine
import UniformDirectMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformHeapDirectFourier
open UniformMachine UniformAssembly UniformPairMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section
open scoped BigOperators

/-- Heap-to-heap direct Fourier transform. The root is read from a prepared
bank; all data, coefficient, address and control operations are charged. -/
def boot : List Op := [.literal 4806 1,.literal 4804 0,
  .getScalar 90 4803,.literalScalar 91 1]
def enter : List Op := [.literal 4805 0,.literalScalar 92 1,.literalScalar 93 0]
def read : List Op := [.add 4807 4801 4805,.getScalar 94 4807,.scalarMul 95 92 94]
def advance : List Op := [.scalarMul 92 92 91,.add 4805 4805 4806]
def finish : List Op := [.add 4807 4802 4804,.putScalar 4807 93,
  .scalarMul 91 91 90,.add 4804 4804 4806]
def program : Program := boot.map Op.code ++ [.branchLT 4804 4800 5 21] ++
  enter.map Op.code ++ [.branchLT 4805 4800 9 16] ++ read.map Op.code ++
  [.fieldBinary .add 93 93 95] ++ advance.map Op.code ++ [.jump 8] ++
  finish.map Op.code ++ [.jump 4,.halt]
theorem program_length : program.length=22 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem enter_code : BlockAt enter program 5 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem read_code : BlockAt read program 9 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advance program 13 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem finish_code : BlockAt finish program 16 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem inner_branch : program[8]?=some (.branchLT 4805 4800 9 16) := rfl
theorem add_code : program[12]?=some (.fieldBinary .add 93 93 95) := rfl
theorem inner_jump : program[15]?=some (.jump 8) := rfl
theorem outer_branch : program[4]?=some (.branchLT 4804 4800 5 21) := rfl
theorem outer_jump : program[20]?=some (.jump 4) := rfl
theorem halt_code : program[21]?=some .halt := rfl

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ (∀r,r<4804 ∨ 4807<r→u.natReg r=s.natReg r) ∧
  ∀r,r<90 ∨ 95<r→u.scalarReg r=s.scalarReg r
theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

def Bank (r a : ℕ) (v : Fin r→Scalar) (s : State) : Prop :=
  ∀j,s.scalarHeap (a+j.val)=some (v j)
def partialSum {r : ℕ} (eta : ℂ) (v : Fin r→Scalar) (k j : ℕ) : ℂ :=
  ∑l∈Finset.range j,if h:l<r then eta^(k*l)*(v ⟨l,h⟩).value else 0
theorem partialSum_zero {r : ℕ} (eta : ℂ) (v : Fin r→Scalar) (k : ℕ) : partialSum eta v k 0=0 := by
  simp [partialSum]
theorem partialSum_succ {r : ℕ} (eta : ℂ) (v : Fin r→Scalar) (k j : ℕ) (hj:j<r) :
  partialSum eta v k (j+1)=partialSum eta v k j+eta^(k*j)*(v ⟨j,hj⟩).value := by
  simp [partialSum,Finset.sum_range_succ,hj]
theorem partialSum_full {r : ℕ} (eta : ℂ) (v : Fin r→Scalar) (k : ℕ) :
  partialSum eta v k r=∑j:Fin r,eta^(k*j.val)*(v j).value := by
  rw [partialSum,←Fin.sum_univ_eq_sum_range];simp

structure Context (r a d : ℕ) (eta : ℂ) (k : ℕ) (s : State) : Prop where
  width : s.natReg 4800=r
  source : s.natReg 4801=a
  destination : s.natReg 4802=d
  index : s.natReg 4804=k
  one : s.natReg 4806=1
  root : s.scalarReg 90=prepared eta
  row : s.scalarReg 91=prepared (eta^k)
structure Inner {r : ℕ} (a d : ℕ) (eta : ℂ) (v : Fin r→Scalar) (k j : ℕ) (s : State) : Prop where
  context : Context r a d eta k s
  pc : s.pc=8
  index : s.natReg 4805=j
  power : s.scalarReg 92=prepared (eta^(k*j))
  sum : (s.scalarReg 93).value=partialSum eta v k j
  source : Bank r a v s

def reading (s : State) : State := applyBlock read {s with pc:=9}
def adding (s : State) : State :=
  writeScalar (reading s) 93 ⟨((reading s).scalarReg 93).value+((reading s).scalarReg 95).value,
    ((reading s).scalarReg 93).dependent || ((reading s).scalarReg 95).dependent⟩
def innerNext (s : State) : State := {applyBlock advance (adding s) with pc:=8}
theorem innerNext_frame (s : State) : Frame s (innerNext s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp (disch:=omega) [innerNext,advance,adding,reading,read,applyBlock,Op.apply,writeNat,writeScalar,next]
  · intro r hr
    simp (disch:=omega) [innerNext,advance,adding,reading,read,applyBlock,Op.apply,writeNat,writeScalar,next]

theorem read_values {r : ℕ} {a d k j : ℕ} {eta : ℂ} {v : Fin r→Scalar} {s : State}
    (hi:Inner a d eta v k j s) (hj:j<r) :
    (reading s).scalarReg 95=product (eta^(k*j)) (v ⟨j,hj⟩) ∧
    (reading s).scalarReg 93=s.scalarReg 93 ∧
    (reading s).scalarReg 92=s.scalarReg 92 ∧
    (reading s).scalarReg 91=s.scalarReg 91 := by
  simp [reading,applyBlock,read,Op.apply,writeNat,writeScalar,next,
    hi.context.source,hi.index,hi.power,hi.source ⟨j,hj⟩,prepared_mul]

theorem innerNext_invariant {r : ℕ} {a d k j : ℕ} {eta : ℂ} {v : Fin r→Scalar} {s : State}
    (hi:Inner a d eta v k j s) (hj:j<r) : Inner a d eta v k (j+1) (innerNext s) := by
  obtain ⟨ht,ha,hp,hw⟩:=read_values hi hj
  have hc:=hi.context
  constructor
  · constructor <;> simp [innerNext,advance,adding,reading,read,applyBlock,Op.apply,
      writeNat,writeScalar,next,hc.width,hc.source,hc.destination,hc.index,hc.one,hc.root,hc.row]
  · rfl
  · simp [innerNext,advance,adding,reading,read,applyBlock,Op.apply,writeNat,writeScalar,next,hi.index,hc.one]
  · simp only [innerNext,applyBlock,advance,Op.apply,writeNat,writeScalar,next,
      Function.update_self]
    simp [adding,writeScalar,next,hp,hw,hi.power,hc.row,evalField,prepared]
    rw [←pow_add,Nat.mul_add,Nat.mul_one]
  · simp only [innerNext,advance,applyBlock,Op.apply,writeNat,writeScalar,next,
      Function.update_of_ne (by decide : (93:ℕ)≠92),adding,Function.update_self]
    rw [ha,ht,hi.sum,partialSum_succ eta v k j hj];rfl
  · exact hi.source

theorem inner_round {n r : ℕ} (x : Fin n→ℂ) {a d k j B : ℕ} {eta : ℂ}
    {v : Fin r→Scalar} {s : State} (hi:Inner a d eta v k j s) (hj:j<r)
    (hB:22≤B) (ha:a+r≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 8 (innerNext s) := by
  let e:State:={s with pc:=9}
  have he:WordBound B e:=changePC_bound B s 9 hs (by omega)
  have branch:BoundedRuns program n x B s 1 e := .next hs
    (by simp [step,inner_branch,hi.pc,hi.index,hi.context.width,hj,e]) (.refl he)
  have load:=block_runs read program 9 n B x e read_code rfl he (by change 9+3≤B;omega)
    (by simp [readable,read,Op.readable,Op.apply,writeNat,writeScalar,next,e,
      hi.context.source,hi.index,hi.source ⟨j,hj⟩,hi.power,evalField,prepared])
    (by simp [peak,read,Op.peak,e,
      hi.context.source,hi.index];omega)
  change BoundedRuns program n x B e 3 (reading s) at load
  have hrpc:(reading s).pc=12 := by
    rw [reading,UniformTensorMonomialMachine.applyBlock_pc];rfl
  have addBound:WordBound B (adding s):=writeScalar_bound B (reading s) 93 _ load.final_bound (by omega)
  have addRun:BoundedRuns program n x B (reading s) 1 (adding s):=.next load.final_bound
    (by simp [step,add_code,hrpc,adding,evalField]) (.refl addBound)
  obtain ⟨_,_,hp,hw⟩:=read_values hi hj
  have hac:(adding s).pc=13 := by simp [adding,writeScalar,next,hrpc]
  have h92:(adding s).scalarReg 92=prepared (eta^(k*j)) := by
    simp [adding,writeScalar,next,hp,hi.power]
  have h91:(adding s).scalarReg 91=prepared (eta^k) := by
    simp [adding,writeScalar,next,hw,hi.context.row]
  have hindex:(adding s).natReg 4805=j := by
    simp [adding,reading,read,applyBlock,Op.apply,writeNat,writeScalar,next,hi.index]
  have hone:(adding s).natReg 4806=1 := by
    simp [adding,reading,read,applyBlock,Op.apply,writeNat,writeScalar,next,hi.context.one]
  have advancing:=block_runs advance program 13 n B x (adding s) advance_code hac addBound
    (by change 13+2≤B;omega)
    (by simp [readable,advance,Op.readable,h92,h91,evalField,prepared])
    (by simp [peak,advance,Op.peak,Op.apply,writeScalar,next,hindex,hone];
        have hr:r≤B := (Nat.le_add_left r a).trans ha;omega)
  have hpc:(applyBlock advance (adding s)).pc=15 := by
    rw [UniformTensorMonomialMachine.applyBlock_pc,hac];rfl
  have finalBound:WordBound B (innerNext s):=
    changePC_bound B _ 8 advancing.final_bound (by omega)
  have back:BoundedRuns program n x B (applyBlock advance (adding s)) 1 (innerNext s):=
    .next advancing.final_bound (by simp [step,inner_jump,hpc,innerNext]) (.refl finalBound)
  convert ((branch.trans load).trans addRun).trans (advancing.trans back) using 1
  rfl

theorem inner_loop {n r : ℕ} (x : Fin n→ℂ) {a d k j B : ℕ} {eta : ℂ}
    {v : Fin r→Scalar} {s : State} (f : ℕ) (hi:Inner a d eta v k j s) (hj:j+f=r)
    (hB:22≤B) (ha:a+r≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (8*f) u ∧ Inner a d eta v k r u ∧
    u.scalarHeap=s.scalarHeap ∧ Frame s u := by
  induction f generalizing j s with
  | zero=>
    have he:j=r:=by omega
    subst j
    exact ⟨s,.refl hs,hi,rfl,.refl s⟩
  | succ f ih=>
    have hjr:j<r:=by omega
    have run:=inner_round x hi hjr hB ha hs
    obtain ⟨u,hu,hiu,hheap,hframe⟩:=ih (s:=innerNext s) (j:=j+1)
      (innerNext_invariant hi hjr) (by omega) run.final_bound
    refine ⟨u,?_,hiu,hheap,(innerNext_frame s).trans hframe⟩
    convert run.trans hu using 1
    omega

def entering (s : State) : State := applyBlock enter {s with pc:=5}
structure Outer {r : ℕ} (a d : ℕ) (eta : ℂ) (v : Fin r→Scalar) (k : ℕ) (s : State) : Prop where
  context : Context r a d eta k s
  pc : s.pc=4
  source : Bank r a v s
  values : ∀l:Fin r,l.val<k→∃w,s.scalarHeap (d+l.val)=some w ∧
    w.value=partialSum eta v l.val r
theorem entering_invariant {r a d k : ℕ} {eta : ℂ} {v : Fin r→Scalar} {s : State}
    (hi:Outer a d eta v k s) : Inner a d eta v k 0 (entering s) := by
  have hc:=hi.context
  constructor
  · constructor <;> simp [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next,
      hc.width,hc.source,hc.destination,hc.index,hc.one,hc.root,hc.row]
  · rfl
  · simp [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next]
  · simp [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next,prepared]
  · simp [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next,partialSum_zero]
  · exact hi.source
theorem entering_frame (s : State) : Frame s (entering s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp (disch:=omega) [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next]
  · intro r hr
    simp (disch:=omega) [entering,enter,applyBlock,Op.apply,writeNat,writeScalar,next]

theorem enter_row {n r : ℕ} (x : Fin n→ℂ) {a d k B : ℕ} {eta : ℂ} {v : Fin r→Scalar}
    {s : State} (hi:Outer a d eta v k s) (hk:k<r) (hB:22≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 4 (entering s) := by
  let e:State:={s with pc:=5}
  have he:=changePC_bound B s 5 hs (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [step,outer_branch,hi.pc,hi.context.index,hi.context.width,hk,e]) (.refl he)
  have enterRun:=block_runs enter program 5 n B x e enter_code rfl he
    (by change 5+3≤B;omega) (by simp [readable,enter,Op.readable]) (by simp [peak,enter,Op.peak])
  exact branch.trans enterRun

def outerNext (s : State) : State := {applyBlock finish {s with pc:=16} with pc:=4}
theorem outerNext_heap {r a d k : ℕ} {eta : ℂ} {s : State} (hc:Context r a d eta k s) :
  (outerNext s).scalarHeap=Function.update s.scalarHeap (d+k) (some (s.scalarReg 93)) := by
  simp [outerNext,finish,applyBlock,Op.apply,writeNat,writeScalar,next,hc.destination,hc.index]
theorem outerNext_frame (s : State) : Frame s (outerNext s) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro r hr
    simp (disch:=omega) [outerNext,finish,applyBlock,Op.apply,writeNat,writeScalar,next]
  · intro r hr
    simp (disch:=omega) [outerNext,finish,applyBlock,Op.apply,writeNat,writeScalar,next]

theorem outerNext_context {r a d k : ℕ} {eta : ℂ} {s : State} (hc:Context r a d eta k s) :
    Context r a d eta (k+1) (outerNext s) := by
  constructor <;> simp [outerNext,finish,applyBlock,Op.apply,writeNat,writeScalar,next,
    hc.width,hc.source,hc.destination,hc.index,hc.one,hc.root,hc.row,prepared,evalField]
  exact (pow_succ eta k).symm

theorem exit_row {n r : ℕ} (x : Fin n→ℂ) {a d k B : ℕ} {eta : ℂ} {v : Fin r→Scalar}
    {s : State} (hi:Inner a d eta v k r s) (hk:k<r)
    (hB:22≤B) (hd:d+r≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 6 (outerNext s) := by
  let e:State:={s with pc:=16}
  have he:=changePC_bound B s 16 hs (by omega)
  have branch:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [step,inner_branch,hi.pc,hi.index,hi.context.width,e]) (.refl he)
  have body:=block_runs finish program 16 n B x e finish_code rfl he
    (by change 16+4≤B;omega)
    (by simp [readable,finish,Op.readable,Op.apply,writeNat,next,e,
      hi.context.root,hi.context.row,evalField,prepared])
    (by simp [peak,finish,Op.peak,Op.apply,writeNat,writeScalar,next,e,
      hi.context.destination,hi.context.index,hi.context.one];
        have hr:r≤B:=(Nat.le_add_left r d).trans hd;omega)
  have hpc:(applyBlock finish e).pc=20:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have finalBound:WordBound B (outerNext s):=changePC_bound B _ 4 body.final_bound (by omega)
  have back:BoundedRuns program n x B (applyBlock finish e) 1 (outerNext s):=.next body.final_bound
    (by simp [step,outer_jump,hpc,outerNext,e]) (.refl finalBound)
  convert branch.trans (body.trans back) using 1
  rfl

def Outside (d r : ℕ) (s u : State) : Prop :=
  ∀a,a<d ∨ d+r≤a→u.scalarHeap a=s.scalarHeap a
theorem Outside.refl (d r : ℕ) (s : State) : Outside d r s s := fun _ _=>rfl
theorem Outside.trans {d r : ℕ} {s u v : State} (h:Outside d r s u) (h':Outside d r u v) :
    Outside d r s v := fun a ha=>(h' a ha).trans (h a ha)
theorem outerNext_outside {r a d k : ℕ} {eta : ℂ} {s : State} (hc:Context r a d eta k s)
    (hk:k<r) : Outside d r s (outerNext s) := by
  intro i hi
  rw [outerNext_heap hc]
  exact Function.update_of_ne (by omega) _ _

theorem outerNext_invariant {r a d k : ℕ} {eta : ℂ} {v : Fin r→Scalar} {s : State}
    (hi:Inner a d eta v k r s) (hk:k<r) (hsep:a+r≤d ∨ d+r≤a)
    (hold:∀l:Fin r,l.val<k→∃w,s.scalarHeap (d+l.val)=some w ∧ w.value=partialSum eta v l.val r) :
    Outer a d eta v (k+1) (outerNext s) := by
  refine ⟨outerNext_context hi.context,rfl,?_,?_⟩
  · intro j
    rw [outerNext_heap hi.context,Function.update_of_ne (by have h:=j.isLt;omega)]
    exact hi.source j
  · intro l hl
    by_cases he:l.val=k
    · refine ⟨s.scalarReg 93,?_,?_⟩
      · rw [outerNext_heap hi.context,he,Function.update_self]
      · simpa [he] using hi.sum
    · obtain ⟨w,hw,hval⟩:=hold l (by omega)
      refine ⟨w,?_,hval⟩
      rw [outerNext_heap hi.context,Function.update_of_ne (by omega)]
      exact hw

theorem outer_loop {n r : ℕ} (x : Fin n→ℂ) {a d k B : ℕ} {eta : ℂ}
    {v : Fin r→Scalar} {s : State} (f : ℕ) (hi:Outer a d eta v k s) (hk:k+f=r)
    (hB:22≤B) (ha:a+r≤B) (hd:d+r≤B) (hsep:a+r≤d ∨ d+r≤a) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s ((8*r+10)*f) u ∧ Outer a d eta v r u ∧
    Frame s u ∧ Outside d r s u := by
  induction f generalizing k s with
  | zero=>
    have he:k=r:=by omega
    subst k
    exact ⟨s,.refl hs,hi,.refl s,.refl d r s⟩
  | succ f ih=>
    have hkr:k<r:=by omega
    have enterRun:=enter_row x hi hkr hB hs
    obtain ⟨vstate,vr,vi,vheap,vframe⟩:=inner_loop x r (entering_invariant hi) (by omega) hB ha enterRun.final_bound
    have exitRun:=exit_row x vi hkr hB hd vr.final_bound
    have vprior:∀l:Fin r,l.val<k→∃w,vstate.scalarHeap (d+l.val)=some w ∧ w.value=partialSum eta v l.val r := by
      intro l hl
      rw [vheap]
      exact hi.values l hl
    have nextI:=outerNext_invariant vi hkr hsep vprior
    obtain ⟨u,hu,ui,uf,uo⟩:=ih (s:=outerNext vstate) (k:=k+1) nextI (by omega) exitRun.final_bound
    refine ⟨u,?_,ui,((entering_frame s).trans vframe).trans ((outerNext_frame vstate).trans uf),?_⟩
    · convert ((enterRun.trans vr).trans exitRun).trans hu using 1
      ring
    · have hop:Outside d r s vstate := by intro i _;exact congrFun vheap i
      exact (hop.trans (outerNext_outside vi.context hkr)).trans uo

theorem execution {n r : ℕ} (x : Fin n→ℂ) (a d rootAddress B : ℕ) (eta : ℂ)
    (v : Fin r→Scalar) (s : State) (hp:s.pc=0)
    (h0:s.natReg 4800=r) (h1:s.natReg 4801=a) (h2:s.natReg 4802=d)
    (h3:s.natReg 4803=rootAddress) (hroot:s.scalarHeap rootAddress=some (prepared eta))
    (hsource:Bank r a v s) (hsep:a+r≤d ∨ d+r≤a)
    (hB:22≤B) (ha:a+r≤B) (hd:d+r≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s ((8*r+10)*r+6) u ∧
    (∀k:Fin r,∃w,u.scalarHeap (d+k.val)=some w ∧ w.value=∑j:Fin r,eta^(k.val*j.val)*(v j).value) ∧
    Bank r a v u ∧ Frame s u ∧ Outside d r s u ∧ u.pc=21 := by
  have start:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+4≤B;omega)
    (by simp [readable,boot,Op.readable,Op.apply,writeNat,next,h3,hroot])
    (by simp [peak,boot,Op.peak];omega)
  let e:=applyBlock boot s
  have initialI:Outer a d eta v 0 e:=by
    refine ⟨?_,?_,hsource,fun l hl=>by omega⟩
    · constructor <;> simp [e,boot,applyBlock,Op.apply,writeNat,writeScalar,next,
        h0,h1,h2,h3,hroot,prepared]
    · rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  obtain ⟨vstate,run,vi,vframe,voutside⟩:=outer_loop x r initialI (by omega) hB ha hd hsep start.final_bound
  let u:State:={vstate with pc:=21}
  have ub:=changePC_bound B vstate 21 run.final_bound (by omega)
  have stop:BoundedExecution program n x B vstate 2 u:=.next run.final_bound
    (by simp [step,outer_branch,vi.pc,vi.context.index,vi.context.width,u])
    (.halt ub (by simp [step,halt_code,u]))
  have bootFrame:Frame s e:=by
    refine ⟨rfl,rfl,rfl,?_,?_⟩
    · intro i hi
      simp (disch:=omega) [e,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
    · intro i hi
      simp (disch:=omega) [e,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
  refine ⟨u,?_,?_,vi.source,bootFrame.trans vframe,voutside,rfl⟩
  · convert start.executes (run.executes stop) using 1
    change (8*r+10)*r+6=4+((8*r+10)*r+2)
    ring
  · intro k
    obtain ⟨w,hw,hval⟩:=vi.values k k.isLt
    exact ⟨w,hw,hval.trans (partialSum_full eta v k.val)⟩

theorem runtime_quadratic (r : ℕ) : (8*r+10)*r+6≤24*(r+1)^2 := by nlinarith

theorem sum_standardFourier {r : ℕ} (v : Fin r→Scalar) (k : Fin r) :
    (∑j:Fin r,OAI.ExactFourier.zeta r^(k.val*j.val)*(v j).value)=
      (OAI.ExactFourier.fourierMatrix r).mulVec (fun j=>(v j).value) k := by
  simp [OAI.ExactFourier.fourierMatrix,Matrix.mulVec,dotProduct]

end
end ExactFourierCircuits.UniformHeapDirectFourier
