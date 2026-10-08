import UniformHadamardPairMachine
import UniformBoundedAssembly
import UniformLocalShear
import UniformReciprocalMachine
import UniformInitialPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformZeroFreePairShearMachine
open UniformMachine UniformAssembly UniformPairMachine
open UniformHadamardPairMachine
open UniformReciprocalMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- Same literal40 and state semantics, with tight relocated PC bounds. -/
theorem hadamard_bounded (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (u v : Scalar) (hp : s.pc=0) (hc : Constants s) (hs : WordBound B s) (hB : 40≤B)
    (h0 : 6 ≤ s.natReg 0) (h1 : 6 ≤ s.natReg 1) (hne : s.natReg 0≠s.natReg 1)
    (hu : s.scalarHeap (s.natReg 0)=some u) (hv : s.scalarHeap (s.natReg 1)=some v) :
    ∃ t, BoundedExecution UniformHadamardPairMachine.program n x B s 40 t ∧ Protected s t ∧ Constants t ∧
      t.scalarHeap (s.natReg 0)=some ⟨u.value+v.value,u.dependent || v.dependent⟩ ∧
      t.scalarHeap (s.natReg 1)=some ⟨u.value-v.value,u.dependent || v.dependent⟩ ∧ t.pc=39 := by
  let s1:=rightState s
  have ex1:=right_execution n x B s hp hc.2.2.2.1 (by omega) hs
  have f1 : Protected s s1:=protected_right s
  let t1:=reset s1
  have hb1 : WordBound B t1:=changePC_bound B s1 0 ex1.final_bound (by omega)
  have hn1 : t1.natReg 0≠t1.natReg 1 := by
    simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hne
  have hr1 : Ready 1 Complex.I u v t1 := by
    constructor
    · rfl
    · simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hu
    · simpa [t1,s1,reset,rightState,writeScalar,writeNat,next] using hv
    · simp [t1,s1,reset,rightState,writeScalar,writeNat,next]
    · simp [t1,s1,reset,rightState,writeScalar,writeNat,next]
  let s2:=UniformPairDiagonalMachine.finalState t1 1 Complex.I u v
  have ex2:=UniformPairDiagonalMachine.bounded_execution n x B t1 1 Complex.I u v hr1 (by omega) hb1
  have f2 : Protected s s2:=(f1.trans (protected_reset s1)).trans (protected_diagonal _ _ _ _ _)
  have c2:=hc.protected f2 h0 h1
  have hv2 : s2.scalarHeap (s.natReg 0)=some (product 1 u) ∧
      s2.scalarHeap (s.natReg 1)=some (product Complex.I v) := by
    simpa [s2,t1,s1,reset,rightState,writeScalar,writeNat,next] using
      UniformPairDiagonalMachine.final_values t1 1 Complex.I u v hn1
  let t2:=reset s2
  let s3:=loadState t2 1 2 a b
  have hb2 : WordBound B t2:=changePC_bound B s2 0 ex2.final_bound (by omega)
  have ex3:=load_execution n x B t2 1 2 a b rfl c2.1 c2.2.1 (by omega) (by omega) (by omega) hb2
  have f3 : Protected s s3:=(f2.trans (protected_reset s2)).trans (protected_load _ _ _ _ _)
  let t3:=reset s3
  have hb3 : WordBound B t3:=changePC_bound B s3 0 ex3.final_bound (by omega)
  have hn3 : t3.natReg 0≠t3.natReg 1 := by
    simpa [t3,reset,f3.1 0 (by decide),f3.1 1 (by decide)] using hne
  have hr3 : Ready a b (product 1 u) (product Complex.I v) t3 := by
    constructor
    · rfl
    · simpa [t3,s3,t2,reset,loadState,writeScalar,writeNat,next,f2.1 0 (by decide)] using hv2.1
    · simpa [t3,s3,t2,reset,loadState,writeScalar,writeNat,next,f2.1 1 (by decide)] using hv2.2
    · simp [t3,s3,reset,loadState,writeScalar,writeNat,next]
    · simp [t3,s3,reset,loadState,writeScalar,writeNat,next]
  let U:=combine a b (product 1 u) (product Complex.I v)
  let V:=combine b a (product 1 u) (product Complex.I v)
  let s4:=UniformPairMachine.finalState t3 a b (product 1 u) (product Complex.I v)
  have ex4:=UniformPairMachine.bounded_execution n x B t3 a b
    (product 1 u) (product Complex.I v) hr3 (by omega) hb3
  have f4 : Protected s s4:=(f3.trans (protected_reset s3)).trans (protected_C _ _ _ _ _)
  have c4:=hc.protected f4 h0 h1
  have hv4 : s4.scalarHeap (s.natReg 0)=some U ∧ s4.scalarHeap (s.natReg 1)=some V := by
    simpa [s4,U,V,t3,reset,f3.1 0 (by decide),f3.1 1 (by decide)] using
      UniformPairMachine.final_values t3 a b (product 1 u) (product Complex.I v) hn3
  let t4:=reset s4
  let s5:=loadState t4 3 5 a⁻¹ (Complex.I*a⁻¹)
  have hb4 : WordBound B t4:=changePC_bound B s4 0 ex4.final_bound (by omega)
  have ex5:=load_execution n x B t4 3 5 a⁻¹ (Complex.I*a⁻¹) rfl c4.2.2.1 c4.2.2.2.2
    (by omega) (by omega) (by omega) hb4
  have f5 : Protected s s5:=(f4.trans (protected_reset s4)).trans (protected_load _ _ _ _ _)
  let t5:=reset s5
  have hb5 : WordBound B t5:=changePC_bound B s5 0 ex5.final_bound (by omega)
  have hn5 : t5.natReg 0≠t5.natReg 1 := by
    simpa [t5,reset,f5.1 0 (by decide),f5.1 1 (by decide)] using hne
  have hr5 : Ready a⁻¹ (Complex.I*a⁻¹) U V t5 := by
    constructor
    · rfl
    · simpa [t5,s5,t4,reset,loadState,writeScalar,writeNat,next,f4.1 0 (by decide)] using hv4.1
    · simpa [t5,s5,t4,reset,loadState,writeScalar,writeNat,next,f4.1 1 (by decide)] using hv4.2
    · simp [t5,s5,reset,loadState,writeScalar,writeNat,next]
    · simp [t5,s5,reset,loadState,writeScalar,writeNat,next]
  let s6:=UniformPairDiagonalMachine.finalState t5 a⁻¹ (Complex.I*a⁻¹) U V
  have ex6:=UniformPairDiagonalMachine.bounded_execution n x B t5 a⁻¹ (Complex.I*a⁻¹) U V
    hr5 (by omega) hb5
  have f6 : Protected s s6:=(f5.trans (protected_reset s5)).trans (protected_diagonal _ _ _ _ _)
  have hv6 : s6.scalarHeap (s.natReg 0)=some (product a⁻¹ U) ∧
      s6.scalarHeap (s.natReg 1)=some (product (Complex.I*a⁻¹) V) := by
    simpa [s6,t5,reset,f5.1 0 (by decide),f5.1 1 (by decide)] using
      UniformPairDiagonalMachine.final_values t5 a⁻¹ (Complex.I*a⁻¹) U V hn5
  have r1 : BoundedRuns UniformHadamardPairMachine.program n x B s 4 {s1 with pc:=4} := by
    simpa [placed] using UniformBoundedAssembly.boundedExecution_placed right_code
      (by omega : 0+4≤B) (by omega : 4≤B) ex1
  have r2 : BoundedRuns UniformHadamardPairMachine.program n x B {s1 with pc:=4} 7 {s2 with pc:=11} := by
    simpa [placed,s2,t1,reset] using UniformBoundedAssembly.boundedExecution_placed first_diagonal_code
      (by omega : 4+7≤B) (by omega : 11≤B) ex2
  have r3 : BoundedRuns UniformHadamardPairMachine.program n x B {s2 with pc:=11} 5 {s3 with pc:=16} := by
    simpa [placed,s3,t2,reset] using UniformBoundedAssembly.boundedExecution_placed C_load_code
      (by omega : 11+5≤B) (by omega : 16≤B) ex3
  have r4 : BoundedRuns UniformHadamardPairMachine.program n x B {s3 with pc:=16} 11 {s4 with pc:=27} := by
    simpa [placed,s4,t3,reset] using UniformBoundedAssembly.boundedExecution_placed C_code
      (by omega : 16+11≤B) (by omega : 27≤B) ex4
  have r5 : BoundedRuns UniformHadamardPairMachine.program n x B {s4 with pc:=27} 5 {s5 with pc:=32} := by
    simpa [placed,s5,t4,reset] using UniformBoundedAssembly.boundedExecution_placed diagonal_load_code
      (by omega : 27+5≤B) (by omega : 32≤B) ex5
  have r6 : BoundedRuns UniformHadamardPairMachine.program n x B {s5 with pc:=32} 7 {s6 with pc:=39} := by
    simpa [placed,s6,t5,reset] using UniformBoundedAssembly.boundedExecution_placed last_diagonal_code
      (by omega : 32+7≤B) (by omega : 39≤B) ex6
  have hhalt : BoundedExecution UniformHadamardPairMachine.program n x B {s6 with pc:=39} 1 {s6 with pc:=39} :=
    .halt r6.final_bound (by rfl)
  refine ⟨{s6 with pc:=39},(((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).executes hhalt,
    f6,hc.protected f6 h0 h1,?_,?_,rfl⟩
  · exact hv6.1.trans (congrArg some (left_value u v))
  · exact hv6.2.trans (congrArg some (right_value u v))


inductive Coefficient where
 | rational (q : ℚ)
 | register (r : ℕ)
 deriving DecidableEq

def Coefficient.code (dst : ℕ) : Coefficient→Instruction
 | .rational q=>.scalarLiteral dst q
 | .register r=>.fieldBinary .add dst r 107

def Coefficient.value (env : State) : Coefficient→ℂ
 | .rational q=>q
 | .register r=>(env.scalarReg r).value

def Coefficient.ready (env : State) : Coefficient→Prop
 | .rational _=>True
 | .register r=>8≤r ∧ (env.scalarReg r).dependent=false

inductive Phase where
 | diagonal (left right : Coefficient)
 | hadamard
 deriving DecidableEq

def Phase.code : Phase→Program
 | .diagonal c d=>[c.code 0,d.code 1] ++
    UniformPairDiagonalMachine.program.map (relocate 2 9) ++ [.halt]
 | .hadamard=>UniformHadamardPairMachine.program

def Phase.ready (env : State) : Phase→Prop
 | .diagonal c d=>c.ready env ∧ d.ready env
 | .hadamard=>True

def Phase.action (env : State) : Phase→(Scalar×Scalar)→Scalar×Scalar
 | .diagonal c d,(u,v)=>(product (c.value env) u,product (d.value env) v)
 | .hadamard,(u,v)=>(⟨u.value+v.value,u.dependent||v.dependent⟩,
                      ⟨u.value-v.value,u.dependent||v.dependent⟩)

def setPC (s : State) (p : ℕ) : State:={s with pc:=p}
lemma setPC_eq (s:State) (p:ℕ) (h:s.pc=p) : setPC s p=s := by
 cases s;simp_all [setPC]

lemma Coefficient.eval (c : Coefficient) (env s : State)
 (h:c.ready env) (hz:env.scalarReg 107=prepared 0)
 (frame:∀r,8≤r→s.scalarReg r=env.scalarReg r) :
 (match c with | .rational q=>some (prepared (q:ℂ))
               | .register r=>evalField .add (s.scalarReg r) (s.scalarReg 107))=
 some (prepared (c.value env)) := by
 cases c with
 | rational q=>rfl
 | register r=>
   have hd:(env.scalarReg r).dependent=false:=h.2
   have he:s.scalarReg r=prepared ((env.scalarReg r).value):=by
    rw [frame r h.1];cases hh:env.scalarReg r with
    | mk value dep=>simp only [hh] at hd;subst dep;rfl
   simp [Coefficient.value,he,frame 107 (by decide),hz,evalField,prepared]

lemma Coefficient.step (c : Coefficient) (dst n : ℕ) (x:Fin n→ℂ)
 (p:Program) (env s : State) (code:p[s.pc]?=some (c.code dst))
 (h:c.ready env) (hz:env.scalarReg 107=prepared 0)
 (frame:∀r,8≤r→s.scalarReg r=env.scalarReg r) :
 step p n x s=.running (writeScalar s dst (prepared (c.value env))) := by
 have hh:=c.eval env s h hz frame
 cases c with
 | rational q=>simp [UniformMachine.step,code,Coefficient.code,Coefficient.value,prepared]
 | register r=>
   change evalField .add (s.scalarReg r) (s.scalarReg 107)=some (prepared ((env.scalarReg r).value)) at hh
   simp only [UniformMachine.step,code,Coefficient.code]
   rw [hh];rfl

lemma diagonal_code (c d : Coefficient) :
 CodeAt UniformPairDiagonalMachine.program (Phase.code (.diagonal c d)) 2 9 := by
 intro i hi;change i<7 at hi;interval_cases i <;> rfl

lemma diagonal_bounded (n B : ℕ) (x:Fin n→ℂ) (env s : State)
 (c d : Coefficient) (u v : Scalar) (pc:s.pc=0)
 (hc:c.ready env) (hd:d.ready env) (hz:env.scalarReg 107=prepared 0)
 (fr:∀r,8≤r→s.scalarReg r=env.scalarReg r)
 (hs:WordBound B s) (hB:10≤B) (hne:s.natReg 0≠s.natReg 1)
 (hu:s.scalarHeap (s.natReg 0)=some u) (hv:s.scalarHeap (s.natReg 1)=some v) : ∃t,
 BoundedExecution (Phase.code (.diagonal c d)) n x B s 10 t ∧ Protected s t ∧
 t.scalarHeap (s.natReg 0)=some (product (c.value env) u) ∧
 t.scalarHeap (s.natReg 1)=some (product (d.value env) v) ∧ t.pc=9 := by
 let a:=writeScalar s 0 (prepared (c.value env))
 let b:=writeScalar a 1 (prepared (d.value env))
 have ha:WordBound B a:=writeScalar_bound B s 0 _ hs (by omega)
 have hb:WordBound B b:=writeScalar_bound B a 1 _ ha (by simp [a,writeScalar,next,pc];omega)
 have first:step (Phase.code (.diagonal c d)) n x s=.running a:=
  c.step 0 n x _ env s (by simp [Phase.code,pc]) hc hz fr
 have second:step (Phase.code (.diagonal c d)) n x a=.running b:=by
  have hfr:∀r,8≤r→a.scalarReg r=env.scalarReg r:=by
   intro r hr;simp [a,writeScalar,next,show r≠0 by omega,fr r hr]
  exact d.step 1 n x _ env a (by simp [Phase.code,a,writeScalar,next,pc]) hd hz hfr
 let reset:=setPC b 0
 have br:WordBound B reset:=changePC_bound B b 0 hb (by omega)
 have ready:Ready (c.value env) (d.value env) u v reset:=by
  constructor <;> simp [reset,setPC,b,a,writeScalar,next,hu,hv]
 let out:=UniformPairDiagonalMachine.finalState reset (c.value env) (d.value env) u v
 have diag:=UniformPairDiagonalMachine.bounded_execution n x B reset (c.value env) (d.value env) u v ready (by omega) br
 have run:BoundedRuns (Phase.code (.diagonal c d)) n x B b 7 (setPC out 9):=by
  have hp:placed 2 reset=b:=by
   change setPC b (2+0)=b
   apply setPC_eq;simp [b,a,writeScalar,next,pc]
  rw [←hp]
  exact UniformBoundedAssembly.boundedExecution_placed (diagonal_code c d) (by change 2+7≤B;omega) (by omega:9≤B) diag
 have values:=UniformPairDiagonalMachine.final_values reset (c.value env) (d.value env) u v (by simpa [reset,setPC,b,a,writeScalar,next] using hne)
 refine ⟨setPC out 9,.next hs first (.next ha second (run.executes (.halt run.final_bound (by rfl)))),?_,?_,?_,rfl⟩
 · have hp:Protected s reset:=by
    refine ⟨fun r _=>rfl,rfl,rfl,rfl,fun _ _ _=>rfl,?_⟩
    intro r hr;simp [reset,setPC,b,a,writeScalar,next,show r≠0 by omega,show r≠1 by omega]
   have ht:=hp.trans (protected_diagonal reset (c.value env) (d.value env) u v)
   exact ht
 · exact values.1
 · exact values.2

lemma Phase.bounded (phase:Phase) (n B:ℕ) (x:Fin n→ℂ) (env s:State)
 (u v:Scalar) (pc:s.pc=0) (hr:phase.ready env) (hz:env.scalarReg 107=prepared 0)
 (fr:∀r,8≤r→s.scalarReg r=env.scalarReg r) (hs:WordBound B s) (hB:40≤B)
 (constants:Constants s) (h0 : 6 ≤ s.natReg 0) (h1 : 6 ≤ s.natReg 1)
 (hne:s.natReg 0≠s.natReg 1) (hu:s.scalarHeap (s.natReg 0)=some u)
 (hv:s.scalarHeap (s.natReg 1)=some v) : ∃t,
 BoundedExecution phase.code n x B s phase.code.length t ∧ Protected s t ∧ Constants t ∧
 t.scalarHeap (s.natReg 0)=some (phase.action env (u,v)).1 ∧
 t.scalarHeap (s.natReg 1)=some (phase.action env (u,v)).2 ∧ t.pc=phase.code.length-1 := by
 cases phase with
 | hadamard=>exact hadamard_bounded n x B s u v pc constants hs hB h0 h1 hne hu hv
 | diagonal c d=>
   obtain ⟨t,run,frame,left,right,last⟩:=diagonal_bounded n B x env s c d u v pc hr.1 hr.2 hz fr hs (by omega) hne hu hv
   exact ⟨t,run,frame,constants.protected frame h0 h1,left,right,last⟩


def blockPhases (front back : ℕ) : List Phase :=
 [.diagonal (.register front) (.rational 1),.hadamard,
  .diagonal (.rational (-3)) (.rational 1),.hadamard,
  .diagonal (.rational 2) (.rational 1),.hadamard,
  .diagonal (.rational (-1/8)) (.rational (-1/6)),
  .diagonal (.register back) (.rational 1)]
def phases : List Phase:=blockPhases 104 105++blockPhases 108 109

def phaseCost : List Phase→ℕ
 | []=>0
 | p::ps=>p.code.length+phaseCost ps

def emit (base : ℕ) : List Phase→Program
 | []=>[.halt]
 | p::ps=>p.code.map (relocate base (base+p.code.length))++emit (base+p.code.length) ps

def ScheduleAt : List Phase→Program→ℕ→Prop
 | [],p,b=>p[b]?=some .halt
 | a::as,p,b=>CodeAt a.code p b (b+a.code.length) ∧ ScheduleAt as p (b+a.code.length)

lemma emit_schedule (ps:List Phase) (prelude:Program) (base:ℕ) (hb:prelude.length=base) :
 ScheduleAt ps (prelude++emit base ps) base := by
 induction ps generalizing prelude base with
 | nil=>simp [ScheduleAt,emit,←hb]
 | cons a ps ih=>
   constructor
   · intro i hi
     change (prelude++(a.code.map (relocate base (base+a.code.length))++emit (base+a.code.length) ps))[base+i]?=_
     rw [List.getElem?_append_right (by omega)]
     rw [show base+i-prelude.length=i by omega]
     rw [List.getElem?_append_left (by simpa using hi)]
     simp [List.getElem?_map,List.getElem?_eq_getElem hi]
   · simpa only [ScheduleAt,emit,List.append_assoc] using
      ih (prelude++a.code.map (relocate base (base+a.code.length))) (base+a.code.length)
       (by simp [List.length_append,hb])

def actions (ps:List Phase) (env:State) (uv:Scalar×Scalar) : Scalar×Scalar:=
 ps.foldl (fun v p=>p.action env v) uv

lemma phases_execution (ps:List Phase) (p:Program) (base n B:ℕ) (x:Fin n→ℂ)
 (env s:State) (u v:Scalar) (code:ScheduleAt ps p base) (pc:s.pc=base)
 (hs:WordBound B s) (hb:base+phaseCost ps+1≤B) (hB:40≤B)
 (ready:∀a∈ps,a.ready env) (zero:env.scalarReg 107=prepared 0)
 (fr:∀r,8≤r→s.scalarReg r=env.scalarReg r) (constants:Constants s)
 (h0:6≤ s.natReg 0) (h1:6≤ s.natReg 1) (hne:s.natReg 0≠s.natReg 1)
 (hu:s.scalarHeap (s.natReg 0)=some u) (hv:s.scalarHeap (s.natReg 1)=some v) : ∃t,
 BoundedExecution p n x B s (phaseCost ps+1) t ∧ Protected s t ∧ Constants t ∧
 t.scalarHeap (s.natReg 0)=some (actions ps env (u,v)).1 ∧
 t.scalarHeap (s.natReg 1)=some (actions ps env (u,v)).2 ∧ t.pc=base+phaseCost ps := by
 induction ps generalizing base s u v with
 | nil=>
   have last:p[base]?=some .halt:=code
   exact ⟨s,.halt hs (by simp [step,pc,last]),protected_reset s,constants,hu,hv,pc⟩
 | cons a ps ih=>
   let r:=setPC s 0
   have rb:=changePC_bound B s 0 hs (by omega)
   obtain ⟨out,run,pf,cf,lu,rv,ep⟩:=a.bounded n B x env r u v rfl (ready a (by simp)) zero fr rb hB constants h0 h1 hne hu hv
   let nextState:=setPC out (base+a.code.length)
   have moved:BoundedRuns p n x B s a.code.length nextState:=by
    have placed_eq:placed base r=s:=by change setPC s (base+0)=s;apply setPC_eq;simpa using pc
    rw [←placed_eq]
    exact UniformBoundedAssembly.boundedExecution_placed code.1 (by simp only [phaseCost] at hb;omega) (by simp only [phaseCost] at hb;omega) run
   have pf':Protected s nextState:=pf
   have nr (q:ℕ) (hq:q≠2):nextState.natReg q=s.natReg q:=pf'.1 q hq
   have rf:∀q,8≤q→nextState.scalarReg q=env.scalarReg q:=by
    intro q hq;exact (pf'.2.2.2.2.2 q hq).trans (fr q hq)
   obtain ⟨t,run2,pf2,cf2,lv2,rv2,last⟩:=ih (base+a.code.length) nextState
    (a.action env (u,v)).1 (a.action env (u,v)).2 code.2 rfl moved.final_bound
    (by simp only [phaseCost] at hb;omega) (fun q hq=>ready q (by simp [hq])) rf cf
    (by simpa [nr 0 (by decide)] using h0) (by simpa [nr 1 (by decide)] using h1)
    (by simpa [nr 0 (by decide),nr 1 (by decide)] using hne)
    (by rw [nr 0 (by decide)];exact lu) (by rw [nr 1 (by decide)];exact rv)
   refine ⟨t,?_,pf'.trans pf2,cf2,?_,?_,?_⟩
   · simpa [phaseCost,Nat.add_assoc] using moved.executes run2
   · simpa [actions,List.foldl_cons,nr 0 (by decide)] using lv2
   · simpa [actions,List.foldl_cons,nr 1 (by decide)] using rv2
   · simpa [phaseCost,Nat.add_assoc] using last

/-- Only ordinary addresses are input. Scale values are computed by this code. -/
def prep : List Op:=
 [.literal 1624 0,.add 0 1620 1624,.add 1 1621 1624,
  .getScalar 100 1622,.getScalar 101 1623,.literalScalar 107 0,.literalScalar 106 1,
  .field .mul 102 100 101,.field .add 102 106 102,.field .sub 103 100 102,
  .literalScalar 104 (5/4),.field .div 104 104 102,
  .literalScalar 105 (4/5),.field .mul 105 105 102,
  .literalScalar 108 (5/4),.field .div 108 108 103,
  .literalScalar 109 (4/5),.field .mul 109 109 103]

def program : Program:=prep.map Op.code++emit prep.length phases
lemma prep_length : prep.length=18:=rfl
lemma emit_length (ps:List Phase) (base:ℕ) : (emit base ps).length=phaseCost ps+1:=by
 induction ps generalizing base with
 | nil=>rfl
 | cons p ps ih=>simp [emit,phaseCost,ih,Nat.add_assoc]
lemma program_length : program.length=359:=by
 simp [program,emit_length,prep_length,show phaseCost phases=340 from rfl]
lemma phases_cost : phaseCost phases=340:=rfl
lemma prep_code : BlockAt prep program 0:=by
 intro i hi;change i<18 at hi;interval_cases i <;> rfl
lemma schedule_code : ScheduleAt phases program 18:=
 emit_schedule phases (prep.map Op.code) 18 rfl

structure Args (left right mu conjugate:ℕ) (s:State) : Prop where
 leftAddress:s.natReg 1620=left
 rightAddress:s.natReg 1621=right
 coefficient:s.natReg 1622=mu
 conjugateCoefficient:s.natReg 1623=conjugate

def Sources (mu:ℂ) (co conjugate:ℕ) (s:State) : Prop:=
 s.scalarHeap co=some (prepared mu) ∧ s.scalarHeap conjugate=some (prepared (starRingEnd ℂ mu))
def Scales (mu:ℂ) (s:State) : Prop:=
 s.scalarReg 104=prepared ((5/4)/UniformLocalShear.kappa mu) ∧
 s.scalarReg 105=prepared ((4/5)*UniformLocalShear.kappa mu) ∧
 s.scalarReg 108=prepared ((5/4)/(mu-UniformLocalShear.kappa mu)) ∧
 s.scalarReg 109=prepared ((4/5)*(mu-UniformLocalShear.kappa mu)) ∧
 s.scalarReg 107=prepared 0

lemma prep_scales (mu:ℂ) (left right co conjugate:ℕ) (s:State)
 (args:Args left right co conjugate s) (source:Sources mu co conjugate s) :
 Scales mu (applyBlock prep s) := by
 have hk:1+mu*starRingEnd ℂ mu≠0:=UniformLocalShear.kappa_ne_zero mu
 have hr:mu-(1+mu*starRingEnd ℂ mu)≠0:=UniformLocalShear.second_ne_zero mu
 simp [Scales,applyBlock,prep,Op.apply,writeNat,writeScalar,next,evalField,prepared,
  args.coefficient,args.conjugateCoefficient,source.1,source.2,UniformLocalShear.kappa,hk,hr]

lemma prep_bounded (n B:ℕ) (x:Fin n→ℂ) (mu:ℂ) (left right co conjugate:ℕ)
 (s:State) (args:Args left right co conjugate s) (source:Sources mu co conjugate s)
 (pc:s.pc=0) (hs:WordBound B s) (hB:359≤B) :
 BoundedRuns program n x B s 18 (applyBlock prep s) := by
 have hk:1+mu*starRingEnd ℂ mu≠0:=UniformLocalShear.kappa_ne_zero mu
 have hr:mu-(1+mu*starRingEnd ℂ mu)≠0:=UniformLocalShear.second_ne_zero mu
 have reads:readable prep s:=by
  simp [readable,prep,Op.readable,Op.apply,writeNat,writeScalar,next,evalField,prepared,
    args.coefficient,args.conjugateCoefficient,source.1,source.2,hk,hr]
 have peaks:peak prep s≤B:=by
  simp [peak,prep,Op.peak,Op.apply,writeNat,next,args.leftAddress,args.rightAddress]
  exact ⟨by simpa only [args.leftAddress] using hs.2.1 1620,by simpa only [args.rightAddress] using hs.2.1 1621⟩
 exact block_runs prep program 0 n B x s prep_code pc hs (by change 0+18≤B;omega) reads peaks


lemma scalar_ext {u v:Scalar} (hv:u.value=v.value) (hd:u.dependent=v.dependent) : u=v := by
 cases u;cases v;simp_all

lemma block_action (env:State) (front back:ℕ) (t:ℂ) (ht:t≠0) (u v:Scalar)
 (hf:env.scalarReg front=prepared ((5/4)/t))
 (hb:env.scalarReg back=prepared ((4/5)*t)) :
 actions (blockPhases front back) env (u,v)=
 (⟨u.value+t*v.value,u.dependent||v.dependent⟩,
  ⟨v.value,u.dependent||v.dependent⟩) := by
 apply Prod.ext <;> apply scalar_ext
 all_goals simp [actions,blockPhases,Phase.action,Coefficient.value,product,prepared,hf,hb,
   Bool.or_self]
 all_goals field_simp [ht]
 all_goals ring

lemma actions_append (ps qs:List Phase) (env:State) (uv:Scalar×Scalar) :
 actions (ps++qs) env uv=actions qs env (actions ps env uv) := List.foldl_append

lemma complete_action (env:State) (mu:ℂ) (h:Scales mu env) (u v:Scalar) :
 actions phases env (u,v)=
 (⟨u.value+mu*v.value,u.dependent||v.dependent⟩,
  ⟨v.value,u.dependent||v.dependent⟩) := by
 rw [phases,actions_append,block_action env 104 105 _ (UniformLocalShear.kappa_ne_zero mu) u v h.1 h.2.1]
 rw [block_action env 108 109 _ (UniformLocalShear.second_ne_zero mu) _ _ h.2.2.1 h.2.2.2.1]
 simp [Bool.or_self]
 ring

lemma prep_addresses (left right co conjugate:ℕ) (s:State) (h:Args left right co conjugate s) :
 (applyBlock prep s).natReg 0=left ∧ (applyBlock prep s).natReg 1=right := by
 simp [applyBlock,prep,Op.apply,writeNat,writeScalar,next,h.leftAddress,h.rightAddress]

structure PrepFrame (s t:State) : Prop where
 scalarHeap:t.scalarHeap=s.scalarHeap
 natHeap:t.natHeap=s.natHeap
 outputs:t.outputs=s.outputs
 roots:t.rootOrders=s.rootOrders
 natReg:∀q,q≠0→q≠1→q≠1624→t.natReg q=s.natReg q
 scalarReg:∀q,(q<100∨110≤q)→t.scalarReg q=s.scalarReg q

lemma prep_frame (s:State) : PrepFrame s (applyBlock prep s) := by
 constructor
 · rfl
 · rfl
 · rfl
 · rfl
 · intro q h0 h1 h2
   simp [applyBlock,prep,Op.apply,writeNat,writeScalar,next,h0,h1,h2]
 · intro q hq
   simp (disch:=omega) [applyBlock,prep,Op.apply,writeNat,writeScalar,next]

structure Frame (left right:ℕ) (s t:State) : Prop where
 natHeap:t.natHeap=s.natHeap
 outputs:t.outputs=s.outputs
 roots:t.rootOrders=s.rootOrders
 outside:∀q,q≠left→q≠right→t.scalarHeap q=s.scalarHeap q
 natReg:∀q,3≤q→q≠1624→t.natReg q=s.natReg q
 scalarReg:∀q,8≤q→(q<100∨110≤q)→t.scalarReg q=s.scalarReg q

/-- Genuine reads plus internally guarded preparation and both literal three-C
blocks. No test of a complex value occurs, including mu=0. -/
theorem execution (n B:ℕ) (x:Fin n→ℂ) (mu:ℂ) (left right co conjugate:ℕ)
 (s:State) (u v:Scalar) (args:Args left right co conjugate s)
 (source:Sources mu co conjugate s) (constants:Constants s)
 (hl:6≤left) (hr:6≤right) (hne:left≠right)
 (hu:s.scalarHeap left=some u) (hv:s.scalarHeap right=some v)
 (pc:s.pc=0) (hs:WordBound B s) (hB:359≤B) : ∃out,
 BoundedExecution program n x B s 359 out ∧ out.pc=358 ∧ Constants out ∧
 out.scalarHeap left=some ⟨u.value+mu*v.value,u.dependent||v.dependent⟩ ∧
 out.scalarHeap right=some ⟨v.value,u.dependent||v.dependent⟩ ∧ Frame left right s out := by
 let env:=applyBlock prep s
 have start:=prep_bounded n B x mu left right co conjugate s args source pc hs hB
 have addresses : env.natReg 0=left ∧ env.natReg 1=right:=prep_addresses left right co conjugate s args
 have pf : PrepFrame s env:=prep_frame s
 have scales : Scales mu env:=prep_scales mu left right co conjugate s args source
 have ready:∀p∈phases,p.ready env:=by
  simp [phases,blockPhases,Phase.ready,Coefficient.ready,scales.1,scales.2.1,
    scales.2.2.1,scales.2.2.2.1,prepared]
 obtain ⟨out,run,protect,coef,lv,rv,last⟩:=phases_execution phases program 18 n B x env env u v schedule_code
  (by rw [UniformReciprocalMachine.applyBlock_pc,pc];rfl) start.final_bound
  (by rw [phases_cost];omega) (by omega) ready scales.2.2.2.2 (fun _ _=>rfl)
  (by simpa only [Constants,pf.scalarHeap] using constants)
  (by simpa only [addresses.1] using hl) (by simpa only [addresses.2] using hr)
  (by simpa only [addresses.1,addresses.2] using hne)
  (by simpa only [addresses.1,pf.scalarHeap] using hu)
  (by simpa only [addresses.2,pf.scalarHeap] using hv)
 have action:=complete_action env mu scales u v
 refine ⟨out,?_,?_,coef,?_,?_,?_⟩
 · simpa only [phases_cost,Nat.reduceAdd] using start.executes run
 · simpa only [phases_cost,Nat.reduceAdd] using last
 · simpa only [addresses.1,action] using lv
 · simpa only [addresses.2,action] using rv
 · refine ⟨protect.2.1.trans pf.natHeap,protect.2.2.1.trans pf.outputs,
    protect.2.2.2.1.trans pf.roots,?_,?_,?_⟩
   · intro q ql qr
     rw [protect.2.2.2.2.1 q (by simpa only [addresses.1] using ql) (by simpa only [addresses.2] using qr)]
     exact congrFun pf.scalarHeap q
   · intro q hq he
     exact (protect.1 q (by omega)).trans (pf.natReg q (by omega) (by omega) he)
   · intro q hq he
     exact (protect.2.2.2.2.2 q hq).trans (pf.scalarReg q he)


structure Result (left right:ℕ) (mu:ℂ) (u v:Scalar) (s t:State) : Prop where
 pc:t.pc=358
 constants:Constants t
 leftValue:t.scalarHeap left=some ⟨u.value+mu*v.value,u.dependent||v.dependent⟩
 rightValue:t.scalarHeap right=some ⟨v.value,u.dependent||v.dependent⟩
 frame:Frame left right s t

theorem execution_result (n B:ℕ) (x:Fin n→ℂ) (mu:ℂ) (left right co conjugate:ℕ)
 (s:State) (u v:Scalar) (args:Args left right co conjugate s)
 (source:Sources mu co conjugate s) (constants:Constants s)
 (hl:6≤left) (hr:6≤right) (hne:left≠right)
 (hu:s.scalarHeap left=some u) (hv:s.scalarHeap right=some v)
 (pc:s.pc=0) (hs:WordBound B s) (hB:359≤B) : ∃out,
 BoundedExecution program n x B s 359 out ∧ Result left right mu u v s out := by
 obtain ⟨out,run,last,coef,lv,rv,frame⟩:=execution n B x mu left right co conjugate s u v args source constants hl hr hne hu hv pc hs hB
 exact ⟨out,run,⟨last,coef,lv,rv,frame⟩⟩

lemma Result.coefficients {left right co conjugate:ℕ} {mu:ℂ} {u v:Scalar} {s t:State}
 (h:Result left right mu u v s t) (source:Sources mu co conjugate s)
 (cl:co≠left) (cr:co≠right) (bl:conjugate≠left) (br:conjugate≠right) :
 Sources mu co conjugate t := by
 exact ⟨(h.frame.outside co cl cr).trans source.1,(h.frame.outside conjugate bl br).trans source.2⟩

lemma Result.saved_headers {left right:ℕ} {mu:ℂ} {u v:Scalar} {s t:State}
 (h:Result left right mu u v s t) (q:ℕ) (lo:100≤q) (hi:q≤106) :
 t.natReg q=s.natReg q:=h.frame.natReg q (by omega) (by omega)

def kernelCalls (ps:List Phase) : ℕ:=ps.count .hadamard
lemma six_kernel_calls : kernelCalls phases=6:=by decide

/-- Numeric output agrees with the actual typed two-three-C word. The physical
chronology is exactly the same five diagonals and three Hadamards per block. -/
lemma Result.typed_word {left right:ℕ} {mu:ℂ} {u v:Scalar} {s t:State}
 (h:Result left right mu u v s t) :
 t.scalarHeap left=some ⟨(OAI.ExactFourier.wordMatrix (UniformLocalShear.word mu)).mulVec ![u.value,v.value] 0,
 u.dependent||v.dependent⟩ ∧
 t.scalarHeap right=some ⟨(OAI.ExactFourier.wordMatrix (UniformLocalShear.word mu)).mulVec ![u.value,v.value] 1,
 u.dependent||v.dependent⟩ ∧ OAI.ExactFourier.wordCalls (UniformLocalShear.word mu)=6 := by
 have action:=UniformLocalShear.word_action mu ![u.value,v.value]
 simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,action.1,action.2]
  using ⟨h.leftValue,h.rightValue,UniformLocalShear.word_calls mu⟩

/-- The actual initial prepared bank discharges every fixed constant heap load. -/
theorem startup_execution (n B:ℕ) (x:Fin n→ℂ) (mu:ℂ) (left right co conjugate:ℕ)
 (s:State) (u v:Scalar) (args:Args left right co conjugate s)
 (source:Sources mu co conjugate s) (ops:UniformInitialPreparation.Operands n x s)
 (hl:6≤left) (hr:6≤right) (hne:left≠right)
 (hu:s.scalarHeap left=some u) (hv:s.scalarHeap right=some v)
 (pc:s.pc=0) (hs:WordBound B s) (hB:359≤B) : ∃out,
 BoundedExecution program n x B s 359 out ∧ Result left right mu u v s out :=
 execution_result n B x mu left right co conjugate s u v args source
  (UniformHadamardPairMachine.constants_from_bank n s ops.constants)
  hl hr hne hu hv pc hs hB

end
end ExactFourierCircuits.UniformZeroFreePairShearMachine
