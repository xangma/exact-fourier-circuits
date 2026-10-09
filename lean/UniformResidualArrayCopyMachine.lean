import UniformResidualPermutation
import UniformTensorFiberCopyMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualArrayCopyMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- Full-Scalar gather/scatter through an actual Nat address table. The mode is
read sourceIndex a register; this is one fixed program, with no field arithmetic. -/
def boot : List Op := [.literal 4075 0,.literal 4076 1]
def lookup : List Op := [.add 4077 4071 4075,.getNat 4077 4077]
def gather : List Op := [.add 4078 4072 4077,.add 4081 4073 4075]
def scatter : List Op := [.add 4078 4072 4075,.add 4081 4073 4077]
def body : List Op := [.getScalar 120 4078,.putScalar 4081 120,.add 4075 4075 4076]
def program : Program := boot.map Op.code++[.branchLT 4075 4070 3 15]++lookup.map Op.code++
 [.branchLT 4074 4076 6 9]++gather.map Op.code++[.jump 11]++scatter.map Op.code++body.map Op.code++[.jump 2,.halt]
theorem program_length : program.length=16 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem lookup_code : BlockAt lookup program 3 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem gather_code : BlockAt gather program 6 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem scatter_code : BlockAt scatter program 9 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem body_code : BlockAt body program 11 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem branch_at : program[2]?=some (.branchLT 4075 4070 3 15) := rfl
theorem mode_at : program[5]?=some (.branchLT 4074 4076 6 9) := rfl
theorem gather_jump : program[8]?=some (.jump 11) := rfl
theorem loop_at : program[14]?=some (.jump 2) := rfl
theorem halt_at : program[15]?=some .halt := rfl

def sourceIndex (g:Bool) (F:ℕ→ ℕ) (j:ℕ) := if g then F j else j
def targetIndex (g:Bool) (F:ℕ→ ℕ) (j:ℕ) := if g then j else F j
structure Header (N T A D : ℕ) (g:Bool) (s:State) : Prop where
 length : s.natReg 4070=N
 table : s.natReg 4071=T
 source : s.natReg 4072=A
 destination : s.natReg 4073=D
 mode : s.natReg 4074=(if g then 0 else 1)
structure Frame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,(r<4075 ∨ 4081<r)→ u.natReg r=s.natReg r
 scalarReg : ∀r,r≠120→ u.scalarReg r=s.scalarReg r
lemma Frame.refl (s:State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u v:State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h=>(g.scalarReg r h).trans (f.scalarReg r h)⟩
lemma Header.frame {N T A D:ℕ} {g:Bool} {s u:State} (h:Header N T A D g s) (f:Frame s u) : Header N T A D g u :=
 ⟨(f.natReg _ (by omega)).trans h.length,(f.natReg _ (by omega)).trans h.table,
 (f.natReg _ (by omega)).trans h.source,(f.natReg _ (by omega)).trans h.destination,(f.natReg _ (by omega)).trans h.mode⟩
def Outside (N D:ℕ) (heap:ℕ→ Option Scalar) (s:State) : Prop := ∀z,z<D ∨ D+N≤ z→ s.scalarHeap z=heap z
structure Cursor (N T A D k:ℕ) (g:Bool) (F:ℕ→ ℕ) (heap:ℕ→ Option Scalar) (s:State) : Prop where
 header : Header N T A D g s
 index : s.natReg 4075=k
 one : s.natReg 4076=1
 copied : ∀j,j<k→ s.scalarHeap (D+targetIndex g F j)=heap (A+sourceIndex g F j)
 outside : Outside N D heap s

def iterationEnd (g:Bool) (s:State) : State :=
 {applyBlock body {applyBlock (if g then gather else scatter)
  {applyBlock lookup {s with pc:=3} with pc:=(if g then 6 else 9)} with pc:=11} with pc:=2}
lemma iteration_heap {N T A D k:ℕ} {g:Bool} {F:ℕ→ ℕ} {s:State}
 (h:Header N T A D g s) (idx:s.natReg 4075=k) (bank:s.natHeap (T+k)=some (F k)) :
 (iterationEnd g s).scalarHeap=Function.update s.scalarHeap (D+targetIndex g F k)
  (some ((s.scalarHeap (A+sourceIndex g F k)).getD Scalar.zero)) := by
 cases g <;> simp [iterationEnd,gather,scatter,body,lookup,sourceIndex,targetIndex,applyBlock,Op.apply,writeNat,writeScalar,next,
 h.table,h.source,h.destination,idx,bank]
lemma iteration_frame (g:Bool) (s:State) : Frame s (iterationEnd g s) := by
 cases g <;> refine ⟨rfl,rfl,rfl,?_,?_⟩
 all_goals intro r hr
 all_goals simp (disch:=omega) [iterationEnd,gather,scatter,body,lookup,applyBlock,Op.apply,writeNat,writeScalar,next,hr]

lemma from_small (g:Bool) (F:ℕ→ ℕ) (N j:ℕ) (hj:j<N) (hF:F j<N) : sourceIndex g F j<N := by cases g <;> simp_all [sourceIndex]
lemma into_small (g:Bool) (F:ℕ→ ℕ) (N j:ℕ) (hj:j<N) (hF:F j<N) : targetIndex g F j<N := by cases g <;> simp_all [targetIndex]
lemma into_injective (g:Bool) (F:ℕ→ ℕ) (N i j:ℕ) (hi:i<N) (hj:j<N)
 (inj:∀i,i<N→∀j,j<N→ F i=F j→ i=j) (eq:targetIndex g F i=targetIndex g F j) : i=j := by
 cases g
 · exact inj i hi j hj eq
 · exact eq

lemma iteration_cursor {N T A D k:ℕ} {g:Bool} {F:ℕ→ ℕ} {heap:ℕ→ Option Scalar} {s:State}
 (c:Cursor N T A D k g F heap s) (hk:k<N) (small:∀j,j<N→ F j<N)
 (inj:∀i,i<N→∀j,j<N→ F i=F j→ i=j) (bank:s.natHeap (T+k)=some (F k))
 (src:∀j,j<N→∃v,heap (A+j)=some v) (separate:A+N≤ D ∨ D+N≤ A) :
 Cursor N T A D (k+1) g F heap (iterationEnd g s) := by
 have Fk:=small k hk
 have fs:=from_small g F N k hk Fk
 have ds:=into_small g F N k hk (small k hk)
 obtain ⟨v,hv⟩:=src (sourceIndex g F k) fs
 have load:s.scalarHeap (A+sourceIndex g F k)=some v := (c.outside _ (by rcases separate with h|h <;> omega)).trans hv
 refine ⟨c.header.frame (iteration_frame g s),?_,?_,?_,?_⟩
 · cases g <;> simp [iterationEnd,gather,scatter,body,lookup,applyBlock,Op.apply,writeNat,writeScalar,next,c.index,c.one]
 · cases g <;> simp [iterationEnd,gather,scatter,body,lookup,applyBlock,Op.apply,writeNat,writeScalar,next,c.one]
 · intro j hj
   rw [iteration_heap c.header c.index bank,load]
   by_cases eq:j=k
   · subst j;simp [hv]
   · rw [Function.update_of_ne (by intro he;exact eq (into_injective g F N j k (by omega) hk inj (Nat.add_left_cancel he)))]
     exact c.copied j (by omega)
 · intro z hz
   rw [iteration_heap c.header c.index bank,Function.update_of_ne (by omega)]
   exact c.outside z hz

/-- Every table read, load, store and branch is charged. -/
theorem iteration (n B N T A D k:ℕ) (g:Bool) (F:ℕ→ ℕ) (x:Fin n→ ℂ) (heap:ℕ→ Option Scalar) (s:State)
 (c:Cursor N T A D k g F heap s) (hk:k<N) (small:∀j,j<N→ F j<N)
 (inj:∀i,i<N→∀j,j<N→ F i=F j→ i=j) (bank:∀j,j<N→ s.natHeap (T+j)=some (F j))
 (src:∀j,j<N→∃v,heap (A+j)=some v) (separate:A+N≤ D ∨ D+N≤ A)
 (ha:A+N≤ B) (hd:D+N≤ B) (ht:T+N≤ B) (code:16≤ B) (pc:s.pc=2) (bound:WordBound B s) :
 ∃u,BoundedRuns program n x B s (10+(if g then 1 else 0)) u ∧
 Cursor N T A D (k+1) g F heap u ∧ u.pc=2 ∧ Frame s u := by
 have Fk:=small k hk
 have fs:=from_small g F N k hk Fk
 have ds:=into_small g F N k hk (small k hk)
 obtain ⟨v,hv⟩:=src (sourceIndex g F k) fs
 have load:s.scalarHeap (A+sourceIndex g F k)=some v := (c.outside _ (by rcases separate with h|h <;> omega)).trans hv
 let t:State:={s with pc:=3}
 have tb:=changePC_bound B s 3 bound (by omega)
 have enter:BoundedRuns program n x B s 1 t:=.next bound
  (by simp [step,pc,branch_at,c.index,c.header.length,hk,t]) (.refl tb)
 have lrun:=block_runs lookup program 3 n B x t lookup_code rfl tb (by change 5≤ B;omega)
  (by simp [lookup,readable,Op.readable,Op.apply,writeNat,next,t,c.index,c.header.table,bank k hk])
  (by simp [lookup,peak,Op.peak,Op.apply,writeNat,next,t,c.index,c.header.table,bank k hk];omega)
 let l:=applyBlock lookup t
 have lp:l.pc=5:=by simp [l,lookup,applyBlock,Op.apply,writeNat,next,t]
 let chosen:State:={l with pc:=(if g then 6 else 9)}
 have chooseBound:=changePC_bound B l (if g then 6 else 9) lrun.final_bound (by cases g <;> simp <;> omega)
 have branch:BoundedRuns program n x B l 1 chosen:=.next lrun.final_bound
  (by cases g <;> simp [step,lp,mode_at,chosen,l,t,lookup,applyBlock,Op.apply,writeNat,next,c.header.mode,c.one]) (.refl chooseBound)
 let z:=applyBlock (if g then gather else scatter) chosen
 have zrun:BoundedRuns program n x B chosen 2 z:=by
  cases g
  · exact block_runs scatter program 9 n B x chosen scatter_code rfl chooseBound (by change 11≤ B;omega)
     (by simp [scatter,readable,Op.readable])
     (by simp [scatter,peak,Op.peak,Op.apply,chosen,l,t,lookup,applyBlock,writeNat,next,c.header.source,c.header.destination,c.header.table,c.index,bank k hk];omega)
  · exact block_runs gather program 6 n B x chosen gather_code rfl chooseBound (by change 8≤ B;omega)
     (by simp [gather,readable,Op.readable])
     (by simp [gather,peak,Op.peak,Op.apply,chosen,l,t,lookup,applyBlock,writeNat,next,c.header.source,c.header.destination,c.header.table,c.index,bank k hk];omega)
 let ready:State:={z with pc:=11}
 have rb:=changePC_bound B z 11 zrun.final_bound (by omega)
 have jump:BoundedRuns program n x B z (if g then 1 else 0) ready:=by
  cases g
  · have zp:z.pc=11:=by simp [z,chosen,l,t,scatter,lookup,applyBlock,Op.apply,writeNat,next]
    have eq:ready=z:=by change {z with pc:=11}=z;rw [←zp]
    rw [eq];exact .refl zrun.final_bound
  · have zp:z.pc=8:=by simp [z,chosen,l,t,gather,lookup,applyBlock,Op.apply,writeNat,next]
    exact .next zrun.final_bound (by simp [step,zp,gather_jump,ready]) (.refl rb)
 have rsrc:ready.natReg 4078=A+sourceIndex g F k := by
  cases g <;> simp [ready,z,chosen,l,t,gather,scatter,lookup,sourceIndex,applyBlock,Op.apply,writeNat,next,
   c.header.source,c.header.table,c.index,bank k hk]
 have rdst:ready.natReg 4081=D+targetIndex g F k := by
  cases g <;> simp [ready,z,chosen,l,t,gather,scatter,lookup,targetIndex,applyBlock,Op.apply,writeNat,next,
   c.header.destination,c.header.table,c.index,bank k hk]
 have ridx:ready.natReg 4075=k:=by cases g <;> simp [ready,z,chosen,l,t,gather,scatter,lookup,applyBlock,Op.apply,writeNat,next,c.index]
 have rone:ready.natReg 4076=1:=by cases g <;> simp [ready,z,chosen,l,t,gather,scatter,lookup,applyBlock,Op.apply,writeNat,next,c.one]
 have rload:ready.scalarHeap (A+sourceIndex g F k)=some v:=by cases g <;> exact load
 have brun:=block_runs body program 11 n B x ready body_code rfl rb (by change 14≤ B;omega)
  (by simp [body,readable,Op.readable,Op.apply,writeNat,writeScalar,next,rsrc,rload])
  (by simp [body,peak,Op.peak,Op.apply,writeNat,writeScalar,next,rdst,ridx,rone];omega)
 have bp:(applyBlock body ready).pc=14:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have back:BoundedRuns program n x B (applyBlock body ready) 1 (iterationEnd g s):=.next brun.final_bound
  (by simp [step,bp,loop_at,iterationEnd,ready,z,chosen,l,t])
  (.refl (changePC_bound B _ 2 brun.final_bound (by omega)))
 exact ⟨iterationEnd g s,by convert enter.trans (lrun.trans (branch.trans (zrun.trans (jump.trans (brun.trans back))))) using 1;simp [lookup,body];omega,
  iteration_cursor c hk small inj (bank k hk) src separate,rfl,iteration_frame g s⟩

theorem loop (n B N T A D k fuel:ℕ) (g:Bool) (F:ℕ→ ℕ) (x:Fin n→ ℂ) (heap:ℕ→ Option Scalar) (s:State)
 (c:Cursor N T A D k g F heap s) (total:k+fuel=N) (small:∀j,j<N→ F j<N)
 (inj:∀i,i<N→∀j,j<N→ F i=F j→ i=j) (bank:∀j,j<N→ s.natHeap (T+j)=some (F j))
 (src:∀j,j<N→∃v,heap (A+j)=some v) (separate:A+N≤ D ∨ D+N≤ A)
 (ha:A+N≤ B) (hd:D+N≤ B) (ht:T+N≤ B) (code:16≤ B) (pc:s.pc=2) (bound:WordBound B s) :
 ∃u,BoundedRuns program n x B s ((10+(if g then 1 else 0))*fuel) u ∧
 Cursor N T A D N g F heap u ∧ u.pc=2 ∧ Frame s u := by
 induction fuel generalizing k s with
 | zero=>
  have eq:k=N:=by omega
  subst k
  exact ⟨s,by simpa using BoundedRuns.refl bound,c,pc,Frame.refl s⟩
 | succ fuel ih=>
  obtain ⟨u,first,cu,up,fu⟩:=iteration n B N T A D k g F x heap s c (by omega) small inj bank src separate ha hd ht code pc bound
  have ubank:∀j,j<N→ u.natHeap (T+j)=some (F j):=by intro j hj;rw [fu.natHeap];exact bank j hj
  obtain ⟨v,rest,cv,vp,fv⟩:=ih (k+1) u cu (by omega) ubank up first.final_bound
  exact ⟨v,by convert first.trans rest using 1;ring,cv,vp,fu.trans fv⟩

lemma boot_frame (s:State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro r hr
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]

/-- Complete continuous execution through a present physical permutation table.
The copied equality is on Scalar structures, including the dependency flag. -/
theorem execution (n B N T A D:ℕ) (g:Bool) (F:ℕ→ ℕ) (x:Fin n→ ℂ) (s:State)
 (header:Header N T A D g s) (small:∀j,j<N→ F j<N)
 (inj:∀i,i<N→∀j,j<N→ F i=F j→ i=j) (bank:∀j,j<N→ s.natHeap (T+j)=some (F j))
 (src:∀j,j<N→∃v,s.scalarHeap (A+j)=some v) (separate:A+N≤ D ∨ D+N≤ A)
 (ha:A+N≤ B) (hd:D+N≤ B) (ht:T+N≤ B) (code:16≤ B) (pc:s.pc=0) (bound:WordBound B s) :
 ∃u,BoundedExecution program n x B s ((10+(if g then 1 else 0))*N+4) u ∧ u.pc=15 ∧
 (∀j,j<N→ u.scalarHeap (D+targetIndex g F j)=s.scalarHeap (A+sourceIndex g F j)) ∧
 Outside N D s.scalarHeap u ∧ Frame s u := by
 have br:=block_runs boot program 0 n B x s boot_code pc bound (by change 2≤ B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let ready:=applyBlock boot s
 have init:Cursor N T A D 0 g F s.scalarHeap ready:=by
  refine ⟨header.frame (boot_frame s),?_,?_,?_,?_⟩
  · simp [ready,boot,applyBlock,Op.apply,writeNat,next]
  · simp [ready,boot,applyBlock,Op.apply,writeNat,next]
  · intro j hj;omega
  · intro z _;rfl
 have rp:ready.pc=2:=by simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc]
 have readyBank:∀j,j<N→ ready.natHeap (T+j)=some (F j):=bank
 obtain ⟨v,run,cv,vp,fv⟩:=loop n B N T A D 0 N g F x s.scalarHeap ready init (by omega)
  small inj readyBank src separate ha hd ht code rp br.final_bound
 let u:State:={v with pc:=15}
 have finish:BoundedExecution program n x B v 2 u:=.next run.final_bound
  (by simp [step,vp,branch_at,cv.index,cv.header.length,u])
  (.halt (changePC_bound B v 15 run.final_bound (by omega)) (by simp [step,u,halt_at]))
 have ff:Frame v u:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 exact ⟨u,by convert br.executes (run.executes finish) using 1;simp [boot];omega,rfl,
  cv.copied,cv.outside,(boot_frame s).trans (fv.trans ff)⟩

/-- Gather and scatter are inverse full-Scalar transports through the generated
finite permutation, even on arbitrary dirty values and tags. -/
def finiteIndex {N:ℕ} (F:Fin N≃Fin N) (j:ℕ) : ℕ := if h:j<N then (F ⟨j,h⟩).val else 0
lemma finiteIndex_value {N:ℕ} (F:Fin N≃Fin N) (j:Fin N) : finiteIndex F j.val=(F j).val := by simp [finiteIndex,j.isLt]
lemma finiteIndex_small {N:ℕ} (F:Fin N≃Fin N) (j:ℕ) (hj:j<N) : finiteIndex F j<N := by simp only [finiteIndex,dite_eq_left hj];exact Fin.isLt _
lemma finiteIndex_injective {N:ℕ} (F:Fin N≃Fin N) (i j:ℕ) (hi:i<N) (hj:j<N)
 (eq:finiteIndex F i=finiteIndex F j) : i=j := by
 simp only [finiteIndex,dite_eq_left hi,dite_eq_left hj] at eq
 exact congrArg Fin.val (F.injective (Fin.ext eq))
lemma gather_scatter_inverse {N:ℕ} (F:Fin N≃Fin N) (f:Fin N→ Scalar) :
 (fun j=>(fun i=>f (F i)) (F.symm j))=f := by funext j;simp

end
end ExactFourierCircuits.UniformResidualArrayCopyMachine

