import UniformGlobalCalendarUnionRows

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarUnionRows
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

/-- Copy every actual ordered pair, retaining the source partition. -/
theorem loop {n P N O used j fuel B : ℕ} (x : Fin n → ℂ) (records : ℕ → ℕ × ℕ)
 (s : State) (h : Header P N O used j s) (pc : s.pc=5) (wb : WordBound B s)
 (code : 23 ≤ B) (ending : j+fuel=N) (source : Rows P N records s.natHeap)
 (sourceFit : P+2*N ≤ B) (fresh : P+2*N ≤ O)
 (values : ∀ k, k<N → (records k).1 ≤ B ∧ (records k).2 ≤ B)
 (outputFit : O+3*(used+N) ≤ B) :
 ∃ ticks u, BoundedRuns program n x B s ticks u ∧ ticks=16*fuel+1 ∧ u.pc=21 ∧
 Header P N O used N u ∧ u.natHeap=writeRows O used records j fuel s.natHeap := by
 induction fuel generalizing j s with
 | zero =>
   have eq : j=N := by omega
   have stepEq : step program n x s = .running (setPC s 21) := by
    simp [step,pc,code_5,h.index,h.count,eq,setPC]
   refine ⟨1,_,control_run program n B 21 x s wb (by omega) stepEq,by omega,rfl,?_,rfl⟩
   change Header P N O used N (setPC s 21)
   simpa only [eq] using h.pc 21
 | succ fuel ih =>
   have index : j<N := by omega
   let a := setPC s 6
   have branch : BoundedRuns program n x B s 1 a := control_run program n B 6 x s wb
    (by omega) (by simp [step,pc,code_5,h.index,h.count,index])
   have ah : Header P N O used j a := h.pc 6
   have body := pairBody_execution x a ah rfl branch.final_bound code index sourceFit outputFit
    (values j index).1 (values j index).2 (source j index).1 (source j index).2
   let b := applyBlock pairBody a
   have bp : b.pc=20 := by rw [applyBlock_pc];rfl
   have bh : Header P N O used (j+1) b := pairBody_header ah
   have heap : b.natHeap=storeRow O (used+j) (records j).1 (records j).2 s.natHeap :=
    pairBody_heap ah (source j index).1 (source j index).2
   let c := setPC b 5
   have jump : BoundedRuns program n x B b 1 c := control_run program n B 5 x b body.final_bound
    (by omega) (by simp [step,bp,code_20])
   have ch : Header P N O used (j+1) c := bh.pc 5
   have retained : Rows P N records c.natHeap := by
    change Rows P N records b.natHeap
    rw [heap]
    exact source.storeRow fresh
   obtain ⟨ticks,u,tail,cost,up,uh,out⟩ := ih (j:=j+1) c ch rfl jump.final_bound
    (by omega) retained
   refine ⟨(1+14+1)+ticks,u,((branch.trans body).trans jump).trans tail,by omega,up,uh,?_⟩
   simpa only [c,setPC,heap,writeRows] using out

structure Args (P N O used : ℕ) (s : State) : Prop where
 pairs : s.natReg 6740=P
 count : s.natReg 6741=N
 output : s.natReg 6742=O
 used : s.natReg 6743=used

lemma boot_header {P N O used : ℕ} {s : State} (h : Args P N O used s) :
 Header P N O used 0 (applyBlock boot s) := by
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.pairs,h.count,h.output,h.used]

lemma finish_header {P N O used : ℕ} {s : State} (h : Header P N O used N s) :
 Header P N O (used+N) N (applyBlock finish s) := by
 constructor <;> simp [finish,applyBlock,Op.apply,writeNat,next,h.pairs,h.count,h.output,h.used,
  h.zero,h.one,h.two,h.three,h.index]

/-- Full literal23 row printer, including initialization, final row-count update
and halt. Its exact output uses all physical ordered endpoints. -/
theorem execution {n P N O used B : ℕ} (x : Fin n → ℂ) (records : ℕ → ℕ × ℕ)
 (s : State) (args : Args P N O used s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 23 ≤ B) (source : Rows P N records s.natHeap)
 (sourceFit : P+2*N ≤ B) (fresh : P+2*N ≤ O)
 (values : ∀ k, k<N → (records k).1 ≤ B ∧ (records k).2 ≤ B)
 (outputFit : O+3*(used+N) ≤ B) :
 ∃ u, BoundedExecution program n x B s (16*N+8) u ∧
 Header P N O (used+N) N u ∧ u.natHeap=writeRows O used records 0 N s.natHeap := by
 have start := block_runs boot program 0 n B x s boot_code pc wb (by change 5≤B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let a := applyBlock boot s
 have ap : a.pc=5 := by rw [applyBlock_pc,pc];rfl
 obtain ⟨ticks,u,run,cost,up,uh,heap⟩ := loop (fuel:=N) x records a (boot_header args) ap
  start.final_bound code (by omega) source sourceFit fresh values outputFit
 have finishRun := block_runs finish program 21 n B x u finish_code up run.final_bound
  (by change 22≤B;omega) (by simp [finish,readable,Op.readable])
  (by simp [finish,peak,Op.peak,uh.used,uh.index];omega)
 let v := applyBlock finish u
 have vp : v.pc=22 := by rw [applyBlock_pc,up];rfl
 have haltEq : step program n x v = .halted v := by simp [step,vp,code_22]
 have done := ((start.trans run).trans finishRun).executes (.halt finishRun.final_bound haltEq)
 refine ⟨v,?_,finish_header uh,heap⟩
 simp only [show boot.length=5 from rfl,show finish.length=1 from rfl,cost] at done
 convert done using 1; omega

end
end ExactFourierCircuits.UniformGlobalCalendarUnionRows
