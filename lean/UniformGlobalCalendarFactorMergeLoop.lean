import UniformGlobalCalendarFactorMerge

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarFactorMerge
open UniformMachine UniformAssembly
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
noncomputable section

lemma Factors.storeProduct {A N O j : ℕ} {f g input : ℕ → ℂ} {heap : ℕ → Option Scalar}
 (source : Factors A N input heap) (fresh : A+N≤O) :
 Factors A N input (storeProduct O j f g heap) := by
 intro i hi
 change Function.update heap (O+j) (some (prepared (f j*g j))) (A+i) = some (prepared (input i))
 rw [Function.update_of_ne (by omega)]
 exact source i hi

lemma Tail.storeProduct {O j N : ℕ} {f g : ℕ → ℂ} {heap : ℕ → Option Scalar}
 (target : Tail O j N g heap) : Tail O (j+1) N g (storeProduct O j f g heap) := by
 intro i lo hi
 change Function.update heap (O+j) (some (prepared (f j*g j))) (O+i) = some (prepared (g i))
 rw [Function.update_of_ne (by omega)]
 exact target i (by omega) hi

/-- The complete actual pointwise multiplication loop, with all factor loads
and target stores charged and both source and untouched output cells retained. -/
theorem loop {n P r lane O j fuel B : ℕ} (x : Fin n → ℂ) (f g : ℕ → ℂ)
 (s : State) (h : Header P r lane O j s) (pc : s.pc=5) (wb : WordBound B s)
 (code : 15≤B) (ending : j+fuel=r) (source : Factors (P+lane*r) r f s.scalarHeap)
 (target : Tail O j r g s.scalarHeap) (sourceFit : P+9*r≤B) (fresh : P+9*r≤O)
 (laneFit : lane<9) (outputFit : O+r≤B) :
 ∃ ticks u, BoundedRuns program n x B s ticks u ∧ ticks=9*fuel+1 ∧ u.pc=14 ∧
 Header P r lane O r u ∧ u.scalarHeap=mergeHeap O f g j fuel s.scalarHeap ∧
 u.natHeap=s.natHeap ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs := by
 induction fuel generalizing j s with
 | zero =>
   have eq : j=r := by omega
   have stepEq : step program n x s = .running (setPC s 14) := by
    simp [step,pc,code_5,h.index,h.radix,eq,setPC]
   refine ⟨1,_,control_run program n B 14 x s wb (by omega) stepEq,by omega,rfl,?_,rfl,rfl,rfl,rfl⟩
   change Header P r lane O r (setPC s 14)
   simpa only [eq] using h.pc 14
 | succ fuel ih =>
   have index : j<r := by omega
   let a := setPC s 6
   have branch : BoundedRuns program n x B s 1 a := control_run program n B 6 x s wb
    (by omega) (by simp [step,pc,code_5,h.index,h.radix,index])
   have ah : Header P r lane O j a := h.pc 6
   have bodyRun := body_execution x a ah rfl branch.final_bound code index sourceFit laneFit outputFit
    f g (source j index) (target j le_rfl index)
   let b := applyBlock body a
   have bp : b.pc=13 := by rw [applyBlock_pc];rfl
   have bh : Header P r lane O (j+1) b := body_header ah
   have heap : b.scalarHeap=storeProduct O j f g s.scalarHeap := body_heap ah f g (source j index) (target j le_rfl index)
   let c := setPC b 5
   have jump : BoundedRuns program n x B b 1 c := control_run program n B 5 x b bodyRun.final_bound
    (by omega) (by simp [step,bp,code_13])
   have ch : Header P r lane O (j+1) c := bh.pc 5
   have laneBound : lane*r≤8*r := Nat.mul_le_mul_right r (by omega)
   have retained : Factors (P+lane*r) r f c.scalarHeap := by
    change Factors (P+lane*r) r f b.scalarHeap
    rw [heap]
    exact source.storeProduct (by omega)
   have remaining : Tail O (j+1) r g c.scalarHeap := by
    change Tail O (j+1) r g b.scalarHeap
    rw [heap]
    exact target.storeProduct
   obtain ⟨ticks,u,tail,cost,up,uh,out,nh,roots,outputs⟩ := ih (j:=j+1) c ch rfl jump.final_bound
    (by omega) retained remaining
   refine ⟨(1+7+1)+ticks,u,((branch.trans bodyRun).trans jump).trans tail,by omega,up,uh,?_,nh,roots,outputs⟩
   simpa only [c,setPC,heap,mergeHeap] using out

structure Args (P r lane O : ℕ) (s : State) : Prop where
 pool : s.natReg 6740=P
 radix : s.natReg 6741=r
 laneReg : s.natReg 6742=lane
 output : s.natReg 6743=O

lemma boot_header {P r lane O : ℕ} {s : State} (h : Args P r lane O s) :
 Header P r lane O 0 (applyBlock boot s) := by
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.pool,h.radix,h.laneReg,h.output]

/-- Literal15 lane merger including initialization and actual halt. -/
theorem execution {n P r lane O B : ℕ} (x : Fin n → ℂ) (f g : ℕ → ℂ)
 (s : State) (args : Args P r lane O s) (pc : s.pc=0) (wb : WordBound B s)
 (code : 15≤B) (source : Factors (P+lane*r) r f s.scalarHeap)
 (target : Factors O r g s.scalarHeap) (sourceFit : P+9*r≤B) (fresh : P+9*r≤O)
 (laneFit : lane<9) (outputFit : O+r≤B) :
 ∃ u, BoundedExecution program n x B s (9*r+7) u ∧ Header P r lane O r u ∧
 u.scalarHeap=mergeHeap O f g 0 r s.scalarHeap ∧
 u.natHeap=s.natHeap ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs := by
 have laneBound : lane*r≤8*r := Nat.mul_le_mul_right r (by omega)
 have start := block_runs boot program 0 n B x s boot_code pc wb (by change 5≤B;omega)
  (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next,args.pool,args.radix,args.laneReg];omega)
 let a := applyBlock boot s
 have ap : a.pc=5 := by rw [applyBlock_pc,pc];rfl
 obtain ⟨ticks,u,run,cost,up,uh,heap,nh,roots,outputs⟩ := loop (fuel:=r) x f g a (boot_header args) ap
  start.final_bound code (by omega) source (by intro i _ hi;exact target i hi) sourceFit fresh laneFit outputFit
 have haltEq : step program n x u = .halted u := by simp [step,up,code_14]
 have done := (start.trans run).executes (.halt run.final_bound haltEq)
 refine ⟨u,?_,uh,heap,nh,roots,outputs⟩
 simp only [show boot.length=5 from rfl,cost] at done
 convert done using 1;omega

end
end ExactFourierCircuits.UniformGlobalCalendarFactorMerge
