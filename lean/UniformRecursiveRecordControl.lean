import UniformRecursiveNativeEntries
import UniformRecursiveParentReturn
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRecordControl
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformFixedNetworkScheduleMachine (Record Printed)
open UniformFixedNetworkOpcodeMachine (Fields WellFormed headCost)
noncomputable section

structure DispatchFrame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j≠4177→u.natReg j=s.natReg j

def dispatchCode (start:ℕ) (target:Fin 7→ℕ) : Program :=
 [.branchLT 2851 4153 (target 0) (start+1),
  .natLiteral 4177 2,.branchLT 2851 4177 (target 1) (start+3),
  .natLiteral 4177 3,.branchLT 2851 4177 (target 2) (start+5),
  .natLiteral 4177 4,.branchLT 2851 4177 (target 3) (start+7),
  .natLiteral 4177 5,.branchLT 2851 4177 (target 4) (start+9),
  .natLiteral 4177 6,.branchLT 2851 4177 (target 5) (start+11),.jump (target 6)]
def DispatchAt (p:Program) (start:ℕ) (target:Fin 7→ℕ) : Prop :=
 ∀i,i<12→p[start+i]?=(dispatchCode start target)[i]?
def dispatchCost (k:ℕ) : ℕ := if k=6 then 12 else 2*k+1

theorem branch_control (p:Program) (loc yes no n B left right:ℕ) (x:Fin n→ℂ) (s:State)
 (code:p[loc]?=some (.branchLT left right yes no)) (pc:s.pc=loc)
 (bound:WordBound B s) (yb:yes≤B) (nb:no≤B) :
 BoundedRuns p n x B s 1 {s with pc:=if s.natReg left<s.natReg right then yes else no}:=
 .next bound (by simp only [step,pc,code])
  (.refl (changePC_bound B s _ bound (by split_ifs <;> assumption)))

theorem pair_control (p:Program) (loc yes no value n B k:ℕ) (x:Fin n→ℂ) (s:State)
 (literal:p[loc]?=some (.natLiteral 4177 value))
 (branch:p[loc+1]?=some (.branchLT 2851 4177 yes no))
 (pc:s.pc=loc) (opcode:s.natReg 2851=k) (bound:WordBound B s)
 (cb:loc+1≤B) (vb:value≤B) (yb:yes≤B) (nb:no≤B) :
 BoundedRuns p n x B s 2 {writeNat s 4177 value with pc:=if k<value then yes else no}:=by
 have first:BoundedRuns p n x B s 1 (writeNat s 4177 value):=
  .next bound (by simp [step,pc,literal])
   (.refl (writeNat_bound B s 4177 value bound (by omega) vb))
 have second:=branch_control p (loc+1) yes no n B 2851 4177 x (writeNat s 4177 value)
  branch (by simp [writeNat,next,pc]) first.final_bound yb nb
 have result:BoundedRuns p n x B (writeNat s 4177 value) 1
  {writeNat s 4177 value with pc:=if k<value then yes else no}:=by
  simpa [writeNat,next,opcode] using second
 exact first.trans result

/-- Every opcode0..6 follows the twelve actual branch/literal cells. Only
Nat4177 and the PC change; both heaps and every printed record remain intact. -/
theorem dispatch_generic (p:Program) (start n B k:ℕ) (target:Fin 7→ℕ) (x:Fin n→ℂ) (s:State)
 (code:DispatchAt p start target) (pc:s.pc=start) (opcode:s.natReg 2851=k)
 (one:s.natReg 4153=1) (hk:k<7) (bound:WordBound B s)
 (extent:start+12≤B) (targets:∀j,target j≤B) :∃u,
 BoundedRuns p n x B s (dispatchCost k) u ∧ u.pc=target ⟨k,hk⟩ ∧ DispatchFrame s u:=by
 have cell(i:ℕ)(hi:i<12):p[start+i]?=(dispatchCode start target)[i]?:=code i hi
 have c0:p[start]?=some (.branchLT 2851 4153 (target 0) (start+1)):=by
  simpa only [Nat.add_zero,dispatchCode,List.getElem?_cons_zero] using cell 0 (by decide)
 have first:=branch_control p start (target 0) (start+1) n B 2851 4153 x s c0 pc bound
  (targets 0) (by omega)
 have initial:BoundedRuns p n x B s 1 {s with pc:=if k<1 then target 0 else start+1}:=by
  simpa only [opcode,one] using first
 interval_cases k
 · refine ⟨{s with pc:=target 0},by simpa [dispatchCost] using initial,rfl,?_⟩
   exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬1<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=target 1}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 1 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show 1<2 by decide,ite_true] using got
   refine ⟨t1,?_,rfl,?_⟩
   · simpa [dispatchCost] using (r0).trans r1
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,writeNat,next,Function.update_of_ne hj]
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬2<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=start+3}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 2 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show ¬2<2 by decide,ite_false] using got
   let t2:State:={writeNat t1 4177 3 with pc:=target 2}
   have r2:BoundedRuns p n x B t1 2 t2:=by
    have lit:p[start+3]?=some (.natLiteral 4177 3):=cell 3 (by decide)
    have br:p[(start+3)+1]?=some (.branchLT 2851 4177 (target 2) (start+5)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 4 (by decide)
    have got:=pair_control p (start+3) (target 2) (start+5) 3 n B 2 x t1
     lit br rfl (by simp [t1,t0,writeNat,next,opcode]) r1.final_bound (by omega) (by omega) (targets 2) (by omega)
    simpa only [show 2<3 by decide,ite_true] using got
   refine ⟨t2,?_,rfl,?_⟩
   · simpa [dispatchCost] using ((r0).trans r1).trans r2
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,t2,writeNat,next,Function.update_of_ne hj]
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬3<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=start+3}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 3 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show ¬3<2 by decide,ite_false] using got
   let t2:State:={writeNat t1 4177 3 with pc:=start+5}
   have r2:BoundedRuns p n x B t1 2 t2:=by
    have lit:p[start+3]?=some (.natLiteral 4177 3):=cell 3 (by decide)
    have br:p[(start+3)+1]?=some (.branchLT 2851 4177 (target 2) (start+5)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 4 (by decide)
    have got:=pair_control p (start+3) (target 2) (start+5) 3 n B 3 x t1
     lit br rfl (by simp [t1,t0,writeNat,next,opcode]) r1.final_bound (by omega) (by omega) (targets 2) (by omega)
    simpa only [show ¬3<3 by decide,ite_false] using got
   let t3:State:={writeNat t2 4177 4 with pc:=target 3}
   have r3:BoundedRuns p n x B t2 2 t3:=by
    have lit:p[start+5]?=some (.natLiteral 4177 4):=cell 5 (by decide)
    have br:p[(start+5)+1]?=some (.branchLT 2851 4177 (target 3) (start+7)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 6 (by decide)
    have got:=pair_control p (start+5) (target 3) (start+7) 4 n B 3 x t2
     lit br rfl (by simp [t2,t0,t1,writeNat,next,opcode]) r2.final_bound (by omega) (by omega) (targets 3) (by omega)
    simpa only [show 3<4 by decide,ite_true] using got
   refine ⟨t3,?_,rfl,?_⟩
   · simpa [dispatchCost] using (((r0).trans r1).trans r2).trans r3
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,t2,t3,writeNat,next,Function.update_of_ne hj]
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬4<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=start+3}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 4 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show ¬4<2 by decide,ite_false] using got
   let t2:State:={writeNat t1 4177 3 with pc:=start+5}
   have r2:BoundedRuns p n x B t1 2 t2:=by
    have lit:p[start+3]?=some (.natLiteral 4177 3):=cell 3 (by decide)
    have br:p[(start+3)+1]?=some (.branchLT 2851 4177 (target 2) (start+5)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 4 (by decide)
    have got:=pair_control p (start+3) (target 2) (start+5) 3 n B 4 x t1
     lit br rfl (by simp [t1,t0,writeNat,next,opcode]) r1.final_bound (by omega) (by omega) (targets 2) (by omega)
    simpa only [show ¬4<3 by decide,ite_false] using got
   let t3:State:={writeNat t2 4177 4 with pc:=start+7}
   have r3:BoundedRuns p n x B t2 2 t3:=by
    have lit:p[start+5]?=some (.natLiteral 4177 4):=cell 5 (by decide)
    have br:p[(start+5)+1]?=some (.branchLT 2851 4177 (target 3) (start+7)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 6 (by decide)
    have got:=pair_control p (start+5) (target 3) (start+7) 4 n B 4 x t2
     lit br rfl (by simp [t2,t0,t1,writeNat,next,opcode]) r2.final_bound (by omega) (by omega) (targets 3) (by omega)
    simpa only [show ¬4<4 by decide,ite_false] using got
   let t4:State:={writeNat t3 4177 5 with pc:=target 4}
   have r4:BoundedRuns p n x B t3 2 t4:=by
    have lit:p[start+7]?=some (.natLiteral 4177 5):=cell 7 (by decide)
    have br:p[(start+7)+1]?=some (.branchLT 2851 4177 (target 4) (start+9)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 8 (by decide)
    have got:=pair_control p (start+7) (target 4) (start+9) 5 n B 4 x t3
     lit br rfl (by simp [t3,t0,t1,t2,writeNat,next,opcode]) r3.final_bound (by omega) (by omega) (targets 4) (by omega)
    simpa only [show 4<5 by decide,ite_true] using got
   refine ⟨t4,?_,rfl,?_⟩
   · simpa [dispatchCost] using ((((r0).trans r1).trans r2).trans r3).trans r4
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,t2,t3,t4,writeNat,next,Function.update_of_ne hj]
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬5<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=start+3}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 5 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show ¬5<2 by decide,ite_false] using got
   let t2:State:={writeNat t1 4177 3 with pc:=start+5}
   have r2:BoundedRuns p n x B t1 2 t2:=by
    have lit:p[start+3]?=some (.natLiteral 4177 3):=cell 3 (by decide)
    have br:p[(start+3)+1]?=some (.branchLT 2851 4177 (target 2) (start+5)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 4 (by decide)
    have got:=pair_control p (start+3) (target 2) (start+5) 3 n B 5 x t1
     lit br rfl (by simp [t1,t0,writeNat,next,opcode]) r1.final_bound (by omega) (by omega) (targets 2) (by omega)
    simpa only [show ¬5<3 by decide,ite_false] using got
   let t3:State:={writeNat t2 4177 4 with pc:=start+7}
   have r3:BoundedRuns p n x B t2 2 t3:=by
    have lit:p[start+5]?=some (.natLiteral 4177 4):=cell 5 (by decide)
    have br:p[(start+5)+1]?=some (.branchLT 2851 4177 (target 3) (start+7)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 6 (by decide)
    have got:=pair_control p (start+5) (target 3) (start+7) 4 n B 5 x t2
     lit br rfl (by simp [t2,t0,t1,writeNat,next,opcode]) r2.final_bound (by omega) (by omega) (targets 3) (by omega)
    simpa only [show ¬5<4 by decide,ite_false] using got
   let t4:State:={writeNat t3 4177 5 with pc:=start+9}
   have r4:BoundedRuns p n x B t3 2 t4:=by
    have lit:p[start+7]?=some (.natLiteral 4177 5):=cell 7 (by decide)
    have br:p[(start+7)+1]?=some (.branchLT 2851 4177 (target 4) (start+9)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 8 (by decide)
    have got:=pair_control p (start+7) (target 4) (start+9) 5 n B 5 x t3
     lit br rfl (by simp [t3,t0,t1,t2,writeNat,next,opcode]) r3.final_bound (by omega) (by omega) (targets 4) (by omega)
    simpa only [show ¬5<5 by decide,ite_false] using got
   let t5:State:={writeNat t4 4177 6 with pc:=target 5}
   have r5:BoundedRuns p n x B t4 2 t5:=by
    have lit:p[start+9]?=some (.natLiteral 4177 6):=cell 9 (by decide)
    have br:p[(start+9)+1]?=some (.branchLT 2851 4177 (target 5) (start+11)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 10 (by decide)
    have got:=pair_control p (start+9) (target 5) (start+11) 6 n B 5 x t4
     lit br rfl (by simp [t4,t0,t1,t2,t3,writeNat,next,opcode]) r4.final_bound (by omega) (by omega) (targets 5) (by omega)
    simpa only [show 5<6 by decide,ite_true] using got
   refine ⟨t5,?_,rfl,?_⟩
   · simpa [dispatchCost] using (((((r0).trans r1).trans r2).trans r3).trans r4).trans r5
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,t2,t3,t4,t5,writeNat,next,Function.update_of_ne hj]
 · let t0:State:={s with pc:=start+1}
   have r0:BoundedRuns p n x B s 1 t0:=by simpa only [show ¬6<1 by decide,ite_false] using initial
   let t1:State:={writeNat t0 4177 2 with pc:=start+3}
   have r1:BoundedRuns p n x B t0 2 t1:=by
    have lit:p[start+1]?=some (.natLiteral 4177 2):=cell 1 (by decide)
    have br:p[(start+1)+1]?=some (.branchLT 2851 4177 (target 1) (start+3)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 2 (by decide)
    have got:=pair_control p (start+1) (target 1) (start+3) 2 n B 6 x t0
     lit br rfl (by simp [t0,opcode]) r0.final_bound (by omega) (by omega) (targets 1) (by omega)
    simpa only [show ¬6<2 by decide,ite_false] using got
   let t2:State:={writeNat t1 4177 3 with pc:=start+5}
   have r2:BoundedRuns p n x B t1 2 t2:=by
    have lit:p[start+3]?=some (.natLiteral 4177 3):=cell 3 (by decide)
    have br:p[(start+3)+1]?=some (.branchLT 2851 4177 (target 2) (start+5)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 4 (by decide)
    have got:=pair_control p (start+3) (target 2) (start+5) 3 n B 6 x t1
     lit br rfl (by simp [t1,t0,writeNat,next,opcode]) r1.final_bound (by omega) (by omega) (targets 2) (by omega)
    simpa only [show ¬6<3 by decide,ite_false] using got
   let t3:State:={writeNat t2 4177 4 with pc:=start+7}
   have r3:BoundedRuns p n x B t2 2 t3:=by
    have lit:p[start+5]?=some (.natLiteral 4177 4):=cell 5 (by decide)
    have br:p[(start+5)+1]?=some (.branchLT 2851 4177 (target 3) (start+7)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 6 (by decide)
    have got:=pair_control p (start+5) (target 3) (start+7) 4 n B 6 x t2
     lit br rfl (by simp [t2,t0,t1,writeNat,next,opcode]) r2.final_bound (by omega) (by omega) (targets 3) (by omega)
    simpa only [show ¬6<4 by decide,ite_false] using got
   let t4:State:={writeNat t3 4177 5 with pc:=start+9}
   have r4:BoundedRuns p n x B t3 2 t4:=by
    have lit:p[start+7]?=some (.natLiteral 4177 5):=cell 7 (by decide)
    have br:p[(start+7)+1]?=some (.branchLT 2851 4177 (target 4) (start+9)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 8 (by decide)
    have got:=pair_control p (start+7) (target 4) (start+9) 5 n B 6 x t3
     lit br rfl (by simp [t3,t0,t1,t2,writeNat,next,opcode]) r3.final_bound (by omega) (by omega) (targets 4) (by omega)
    simpa only [show ¬6<5 by decide,ite_false] using got
   let t5:State:={writeNat t4 4177 6 with pc:=start+11}
   have r5:BoundedRuns p n x B t4 2 t5:=by
    have lit:p[start+9]?=some (.natLiteral 4177 6):=cell 9 (by decide)
    have br:p[(start+9)+1]?=some (.branchLT 2851 4177 (target 5) (start+11)):=by
     simpa [Nat.add_assoc,dispatchCode] using cell 10 (by decide)
    have got:=pair_control p (start+9) (target 5) (start+11) 6 n B 6 x t4
     lit br rfl (by simp [t4,t0,t1,t2,t3,writeNat,next,opcode]) r4.final_bound (by omega) (by omega) (targets 5) (by omega)
    simpa only [show ¬6<6 by decide,ite_false] using got
   let t6:State:={t5 with pc:=target 6}
   have r6:BoundedRuns p n x B t5 1 t6:=.next r5.final_bound
    (by simp only [step,show t5.pc=start+11 from rfl,cell 11 (by decide)];rfl)
    (.refl (changePC_bound B t5 (target 6) r5.final_bound (targets 6)))
   refine ⟨t6,?_,rfl,?_⟩
   · simpa [dispatchCost] using ((((((r0).trans r1).trans r2).trans r3).trans r4).trans r5).trans r6
   · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
     intro j hj
     simp only [t0,t1,t2,t3,t4,t5,t6,writeNat,next,Function.update_of_ne hj]

namespace P
export UniformRecursiveSavingProgram (Part program piece address size)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R

lemma dispatch_vector (start a b c d e f g:ℕ):
 dispatchCode start ![a,b,c,d,e,f,g]=
 [.branchLT 2851 4153 a (start+1),
  .natLiteral 4177 2,.branchLT 2851 4177 b (start+3),
  .natLiteral 4177 3,.branchLT 2851 4177 c (start+5),
  .natLiteral 4177 4,.branchLT 2851 4177 d (start+7),
  .natLiteral 4177 5,.branchLT 2851 4177 e (start+9),
  .natLiteral 4177 6,.branchLT 2851 4177 f (start+11),.jump g]:=rfl

def targets : Fin 7→ℕ := ![P.address .residualMark,P.address .scalar,P.address .marker,
 P.address .translation,P.address .exchange,P.address .paddingInit,P.address .marker]
lemma dispatch_from_slice (main piece:Program)(start:ℕ)(target:Fin 7→ℕ)
 (slice:UniformRecursiveSavingProgram.Slice piece main start)
 (eq:piece=dispatchCode start target):DispatchAt main start target:=by
 intro i hi
 have len:(dispatchCode start target).length=12:=rfl
 have ip:i<piece.length:=by rw [eq,len];exact hi
 exact (slice i ip).trans (congrArg (fun z:Program=>z[i]?) eq)
lemma dispatch_piece:P.piece .dispatch=dispatchCode (P.address .dispatch) targets:=
 (dispatch_vector (P.address .dispatch) (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .translation) (P.address .exchange) (P.address .paddingInit) (P.address .marker)).symm
lemma dispatch_code : DispatchAt P.program (P.address .dispatch) targets:=
 dispatch_from_slice P.program (P.piece .dispatch) (P.address .dispatch) targets
  (UniformRecursiveSavingProgram.part_slice .dispatch) dispatch_piece
lemma vector_bound (a b c d e f g B:ℕ)
 (ha:a≤B)(hb:b≤B)(hc:c≤B)(hd:d≤B)(he:e≤B)(hf:f≤B)(hg:g≤B):
 ∀j:Fin 7,(![a,b,c,d,e,f,g]) j≤B:=by
 intro j;fin_cases j <;> assumption
lemma targets_bound (B:ℕ)(code:P.program.length≤B):∀j,targets j≤B:=
 vector_bound _ _ _ _ _ _ _ B (R.start_bound .residualMark B code) (R.start_bound .scalar B code)
  (R.start_bound .marker B code) (R.start_bound .translation B code) (R.start_bound .exchange B code)
  (R.start_bound .paddingInit B code) (R.start_bound .marker B code)

theorem dispatch_execution (n B k:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=P.address .dispatch) (opcode:s.natReg 2851=k)
 (one:s.natReg 4153=1) (hk:k<7) (bound:WordBound B s) (code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s (dispatchCost k) u ∧ u.pc=targets ⟨k,hk⟩ ∧ DispatchFrame s u:=by
 exact dispatch_generic P.program (P.address .dispatch) n B k targets x s dispatch_code pc opcode one hk bound
  (R.code_bound .dispatch 12 B rfl code) (targets_bound B code)

open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
def loopBlock : List Op := [.literal 4179 1,.binary .sub 4178 4123 4179,.load 3301 4178]
lemma loopBlock_length : loopBlock.length=3:=rfl
structure LoopFrame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j≠3301→j≠4178→j≠4179→u.natReg j=s.natReg j
lemma loop_frame (s:State):LoopFrame s (applyBlock loopBlock s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j a b c
 simp only [loopBlock,applyBlock,Op.apply,writeNat,next,Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c]

/-- The loop reads the physically stored main-tape end at work-1 before
performing its actual comparison. No prepared end register is supplied. -/
theorem loop_generic (p:Program) (start yes no n B work cursor tapeEnd:ℕ) (x:Fin n→ℂ) (s:State)
 (block:BlockAt loopBlock p start) (branch:p[start+3]?=some (.branchLT 2850 3301 yes no))
 (pc:s.pc=start) (w:s.natReg 4123=work) (ptr:s.natReg 2850=cursor)
 (metadata:s.natHeap (work-1)=some tapeEnd) (bound:WordBound B s)
 (extent:start+4≤B) (yb:yes≤B) (nb:no≤B):∃u,
 BoundedRuns p n x B s 4 u ∧ u.pc=(if cursor<tapeEnd then yes else no) ∧
 u.natReg 2850=cursor ∧ u.natReg 3301=tapeEnd ∧ LoopFrame s u:=by
 have wb:work≤B:=by have h:=bound.2.1 4123;rwa [w] at h
 have eb:tapeEnd≤B:=(bound.2.2.1 (work-1) tapeEnd metadata).2
 have safe:readable loopBlock s∧peak loopBlock s≤B:=by
  simp [loopBlock,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,w,metadata]
  omega
 have run:=block_runs loopBlock p start n B x s block pc bound (by rw [loopBlock_length];omega) safe.1 safe.2
 let t:=applyBlock loopBlock s
 have tp:t.pc=start+3:=by
  simp [t,loopBlock,applyBlock,Op.apply,writeNat,next,pc,Nat.add_assoc]
 have tc:t.natReg 2850=cursor:=by
  simp [t,loopBlock,applyBlock,Op.apply,writeNat,next,ptr]
 have te:t.natReg 3301=tapeEnd:=by
  simp [t,loopBlock,applyBlock,Op.apply,evalNat,writeNat,next,w,metadata]
 have branchRun:=branch_control p (start+3) yes no n B 2850 3301 x t branch tp run.final_bound yb nb
 let u:State:={t with pc:=if cursor<tapeEnd then yes else no}
 have br:BoundedRuns p n x B t 1 u:=by simpa only [tc,te] using branchRun
 refine ⟨u,by simpa only [loopBlock_length] using run.trans br,rfl,tc,te,?_⟩
 have fr:=loop_frame s
 exact ⟨fr.natHeap,fr.scalarHeap,fr.scalarReg,fr.outputs,fr.roots,fr.natReg⟩
lemma loop_code : BlockAt loopBlock P.program (P.address .loop):=
 UniformRecursiveSavingExecution.part_block .loop loopBlock _ rfl
lemma loop_branch : P.program[P.address .loop+3]?=some (.branchLT 2850 3301 (P.address .reader) (P.address .spectatorSetup)):=
 UniformRecursiveSavingExecution.part_at .loop 3 (by decide)
theorem loop_execution (n B work cursor tapeEnd:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=P.address .loop) (w:s.natReg 4123=work) (ptr:s.natReg 2850=cursor)
 (metadata:s.natHeap (work-1)=some tapeEnd) (bound:WordBound B s) (code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s 4 u ∧
 u.pc=(if cursor<tapeEnd then P.address .reader else P.address .spectatorSetup) ∧
 u.natReg 2850=cursor ∧ u.natReg 3301=tapeEnd ∧ LoopFrame s u:=by
 exact loop_generic P.program (P.address .loop) (P.address .reader) (P.address .spectatorSetup) n B work cursor tapeEnd x s
  loop_code loop_branch pc w ptr metadata bound (R.code_bound .loop 4 B rfl code)
  (R.start_bound .reader B code) (R.start_bound .spectatorSetup B code)

lemma reader_code:CodeAt UniformFixedNetworkOpcodeMachine.headProgram P.program (P.address .reader) (P.address .dispatch):=
 UniformRecursiveSavingProgram.part_child rfl
/-- Relocated real52-cell header reader; all fields come from the Nat heap. -/
theorem reader_generic (main:Program)(start exit A B n:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (link:CodeAt UniformFixedNetworkOpcodeMachine.headProgram main start exit)
 (pc:s.pc=start)(ptr:s.natReg 2850=A)(bound:WordBound B s)(bank:Printed A r.data s)
 (good:WellFormed r)(extent:A+r.data.length≤B)(width:r.width+1≤B)
 (code:start+UniformFixedNetworkOpcodeMachine.headProgram.length≤B)(ret:exit≤B):∃u,
 BoundedRuns main n x B s (headCost r) u ∧ u.pc=exit ∧ Fields A r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=A+r.data.length ∧ UniformFixedNetworkOpcodeMachine.Frame s u:=by
 have localCode:UniformFixedNetworkOpcodeMachine.headProgram.length≤B:=(Nat.le_add_left _ _).trans code
 have small:52≤B:=by simpa only [UniformFixedNetworkOpcodeMachine.headProgram_length] using localCode
 obtain ⟨u,run,fields,body,nextval,frame⟩:=UniformFixedNetworkOpcodeMachine.head_execution A B n r x (setPC s 0)
  ptr rfl (changePC_bound B s 0 bound (by omega)) bank good extent width small
 have placed:=UniformBoundedAssembly.boundedExecution_placed link code ret run
 have begin:UniformAssembly.placed start (setPC s 0)=s:=by
  change setPC s start=s;rw [←pc];cases s;rfl
 rw [begin] at placed
 exact ⟨setPC u exit,placed,rfl,fields.pc _,body,nextval,⟨frame.natHeap,frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots,frame.natReg⟩⟩

theorem reader_execution (A B n:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .reader)(ptr:s.natReg 2850=A)(bound:WordBound B s)(bank:Printed A r.data s)
 (good:WellFormed r)(extent:A+r.data.length≤B)(width:r.width+1≤B)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s (headCost r) u ∧ u.pc=P.address .dispatch ∧ Fields A r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=A+r.data.length ∧ UniformFixedNetworkOpcodeMachine.Frame s u:=by
 exact reader_generic P.program (P.address .reader) (P.address .dispatch) A B n r x s reader_code pc ptr bound bank good extent width
  (R.code_bound .reader UniformFixedNetworkOpcodeMachine.headProgram.length B rfl code) (R.start_bound .dispatch B code)

def ControlChanged (j:ℕ):Prop:=j=3301∨j=4177∨j=4178∨j=4179∨(2850≤j∧j<2877)
structure ControlFrame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬ControlChanged j→u.natReg j=s.natReg j
lemma fields_dispatch {A:ℕ}{r:Record}{s u:State}(fields:Fields A r s)(frame:DispatchFrame s u):Fields A r u:=by
 constructor
 all_goals first
 | (intro j
    have ne:UniformFixedNetworkOpcodeMachine.thresholdRegister j.val≠4177:=by
     unfold UniformFixedNetworkOpcodeMachine.thresholdRegister;split_ifs <;> omega
    exact (frame.natReg _ ne).trans (fields.threshold j))
 | exact (frame.natReg _ (by omega)).trans (by first | exact fields.cursor | exact fields.opcode | exact fields.columns | exact fields.width | exact fields.dest | exact fields.source | exact fields.inverse | exact fields.dimension | exact fields.scalar | exact fields.one | exact fields.eight | exact fields.four | exact fields.zero)

/-- Continuous physical loop, raw header read, and decoded dispatch in one
Program. The syntactic link premises are discharged by the actual caller. -/
theorem read_dispatch_generic (main:Program)(loop reader dispatch finish work A tapeEnd B n:ℕ)
 (target:Fin 7→ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (loopCode:BlockAt loopBlock main loop)
 (loopBranch:main[loop+3]?=some (.branchLT 2850 3301 reader finish))
 (headLink:CodeAt UniformFixedNetworkOpcodeMachine.headProgram main reader dispatch)
 (dispatchLink:DispatchAt main dispatch target)
 (pc:s.pc=loop)(workHeader:s.natReg 4123=work)(ptr:s.natReg 2850=A)(one:s.natReg 4153=1)
 (metadata:s.natHeap (work-1)=some tapeEnd)(live:A<tapeEnd)
 (bank:Printed A r.data s)(good:WellFormed r)(bound:WordBound B s)
 (dataEnd:A+r.data.length≤B)(width:r.width+1≤B)
 (loopBound:loop+4≤B)(readerBound:reader+UniformFixedNetworkOpcodeMachine.headProgram.length≤B)
 (dispatchBound:dispatch+12≤B)(finishBound:finish≤B)(targetBound:∀j,target j≤B):∃u,
 BoundedRuns main n x B s (4+headCost r+dispatchCost r.opcode) u ∧
 u.pc=target ⟨r.opcode,good.1⟩ ∧ Fields A r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=A+r.data.length ∧ ControlFrame s u:=by
 have rb:reader≤B:=(Nat.le_add_right _ _).trans readerBound
 have db:dispatch≤B:=(Nat.le_add_right _ _).trans dispatchBound
 obtain ⟨a,first,ap,cursor,_,lf⟩:=loop_generic main loop reader finish n B work A tapeEnd x s loopCode loopBranch
  pc workHeader ptr metadata bound loopBound rb finishBound
 have atReader:a.pc=reader:=by simpa only [live,ite_true] using ap
 have printed:Printed A r.data a:=by intro j hj;rw [lf.natHeap];exact bank j hj
 obtain ⟨b,head,bp,fields,body,nextval,hf⟩:=reader_generic main reader dispatch A B n r x a headLink atReader cursor
  first.final_bound printed good dataEnd width readerBound db
 have ao:a.natReg 4153=1:=(lf.natReg _ (by omega) (by omega) (by omega)).trans one
 have bo:b.natReg 4153=1:=(hf.natReg _ (by omega)).trans ao
 obtain ⟨u,last,up,df⟩:=dispatch_generic main dispatch n B r.opcode target x b dispatchLink bp fields.opcode bo good.1
  head.final_bound dispatchBound targetBound
 refine ⟨u,(first.trans head).trans last,up,fields_dispatch fields df,?_,?_,?_⟩
 · exact (df.natReg _ (by omega)).trans body
 · exact (df.natReg _ (by omega)).trans nextval
 · refine ⟨df.natHeap.trans (hf.natHeap.trans lf.natHeap),df.scalarHeap.trans (hf.scalarHeap.trans lf.scalarHeap),
   df.scalarReg.trans (hf.scalarReg.trans lf.scalarReg),df.outputs.trans (hf.outputs.trans lf.outputs),
   df.roots.trans (hf.roots.trans lf.roots),?_⟩
   intro j hj
   unfold ControlChanged at hj
   exact (df.natReg j (by omega)).trans ((hf.natReg j (by omega)).trans (lf.natReg j (by omega) (by omega) (by omega)))

/-- Actual caller discharges all syntactic links for the unchanged common
recursive Program. Entry information is only raw headers/bank and bounds. -/
theorem read_dispatch_execution (work A tapeEnd B n:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .loop)(workHeader:s.natReg 4123=work)(ptr:s.natReg 2850=A)(one:s.natReg 4153=1)
 (metadata:s.natHeap (work-1)=some tapeEnd)(live:A<tapeEnd)
 (bank:Printed A r.data s)(good:WellFormed r)(bound:WordBound B s)
 (dataEnd:A+r.data.length≤B)(width:r.width+1≤B)(code:P.program.length≤B):∃u,
 BoundedRuns P.program n x B s (4+headCost r+dispatchCost r.opcode) u ∧
 u.pc=targets ⟨r.opcode,good.1⟩ ∧ Fields A r u ∧
 u.natReg 2864=r.directions.length ∧ u.natReg 2865=A+r.data.length ∧ ControlFrame s u:=by
 exact read_dispatch_generic P.program (P.address .loop) (P.address .reader) (P.address .dispatch)
  (P.address .spectatorSetup) work A tapeEnd B n targets r x s loop_code loop_branch reader_code dispatch_code
  pc workHeader ptr one metadata live bank good bound dataEnd width
  (R.code_bound .loop 4 B rfl code) (R.code_bound .reader UniformFixedNetworkOpcodeMachine.headProgram.length B rfl code)
  (R.code_bound .dispatch 12 B rfl code) (R.start_bound .spectatorSetup B code) (targets_bound B code)

end
end ExactFourierCircuits.UniformRecursiveRecordControl
