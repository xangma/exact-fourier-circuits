import UniformBoundaryDiagonalSlotOutside
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBoundaryDiagonalOutside
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC applyBlock_pc)
open UniformBoundaryDiagonalMachine
open UniformPairMachine (prepared)
noncomputable section

structure CoreResultOutside (n B r time pool arena:ℕ)(positive:2≤r)(q:Fin 3)(omega:ℂ)
 (x:Fin n→ℂ)(s u:State):Prop extends CoreResult n B r time pool arena positive q omega x s u where
 natOutside:∀j,(j<arena∨arena+3*r+11≤j)→u.natHeap j=s.natHeap j

theorem execution_outside {n B seedCell seed r time pool arena:ℕ}(q:Fin 3)(omega:ℂ)
 (x:Fin n→ℂ)(s:State)(args:Args seedCell q.val time pool arena s)
 (address:s.natHeap seedCell=some seed)(width:s.natHeap (seedCell+1)=some r)
 (original:UniformLocalSeedTableMachine.Compact r seed omega s)
 (positive:2≤r)(sourceBelow:seed+5*r≤pool)(sourceFit:seedCell+2≤B)
 (natFit:arena+3*r+11≤B)(poolFit:pool+9*r≤B)(code:127≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,CoreResultOutside n B r time pool arena positive q omega x s u:=by
 obtain ⟨p,pRun,pp,pHead,pOnes,pOutside,pNat,pFrame⟩:=
  prefix_execution x s args address width sourceFit poolFit code pc wb
 have originalP:UniformLocalSeedTableMachine.Compact r seed omega p:=by
  intro lane j
  have fit:lane.val*r+j.val<5*r:=by
   have mul:=Nat.mul_le_mul_right r (show lane.val+1≤5 by have:=lane.isLt;omega)
   have:=j.isLt;nlinarith
  exact (pOutside _ (Or.inl (by omega))).trans (original lane j)
 obtain ⟨v,vRun,vp,vHead,copied,vOutside,vNat,vFrame⟩:=
  copy_execution q omega x p pHead originalP sourceBelow poolFit code pp pRun.final_bound
 obtain ⟨u,uRun,up,entry,row,widths,perm,heap,regs,outputs,roots,nat,headers⟩:=
  slot_execution_outside x v vHead positive natFit code vp vRun.final_bound
 refine ⟨u,⟨?_,up,entry,row,widths,perm,?_,?_,?_,?_,
  pFrame.trans (vFrame.trans ⟨outputs,roots,fun j _ _=>congrFun regs j⟩),headers⟩,?_⟩
 · convert pRun.executes (vRun.executes uRun) using 1;omega
 · intro j;exact (congrFun heap _).trans (copied j)
 · intro lane nonzero j
   have lower:pool+r≤pool+lane.val*r+j.val:=by
    have mul:=Nat.mul_le_mul_right r (show 1≤lane.val by omega);omega
   have upper:lane.val*r+j.val<9*r:=by
    have mul:=Nat.mul_le_mul_right r (show lane.val+1≤9 by have:=lane.isLt;omega)
    have:=j.isLt;nlinarith
   exact (congrFun heap _).trans ((vOutside _ (Or.inr lower)).trans (by simpa only[Nat.add_assoc] using pOnes _ upper))
 · intro j hj;exact (nat j (Or.inl hj)).trans ((congrFun vNat j).trans (congrFun pNat j))
 · intro j outside;exact (congrFun heap j).trans ((vOutside j (by omega)).trans (pOutside j outside))
 · intro j hj;exact (nat j hj).trans ((congrFun vNat j).trans (congrFun pNat j))

end
end ExactFourierCircuits.UniformBoundaryDiagonalOutside
