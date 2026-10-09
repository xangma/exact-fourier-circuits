import UniformMatchingPhaseControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingPhaseControl
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalMatchingScaleMachine (Phase phases)
noncomputable section

lemma skipped_dispatch {n B i j:ℕ} (d k:Program) (x:Fin n→ℂ) (s:State)
 (hi:i<28) (hj:j < i) (pc:s.pc=3+4*j) (index:s.natReg 5942=i)
 (code:(controlFor d k).length≤B) (wb:WordBound B s):
 ∃u,BoundedRuns (controlFor d k) n x B s 2 u ∧u.pc=3+4*(j+1) ∧
 u.natReg 5942=i ∧u.natReg 5941=s.natReg 5941 ∧u.natHeap=s.natHeap ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let a:=writeNat s 5944 (j+1)
 let u:=setPC a (7+4*j)
 have bound:j<28:=by omega
 have c0:(controlFor d k)[3+4*j]?=some (.natLiteral 5944 (j+1)):=by
  have h:=dispatch_code d k j 0 bound (by omega)
  change (controlFor d k)[3+4*j+0]?=some (.natLiteral 5944 (j+1)) at h
  simpa only[Nat.add_zero] using h
 have c1:(controlFor d k)[4+4*j]?=some (.branchLT 5942 5944 (5+4*j) (7+4*j)):=by
  have h:=dispatch_code d k j 1 bound (by omega)
  change (controlFor d k)[3+4*j+1]?=some (.branchLT 5942 5944 (5+4*j) (7+4*j)) at h
  simpa only[show 3+4*j+1=4+4*j by omega] using h
 have big:119≤B:=by rw[control_length] at code;omega
 have ab:WordBound B a:=writeNat_bound B s 5944 (j+1) wb (by omega) (by omega)
 have ub:WordBound B u:=changePC_bound B a (7+4*j) ab (by omega)
 have ap:a.pc=4+4*j:=by simp only[a,writeNat,next,pc];omega
 refine ⟨u,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
 · refine .next wb ?_ (.next ab ?_ (.refl ub))
   · simp only[step,pc,c0];rfl
   · rw[step,ap,c1]
     simp[a,writeNat,index,show ¬i < j+1 by omega,u,setPC]
 · change 7+4*j=3+4*(j+1);omega
 · simp[u,a,writeNat,setPC,index]
 · simp[u,a,writeNat,setPC]

/-- Every preceding phase check is executed physically. The returned lane
and destination come from the genuine28-entry phase list, with no supplied
phase-kind table, cache callback or transform premise. -/
theorem seek (remaining:ℕ) {n B:ℕ} (d k:Program) (x:Fin n→ℂ):
 ∀i j s (hi:i<28),j ≤ i→i-j=remaining→s.pc=3+4*j→s.natReg 5942=i→
  (controlFor d k).length≤B→WordBound B s→
 ∃u,BoundedRuns (controlFor d k) n x B s (2*remaining+4) u ∧
 u.pc=destination diagonalPC (kernelPC d) (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 4582=lane (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 5942=i ∧u.natReg 5941=s.natReg 5941 ∧u.natHeap=s.natHeap ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 induction remaining with
 |zero=>
  intro i j s hi hj remaining pc index code wb
  have equal:j=i:=by omega
  subst j
  exact selected_dispatch d k x s hi pc index code wb
 |succ remaining ih=>
  intro i j s hi hj count pc index code wb
  have lt:j < i:=by omega
  obtain ⟨t,first,tp,ti,one,nat,scalar,regs,outs,roots⟩:=skipped_dispatch d k x s hi lt pc index code wb
  obtain ⟨u,rest,up,ul,ui,uone,unat,uscalar,uregs,uouts,uroots⟩:=
   ih i (j+1) t hi (by omega) (by omega) tp ti code first.final_bound
  refine ⟨u,?_,up,ul,ui,uone.trans one,unat.trans nat,uscalar.trans scalar,
   uregs.trans regs,uouts.trans outs,uroots.trans roots⟩
  convert first.trans rest using 1;omega

theorem dispatch_execution {n B i:ℕ} (d k:Program) (x:Fin n→ℂ) (s:State)
 (hi:i<28) (pc:s.pc=3) (index:s.natReg 5942=i)
 (code:(controlFor d k).length≤B) (wb:WordBound B s):
 ∃u,BoundedRuns (controlFor d k) n x B s (2*i+4) u ∧
 u.pc=destination diagonalPC (kernelPC d) (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 4582=lane (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 5942=i ∧u.natReg 5941=s.natReg 5941 ∧u.natHeap=s.natHeap ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=
 seek i d k x i 0 s hi (by omega) (by omega) (by simpa using pc) index code wb

end
end ExactFourierCircuits.UniformMatchingPhaseControl
