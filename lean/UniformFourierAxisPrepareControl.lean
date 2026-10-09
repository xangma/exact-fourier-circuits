import UniformFourierAxisPrepareMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareControl
open UniformMachine UniformNatBlockMachine
namespace P
export UniformFourierAxisPrepareMachine (program code_138 code_139 code_140 code_141 footer_code halt_at)
end P
namespace F
export UniformFourierAxisPrepareFooter (block block_length Args Result)
end F
noncomputable section

structure Frame (writes:List Nat)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j ∉ writes → u.natReg j=s.natReg j

def decisionState (mode:Nat)(s:State):State :=
 if mode=0 then {writeNat s 7081 1 with pc:=142}
 else {writeNat {writeNat s 7081 1 with pc:=140} 7081 2 with pc:=if mode=1 then 232 else 370}

def decisionTicks (mode:Nat):Nat := if mode=0 then 2 else 4

def decisionTarget (mode:Nat):Nat := if mode=0 then 142 else if mode=1 then 232 else 370

lemma decision_frame (mode:Nat)(s:State):Frame [7081] s (decisionState mode s):=by
 unfold decisionState
 split_ifs <;> refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 all_goals intro j away
 all_goals have ne:j ≠ 7081:=by simpa using away
 all_goals simp [writeNat,next,ne]

/-- Actual PCs138..141, with every literal and branch charged. -/
theorem decision_execution (n B mode:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=138)(value:s.natReg 7080=mode)(bound:WordBound B s)(code:389 ≤ B):
 BoundedRuns P.program n x B s (decisionTicks mode) (decisionState mode s):=by
 let a:=writeNat s 7081 1
 have ab:WordBound B a:=writeNat_bound B s 7081 1 bound (by omega) (by omega)
 have enter:step P.program n x s=.running a:=by simp [step,pc,P.code_138,a]
 by_cases zero:mode=0
 · have branch:step P.program n x a=.running {a with pc:=142}:=by
    simp [step,a,writeNat,next,pc,P.code_139,value,zero]
   have stop:WordBound B {a with pc:=142}:=changePC_bound B a 142 ab (by omega)
   simpa only [decisionTicks,decisionState,ite_eq_left zero,a] using
    (BoundedRuns.next bound enter (BoundedRuns.next ab branch (BoundedRuns.refl stop)))
 · let b:State:={a with pc:=140}
   have bb:WordBound B b:=changePC_bound B a 140 ab (by omega)
   have branch:step P.program n x a=.running b:=by
    simp [step,a,b,writeNat,next,pc,P.code_139,value,show ¬mode < 1 by omega]
   let c:=writeNat b 7081 2
   have cb:WordBound B c:=writeNat_bound B b 7081 2 bb (by change 141 ≤ B; omega) (by omega)
   have literal:step P.program n x b=.running c:=by simp [step,b,P.code_140,c]
   let u:State:={c with pc:=if mode=1 then 232 else 370}
   have ub:WordBound B u:=changePC_bound B c _ cb (by split_ifs <;> omega)
   have final:step P.program n x c=.running u:=by
    by_cases one:mode=1
    · simp [step,c,b,a,u,writeNat,next,pc,P.code_141,value,one]
    · simp [step,c,b,a,u,writeNat,next,pc,P.code_141,value,one,show ¬mode < 2 by omega]
   simpa only [decisionTicks,decisionState,ite_eq_right zero,a,b,c,u] using
    (BoundedRuns.next bound enter (BoundedRuns.next ab branch
     (BoundedRuns.next bb literal (BoundedRuns.next cb final (BoundedRuns.refl ub)))))

lemma decision_pc (mode:Nat)(s:State):(decisionState mode s).pc=decisionTarget mode:=by
 simp [decisionState,decisionTarget];split_ifs <;> rfl
lemma decision_mode (mode:Nat)(s:State):
 (decisionState mode s).natReg 7080=s.natReg 7080:=
 (decision_frame mode s).natReg 7080 (by decide)

lemma decision_selected {d g mode:Nat}{s:State}(selected:UniformEpochSelectorMachine.Selected d g s):
 UniformEpochSelectorMachine.Selected d g (decisionState mode s):=by
 have f:=decision_frame mode s
 have a:=f.natReg 7080 (by decide)
 have b:=f.natReg 7001 (by decide)
 have c:=f.natReg 6703 (by decide)
 have e:=f.natReg 6702 (by decide)
 have h:=f.natReg 6705 (by decide)
 simpa only [UniformEpochSelectorMachine.Selected,a,b,c,e,h] using selected

lemma decision_workspace {r N S mode:Nat}{s:State}
 (header:UniformFourierAxisWorkspaceHeader.Header r N S s):
 UniformFourierAxisWorkspaceHeader.Header r N S (decisionState mode s):=by
 have f:=decision_frame mode s
 constructor
 · exact (f.natReg 7050 (by decide)).trans header.selected
 · exact (f.natReg 7051 (by decide)).trans header.boundary
 · exact (f.natReg 7052 (by decide)).trans header.phase
 · exact (f.natReg 7053 (by decide)).trans header.rows
 · exact (f.natReg 7054 (by decide)).trans header.permutation
 · exact (f.natReg 7055 (by decide)).trans header.widths
 · exact (f.natReg 7056 (by decide)).trans header.markers
 · exact (f.natReg 7057 (by decide)).trans header.pool
 · exact (f.natReg 7058 (by decide)).trans header.endNat
 · exact (f.natReg 7059 (by decide)).trans header.endScalar
 · exact (f.natReg 5934 (by decide)).trans header.nextNat
 · exact (f.natReg 5935 (by decide)).trans header.nextScalar

def footerWrites:List Nat :=
 [7065,7067,6766,6767,6768,6769,6770,6772,5926,5927,5928,5929,5930,6801,6802,5934,5935]

lemma footer_frame (s:State):Frame footerWrites s (applyBlock F.block s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j away
 simp [footerWrites] at away
 simp (disch:=omega) [UniformFourierAxisPrepareFooter.block,applyBlock,Op.apply,evalNat,writeNat,next]

lemma block_pc (b:List Op)(s:State):(applyBlock b s).pc=s.pc+b.length:=by
 induction b generalizing s with
 | nil => rfl
 | cons o b ih => rw [applyBlock,ih,Op.apply_pc,List.length_cons];omega

/-- Actual common footer370..387 followed by the genuine halt388. -/
theorem footer_execution (n B r N S count j physical directory cacheN cacheS:Nat)
 (x:Fin n→ℂ)(s:State)(args:F.Args r N S count j physical directory cacheN cacheS s)
 (pc:s.pc=370)(bound:WordBound B s)(code:389 ≤ B)(physicalFit:physical+4*j ≤ B):
 BoundedExecution P.program n x B s 19 (applyBlock F.block s) ∧
 F.Result r N S count j physical directory cacheN cacheS (applyBlock F.block s) ∧
 Frame footerWrites s (applyBlock F.block s):=by
 obtain ⟨run,result⟩:=UniformFourierAxisPrepareFooter.execution P.program x s args P.footer_code pc
  (by omega) (by omega) physicalFit bound
 have stopPc:(applyBlock F.block s).pc=388:=by rw [block_pc,pc,F.block_length]
 have stop:step P.program n x (applyBlock F.block s)=.halted (applyBlock F.block s):=by
  simp [step,stopPc,P.halt_at]
 exact ⟨run.executes (.halt run.final_bound stop),result,footer_frame s⟩

lemma footer_selected {d g:Nat}{s:State}(selected:UniformEpochSelectorMachine.Selected d g s):
 UniformEpochSelectorMachine.Selected d g (applyBlock F.block s):=by
 have f:=footer_frame s
 have a:=f.natReg 7080 (by decide)
 have b:=f.natReg 7001 (by decide)
 have c:=f.natReg 6703 (by decide)
 have e:=f.natReg 6702 (by decide)
 have h:=f.natReg 6705 (by decide)
 simpa only [UniformEpochSelectorMachine.Selected,a,b,c,e,h] using selected

lemma footer_workspace {r N S count j physical directory cacheN cacheS:Nat}{s:State}
 (args:F.Args r N S count j physical directory cacheN cacheS s):
 UniformFourierAxisWorkspaceHeader.Header r N S (applyBlock F.block s):=by
 have f:=footer_frame s
 have result:=UniformFourierAxisPrepareFooter.values args
 constructor
 · exact (f.natReg 7050 (by decide)).trans args.workspace.selected
 · exact (f.natReg 7051 (by decide)).trans args.workspace.boundary
 · exact (f.natReg 7052 (by decide)).trans args.workspace.phase
 · exact (f.natReg 7053 (by decide)).trans args.workspace.rows
 · exact (f.natReg 7054 (by decide)).trans args.workspace.permutation
 · exact (f.natReg 7055 (by decide)).trans args.workspace.widths
 · exact (f.natReg 7056 (by decide)).trans args.workspace.markers
 · exact (f.natReg 7057 (by decide)).trans args.workspace.pool
 · exact (f.natReg 7058 (by decide)).trans args.workspace.endNat
 · exact (f.natReg 7059 (by decide)).trans args.workspace.endScalar
 · exact result.nextNat
 · exact result.nextScalar

end
end ExactFourierCircuits.UniformFourierAxisPrepareControl
