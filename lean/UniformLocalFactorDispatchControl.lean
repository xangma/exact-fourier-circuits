import UniformLocalFactorDispatchResult
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFactorDispatchMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
def target (slot:Slot):ℕ:=if slot.broadcast then 439 else if slot.inverse then 680 else 9
def branches (slot:Slot):ℕ:=if slot.broadcast then 1 else 2
lemma select {n B:ℕ} (slot:Slot) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=7) (zero:s.natReg 6210=0)
 (broadcast:s.natReg 6213=UniformLocalReplaySlotMachine.bit slot.broadcast)
 (inverse:s.natReg 6214=UniformLocalReplaySlotMachine.bit slot.inverse)
 (wb:WordBound B s) (code:1156≤B):
 BoundedRuns program n x B s (branches slot) (setPC s (target slot)) := by
 cases hb:slot.broadcast with
 | true=>
  have bound:=changePC_bound B s 439 wb (by omega)
  have first:BoundedRuns program n x B s 1 (setPC s 439):=.next wb (by simp [step,pc,broadcast_branch,zero,broadcast,hb,
   UniformLocalReplaySlotMachine.bit,setPC]) (.refl bound)
  simpa only [branches,target,hb,ite_true] using first
 | false=>
  let a:=setPC s 8
  have ab:=changePC_bound B s 8 wb (by omega)
  have first:BoundedRuns program n x B s 1 a:=.next wb
   (by simp [step,pc,broadcast_branch,zero,broadcast,hb,UniformLocalReplaySlotMachine.bit,a,setPC]) (.refl ab)
  cases hi:slot.inverse with
  | true=>
   have bound:=changePC_bound B s 680 wb (by omega)
   have second:BoundedRuns program n x B a 1 (setPC s 680):=.next ab
    (by simp [step,a,setPC,inverse_branch,zero,inverse,hi,UniformLocalReplaySlotMachine.bit]) (.refl bound)
   simpa only [branches,target,hb,hi,Bool.false_eq_true,ite_false,ite_true] using first.trans second
  | false=>
   have bound:=changePC_bound B s 9 wb (by omega)
   have second:BoundedRuns program n x B a 1 (setPC s 9):=.next ab
    (by simp [step,a,setPC,inverse_branch,zero,inverse,hi,UniformLocalReplaySlotMachine.bit]) (.refl bound)
   simpa only [branches,target,hb,hi,Bool.false_eq_true,ite_false] using first.trans second
lemma finish {p:Program} {base n B ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:CodeAt p program base 1155) (length:base+p.length≤B) (bound:1156≤B)
 (run:BoundedExecution p n x B s ticks u):
 BoundedExecution program n x B (placed base s) (ticks+1) (setPC u 1155) := by
 have moved:=UniformBoundedAssembly.boundedExecution_placed code length (by omega) run
 have stop:BoundedExecution program n x B (setPC u 1155) 1 (setPC u 1155):=
  .halt moved.final_bound (by simp [step,setPC,halt_at])
 exact moved.executes stop
lemma inverseSetup_safe {s:State} {B:ℕ} (zero:s.natReg 6210=0) (wb:WordBound B s):
 readable inverseSetup s ∧peak inverseSetup s≤B := by
 have bound:=wb.2.1 4460
 simpa [inverseSetup,readable,peak,Op.readable,Op.peak,zero] using bound
lemma inverseSetup_nat (s:State) (q:ℕ) (ne:q≠5847):
 (applyBlock inverseSetup s).natReg q=s.natReg q := by
 simp [inverseSetup,applyBlock,Op.apply,writeNat,next,ne]
lemma prepared_rowBase {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State}
 (h:H.Prepared c q slot s):s.natReg 5847=c.translated := h.2.2.2.2.2.2.2.2.2.1
lemma final_saved {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u):
 (∀ (i : ℕ), 100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧
 (∀ (i : ℕ), 6100 ≤ i → i < 6210 ∨ 6214 < i → u.natReg i=s.natReg i):=by
 constructor
 · intro i lo hi;exact execution_nat run (Or.inl ⟨lo,hi⟩) (by omega) (by omega) (by intro j a b;omega)
 · intro i lo hi;exact execution_nat run (Or.inr (by omega)) (by omega) (by omega) (by intro j a b;omega)
lemma final_cacheHeaders {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u):
 ∀ (i : ℕ), 5840 ≤ i → i ≤ 5849 → i≠5847 → u.natReg i=s.natReg i := by
 intro i lo hi ne
 exact execution_nat run (Or.inr (by omega)) (by omega) ne (by intro j a b;omega)
end
end ExactFourierCircuits.UniformLocalFactorDispatchMachine
