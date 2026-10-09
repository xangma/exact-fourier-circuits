import UniformDirectLeafCacheSetup
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheScale
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheProgram UniformDirectLeafCacheSetup
open UniformPairMachine (prepared)
open UniformTransposeDescriptorMachine (Record)
noncomputable section

def Value (mu : ℂ) (d lane j : ℕ) : ℂ := if lane=0 ∧ j=d then mu else 1
def Table (pool r d : ℕ) (mu : ℂ) (s : State) : Prop :=
 ∀lane:Fin 9,∀j:Fin r,s.scalarHeap (pool+lane.val*r+j.val)=some (prepared (Value mu d lane.val j.val))
lemma scale_heap {c : Config} {r A C : ℕ} {q : Record} {mu : ℂ} {s : State}
 (args:Args c s) (h:Read r A C q s) (src:s.scalarHeap q.coefficient=some (prepared mu)) :
 (applyBlock scale s).scalarHeap=Function.update s.scalarHeap (c.pool+q.dest) (some (prepared mu)) := by
 simp [scale,applyBlock,Op.apply,writeNat,writeScalar,next,args.pool,h.dest,h.coefficient,src]
lemma scale_values {c : Config} {r A C : ℕ} {q : Record} {mu : ℂ} {s : State}
 (args:Args c s) (h:Read r A C q s) (src:s.scalarHeap q.coefficient=some (prepared mu))
 (ones:UniformGlobalScalePoolMachine.Prefix c.pool (9*r) s) (dest:q.dest<r) :
 Table c.pool r q.dest mu (applyBlock scale s) := by
 intro lane j
 rw [scale_heap args h src]
 by_cases eq:lane.val*r+j.val=q.dest
 · have lz:lane.val=0:=by
    by_contra ne
    have pos:1≤lane.val:=by omega
    nlinarith
   have jd:j.val=q.dest:=by simpa [lz] using eq
   simp [Value,lz,jd]
 · rw [Function.update_of_ne (by omega)]
   have off:lane.val*r+j.val<9*r:=by have:=lane.isLt;have:=j.isLt;nlinarith
   have val:=ones (lane.val*r+j.val) off
   simpa only [Nat.add_assoc,Value,show ¬(lane.val=0∧j.val=q.dest) by rintro ⟨h0,h1⟩;simp_all,ite_false] using val
lemma scale_safe {c : Config} {r A C B : ℕ} {q : Record} {mu : ℂ} {s : State}
 (args:Args c s) (h:Read r A C q s) (src:s.scalarHeap q.coefficient=some (prepared mu))
 (dest:q.dest<r) (pool:c.pool+r≤B) (_coefficient:q.coefficient≤B) (code:264≤B) :
 readable scale s ∧peak scale s≤B := by
 constructor
 · simp [scale,readable,Op.readable,h.coefficient,src]
 · simp [scale,peak,Op.peak,Op.apply,writeNat,writeScalar,next,h.coefficient,args.pool,h.dest];omega
lemma scale_frames (s:State) : (applyBlock scale s).natHeap=s.natHeap ∧
 (applyBlock scale s).outputs=s.outputs ∧(applyBlock scale s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl⟩
lemma scale_other {c : Config} {r A C : ℕ} {q : Record} {mu : ℂ} {s : State}
 (args:Args c s) (h:Read r A C q s) (src:s.scalarHeap q.coefficient=some (prepared mu))
 (j:ℕ) (outside:j<c.pool∨c.pool+9*r≤j) (dest:q.dest<r) :
 (applyBlock scale s).scalarHeap j=s.scalarHeap j := by
 rw[scale_heap args h src]
 exact Function.update_of_ne (by omega) _ _
lemma scale_nat (s:State) (j:ℕ) (h0:j≠6650) (h1:j≠894) (h2:j≠5849) :
 (applyBlock scale s).natReg j=s.natReg j := by
 simp [scale,applyBlock,Op.apply,writeNat,writeScalar,next,h0,h1,h2]
lemma scale_core {c:Config} {r:ℕ} {s:State} (h:Core c r s) : Core c r (applyBlock scale s) := by
 exact ⟨(scale_nat s _ (by omega) (by omega) (by omega)).trans h.time,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.radix,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.pool,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.permutation,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.widths,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.markers,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.axis,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.rows,
  (scale_nat s _ (by omega) (by omega) (by omega)).trans h.directory⟩
lemma scale_directory {c:Config} {r:ℕ} {s:State} (h:Core c r s) :
 UniformLocalMatchingSlotDirectory.Args c.time r c.pool c.permutation c.widths c.markers
 c.axis c.rows c.entry 1 0 (applyBlock scale s) := by
 have core:=scale_core h
 exact ⟨core.time,core.radix,core.pool,core.permutation,core.widths,core.markers,core.axis,
  core.rows,core.directory,by simp[scale,applyBlock,Op.apply,writeNat,writeScalar,next],
  by simp[scale,applyBlock,Op.apply,writeNat,writeScalar,next]⟩
end
end ExactFourierCircuits.UniformDirectLeafCacheScale
