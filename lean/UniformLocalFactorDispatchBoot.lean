import UniformLocalFactorDispatchMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFactorDispatchMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace H
abbrev Parameters:=UniformLocalCacheSlotHeaderMachine.Parameters
abbrev Prepared:=UniformLocalCacheSlotHeaderMachine.Prepared
abbrev forward:=UniformLocalCacheSlotHeaderMachine.forward
end H
abbrev Rectangle:=UniformLocalRectangleDescriptors.Row
abbrev Slot:=UniformLocalCacheChronology.Slot
noncomputable section
lemma forward_translated (c:H.Parameters) (q:Rectangle) (slot:Slot):
 (H.forward c q slot).translated=c.translated := rfl
lemma boot_heaps (s:State):(applyBlock boot s).natHeap=s.natHeap ∧
 (applyBlock boot s).scalarHeap=s.scalarHeap ∧(applyBlock boot s).scalarReg=s.scalarReg ∧
 (applyBlock boot s).outputs=s.outputs ∧(applyBlock boot s).rootOrders=s.rootOrders :=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma boot_nat (s:State) (q:ℕ) (hz:q≠4460) (hs:q<6210 ∨6214<q):
 (applyBlock boot s).natReg q=s.natReg q := by
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_zero (s:State):(applyBlock boot s).natReg 6210=0 := by
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_inverse (s:State):(applyBlock boot s).natReg 4460=s.natReg 6200 := by
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_flags {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State}
 (args:H.Prepared c q slot s)
 (source:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s) :
 (applyBlock boot s).natReg 6213=UniformLocalReplaySlotMachine.bit slot.broadcast ∧
 (applyBlock boot s).natReg 6214=UniformLocalReplaySlotMachine.bit slot.inverse := by
 have addr:s.natReg 4421=c.slot:=args.1.slot
 have h0:s.natHeap c.slot=some (UniformLocalReplaySlotMachine.bit slot.broadcast):=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using source ⟨0,by decide⟩
 have h2:s.natHeap (c.slot+2)=some (UniformLocalReplaySlotMachine.bit slot.inverse):=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using source ⟨2,by decide⟩
 simp [boot,applyBlock,Op.apply,writeNat,next,addr,Nat.add_assoc,h0,h2]
lemma boot_safe {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State} {B:ℕ}
 (args:H.Prepared c q slot s)
 (source:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (slotEnd:c.slot+2≤B) (_code:1156≤B) (wb:WordBound B s):readable boot s ∧peak boot s≤B := by
 have addr:s.natReg 4421=c.slot:=args.1.slot
 have h0:s.natHeap c.slot=some (UniformLocalReplaySlotMachine.bit slot.broadcast):=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using source ⟨0,by decide⟩
 have h2:s.natHeap (c.slot+2)=some (UniformLocalReplaySlotMachine.bit slot.inverse):=by
  simpa [UniformLocalReplaySlotMachine.Slot.words] using source ⟨2,by decide⟩
 have a:=wb.2.1 6200
 have b:=(wb.2.2.1 _ _ h0).2
 have d:=(wb.2.2.1 _ _ h2).2
 constructor
 · simp [boot,readable,Op.readable,Op.apply,writeNat,next,addr,Nat.add_assoc,h0,h2]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,addr,Nat.add_assoc,h0,h2]
   omega

lemma forwardArgs_transport {c:UniformForwardMatchingFactorPreparation.Config} {s u:State}
 (h:UniformForwardMatchingFactorHeaderPreparation.Args c s)
 (eq:∀j : ℕ, 4410≤j → j≤4452 → u.natReg j=s.natReg j):
 UniformForwardMatchingFactorHeaderPreparation.Args c u := by
 rcases h with ⟨height,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19⟩
 constructor
 · rcases height with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩
   constructor <;>rw [eq _ (by omega) (by omega)] <;>assumption
 all_goals rwa [eq _ (by omega) (by omega)]
lemma prepared_nat {c:H.Parameters} {q:Rectangle} {slot:Slot} {s u:State}
 (h:H.Prepared c q slot s)
 (eq:∀j : ℕ, (j≤4452 ∨(5840≤j ∧j≤5849)) → u.natReg j=s.natReg j):
 H.Prepared c q slot u := by
 refine ⟨forwardArgs_transport h.1 (fun j _ hi=>eq j (Or.inl hi)),
  UniformLocalBroadcastPoolMachine.Args.transport h.2.1 ?_,?_⟩
 · intro j member
   apply eq j (Or.inl ?_)
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>omega
 · rcases h.2.2 with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
   repeat' apply And.intro
   all_goals rwa [eq _ (Or.inr (by omega))]
lemma boot_prepared {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State}
 (h:H.Prepared c q slot s) (pc:ℕ):H.Prepared c q slot (setPC (applyBlock boot s) pc) := by
 apply prepared_nat h
 intro j hj
 exact boot_nat s j (by omega) (Or.inl (by omega))
lemma forward_slot {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State}
 (source:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (hb:slot.broadcast=false) (hi:slot.inverse=false):
 UniformForwardMatchingFactorPreparation.Slot c.slot (H.forward c q slot).chunk s := by
 have a:=source ⟨0,by decide⟩;have b:=source ⟨1,by decide⟩;have d:=source ⟨2,by decide⟩
 have e:=source ⟨3,by decide⟩;have f:=source ⟨4,by decide⟩
 change s.natHeap c.slot=some 0 ∧s.natHeap (c.slot+1)=some (if slot.enabled then 1 else 0) ∧
  s.natHeap (c.slot+2)=some 0 ∧s.natHeap (c.slot+3)=some slot.depth ∧s.natHeap (c.slot+4)=some slot.color
 refine ⟨?_,?_,?_,?_,?_⟩
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit,hb] using a
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit] using b
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit,hi] using d
 · simpa [UniformLocalReplaySlotMachine.Slot.words] using e
 · simpa [UniformLocalReplaySlotMachine.Slot.words] using f
lemma inverse_slot {c:H.Parameters} {q:Rectangle} {slot:Slot} {s:State}
 (source:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (hb:slot.broadcast=false) (hi:slot.inverse=true):
 UniformInverseMatchingFactorPreparation.Slot c.slot (H.forward c q slot).chunk s := by
 have a:=source ⟨0,by decide⟩;have b:=source ⟨1,by decide⟩;have d:=source ⟨2,by decide⟩
 have e:=source ⟨3,by decide⟩;have f:=source ⟨4,by decide⟩
 change s.natHeap c.slot=some 0 ∧s.natHeap (c.slot+1)=some (if slot.enabled then 1 else 0) ∧
  s.natHeap (c.slot+2)=some 1 ∧s.natHeap (c.slot+3)=some slot.depth ∧s.natHeap (c.slot+4)=some slot.color
 refine ⟨?_,?_,?_,?_,?_⟩
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit,hb] using a
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit] using b
 · simpa [UniformLocalReplaySlotMachine.Slot.words,UniformLocalReplaySlotMachine.bit,hi] using d
 · simpa [UniformLocalReplaySlotMachine.Slot.words] using e
 · simpa [UniformLocalReplaySlotMachine.Slot.words] using f
end
end ExactFourierCircuits.UniformLocalFactorDispatchMachine
