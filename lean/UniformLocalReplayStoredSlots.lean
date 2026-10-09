import UniformLocalReplayAssembly
import UniformLocalBroadcastPoolMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalReplayStoredSlots
open UniformMachine UniformLocalCacheChronology UniformLocalReplayAssembly

/-- A decoded ordinal is read from the actual five-word phase output. -/
theorem phase_slot {H A used j : ℕ} {b e i : Bool} {s : State}
 (table : UniformLocalReplaySlotMachine.Done H A b e i used s)
 (hj : j < used) (usedBound : used ≤ 11*UniformLocalReplaySlotMachine.levelCount H b) :
 UniformLocalBroadcastPoolMachine.SlotSource (A+5*j)
  (UniformLocalReplaySlotMachine.decodedSlot H b e i (j/11) (j%11)) s := by
 have hmod : j%11<11 := Nat.mod_lt j (by omega)
 have hdiv : j/11<UniformLocalReplaySlotMachine.levelCount H b := by omega
 intro f
 have h := table ⟨j/11,hdiv⟩ ⟨j%11,hmod⟩ (by change 11*(j/11)+j%11<used;omega) f
 simpa only [Fin.val_mk,show 11*(j/11)+j%11=j by omega,
  UniformLocalReplaySlotMachine.Slot.words] using h

/-- Exact integer cover of the physically printed phase prefixes. -/
theorem phase_cover (H k j : ℕ) (hk : k ≤ 6) (hj : j < 11*phasePrefix H k) :
 ∃p : Fin 6, p.val<k ∧ 11*phasePrefix H p.val ≤ j ∧
  j<11*(phasePrefix H p.val+levels H p) := by
 induction k with
 | zero => simp only [phasePrefix] at hj;omega
 | succ k ih =>
   have kl : k<6 := by omega
   rw [prefix_next H ⟨k,kl⟩] at hj
   by_cases earlier : j<11*phasePrefix H k
   · obtain ⟨p,hp,lo,hi⟩ := ih (by omega) earlier
     exact ⟨p,by omega,lo,hi⟩
   · refine ⟨⟨k,kl⟩,?_,?_,?_⟩
     · change k<k+1;omega
     · change 11*phasePrefix H k≤j;omega
     · change j<11*(phasePrefix H k+levels H ⟨k,kl⟩)
       exact hj

/-- Every integer slot cursor in the genuine six-phase bank has a physical
record, with its exact phase/level/color decoder. No initialized slot table is
supplied separately. -/
theorem generated_slot {K A j : ℕ} {s : State}
 (table : Generated K A 6 s) (hj : j<11*phasePrefix (8*K+6) 6) :
 ∃p : Fin 6, ∃t : ℕ,
  j=11*phasePrefix (8*K+6) p.val+t ∧ t<11*levels (8*K+6) p ∧
  UniformLocalBroadcastPoolMachine.SlotSource (A+5*j)
   (UniformLocalReplaySlotMachine.decodedSlot (8*K+6) (flags p).broadcast
     (flags p).enabled (flags p).inverse (t/11) (t%11)) s := by
 obtain ⟨p,hp,lo,hi⟩ := phase_cover (8*K+6) 6 j (by omega) hj
 let t := j-11*phasePrefix (8*K+6) p.val
 have jt : j=11*phasePrefix (8*K+6) p.val+t := by dsimp [t];omega
 have tl : t<11*levels (8*K+6) p := by omega
 have source := phase_slot (table p hp) tl (le_refl _)
 refine ⟨p,t,jt,tl,?_⟩
 convert source using 1
 simp only [jt]
 ring

lemma slot_count (K : ℕ) : 11*phasePrefix (8*K+6) 6=352*K+330 := by
 rw [prefix_total];ring

lemma chronology_count (K : ℕ) : (replaySlots (8*K+6)).length=352*K+330 := by
 rw [replaySlots_length];ring

end ExactFourierCircuits.UniformLocalReplayStoredSlots
