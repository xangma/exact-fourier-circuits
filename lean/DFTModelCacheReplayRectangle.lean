import DFTModelCacheReplayAssembly
import DFTModelCacheReplayTiming

set_option autoImplicit false

/-! A genuine rectangle Row7 produces its replay height, all six slot phases,
and exact native start times. No exponent, plan, duration or schedule is supplied.
Matching endpoints and scalar factors still require the separate layer producer. -/
namespace ExactFourierCircuits.DFTModelCacheReplayRectangle
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformWorkspacePlanner
open DFTModelCacheCalendar (Row7 rowExponent rowExponent_spec)
open DFTModelCacheReplaySlots (Slot5 Event annotate)
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section

abbrev Input : Ty := p w Row7
def height : Prog false w w :=
  DFTModelCacheReplaySlots.nat .add
    (DFTModelCacheReplaySlots.nat .mul (.atom (.lit 8)) (.atom .id)) (.atom (.lit 6))
def generated : Prog false Input (Ty.a Slot5) :=
  .comp (.atom .snd) (.comp rowExponent (.comp height DFTModelCacheReplayAssembly.program))
def prepare : Prog false Input DFTModelCacheReplaySlots.TimingInput :=
  .fork (.atom .fst) (.fork (.atom .snd) generated)
def program : Prog false Input (Ty.a Event) := .comp prepare annotate

theorem height_run (K : ℕ) : run height K=⟨8*K+6,9,max 8 (8*K+6),True⟩ := by
  simp [height,DFTModelCacheReplaySlots.nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]

attribute [local irreducible] height rowExponent DFTModelCacheReplayAssembly.program annotate

theorem generated_run (start : ℕ) (q : Row7.T) :
    run generated (start,q)=((run rowExponent q).pass (fun K=>
      (run height K).pass (fun H=>run DFTModelCacheReplayAssembly.program H))).pay 4 0 := by
  simp [generated,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] generated

theorem program_run (start : ℕ) (q : Row7.T) :
    run program (start,q)=((run generated (start,q)).pass
      (fun ss=>run annotate (start,(q,ss)))).pay 5 0 := by
  simp [program,prepare,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem generated_value (start : ℕ) (q : Row) :
    (run generated (start,rectangleEncode q)).val=
      ofList ((UniformLocalCacheChronology.replaySlots (8*exponent q.a q.e+6)).map
        DFTModelCacheReplaySlots.encode) := by
  rw [generated_run]
  change (run DFTModelCacheReplayAssembly.program
    (run height (run rowExponent (rectangleEncode q)).val).val).val=_
  rw [(rowExponent_spec q).1,height_run,DFTModelCacheReplayAssembly.program_value]

theorem generated_valid (start : ℕ) (q : Row) :
    (run generated (start,rectangleEncode q)).valid := by
  rw [generated_run]
  change (run rowExponent (rectangleEncode q)).valid ∧
    (run height (run rowExponent (rectangleEncode q)).val).valid ∧
    (run DFTModelCacheReplayAssembly.program
      (run height (run rowExponent (rectangleEncode q)).val).val).valid
  rw [height_run]
  exact ⟨(rowExponent_spec q).2.1,trivial,DFTModelCacheReplayAssembly.program_valid _⟩

theorem program_value (start : ℕ) (q : Row) :
    (run program (start,rectangleEncode q)).val=
      Tape.tab (352*exponent q.a q.e+330) (fun j=>
        (start+28*j,(0,(rectangleEncode q,
          (ofList ((UniformLocalCacheChronology.replaySlots (8*exponent q.a q.e+6)).map
            DFTModelCacheReplaySlots.encode)).look j Slot5.blank)))) := by
  rw [program_run]
  change (run annotate (start,(rectangleEncode q,(run generated (start,rectangleEncode q)).val))).val=_
  rw [DFTModelCacheReplaySlots.annotate_value,generated_value]
  congr 1
  simp [ofList,UniformLocalCacheChronology.replaySlots_length]
  omega

theorem program_valid (start : ℕ) (q : Row) :
    (run program (start,rectangleEncode q)).valid := by
  rw [program_run]
  change (run generated (start,rectangleEncode q)).valid ∧
    (run annotate (start,(rectangleEncode q,(run generated (start,rectangleEncode q)).val))).valid
  exact ⟨generated_valid start q,DFTModelCacheReplaySlots.annotate_valid _ _ _⟩

theorem program_work (start : ℕ) (q : Row) :
    (run program (start,rectangleEncode q)).work≤400000*(exponent q.a q.e+1) := by
  have exponentWork:=(rowExponent_spec q).2.2.1
  have phaseWork:=DFTModelCacheReplayAssembly.program_work (8*exponent q.a q.e+6)
  have annotated:=DFTModelCacheReplaySlots.annotate_work start (rectangleEncode q)
    (run generated (start,rectangleEncode q)).val
  have len:(run generated (start,rectangleEncode q)).val.len=352*exponent q.a q.e+330 := by
    rw [generated_value]
    simp [ofList,UniformLocalCacheChronology.replaySlots_length]
    omega
  rw [program_run]
  change (run generated (start,rectangleEncode q)).work+
    (run annotate (start,(rectangleEncode q,(run generated (start,rectangleEncode q)).val))).work+5≤_
  have gw:(run generated (start,rectangleEncode q)).work=
      (run rowExponent (rectangleEncode q)).work+9+
        (run DFTModelCacheReplayAssembly.program (8*exponent q.a q.e+6)).work+4 := by
    rw [generated_run]
    change (run rowExponent (rectangleEncode q)).work+
      ((run height (run rowExponent (rectangleEncode q)).val).work+
        (run DFTModelCacheReplayAssembly.program
          (run height (run rowExponent (rectangleEncode q)).val).val).work)+4=_
    rw [(rowExponent_spec q).1,height_run]
    dsimp only [Bill.work,Bill.val]
    omega
  rw [gw]
  rw [len] at annotated
  omega

theorem program_peak (start : ℕ) (q : Row) :
    (run program (start,rectangleEncode q)).peak ≤
      start+20000*(exponent q.a q.e+1)+4*(q.a+q.e)+2 := by
  have expPeak:=(rowExponent_spec q).2.2.2
  have phasePeak:=DFTModelCacheReplayAssembly.program_peak (8*exponent q.a q.e+6)
  have annotated:=DFTModelCacheReplaySlots.annotate_peak start (rectangleEncode q)
    (run generated (start,rectangleEncode q)).val
  have len:(run generated (start,rectangleEncode q)).val.len=352*exponent q.a q.e+330 := by
    rw [generated_value]
    simp [ofList,UniformLocalCacheChronology.replaySlots_length]
    omega
  rw [len] at annotated
  have gp:(run generated (start,rectangleEncode q)).peak≤
      4*(q.a+q.e)+2+66*(8*exponent q.a q.e+7)+8 := by
    rw [generated_run]
    change max (max (run rowExponent (rectangleEncode q)).peak
      (max (run height (run rowExponent (rectangleEncode q)).val).peak
        (run DFTModelCacheReplayAssembly.program
          (run height (run rowExponent (rectangleEncode q)).val).val).peak)) 0≤_
    rw [(rowExponent_spec q).1,height_run]
    dsimp only [Bill.peak,Bill.val]
    simp only [max_zero,max_le_iff]
    omega
  rw [program_run]
  change max (max (run generated (start,rectangleEncode q)).peak
    (run annotate (start,(rectangleEncode q,(run generated (start,rectangleEncode q)).val))).peak) 0≤_
  have first : (run generated (start,rectangleEncode q)).peak ≤
      start+20000*(exponent q.a q.e+1)+4*(q.a+q.e)+2 := gp.trans (by omega)
  have second : (run annotate
      (start,(rectangleEncode q,(run generated (start,rectangleEncode q)).val))).peak ≤
      start+20000*(exponent q.a q.e+1)+4*(q.a+q.e)+2 := annotated.trans (by omega)
  exact max_le (max_le first second) (Nat.zero_le _)

theorem program_lookup (start : ℕ) (q : Row) (j : ℕ)
    (hj:j<352*exponent q.a q.e+330) :
    (run program (start,rectangleEncode q)).val.look j Event.blank=
      (start+28*j,(0,(rectangleEncode q,DFTModelCacheReplaySlots.encode
        ((UniformLocalCacheChronology.replaySlots (8*exponent q.a q.e+6))[j]'(by
          rw [UniformLocalCacheChronology.replaySlots_length];omega))))) := by
  rw [program_value,Tape.look_of_lt _ _ hj]
  change (start+28*j,(0,(rectangleEncode q,
    (ofList ((UniformLocalCacheChronology.replaySlots (8*exponent q.a q.e+6)).map
      DFTModelCacheReplaySlots.encode)).look j Slot5.blank)))=_
  rw [DFTModelCacheTraversal.ofList_look,List.getElem?_map,
    List.getElem?_eq_getElem (by rw [UniformLocalCacheChronology.replaySlots_length];omega)]
  rfl

abbrev Output : Ty := p w (Ty.a Event)
def publish : Prog false (Ty.a Event) Output :=
  .fork (DFTModelCacheReplaySlots.nat .mul (.atom (.lit 28)) (.atom .len)) (.atom .id)
def withDuration : Prog false Input Output := .comp program publish

theorem publish_run (ss : Tape Event.T) :
    run publish ss=⟨(28*ss.len,ss),7,max 28 (28*ss.len),True⟩ := by
  simp [publish,DFTModelCacheReplaySlots.nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] program publish

theorem withDuration_value (start : ℕ) (q : Row) :
    (run withDuration (start,rectangleEncode q)).val=
      (rectangleDuration q,(run program (start,rectangleEncode q)).val) := by
  change (run publish (run program (start,rectangleEncode q)).val).val=_
  rw [publish_run]
  dsimp only [Bill.val]
  congr 1
  rw [program_value]
  change 28*(352*exponent q.a q.e+330)=rectangleDuration q
  unfold rectangleDuration
  omega

theorem withDuration_valid (start : ℕ) (q : Row) :
    (run withDuration (start,rectangleEncode q)).valid := by
  change (run program (start,rectangleEncode q)).valid ∧
    (run publish (run program (start,rectangleEncode q)).val).valid
  rw [publish_run]
  exact ⟨program_valid start q,trivial⟩

theorem withDuration_work (start : ℕ) (q : Row) :
    (run withDuration (start,rectangleEncode q)).work≤400008*(exponent q.a q.e+1) := by
  have bound:=program_work start q
  change (run program (start,rectangleEncode q)).work+
    (run publish (run program (start,rectangleEncode q)).val).work+1≤_
  rw [publish_run]
  dsimp only [Bill.work]
  omega

theorem withDuration_peak (start : ℕ) (q : Row) :
    (run withDuration (start,rectangleEncode q)).peak ≤
      start+20000*(exponent q.a q.e+1)+4*(q.a+q.e)+2 := by
  have bound:=program_peak start q
  change max (max (run program (start,rectangleEncode q)).peak
    (run publish (run program (start,rectangleEncode q)).val).peak) 0≤_
  rw [publish_run,program_value]
  change max (max (run program (start,rectangleEncode q)).peak
    (max 28 (28*(352*exponent q.a q.e+330)))) 0≤_
  exact max_le (max_le bound (max_le (by omega) (by omega))) (Nat.zero_le _)

end
end ExactFourierCircuits.DFTModelCacheReplayRectangle
