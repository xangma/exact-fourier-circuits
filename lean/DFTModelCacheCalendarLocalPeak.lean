import DFTModelCacheCalendarBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode append appendValue comp_peak fork_peak)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node DFTModelCacheTraversal.singleton append sequence

theorem direct_peak (v o t : ℕ) : (run direct (v,(o,t))).peak ≤ 15*(v+1)^2+14 := by
  rw [direct,fork_peak,comp_peak,DFTModelCacheTraversal.singleton_run]
  have he:(run directEvent (v,(o,t))).peak=0:=rfl
  rw [he]
  simp only [directCount,nat,width,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_le_iff]
  have hs:v-1 ≤ v:=Nat.sub_le _ _
  repeat' apply And.intro
  all_goals nlinarith

 theorem prepare_peak (v o t : ℕ) : (run prepare (v,(o,t))).peak=
    (run DFTModelCacheDescriptor.node (v,o)).peak := by
  rw [prepare,fork_peak,comp_peak]
  change max 0 (max 0 (run DFTModelCacheDescriptor.node (v,o)).peak)=_
  simp only [zero_max]

 theorem childDuration_peak (nf : NodeFrame.T) (l r : Output.T) :
    (run childDuration (nf,(l,r))).peak ≤ 1 := by
  by_cases h:l.1<r.1 <;>
    simp [childDuration,maximum,nat,left,right,run,Code.run,Atom.run,NOp.run,
      Bill.word,Bill.one,Bill.pass,Bill.pay,h]

attribute [local irreducible] childDuration correction

theorem correctionStart_peak (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run correctionStart (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).peak ≤
      max 1 (t+max l.1 r.1) := by
  have cp:=childDuration_peak ((v,(o,t)),(b,ofList (L.map rectangleEncode))) l r
  simp only [correctionStart,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,
    nodeStart,start]
  simp only [run] at cp
  rw [show (Code.run childDuration () (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=max l.1 r.1 from childDuration_value _ _ _]
  simp only [max_le_iff]
  omega

attribute [local irreducible] correctionStart

theorem correction_peak (v o t b R : ℕ) (L : List Row) (l r : Output.T)
    (ha:∀q∈L,q.a+q.e ≤ 2*R) :
    (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).peak ≤
      t+max l.1 r.1+(L.length+1)*(100000*(2*R+1)) := by
  have cp:=correctionStart_peak v o t b L l r
  have cv:(run correctionStart (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=t+max l.1 r.1:=by
    rw [correctionStart]
    change t+(run childDuration _).val=_
    rw [childDuration_value]
  have arg:(run (.fork correctionStart (.comp (.atom .fst) nodeRows))
    (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
      (t+max l.1 r.1,ofList (L.map rectangleEncode)):=by
    change ((run correctionStart _).val,_)=_
    rw [cv]
    rfl
  have sq:=sequence_peak (t+max l.1 r.1) L R ha
  have unit:1 ≤ (L.length+1)*(100000*(2*R+1)):=by
    have h:=Nat.mul_le_mul (show 1 ≤ L.length+1 by omega) (show 1 ≤ 100000*(2*R+1) by omega)
    simpa only [Nat.one_mul] using h
  rw [correction,comp_peak,fork_peak,arg]
  apply max_le
  · apply max_le
    · exact cp.trans (max_le (by omega) (by omega))
    · change 0 ≤ _
      omega
  · exact sq

 theorem finishedDuration_peak (nf : NodeFrame.T) (l r parent : Output.T) :
    (run finishedDuration ((nf,(l,r)),parent)).peak ≤ max 1 (max l.1 r.1+parent.1) := by
  have cp:=childDuration_peak nf l r
  simp only [finishedDuration,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  simp only [run] at cp
  rw [show (Code.run childDuration () (nf,(l,r))).val=max l.1 r.1 from childDuration_value _ _ _]
  simp only [max_le_iff]
  omega

 theorem finishedEvents_peak (x : Finished.T) :
    (run finishedEvents x).peak ≤ x.1.2.1.2.len+x.1.2.2.2.len+x.2.2.len := by
  have h1:=DFTModelCacheTraversal.append_peak Event9 x.1.2.1.2 x.1.2.2.2
  have h2:=DFTModelCacheTraversal.append_peak Event9
    (appendValue Event9 x.1.2.1.2 x.1.2.2.2) x.2.2
  rw [finishedEvents,comp_peak,fork_peak,comp_peak,fork_peak]
  have hv:(run (.fork firstEvents secondEvents) x).val=(x.1.2.1.2,x.1.2.2.2):=rfl
  have hv2:(run (.fork (.comp (.fork firstEvents secondEvents) (append Event9)) parentEvents) x).val=
      (appendValue Event9 x.1.2.1.2 x.1.2.2.2,x.2.2):=by
    change ((run (append Event9) _).val,_)=_
    rw [DFTModelCacheTraversal.append_value]
    rfl
  rw [hv,hv2]
  have a:(run firstEvents x).peak=0:=rfl
  have b:(run secondEvents x).peak=0:=rfl
  have c:(run parentEvents x).peak=0:=rfl
  rw [a,b,c]
  change (run (append Event9) (appendValue Event9 x.1.2.1.2 x.1.2.2.2,x.2.2)).peak ≤
    x.1.2.1.2.len+x.1.2.2.2.len+x.2.2.len at h2
  exact max_le (max_le (max_le (max_le (by omega) (by omega)) (by omega)) (by omega)) h2

end
end ExactFourierCircuits.DFTModelCacheCalendar
