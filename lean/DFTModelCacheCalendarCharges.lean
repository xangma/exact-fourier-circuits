import DFTModelCacheCalendarGeometry
import DFTModelCacheCalendarValid

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode append appendValue comp_work fork_work)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node DFTModelCacheTraversal.singleton append sequence childDuration

theorem direct_work (v o t : ℕ) : (run direct (v,(o,t))).work≤100 := by
  rw [direct,fork_work,comp_work,DFTModelCacheTraversal.singleton_run]
  have a:(run directCount (v,(o,t))).work=17:=rfl
  have b:(run directEvent (v,(o,t))).work=21:=rfl
  rw [a,b]
  change 17+(21+9+1)+1≤100
  omega

theorem prepare_work (v o t : ℕ) : (run prepare (v,(o,t))).work=
    (run DFTModelCacheDescriptor.node (v,o)).work+8 := by
  change 1+(5+(run DFTModelCacheDescriptor.node (v,o)).work+1)+1=_
  omega

theorem maximum_work {s : Ty} (f g : Prog false s w) (x : s.T) :
    (run (maximum f g) x).work≤2*((run f x).work+(run g x).work)+4 := by
  rw [maximum,DFTModelCacheTraversal.ifz_work]
  change (run f x).work+(run g x).work+3+
    (if (run (nat .lt f g) x).val=0 then (run f x).work else (run g x).work)+1≤_
  split_ifs <;>omega

theorem childDuration_work (x : Joined.T) : (run childDuration x).work≤24 := by
  rw [childDuration]
  have h:=maximum_work (.comp left (.atom .fst)) (.comp right (.atom .fst)) x
  have a:(run (.comp left (.atom .fst)) x).work=5:=rfl
  have b:(run (.comp right (.atom .fst)) x).work=5:=rfl
  rw [a,b] at h
  exact h

theorem correction_work (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).work≤
    (run sequence (t+max l.1 r.1,ofList (L.map rectangleEncode))).work+41 := by
  rw [correction,comp_work,fork_work]
  have hv:(run (.fork correctionStart (.comp (.atom .fst) nodeRows))
    (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
    (t+max l.1 r.1,ofList (L.map rectangleEncode)):=by
      change (t+(run childDuration _).val,_)=_
      rw [childDuration_value]
      rfl
  rw [hv]
  have hc:=childDuration_work (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))
  change (7+(run childDuration _).work+3)+5+1+_+1≤_
  omega

attribute [local irreducible] correction

theorem finishedEvents_work (x : Finished.T) :
    (run finishedEvents x).work≤
      29*(x.1.2.1.2.len+x.1.2.2.2.len)+29*(x.1.2.1.2.len+x.1.2.2.2.len+x.2.2.len)+45 := by
  have h1:=DFTModelCacheTraversal.append_work Event9 x.1.2.1.2 x.1.2.2.2
  have h2:=DFTModelCacheTraversal.append_work Event9
    (appendValue Event9 x.1.2.1.2 x.1.2.2.2) x.2.2
  rw [finishedEvents,comp_work,fork_work,comp_work,fork_work]
  have hv:(run (.fork firstEvents secondEvents) x).val=(x.1.2.1.2,x.1.2.2.2):=rfl
  have hv2:(run (.fork (.comp (.fork firstEvents secondEvents) (append Event9)) parentEvents) x).val=
    (appendValue Event9 x.1.2.1.2 x.1.2.2.2,x.2.2):=by
      change ((run (append Event9) _).val,_)=_
      rw [DFTModelCacheTraversal.append_value]
      rfl
  rw [hv,hv2]
  have a:(run firstEvents x).work=7:=rfl
  have b:(run secondEvents x).work=7:=rfl
  have c:(run parentEvents x).work=3:=rfl
  rw [a,b,c]
  change (run (append Event9) (appendValue Event9 x.1.2.1.2 x.1.2.2.2,x.2.2)).work≤
    29*((appendValue Event9 x.1.2.1.2 x.1.2.2.2).len+x.2.2.len)+12 at h2
  change (run (append Event9) (appendValue Event9 x.1.2.1.2 x.1.2.2.2,x.2.2)).work≤
    29*(x.1.2.1.2.len+x.1.2.2.2.len+x.2.2.len)+12 at h2
  omega

theorem finish_work (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run finish (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).work≤
    (run sequence (t+max l.1 r.1,ofList (L.map rectangleEncode))).work+
      29*(l.2.len+r.2.len)+29*(l.2.len+r.2.len+L.length)+150 := by
  have cor:=correction_work v o t b L l r
  rw [finish,comp_work,fork_work,fork_work]
  have hv:(run (.fork (.atom .id) correction) (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
      ((((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r)),
        (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val):=rfl
  rw [hv]
  change 1+(run correction _).work+1+((run finishedDuration _).work+(run finishedEvents _).work+1)+1≤_
  rw [correction_value]
  have he:=finishedEvents_work
    ((((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))
  have hd:(run finishedDuration
    ((((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))).work≤32 := by
    have hc:=childDuration_work (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))
    change ((1+(run childDuration (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).work+1)+3+3)≤_
    omega
  change (run finishedEvents
    ((((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r)),
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)))).work≤
      29*(l.2.len+r.2.len)+29*(l.2.len+r.2.len+((sequenceRows (t+max l.1 r.1) L).map eventEncode).length)+45 at he
  rw [List.length_map,sequenceRows_length] at he
  omega

end
end ExactFourierCircuits.DFTModelCacheCalendar
