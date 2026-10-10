import DFTModelCacheCalendarProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode append appendValue singleton)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node DFTModelCacheTraversal.singleton sequence prefixProgram

 theorem code_comp_value {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r t u)
    (h : Handler r) (x : s.T) : (Code.run (.comp f g) h x).val=(Code.run g h (Code.run f h x).val).val := rfl
 theorem code_fork_value {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r s u)
    (h : Handler r) (x : s.T) : (Code.run (.fork f g) h x).val=((Code.run f h x).val,(Code.run g h x).val) := rfl
 theorem code_ifz_value {r : Port} {s t : Ty} (q : Code false r s w) (f g : Code false r s t)
    (h : Handler r) (x : s.T) : (Code.run (.ifz q f g) h x).val=
      if (Code.run q h x).val=0 then (Code.run f h x).val else (Code.run g h x).val := by
  change (if (Code.run q h x).val=0 then Code.run f h x else Code.run g h x).val=_
  split_ifs <;>rfl
 theorem code_import_value {r : Port} {s t : Ty} (f : Prog false s t) (h : Handler r) (x : s.T) :
    (Code.run (.importClosed f) h x).val=(run f x).val := rfl

 theorem singleton_list (q : Ty) (x : q.T) : (run (singleton q) x).val=ofList [x] := by
  rw [DFTModelCacheTraversal.singleton_run]
  refine DFTModelCacheTraversal.tape_ext (Tape.tab 1 (fun _=>x)) (ofList [x]) q.blank rfl ?_
  intro j hj
  change j<1 at hj
  have hz:j=0:=by omega
  subst j
  rfl

 theorem direct_value (v o t : ℕ) : (run direct (v,(o,t))).val=
    (directDuration v,ofList [eventEncode ⟨t,.direct v o⟩]) := by
  change (directDuration v,(run (singleton Event9) (t,(0,(v,(o,(0,(0,(0,(0,0))))))))).val)=_
  rw [singleton_list]
  rfl

 theorem prepare_value (v o t : ℕ) : (run prepare (v,(o,t))).val=
    ((v,(o,t)),(selected v,ofList ((currentRows (⟨v,o,0,0⟩:Task)).map rectangleEncode))) := by
  change ((v,(o,t)),(run DFTModelCacheDescriptor.node (v,o)).val)=_
  rw [DFTModelCacheDescriptor.node_value]
  rfl

 theorem maximum_value {s : Ty} (f g : Prog false s w) (x : s.T) :
    (run (maximum f g) x).val=max (run f x).val (run g x).val := by
  rw [maximum]
  change (Code.run (.ifz (nat .lt f g) f g) () x).val=_
  rw [code_ifz_value]
  change (if (if (run f x).val<(run g x).val then 1 else 0)=0
    then (run f x).val else (run g x).val)=_
  let a : ℕ := (run f x).val
  let b : ℕ := (run g x).val
  change (if (if a<b then 1 else 0)=0 then a else b)=max a b
  by_cases hab:a<b
  · simp [hab,max_eq_right hab.le]
  · simp [hab,max_eq_left (Nat.le_of_not_gt hab)]

 theorem childDuration_value (nf : NodeFrame.T) (l r : Output.T) :
    (run childDuration (nf,(l,r))).val=max l.1 r.1 := by
  rw [childDuration,maximum_value]
  rfl

attribute [local irreducible] childDuration append correction

 theorem correction_value (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
      (rectanglesDuration L,ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode)) := by
  rw [correction]
  change (run sequence ((run correctionStart (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val,
    ofList (L.map rectangleEncode))).val=_
  have ht:(run correctionStart (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
      t+max l.1 r.1 := by
    change t+(run childDuration (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=_
    rw [childDuration_value]
  rw [ht,sequence_value]

 theorem finish_value (v o t b : ℕ) (L : List Row) (l r : Output.T) :
    (run finish (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val=
      (max l.1 r.1+rectanglesDuration L,
       appendValue Event9 (appendValue Event9 l.2 r.2)
         (ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode))) := by
  change (run (.fork finishedDuration finishedEvents)
    ((((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r)),
      (run correction (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val)).val=_
  rw [correction_value]
  change ((run childDuration (((v,(o,t)),(b,ofList (L.map rectangleEncode))),(l,r))).val+rectanglesDuration L,
    (run (append Event9) ((run (append Event9) (l.2,r.2)).val,
      ofList ((sequenceRows (t+max l.1 r.1) L).map eventEncode))).val)=_
  rw [childDuration_value,DFTModelCacheTraversal.append_value,DFTModelCacheTraversal.append_value]

 theorem leftInput_value (nf : NodeFrame.T) : (run leftInput nf).val=
    (nf.1.1/2,(nf.1.2.1,nf.1.2.2)) := rfl
 theorem rightInput_value (nf : NodeFrame.T) : (run rightInput nf).val=
    (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2)) := rfl
 theorem directCode_value (h : Handler RecPort) (nf : NodeFrame.T) :
    (directCode.run h nf).val=(run direct nf.1).val := rfl
 theorem splitCode_value (h : Handler RecPort) (nf : NodeFrame.T) :
    (splitCode.run h nf).val=(run finish (nf,
      ((h (nf.1.1/2,(nf.1.2.1,nf.1.2.2))).val,
       (h (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2))).val))).val := by
  change (run finish (nf,((h (run leftInput nf).val).val,(h (run rightInput nf).val).val))).val=_
  rw [leftInput_value,rightInput_value]

 theorem branch_direct (h : Handler RecPort) (v o t b : ℕ) (rows : Tape Row7.T)
    (hd:v<2 ∨ b=0) :
    (branch.run h ((v,(o,t)),(b,rows))).val=(run direct (v,(o,t))).val := by
  rw [branch,code_ifz_value]
  have cmp:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,rows))).val=
      if v<2 then 1 else 0 := rfl
  rw [cmp]
  by_cases hv:v<2
  · simp only [hv,ite_true,Nat.one_ne_zero,ite_false]
    exact directCode_value h _
  · simp only [hv,ite_false,ite_true]
    rw [code_ifz_value]
    have hb:b=0:=by omega
    subst b
    exact directCode_value h _

 theorem branch_split (h : Handler RecPort) (v o t b : ℕ) (rows : Tape Row7.T)
    (hd:¬(v<2 ∨ b=0)) :
    (branch.run h ((v,(o,t)),(b,rows))).val=
      (run finish (((v,(o,t)),(b,rows)),
        ((h (v/2,(o,t))).val,(h (v-v/2,(o+v/2,t))).val))).val := by
  rw [branch,code_ifz_value]
  have cmp:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,rows))).val=
      if v<2 then 1 else 0 := rfl
  have hv:¬v<2:=by omega
  have hb:b≠0:=by omega
  rw [cmp]
  simp only [hv,ite_false,ite_true]
  rw [code_ifz_value]
  change (if b=0 then _ else _)=_
  rw [ite_eq_right hb,splitCode_value]

 theorem body_direct (h : Handler RecPort) (v o t : ℕ) (hd:v<2 ∨ selected v=0) :
    (body.run h (v,(o,t))).val=(run direct (v,(o,t))).val := by
  rw [body,code_comp_value,code_import_value,prepare_value]
  exact branch_direct h v o t _ _ hd

 theorem body_split (h : Handler RecPort) (v o t : ℕ) (hd:¬(v<2 ∨ selected v=0)) :
    (body.run h (v,(o,t))).val=
      (run finish (((v,(o,t)),(selected v,ofList ((rows v o (selected v)).map rectangleEncode))),
        ((h (v/2,(o,t))).val,(h (v-v/2,(o+v/2,t))).val))).val := by
  rw [body,code_comp_value,code_import_value,prepare_value,branch_split _ _ _ _ _ _ hd]
  simp only [currentRows,hd,ite_false]

 theorem sourceTree_eq (v o : ℕ) : sourceTree v o=
    if v<2 ∨ selected v=0 then .direct v o else
      .split v o (selected v) (sourceTree (v/2) o) (sourceTree (v-v/2) (o+v/2)) := by
  rw [sourceTree,UniformBalancedToeplitz.plan]
  split <;>rfl

 theorem expected_direct (v o t : ℕ) (hd:v<2 ∨ selected v=0) :
    expected v o t=(directDuration v,ofList [eventEncode ⟨t,.direct v o⟩]) := by
  rw [expected,sourceTree_eq,ite_eq_left hd]
  rfl

 theorem expected_split (v o t : ℕ) (hd:¬(v<2 ∨ selected v=0)) :
    expected v o t=
      (max (expected (v/2) o t).1 (expected (v-v/2) (o+v/2) t).1+
          rectanglesDuration (rows v o (selected v)),
       appendValue Event9
        (appendValue Event9 (expected (v/2) o t).2 (expected (v-v/2) (o+v/2) t).2)
        (ofList ((sequenceRows (t+max (expected (v/2) o t).1 (expected (v-v/2) (o+v/2) t).1)
          (rows v o (selected v))).map eventEncode))) := by
  unfold expected
  rw [sourceTree_eq v o,ite_eq_right hd]
  simp only [treeDuration,treeTimed,List.map_append]
  rw [DFTModelCacheTraversal.append_lists,DFTModelCacheTraversal.append_lists]

end
end ExactFourierCircuits.DFTModelCacheCalendar
